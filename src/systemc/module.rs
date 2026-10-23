//! SystemC modules and `sc_main` → SystemVerilog modules.
//!
//! A module class becomes an SV module: ports, signals and plain members
//! become ports and variables; the constructor is split into structure
//! (child instances, port bindings, process registrations — all static in
//! SystemC) and elaboration code (an `initial` block at time 0); member
//! functions become tasks/functions; each registered process becomes a
//! wrapper `initial` block that waits for the first `sc_start`
//! (IEEE 1666-2023 §4.3, §5.2).

use std::collections::{BTreeMap, BTreeSet};

use super::build::*;
use super::lower::*;
use super::types::*;
use crate::ast::decl::{ClassItem, ModuleItem};
use crate::ast::expr::{BinaryOp, Expression, UnaryOp};
use crate::ast::module::ModuleDeclaration;
use crate::ast::stmt::{Edge, JoinType, Statement, StatementKind};
use crate::ast::types::PortDirection;
use crate::sv_parser::systemc::ast as sc;
use crate::sv_parser::systemc::classify::ScObjectKind;
use crate::sv_parser::systemc::token::ScSpan;

/// What a parent needs to know about a module to instantiate it.
#[derive(Debug, Clone, Default)]
pub struct ModIface {
    /// Ports in declaration order (C++ name, kind).
    pub ports: Vec<(String, SymKind)>,
    pub members: BTreeMap<String, Sym>,
    /// SV parameter names: template value parameters, then the extra
    /// constructor parameters.
    pub template_params: Vec<String>,
    pub ctor_params: Vec<String>,
}

/// A registered process before lowering.
struct ProcSpec {
    kind: sc::ProcessKind,
    func: String,
    span: ScSpan,
    sens: Vec<(Option<Edge>, Expression, String)>,
    clock: Option<(Edge, Expression)>,
    dont_init: bool,
    resets: Vec<(bool, Expression, Expression, String)>,
}

/// A child instance being assembled.
struct Inst {
    module: String,
    sv: String,
    params: Vec<(String, Expression)>,
    conns: Vec<(String, Expression)>,
}

/// Transport methods registered on a target socket.
#[derive(Default)]
struct TargetReg {
    b_transport: Option<String>,
    transport_dbg: Option<String>,
    get_direct_mem_ptr: Option<String>,
}

#[derive(Default)]
struct Structure {
    procs: Vec<ProcSpec>,
    insts: Vec<Inst>,
    /// Elaboration statements (time 0, before processes start).
    elab: Vec<Statement>,
    targets: BTreeMap<String, TargetReg>,
    clocks: Vec<(String, Vec<sc::Expr>, ScSpan)>,
}

pub struct ModuleLowering<'l, 'a> {
    pub lw: &'l mut Lw<'a>,
    pub ifaces: &'l BTreeMap<String, ModIface>,
    /// Initializer list of the constructor being lowered (sc_vector sizes).
    pub ctor_inits: Vec<&'a sc::MemInit>,
    /// Per process: dont_initialize(), entry function, async resets.
    dont_init: Vec<bool>,
    proc_funcs: Vec<String>,
    async_resets: Vec<Vec<(Expression, Expression)>>,
    /// Clock → its value before the first edge.
    clock_init: BTreeMap<String, u64>,
    /// FIFO channel → its capacity.
    fifo_size: BTreeMap<String, Expression>,
}

impl<'l, 'a> ModuleLowering<'l, 'a> {
    pub fn new(lw: &'l mut Lw<'a>, ifaces: &'l BTreeMap<String, ModIface>) -> Self {
        ModuleLowering {
            lw,
            ifaces,
            ctor_inits: Vec::new(),
            dont_init: Vec::new(),
            proc_funcs: Vec::new(),
            async_resets: Vec::new(),
            clock_init: BTreeMap::new(),
            fifo_size: BTreeMap::new(),
        }
    }
}

fn port_dir(kind: &SymKind) -> Option<PortDirection> {
    match kind {
        SymKind::InPort => Some(PortDirection::Input),
        SymKind::OutPort => Some(PortDirection::Output),
        // SV forbids `inout` variables; an sc_inout is an output its owner
        // also reads.
        SymKind::InOutPort => Some(PortDirection::Output),
        _ => None,
    }
}

fn is_valid_ident(s: &str) -> bool {
    let mut c = s.chars();
    c.next()
        .is_some_and(|f| f.is_ascii_alphabetic() || f == '_')
        && c.all(|x| x.is_ascii_alphanumeric() || x == '_')
}

/// The constructor of a module class: in the body, or `T::T` outside it.
pub fn find_ctor<'a>(
    lw: &Lw<'a>,
    class: &'a sc::ClassDecl,
    name: &str,
) -> Option<(usize, &'a sc::FunctionDecl)> {
    let in_class: Vec<&sc::FunctionDecl> = class
        .members
        .iter()
        .filter_map(|m| match m {
            sc::Member::Constructor(f) => Some(f),
            _ => None,
        })
        .collect();
    if let Some(f) = in_class.iter().find(|f| f.body.is_some()) {
        return Some((lw.tu, f));
    }
    if let Some(defs) = lw.prog.out_of_class.get(name)
        && let Some((tu, f)) = defs.iter().find(|(_, f)| f.base_name() == name)
    {
        return Some((*tu, f));
    }
    in_class.first().map(|f| (lw.tu, *f))
}

/// The extra (non-`sc_module_name`) constructor parameters.
fn ctor_extra_params(ctor: &sc::FunctionDecl) -> Vec<&sc::Param> {
    ctor.params
        .iter()
        .filter(|p| {
            p.ty.name()
                .is_none_or(|q| q.last_name() != "sc_module_name")
        })
        .collect()
}

impl<'l, 'a> ModuleLowering<'l, 'a> {
    // ---- interface ----------------------------------------------------------

    /// Classify a module's data members (ports, signals, channels, child
    /// instances, sockets, plain variables).
    pub fn iface(
        &mut self,
        class: &'a sc::ClassDecl,
        tparams: &[sc::TemplateParam],
    ) -> R<ModIface> {
        let mut iface = ModIface::default();
        for tp in tparams {
            match tp {
                sc::TemplateParam::Value { name: Some(n), .. } => {
                    iface.template_params.push(n.name.clone());
                    self.lw
                        .env
                        .tparams
                        .insert(n.name.clone(), TParam::Value(n.name.clone()));
                }
                sc::TemplateParam::Type { span, .. } | sc::TemplateParam::Value { span, .. } => {
                    return self.lw.err(
                        *span,
                        "type template parameters of modules are not supported in simulation",
                    );
                }
            }
        }
        let name = class.name_str().unwrap_or_default().to_string();
        self.ctor_inits.clear();
        if let Some((_, ctor)) = find_ctor(self.lw, class, &name) {
            self.ctor_inits = ctor.initializers.iter().collect();
            for p in ctor_extra_params(ctor) {
                if let Some(n) = &p.name {
                    iface.ctor_params.push(n.name.clone());
                    let ty = self.lw.ty(&p.ty, p.span)?;
                    iface.members.insert(
                        n.name.clone(),
                        Sym {
                            kind: SymKind::Var,
                            ty,
                            sv: n.name.clone(),
                        },
                    );
                }
            }
        }
        for m in &class.members {
            let sc::Member::Field(v) = m else { continue };
            if v.specifiers.is_static {
                continue;
            }
            for d in &v.declarators {
                let sym = self.member_sym(v, d)?;
                if let Some(sym) = sym {
                    if port_dir(&sym.kind).is_some() {
                        iface.ports.push((d.name.name.clone(), sym.kind.clone()));
                    }
                    iface.members.insert(d.name.name.clone(), sym);
                }
            }
        }
        Ok(iface)
    }

    /// The vector size of an `sc_vector` member from its initializer
    /// (`v{"v", N}`, `SC_NAMED(v, N)`) or constructor init list.
    fn vector_size(&self, d: &sc::Declarator, ctor_inits: &[&sc::MemInit]) -> Option<Expression> {
        let args = match &d.init {
            Some(sc::Initializer::Brace(a) | sc::Initializer::Paren(a)) => Some(a.as_slice()),
            _ => ctor_inits
                .iter()
                .find(|mi| mi.name.last_name() == d.name.name)
                .map(|mi| mi.args.as_slice()),
        }?;
        let n = args.get(1)?;
        self.lw.const_eval(n).map(int).or_else(|| {
            n.as_name()
                .and_then(|q| match self.lw.env.tparams.get(q.last_name()) {
                    Some(TParam::Value(sv)) => Some(ident(sv)),
                    _ => None,
                })
        })
    }

    fn member_sym(&mut self, v: &sc::VarDecl, d: &sc::Declarator) -> R<Option<Sym>> {
        let name = d.name.name.clone();
        let kind = ScObjectKind::of(&v.ty);
        let consts = |e: &sc::Expr| self.lw.const_eval(e);
        let q = v.ty.name();
        let payload = |lw: &Lw| -> R<Ty> {
            let q = q.expect("library object has a name");
            payload_ty(q, &lw.env, &consts).or_else(|m| lw.err(d.span, m))
        };
        let (k, ty) = match &kind {
            ScObjectKind::InPort => (SymKind::InPort, payload(self.lw)?),
            ScObjectKind::OutPort => (SymKind::OutPort, payload(self.lw)?),
            ScObjectKind::InOutPort => (SymKind::InOutPort, payload(self.lw)?),
            ScObjectKind::Signal | ScObjectKind::Buffer => (SymKind::Signal, payload(self.lw)?),
            ScObjectKind::Clock => (SymKind::Clock, Ty::Bool),
            ScObjectKind::Event => (SymKind::Event, Ty::Event),
            ScObjectKind::Fifo => (SymKind::Fifo, Ty::Mailbox(Box::new(payload(self.lw)?))),
            ScObjectKind::FifoIn => (SymKind::FifoIn, Ty::Mailbox(Box::new(payload(self.lw)?))),
            ScObjectKind::FifoOut => (SymKind::FifoOut, Ty::Mailbox(Box::new(payload(self.lw)?))),
            ScObjectKind::InitiatorSocket => (
                SymKind::InitSocket,
                Ty::Class("scrt_initiator_socket".into()),
            ),
            ScObjectKind::TargetSocket => (
                SymKind::TargetSocket,
                Ty::Class("scrt_target_socket".into()),
            ),
            ScObjectKind::Vector(inner) => {
                let elem_kind = match inner.as_ref() {
                    ScObjectKind::InPort => SymKind::InPort,
                    ScObjectKind::OutPort => SymKind::OutPort,
                    ScObjectKind::InOutPort => SymKind::InOutPort,
                    ScObjectKind::Signal => SymKind::Signal,
                    _ => {
                        return self.lw.err(
                            d.span,
                            "sc_vector of this object is not supported in simulation",
                        );
                    }
                };
                let elem_q = match q.and_then(|q| q.last_args()).and_then(|a| a.first()) {
                    Some(sc::TemplateArg::Type(t)) => t.name().cloned(),
                    _ => None,
                };
                let Some(elem_q) = elem_q else {
                    return self.lw.err(d.span, "sc_vector element type expected");
                };
                let ety = payload_ty(&elem_q, &self.lw.env, &consts)
                    .or_else(|m| self.lw.err(d.span, m))?;
                let size = self.vector_size(d, &self.current_ctor_inits(v));
                let Some(size) = size else {
                    return self.lw.err(d.span, "sc_vector size must be a constant given at the declaration or in the constructor's initializer list");
                };
                (elem_kind, Ty::Array(Box::new(ety), size))
            }
            ScObjectKind::Port | ScObjectKind::Export | ScObjectKind::AnalysisPort => {
                return self.lw.err(
                    d.span,
                    "sc_port/sc_export/analysis ports are not supported in simulation yet",
                );
            }
            ScObjectKind::Other => {
                if let Some(q) = q {
                    if self.lw.prog.is_module(q.last_name()) {
                        return Ok(Some(Sym {
                            kind: SymKind::Instance(q.last_name().to_string()),
                            ty: Ty::Void,
                            sv: name,
                        }));
                    }
                    if matches!(q.last_name(), "sc_trace_file") {
                        return Ok(Some(Sym {
                            kind: SymKind::TraceFile,
                            ty: Ty::Void,
                            sv: name,
                        }));
                    }
                    if matches!(q.last_name(), "peq_with_get" | "peq_with_cb_and_phase") {
                        return self.lw.err(
                            d.span,
                            "payload event queues (AT TLM) are not supported in simulation",
                        );
                    }
                }
                let ty = self.lw.decl_ty(&v.ty, d)?;
                let boxed = self.lw.prog.address_taken(&name, self.lw.tu);
                let k = match (&ty, boxed) {
                    (Ty::Array(..), true) => SymKind::BoxedArr,
                    (t, true) if t.is_scalar_bits() => SymKind::Boxed,
                    _ => SymKind::Var,
                };
                (k, ty)
            }
        };
        Ok(Some(Sym {
            kind: k,
            ty,
            sv: name,
        }))
    }

    fn current_ctor_inits(&self, _v: &sc::VarDecl) -> Vec<&'a sc::MemInit> {
        self.ctor_inits.clone()
    }

    // ---- module -------------------------------------------------------------

    pub fn lower_module(
        &mut self,
        name: &str,
        class: &'a sc::ClassDecl,
        iface: &ModIface,
    ) -> R<ModuleDeclaration> {
        self.lw.m = ModCtx {
            name: name.to_string(),
            syms: iface.members.clone(),
            ..Default::default()
        };
        let ctor = find_ctor(self.lw, class, name);
        let mut s = Structure::default();
        let mut params = Vec::new();
        for tp in &iface.template_params {
            params.push(param_decl(
                atom_t(crate::ast::types::IntegerAtomType::Int, false),
                tp,
                int(0),
            ));
        }
        // Defaults of template parameters.
        if let Some((_, _, tps)) = self.lw.prog.classes.get(name) {
            for (i, tp) in tps.iter().enumerate() {
                if let sc::TemplateParam::Value {
                    default: Some(e), ..
                } = tp
                    && let Some(v) = self.lw.const_eval(e)
                {
                    params[i] = param_decl(
                        atom_t(crate::ast::types::IntegerAtomType::Int, false),
                        &iface.template_params[i],
                        int(v),
                    );
                }
            }
        }
        let defs = self.member_function_defs(class, name);
        self.register_sigs(&defs)?;
        self.lw.f = FnCtx {
            scopes: vec![BTreeMap::new()],
            ..Default::default()
        };
        if let Some((tu, c)) = ctor {
            let saved_tu = self.lw.tu;
            self.lw.tu = tu;
            for p in ctor_extra_params(c) {
                let Some(n) = &p.name else { continue };
                let ty = self.lw.ty(&p.ty, p.span)?;
                let default = p
                    .default
                    .as_ref()
                    .and_then(|e| self.lw.const_eval(e))
                    .unwrap_or(0);
                params.push(param_decl(sv_scalar_type(&ty), &n.name, int(default)));
            }
            for mi in &c.initializers {
                if let Err(e) = self.mem_init(mi, &mut s) {
                    self.lw.record(e);
                }
            }
            if let Some(b) = &c.body {
                self.walk(&b.stmts, &mut s);
            }
            self.lw.tu = saved_tu;
        }
        // Value members never created explicitly are default-constructed.
        for (n, sym) in &iface.members {
            if let SymKind::Instance(module) = &sym.kind
                && !s.insts.iter().any(|i| i.sv == *n)
            {
                let decl_is_value = class.members.iter().any(|m| match m {
                    sc::Member::Field(v) => v
                        .declarators
                        .iter()
                        .any(|d| d.name.name == *n && d.ptr_ops.is_empty()),
                    _ => false,
                });
                if decl_is_value {
                    s.insts.push(Inst {
                        module: module.clone(),
                        sv: n.clone(),
                        params: self.type_template_params(class, n)?,
                        conns: Vec::new(),
                    });
                }
            }
        }
        // In-class clock members with constructor arguments.
        for m in &class.members {
            let sc::Member::Field(v) = m else { continue };
            if ScObjectKind::of(&v.ty) != ScObjectKind::Clock {
                continue;
            }
            for d in &v.declarators {
                if let Some(sc::Initializer::Brace(a) | sc::Initializer::Paren(a)) = &d.init {
                    s.clocks.push((d.name.name.clone(), a.clone(), d.span));
                }
            }
        }
        let elab_decls = std::mem::take(&mut self.lw.f.decls);
        let elab_stmts = std::mem::take(&mut s.elab);
        self.register_procs(&s, class, name)?;
        let funcs = self.lower_bodies(defs)?;
        self.finish_module(
            name,
            params,
            &iface.ports,
            s,
            elab_decls,
            elab_stmts,
            funcs,
            None,
        )
    }

    fn type_template_params(
        &mut self,
        class: &sc::ClassDecl,
        member: &str,
    ) -> R<Vec<(String, Expression)>> {
        for m in &class.members {
            let sc::Member::Field(v) = m else { continue };
            if v.declarators.iter().any(|d| d.name.name == member)
                && let Some(q) = v.ty.name()
            {
                return self.template_args(q, v.span);
            }
        }
        Ok(Vec::new())
    }

    /// `child<8>` → `#(.W(8))`.
    fn template_args(
        &mut self,
        q: &sc::QualifiedName,
        span: ScSpan,
    ) -> R<Vec<(String, Expression)>> {
        let Some(args) = q.last_args() else {
            return Ok(Vec::new());
        };
        let Some(iface) = self.ifaces.get(q.last_name()) else {
            return Ok(Vec::new());
        };
        let mut out = Vec::new();
        for (i, a) in args.iter().enumerate() {
            let Some(pname) = iface.template_params.get(i) else {
                return self.lw.err(span, "too many template arguments");
            };
            let e = match a {
                sc::TemplateArg::Expr(e) => self.lw.expr(e)?.0,
                sc::TemplateArg::Type(t) => match t.name() {
                    Some(n) => {
                        self.lw
                            .expr(&sc::Expr {
                                kind: sc::ExprKind::Name(n.clone()),
                                span,
                            })?
                            .0
                    }
                    None => {
                        return self
                            .lw
                            .err(span, "a type template argument is not supported here");
                    }
                },
            };
            out.push((pname.clone(), e));
        }
        Ok(out)
    }

    fn mem_init(&mut self, mi: &sc::MemInit, s: &mut Structure) -> R<()> {
        let n = mi.name.last_name();
        if n == "sc_module" || n == "sc_channel" || n == "sc_behavior" {
            return Ok(());
        }
        let Some(sym) = self.lw.lookup(n) else {
            return self.lw.err(
                mi.span,
                format!("unknown member '{}' in initializer list", n),
            );
        };
        match &sym.kind {
            SymKind::Instance(module) => {
                let params =
                    self.ctor_args_params(module, mi.args.get(1..).unwrap_or(&[]), mi.span)?;
                let mut params = params;
                params.extend(self.type_template_params_by_name(n)?);
                s.insts.push(Inst {
                    module: module.clone(),
                    sv: sym.sv.clone(),
                    params,
                    conns: Vec::new(),
                });
            }
            SymKind::Clock => s.clocks.push((sym.sv.clone(), mi.args.clone(), mi.span)),
            SymKind::Var | SymKind::Boxed => {
                if let [a] = mi.args.as_slice() {
                    let (x, _) = self.lw.expr(a)?;
                    let target = self.lw.sym_read(&sym);
                    s.elab.push(assign(target, x));
                }
            }
            SymKind::Fifo => {
                if let Some(size) = mi.args.get(1) {
                    let (x, _) = self.lw.expr(size)?;
                    self.fifo_size.insert(sym.sv.clone(), x);
                }
            }
            // Name strings of ports, signals, sockets and vectors.
            _ => {}
        }
        Ok(())
    }

    fn type_template_params_by_name(&mut self, _member: &str) -> R<Vec<(String, Expression)>> {
        Ok(Vec::new())
    }

    /// Constructor arguments after the name → the child's SV parameters.
    fn ctor_args_params(
        &mut self,
        module: &str,
        args: &[sc::Expr],
        span: ScSpan,
    ) -> R<Vec<(String, Expression)>> {
        let Some(iface) = self.ifaces.get(module) else {
            return Ok(Vec::new());
        };
        let names = iface.ctor_params.clone();
        let mut out = Vec::new();
        for (i, a) in args.iter().enumerate() {
            let Some(p) = names.get(i) else {
                return self.lw.err(
                    span,
                    format!("too many constructor arguments for '{}'", module),
                );
            };
            out.push((p.clone(), self.lw.expr(a)?.0));
        }
        Ok(out)
    }

    /// Walk constructor (or sc_main) statements, separating structure from
    /// elaboration code; `for` loops that bind or register are unrolled.
    fn walk(&mut self, stmts: &[sc::Stmt], s: &mut Structure) {
        for st_ in stmts {
            if let Err(e) = self.walk_stmt(st_, s) {
                self.lw.record(e);
            }
        }
    }

    fn walk_stmt(&mut self, stmt: &sc::Stmt, s: &mut Structure) -> R<()> {
        use sc::Stmt as S;
        match stmt {
            S::ScProcess {
                kind,
                func,
                clock,
                span,
            } => {
                let clock = match clock {
                    Some(c) => {
                        let ev = self.lw.event_list(c)?;
                        let [e] = ev.as_slice() else {
                            return self.lw.err(*span, "SC_CTHREAD needs one clock edge");
                        };
                        Some((e.edge.unwrap_or(Edge::Posedge), e.expr.clone()))
                    }
                    None => None,
                };
                s.procs.push(ProcSpec {
                    kind: *kind,
                    func: func.name.clone(),
                    span: *span,
                    sens: Vec::new(),
                    clock,
                    dont_init: false,
                    resets: Vec::new(),
                });
                Ok(())
            }
            S::Sensitive { edge, items, span } => {
                for it in items {
                    let mut entry = self.sens_item(it)?;
                    match edge {
                        sc::SensitivityEdge::Pos => entry.0 = Some(Edge::Posedge),
                        sc::SensitivityEdge::Neg => entry.0 = Some(Edge::Negedge),
                        sc::SensitivityEdge::Any => {}
                    }
                    match s.procs.last_mut() {
                        Some(p) => p.sens.push(entry),
                        None => {
                            return self
                                .lw
                                .err(*span, "'sensitive' before any process registration");
                        }
                    }
                }
                Ok(())
            }
            S::DontInitialize(span) => match s.procs.last_mut() {
                Some(p) => {
                    p.dont_init = true;
                    Ok(())
                }
                None => self
                    .lw
                    .err(*span, "dont_initialize() before any process registration"),
            },
            S::ResetSignalIs {
                is_async,
                signal,
                level,
                span,
            } => {
                let (sig, _) = self.lw.expr(signal)?;
                let (lvl, _) = self.lw.expr(level)?;
                let name = signal
                    .as_name()
                    .map(|q| q.last_name().to_string())
                    .unwrap_or_default();
                match s.procs.last_mut() {
                    Some(p) => {
                        p.resets.push((*is_async, sig, lvl, name));
                        Ok(())
                    }
                    None => self
                        .lw
                        .err(*span, "reset_signal_is() before any process registration"),
                }
            }
            S::Block(b) => {
                self.walk(&b.stmts, s);
                Ok(())
            }
            S::Expr(e) => {
                if self.structural(e, s)? {
                    return Ok(());
                }
                let v = self.lw.stmt(stmt)?;
                s.elab.extend(v);
                Ok(())
            }
            S::Decl(v) if self.lw.m.tb => self.tb_decl(v, stmt, s),
            S::For { .. } if is_structural_loop(stmt) => self.unroll(stmt, s),
            _ => {
                let v = self.lw.stmt(stmt)?;
                s.elab.extend(v);
                Ok(())
            }
        }
    }

    /// One `sensitive << x` item.
    fn sens_item(&mut self, e: &sc::Expr) -> R<(Option<Edge>, Expression, String)> {
        let base_name = |e: &sc::Expr| -> String {
            match &e.kind {
                sc::ExprKind::Name(q) => q.last_name().to_string(),
                sc::ExprKind::Index { base, .. } => base
                    .as_name()
                    .map(|q| q.last_name().to_string())
                    .unwrap_or_default(),
                _ => String::new(),
            }
        };
        if let sc::ExprKind::Call { callee, args } = &e.kind
            && let sc::ExprKind::Member { base, name, .. } = &callee.kind
            && args.is_empty()
        {
            let edge = match name.ident.name.as_str() {
                "pos" | "posedge_event" => Some(Edge::Posedge),
                "neg" | "negedge_event" => Some(Edge::Negedge),
                "value_changed"
                | "value_changed_event"
                | "default_event"
                | "data_written_event" => None,
                other => {
                    return self
                        .lw
                        .err(e.span, format!("'{}' is not a sensitivity", other));
                }
            };
            let (x, _) = self.lw.expr(base)?;
            return Ok((edge, x, base_name(base)));
        }
        let (x, _) = self.lw.expr(e)?;
        Ok((None, x, base_name(e)))
    }

    /// Instance creation and binding statements.
    fn structural(&mut self, e: &sc::Expr, s: &mut Structure) -> R<bool> {
        use sc::ExprKind as K;
        // `child = new T("name", args…);`
        if let K::Assign {
            op: sc::AssignOp::Assign,
            lhs,
            rhs,
        } = &e.kind
        {
            if let (Some(q), K::New { ty, args, .. }) = (lhs.as_name(), &rhs.kind)
                && let Some(sym) = self.lw.lookup(q.last_name())
                && let SymKind::Instance(module) = &sym.kind
            {
                let cargs = args.as_deref().unwrap_or(&[]);
                let mut params =
                    self.ctor_args_params(module, cargs.get(1..).unwrap_or(&[]), e.span)?;
                if let Some(tq) = ty.name() {
                    params.extend(self.template_args(tq, e.span)?);
                }
                let sv = sym.sv.clone();
                s.insts.retain(|i| i.sv != sv);
                s.insts.push(Inst {
                    module: module.clone(),
                    sv,
                    params,
                    conns: Vec::new(),
                });
                return Ok(true);
            }
            return Ok(false);
        }
        let K::Call { callee, args } = &e.kind else {
            return Ok(false);
        };
        // Positional binding `child(a, b, c)`.
        if let Some(q) = callee.as_name() {
            if let Some(sym) = self.lw.lookup(q.last_name())
                && let SymKind::Instance(module) = &sym.kind
            {
                let ports = self
                    .ifaces
                    .get(module)
                    .map(|i| i.ports.clone())
                    .unwrap_or_default();
                for (i, a) in args.iter().enumerate() {
                    let Some((p, _)) = ports.get(i) else {
                        return self.lw.err(e.span, "too many positional port bindings");
                    };
                    let (x, _) = self.lw.expr(a)?;
                    self.connect(s, &sym.sv, p, x);
                }
                return Ok(true);
            }
            return Ok(false);
        }
        let K::Member { base, name, .. } = &callee.kind else {
            return Ok(false);
        };
        let m = name.ident.name.as_str();
        // `child->port(x)` / `child.port(x)`.
        if let Some((inst, module)) = self.instance_of(base) {
            if let [a] = args.as_slice() {
                return self
                    .bind_child(s, &inst, &module, m, a, e.span)
                    .map(|_| true);
            }
            return Ok(false);
        }
        // `child->port.bind(x)`.
        if m == "bind"
            && let K::Member {
                base: inner_base,
                name: port,
                ..
            } = &base.kind
            && let Some((inst, module)) = self.instance_of(inner_base)
            && let [a] = args.as_slice()
        {
            return self
                .bind_child(s, &inst, &module, &port.ident.name, a, e.span)
                .map(|_| true);
        }
        // Own target socket registrations.
        if let Some(q) = base.as_name()
            && let Some(sym) = self.lw.lookup(q.last_name())
            && sym.kind == SymKind::TargetSocket
        {
            let reg = s.targets.entry(sym.sv.clone()).or_default();
            let method_of = |a: &sc::Expr| -> Option<String> {
                match &a.kind {
                    sc::ExprKind::Unary {
                        op: sc::UnaryOp::AddrOf,
                        operand,
                    } => operand.as_name().map(|q| q.last_name().to_string()),
                    _ => None,
                }
            };
            match (m, args.as_slice()) {
                ("register_b_transport", [_, f]) => reg.b_transport = method_of(f),
                ("register_transport_dbg", [_, f]) => reg.transport_dbg = method_of(f),
                ("register_get_direct_mem_ptr", [_, f]) => reg.get_direct_mem_ptr = method_of(f),
                ("register_nb_transport_fw", _) => {
                    return self.lw.err(
                        e.span,
                        "non-blocking transport (AT TLM) is not supported in simulation",
                    );
                }
                ("bind", [a]) if matches!(&a.kind, sc::ExprKind::Unary { op: sc::UnaryOp::Deref, operand } if matches!(operand.kind, sc::ExprKind::This)) =>
                {
                    // The module implements the forward interface itself.
                    reg.b_transport = Some("b_transport".to_string());
                    reg.transport_dbg = self
                        .lw
                        .m
                        .funcs
                        .contains_key("transport_dbg")
                        .then(|| "transport_dbg".to_string());
                    reg.get_direct_mem_ptr = None;
                }
                _ => return Ok(false),
            }
            return Ok(true);
        }
        Ok(false)
    }

    /// The instance a binding expression's object names: `u`, `*u`.
    fn instance_of(&self, e: &sc::Expr) -> Option<(String, String)> {
        let e = match &e.kind {
            sc::ExprKind::Unary {
                op: sc::UnaryOp::Deref,
                operand,
            } => operand.as_ref(),
            _ => e,
        };
        let q = e.as_name()?;
        let sym = self.lw.lookup(q.last_name())?;
        match sym.kind {
            SymKind::Instance(module) => Some((sym.sv, module)),
            _ => None,
        }
    }

    fn connect(&mut self, s: &mut Structure, inst: &str, port: &str, x: Expression) {
        if let Some(i) = s.insts.iter_mut().find(|i| i.sv == inst) {
            i.conns.retain(|(p, _)| p != port);
            i.conns.push((port.to_string(), x));
        }
    }

    fn bind_child(
        &mut self,
        s: &mut Structure,
        inst: &str,
        module: &str,
        port: &str,
        a: &sc::Expr,
        span: ScSpan,
    ) -> R<()> {
        let kind = self
            .ifaces
            .get(module)
            .and_then(|i| i.members.get(port))
            .map(|m| m.kind.clone());
        match kind {
            Some(SymKind::InPort | SymKind::OutPort | SymKind::InOutPort) => {
                let (x, _) = self.lw.expr(a)?;
                self.connect(s, inst, port, x);
                Ok(())
            }
            Some(SymKind::FifoIn | SymKind::FifoOut) => {
                let (x, _) = self.lw.expr(a)?;
                s.elab.push(assign(member(ident(inst), port), x));
                Ok(())
            }
            Some(SymKind::InitSocket) => {
                // `a.socket.bind(b.socket)`: the initiator socket holds the
                // target socket object.
                let target = match &a.kind {
                    sc::ExprKind::Member { base, name, .. } => self
                        .instance_of(base)
                        .map(|(i, _)| member(ident(&i), &name.ident.name)),
                    sc::ExprKind::Name(q) => self
                        .lw
                        .lookup(q.last_name())
                        .filter(|s| s.kind == SymKind::TargetSocket)
                        .map(|s| ident(&s.sv)),
                    _ => None,
                };
                let Some(target) = target else {
                    return self.lw.err(
                        span,
                        "an initiator socket must be bound to a target socket of another module",
                    );
                };
                s.elab
                    .push(assign(member(member(ident(inst), port), "peer"), target));
                Ok(())
            }
            Some(_) => self
                .lw
                .err(span, format!("'{}' of '{}' cannot be bound", port, module)),
            None => self
                .lw
                .err(span, format!("'{}' has no port '{}'", module, port)),
        }
    }

    /// Unroll a constant-bound `for` loop around structural statements.
    fn unroll(&mut self, stmt: &sc::Stmt, s: &mut Structure) -> R<()> {
        let sc::Stmt::For {
            init,
            cond: Some(c),
            step: Some(step),
            body,
            span,
        } = stmt
        else {
            return self.lw.err(
                super::lower::stmt_span(stmt),
                "only a counted for loop can bind or register at elaboration",
            );
        };
        let (var, start) = match init.as_deref() {
            Some(sc::Stmt::Decl(v)) => {
                let d = &v.declarators[0];
                let Some(sc::Initializer::Assign(e)) = &d.init else {
                    return self.lw.err(*span, "loop start must be a constant");
                };
                (d.name.name.clone(), self.lw.const_eval(e))
            }
            Some(sc::Stmt::Expr(sc::Expr {
                kind: sc::ExprKind::Assign { lhs, rhs, .. },
                ..
            })) => (
                lhs.as_name()
                    .map(|q| q.last_name().to_string())
                    .unwrap_or_default(),
                self.lw.const_eval(rhs),
            ),
            _ => return self.lw.err(*span, "loop start must be a constant"),
        };
        let Some(mut i) = start else {
            return self.lw.err(*span, "loop start must be a constant");
        };
        let sc::Condition::Expr(c) = c.as_ref() else {
            return self.lw.err(*span, "loop condition must be a comparison");
        };
        let delta = match &step.kind {
            sc::ExprKind::Unary {
                op: sc::UnaryOp::PreInc,
                ..
            }
            | sc::ExprKind::Postfix {
                op: sc::PostfixOp::Inc,
                ..
            } => 1,
            sc::ExprKind::Unary {
                op: sc::UnaryOp::PreDec,
                ..
            }
            | sc::ExprKind::Postfix {
                op: sc::PostfixOp::Dec,
                ..
            } => -1,
            sc::ExprKind::Assign {
                op: sc::AssignOp::Add,
                rhs,
                ..
            } => self.lw.const_eval(rhs).unwrap_or(0),
            _ => 0,
        };
        if delta == 0 {
            return self.lw.err(*span, "loop step must be a constant increment");
        }
        for _ in 0..65536 {
            self.lw.f.scopes.push(BTreeMap::from([(
                var.clone(),
                Sym {
                    kind: SymKind::Const(i),
                    ty: Ty::int32(),
                    sv: var.clone(),
                },
            )]));
            let go = self.lw.const_eval(c);
            if go != Some(1) {
                self.lw.f.scopes.pop();
                if go.is_none() {
                    return self.lw.err(*span, "loop bound must be a constant");
                }
                return Ok(());
            }
            let r = self.walk_stmt(body, s);
            self.lw.f.scopes.pop();
            r?;
            i += delta;
        }
        self.lw.err(*span, "loop runs too long to unroll")
    }

    // ---- processes --------------------------------------------------------------

    fn register_procs(&mut self, s: &Structure, class: &sc::ClassDecl, name: &str) -> R<()> {
        let mut procs = Vec::new();
        let mut fn_proc: BTreeMap<String, Option<usize>> = BTreeMap::new();
        for (i, p) in s.procs.iter().enumerate() {
            let reset = p
                .resets
                .iter()
                .map(|(_, sig, lvl, _)| bin(BinaryOp::Eq, sig.clone(), lvl.clone()))
                .reduce(|a, b| bin(BinaryOp::LogOr, a, b));
            procs.push(ProcCtx {
                index: i,
                kind: p.kind,
                sens: p.sens.clone(),
                clock: p.clock.clone(),
                reset,
            });
        }
        // Every member function a process reaches runs in that process.
        let graph = call_graph(self.lw, class, name);
        for (i, p) in s.procs.iter().enumerate() {
            let mut seen = BTreeSet::new();
            let mut stack = vec![p.func.clone()];
            while let Some(f) = stack.pop() {
                if !seen.insert(f.clone()) {
                    continue;
                }
                let e = fn_proc.entry(f.clone()).or_insert(Some(i));
                if *e != Some(i) {
                    *e = None;
                }
                if let Some(callees) = graph.get(&f) {
                    stack.extend(callees.iter().cloned());
                }
            }
        }
        self.lw.m.procs = procs;
        self.lw.m.fn_proc = fn_proc;
        self.dont_init = s.procs.iter().map(|p| p.dont_init).collect();
        self.proc_funcs = s.procs.iter().map(|p| p.func.clone()).collect();
        self.async_resets = s
            .procs
            .iter()
            .map(|p| {
                p.resets
                    .iter()
                    .filter(|r| r.0)
                    .map(|r| (r.1.clone(), r.2.clone()))
                    .collect()
            })
            .collect();
        for p in &s.procs {
            let defined = self.lw.prog.out_of_class.get(name).is_some_and(|v| v.iter().any(|(_, f)| f.base_name() == p.func))
                || class.members.iter().any(|m| matches!(m, sc::Member::Method(f) if f.base_name() == p.func && f.body.is_some()));
            if !defined {
                return self.lw.err(
                    p.span,
                    format!("process function '{}' has no definition", p.func),
                );
            }
        }
        Ok(())
    }

    /// Signatures and bodies of the member functions.
    fn member_function_defs(
        &mut self,
        class: &'a sc::ClassDecl,
        name: &str,
    ) -> Vec<(usize, &'a sc::FunctionDecl)> {
        let mut defs: Vec<(usize, &'a sc::FunctionDecl)> = Vec::new();
        let tu = self.lw.tu;
        for m in &class.members {
            if let sc::Member::Method(f) = m
                && f.body.is_some()
                && !f.specifiers.is_static
            {
                defs.push((tu, f));
            }
        }
        if let Some(ool) = self.lw.prog.out_of_class.get(name) {
            for (t, f) in ool {
                if f.base_name() != name && !f.base_name().starts_with('~') {
                    defs.push((*t, f));
                }
            }
        }
        self.add_free_functions(&mut defs);
        defs
    }

    /// Free functions the given definitions call (transitively), lowered
    /// into the module alongside its own (they touch no module state).
    fn add_free_functions(&mut self, defs: &mut Vec<(usize, &'a sc::FunctionDecl)>) {
        let mut have: BTreeSet<String> = defs
            .iter()
            .map(|(_, f)| f.base_name().to_string())
            .collect();
        let mut i = 0;
        while i < defs.len() {
            let mut callees = BTreeSet::new();
            if let Some(b) = &defs[i].1.body {
                for s in &b.stmts {
                    stmt_calls(s, &mut callees);
                }
            }
            for c in callees {
                if have.contains(&c) {
                    continue;
                }
                if let Some((t, f)) = self.lw.prog.free_fns.get(&c) {
                    have.insert(c);
                    defs.push((*t, f));
                }
            }
            i += 1;
        }
    }

    /// Register the signatures of `defs` (calls resolve against them).
    fn register_sigs(&mut self, defs: &[(usize, &'a sc::FunctionDecl)]) -> R<()> {
        let tu = self.lw.tu;
        let blocking = blocking_functions(self.lw, defs);
        for (t, f) in defs {
            self.lw.tu = *t;
            let ret = match &f.return_type {
                Some(rt) => {
                    let mut rt = rt.clone();
                    rt.ptr_ops.extend(f.return_ptr_ops.iter().copied());
                    self.lw.ty(&rt, f.span)?
                }
                None => Ty::Void,
            };
            let by_ref = f
                .params
                .iter()
                .map(|p| {
                    p.ty.ptr_ops.contains(&sc::PtrOp::LRef)
                        && !p.ty.is_const
                        && !matches!(self.lw.ty(&p.ty, p.span), Ok(Ty::Class(_)))
                })
                .collect();
            self.lw.m.funcs.insert(
                f.base_name().to_string(),
                FnSig {
                    ret,
                    is_task: blocking.contains(f.base_name()),
                    by_ref,
                },
            );
        }
        self.lw.tu = tu;
        Ok(())
    }

    fn lower_bodies(&mut self, defs: Vec<(usize, &'a sc::FunctionDecl)>) -> R<Vec<ModuleItem>> {
        let tu = self.lw.tu;
        let mut items = Vec::new();
        for (t, f) in defs {
            self.lw.tu = t;
            match self.lower_function(f) {
                Ok(item) => items.push(item),
                Err(e) => self.lw.record(e),
            }
        }
        self.lw.tu = tu;
        Ok(items)
    }

    fn lower_function(&mut self, f: &sc::FunctionDecl) -> R<ModuleItem> {
        let name = f.base_name().to_string();
        let sig = self
            .lw
            .m
            .funcs
            .get(&name)
            .cloned()
            .expect("signature computed");
        self.lw.f = FnCtx {
            scopes: vec![BTreeMap::new()],
            proc: self.lw.m.fn_proc.get(&name).copied().flatten(),
            ret: Some(sig.ret.clone()),
            is_task: sig.is_task,
            ..Default::default()
        };
        let mut ports = Vec::new();
        let mut prologue = Vec::new();
        for (i, p) in f.params.iter().enumerate() {
            let ty = self.lw.ty(&p.ty, p.span)?;
            let pname = p
                .name
                .as_ref()
                .map_or_else(|| format!("__sc_arg{}", i), |n| n.name.clone());
            self.lw.f.used.insert(pname.clone());
            let dir = if sig.by_ref[i] {
                PortDirection::Ref
            } else {
                PortDirection::Input
            };
            ports.push(fport(dir, sv_scalar_type(&ty), &pname));
            // A parameter whose address is taken lives in a box; a reference
            // parameter is copied back on every return.
            if self.lw.prog.address_taken(&pname, self.lw.tu) && ty.is_scalar_bits() {
                let bx = self
                    .lw
                    .declare_local(&pname, ty.clone(), SymKind::Boxed, None);
                prologue.push(assign(ident(&bx), new_obj(None)));
                prologue.push(assign(member(ident(&bx), "v"), ident(&pname)));
                if sig.by_ref[i] {
                    self.lw
                        .f
                        .epilogue
                        .push(assign(ident(&pname), member(ident(&bx), "v")));
                }
                continue;
            }
            self.lw.f.scopes[0].insert(
                pname.clone(),
                Sym {
                    kind: SymKind::Var,
                    ty: ty.clone(),
                    sv: pname.clone(),
                },
            );
        }
        if sig.is_task && !matches!(sig.ret, Ty::Void) {
            self.lw.f.ret_var = Some("__sc_ret".to_string());
            ports.push(fport(
                PortDirection::Output,
                sv_scalar_type(&sig.ret),
                "__sc_ret",
            ));
        }
        let body = f.body.as_ref().expect("defined");
        let stmts = self.lw.block(&body.stmts);
        let mut items = std::mem::take(&mut self.lw.f.decls);
        items.extend(prologue);
        items.extend(stmts);
        items.extend(std::mem::take(&mut self.lw.f.epilogue));
        Ok(if sig.is_task {
            ModuleItem::TaskDeclaration(task_decl(&name, ports, items))
        } else {
            ModuleItem::FunctionDeclaration(function_decl(
                &name,
                sv_scalar_type(&sig.ret),
                ports,
                items,
            ))
        })
    }

    // ---- assembly -------------------------------------------------------------

    #[allow(clippy::too_many_arguments)]
    fn finish_module(
        &mut self,
        name: &str,
        params: Vec<crate::ast::decl::ParameterDeclaration>,
        port_order: &[(String, SymKind)],
        s: Structure,
        elab_decls: Vec<Statement>,
        elab_stmts: Vec<Statement>,
        funcs: Vec<ModuleItem>,
        elab_tb: Option<(Vec<Statement>, Vec<Statement>)>,
    ) -> R<ModuleDeclaration> {
        let mut items = vec![import_all("sc_rt"), timeunits_ps()];
        let mut ports = Vec::new();
        let mut clock_items = Vec::new();
        for (clk, args, span) in &s.clocks {
            clock_items.push(self.clock_gen(clk, args, *span)?);
        }
        let syms = self.lw.m.syms.clone();
        for (pname, kind) in port_order {
            let sym = &syms[pname];
            let (dt, dims) = sv_type(&sym.ty);
            ports.push(ansi_port(port_dir(kind).expect("port"), dt, pname, dims));
        }
        for (n, sym) in &syms {
            if port_dir(&sym.kind).is_some()
                || matches!(sym.kind, SymKind::Instance(_) | SymKind::TraceFile)
            {
                continue;
            }
            if self.is_ctor_param(n) {
                continue;
            }
            let (dt, dims, init) = match sym.kind {
                SymKind::Boxed => (
                    named_t(box_class(&sym.ty), Vec::new()),
                    Vec::new(),
                    Some(new_obj(None)),
                ),
                SymKind::BoxedArr => {
                    let Ty::Array(_, size) = &sym.ty else {
                        unreachable!("boxed arrays are arrays")
                    };
                    (
                        named_t(arr_class(&sym.ty), Vec::new()),
                        Vec::new(),
                        Some(new_obj(Some(vec![size.clone()]))),
                    )
                }
                SymKind::Fifo => {
                    let (dt, dims) = sv_type(&sym.ty);
                    let size = self.fifo_size.get(n).cloned().unwrap_or_else(|| int(16));
                    (dt, dims, Some(new_obj(Some(vec![size]))))
                }
                SymKind::InitSocket => (
                    named_t("scrt_initiator_socket", Vec::new()),
                    Vec::new(),
                    Some(new_obj(Some(vec![string(n)]))),
                ),
                SymKind::TargetSocket => (
                    named_t("scrt_target_socket", Vec::new()),
                    Vec::new(),
                    Some(new_obj(None)),
                ),
                SymKind::Clock => (
                    bit_t(1, false),
                    Vec::new(),
                    Some(sized(1, self.clock_init.get(n).copied().unwrap_or(0))),
                ),
                _ => {
                    let (dt, dims) = sv_type(&sym.ty);
                    (dt, dims, None)
                }
            };
            items.push(data_decl(dt, &sym.sv, dims, init));
        }
        items.append(&mut self.lw.m.extra_items);
        // Children.
        for inst in &s.insts {
            items.push(instance(
                &inst.module,
                &inst.sv,
                inst.params.clone(),
                inst.conns.clone(),
            ));
        }
        items.extend(clock_items);
        // TLM target registrations: a class per target socket whose methods
        // call this module's transport functions.
        let mut fw_assigns = Vec::new();
        let mut aliases = Vec::new();
        for (sock, reg) in &s.targets {
            let cname = format!("__sc_fw_{}", sock);
            let mut citems: Vec<ClassItem> = Vec::new();
            if let Some(f) = &reg.b_transport {
                citems.push(class_task(
                    task_decl(
                        "b_transport",
                        vec![
                            fport(
                                PortDirection::Input,
                                named_t("scrt_tlm_gp", Vec::new()),
                                "trans",
                            ),
                            fport(
                                PortDirection::Inout,
                                atom_t(crate::ast::types::IntegerAtomType::LongInt, true),
                                "delay",
                            ),
                        ],
                        vec![expr_stmt(call_fn(
                            &format!("__sc_call_{}", f),
                            vec![ident("trans"), ident("delay")],
                        ))],
                    ),
                    true,
                ));
                aliases.push(ModuleItem::TaskDeclaration(task_decl(
                    &format!("__sc_call_{}", f),
                    vec![
                        fport(
                            PortDirection::Input,
                            named_t("scrt_tlm_gp", Vec::new()),
                            "trans",
                        ),
                        fport(
                            PortDirection::Inout,
                            atom_t(crate::ast::types::IntegerAtomType::LongInt, true),
                            "delay",
                        ),
                    ],
                    vec![expr_stmt(call_fn(f, vec![ident("trans"), ident("delay")]))],
                )));
            }
            if let Some(f) = &reg.transport_dbg {
                citems.push(class_function(
                    function_decl(
                        "transport_dbg",
                        atom_t(crate::ast::types::IntegerAtomType::Int, true),
                        vec![fport(
                            PortDirection::Input,
                            named_t("scrt_tlm_gp", Vec::new()),
                            "trans",
                        )],
                        vec![ret(Some(call_fn(
                            &format!("__sc_call_{}", f),
                            vec![ident("trans")],
                        )))],
                    ),
                    true,
                ));
                aliases.push(ModuleItem::FunctionDeclaration(function_decl(
                    &format!("__sc_call_{}", f),
                    atom_t(crate::ast::types::IntegerAtomType::Int, true),
                    vec![fport(
                        PortDirection::Input,
                        named_t("scrt_tlm_gp", Vec::new()),
                        "trans",
                    )],
                    vec![ret(Some(call_fn(f, vec![ident("trans")])))],
                )));
            }
            items.push(ModuleItem::ClassDeclaration(class_decl(
                &cname,
                Some("scrt_fw_if"),
                citems,
            )));
            let obj = format!("{}_obj", cname);
            items.push(data_decl(
                named_t(&cname, Vec::new()),
                &obj,
                Vec::new(),
                Some(new_obj(None)),
            ));
            fw_assigns.push(assign(member(ident(sock), "fw"), ident(&obj)));
        }
        items.extend(aliases);
        // Elaboration code.
        let mut elab = elab_decls;
        elab.extend(fw_assigns);
        elab.extend(elab_stmts);
        if !elab.is_empty() && !self.lw.m.tb {
            items.push(initial(block(elab)));
        }
        items.extend(funcs);
        // Process wrappers.
        let procs = std::mem::take(&mut self.lw.m.procs);
        let flags = std::mem::take(&mut self.lw.m.edge_flags);
        for (pi, p) in procs.iter().enumerate() {
            let dont_init = self.dont_init.get(pi).copied().unwrap_or(false);
            let func = self.proc_funcs[pi].clone();
            items.extend(self.proc_wrapper(p, &func, dont_init, &flags));
        }
        if self.lw.m.tb {
            items.extend(self.tb_items(elab_tb));
        }
        Ok(module(name, params, ports, items))
    }

    // ---- sc_main ----------------------------------------------------------------

    /// `sc_main` → module `sc_main`: its channels, clocks and module objects
    /// become module items, the rest of its body the testbench process.
    pub fn lower_main(&mut self, f: &'a sc::FunctionDecl) -> R<ModuleDeclaration> {
        self.lw.m = ModCtx {
            name: "sc_main".to_string(),
            tb: true,
            ..Default::default()
        };
        self.lw.f = FnCtx {
            scopes: vec![BTreeMap::new()],
            ..Default::default()
        };
        let mut s = Structure::default();
        // `argc` is 1 (no command-line arguments reach sc_main).
        for p in &f.params {
            if let Some(n) = &p.name
                && p.ty.ptr_ops.is_empty()
                && p.array_dims.is_empty()
            {
                let sv = self
                    .lw
                    .declare_local(&n.name, Ty::int32(), SymKind::Var, Some(int(1)));
                let _ = sv;
            }
        }
        // Free functions sc_main calls, lowered into the testbench module.
        let mut defs = vec![(self.lw.tu, f)];
        self.add_free_functions(&mut defs);
        defs.remove(0);
        self.register_sigs(&defs)?;
        if let Some(b) = &f.body {
            self.walk(&b.stmts, &mut s);
        }
        let decls = std::mem::take(&mut self.lw.f.decls);
        let stmts = std::mem::take(&mut s.elab);
        self.lw.m.procs.clear();
        let saved = std::mem::take(&mut self.lw.f);
        let funcs = self.lower_bodies(defs)?;
        self.lw.f = saved;
        self.finish_module(
            "sc_main",
            Vec::new(),
            &[],
            s,
            Vec::new(),
            Vec::new(),
            funcs,
            Some((decls, stmts)),
        )
    }

    /// A declaration in sc_main: channels and module objects are structure.
    fn tb_decl(&mut self, v: &sc::VarDecl, stmt: &sc::Stmt, s: &mut Structure) -> R<()> {
        let kind = ScObjectKind::of(&v.ty);
        let module =
            v.ty.name()
                .map(|q| q.last_name().to_string())
                .filter(|n| self.lw.prog.is_module(n));
        match (&kind, module) {
            (
                ScObjectKind::Signal
                | ScObjectKind::Buffer
                | ScObjectKind::Clock
                | ScObjectKind::Fifo
                | ScObjectKind::Event
                | ScObjectKind::Vector(_),
                _,
            ) => {
                for d in &v.declarators {
                    let Some(sym) = self.member_sym(v, d)? else {
                        continue;
                    };
                    let args = match &d.init {
                        Some(sc::Initializer::Paren(a) | sc::Initializer::Brace(a)) => a.clone(),
                        _ => Vec::new(),
                    };
                    match sym.kind {
                        SymKind::Clock => s.clocks.push((d.name.name.clone(), args, d.span)),
                        SymKind::Fifo => {
                            if let Some(n) = args.get(1) {
                                let (x, _) = self.lw.expr(n)?;
                                self.fifo_size.insert(d.name.name.clone(), x);
                            }
                        }
                        _ => {}
                    }
                    self.lw.m.syms.insert(d.name.name.clone(), sym);
                }
                Ok(())
            }
            (_, Some(module)) => {
                for d in &v.declarators {
                    let args: Vec<sc::Expr> = match &d.init {
                        Some(sc::Initializer::Paren(a) | sc::Initializer::Brace(a)) => a.clone(),
                        Some(sc::Initializer::Assign(sc::Expr {
                            kind: sc::ExprKind::New { args: Some(a), .. },
                            ..
                        })) => a.clone(),
                        _ => Vec::new(),
                    };
                    let mut params =
                        self.ctor_args_params(&module, args.get(1..).unwrap_or(&[]), d.span)?;
                    if let Some(q) = v.ty.name() {
                        params.extend(self.template_args(q, d.span)?);
                    }
                    // The SystemC instance name, when it is a valid identifier.
                    let sv = match args.first().map(|a| &a.kind) {
                        Some(sc::ExprKind::StringLit { value, .. })
                            if is_valid_ident(value) && !self.lw.m.syms.contains_key(value) =>
                        {
                            value.clone()
                        }
                        _ => d.name.name.clone(),
                    };
                    self.lw.m.syms.insert(
                        d.name.name.clone(),
                        Sym {
                            kind: SymKind::Instance(module.clone()),
                            ty: Ty::Void,
                            sv: sv.clone(),
                        },
                    );
                    s.insts.push(Inst {
                        module: module.clone(),
                        sv,
                        params,
                        conns: Vec::new(),
                    });
                }
                Ok(())
            }
            (ScObjectKind::InPort | ScObjectKind::OutPort | ScObjectKind::InOutPort, _) => {
                self.lw.err(v.span, "ports cannot be declared in sc_main")
            }
            _ => {
                let out = self.lw.stmt(stmt)?;
                s.elab.extend(out);
                Ok(())
            }
        }
    }

    /// The testbench process and its helpers.
    fn tb_items(&mut self, tb: Option<(Vec<Statement>, Vec<Statement>)>) -> Vec<ModuleItem> {
        let mut items = vec![data_decl(
            atom_t(crate::ast::types::IntegerAtomType::LongInt, true),
            "__sc_dur",
            Vec::new(),
            None,
        )];
        let pending = std::mem::take(&mut self.lw.m.pending);
        let mut apply = Vec::new();
        for (sig, slot, is_elem) in &pending {
            let idx = format!("{}_i", slot);
            let target = if *is_elem {
                index(ident(sig), index(ident(&idx), ident("k")))
            } else {
                ident(sig)
            };
            apply.push(st(StatementKind::For {
                init: vec![crate::ast::stmt::ForInit::VarDecl {
                    data_type: atom_t(crate::ast::types::IntegerAtomType::Int, false),
                    name: id("k"),
                    init: int(0),
                }],
                condition: Some(bin(
                    BinaryOp::Lt,
                    ident("k"),
                    method(ident(slot), "size", vec![]),
                )),
                step: vec![unary(UnaryOp::PostIncr, ident("k"))],
                body: Box::new(assign(target, index(ident(slot), ident("k")))),
            }));
            apply.push(expr_stmt(method(ident(slot), "delete", vec![])));
            apply.push(expr_stmt(method(ident(&idx), "delete", vec![])));
        }
        items.push(ModuleItem::FunctionDeclaration(function_decl(
            "__sc_apply_pending",
            void_t(),
            Vec::new(),
            apply,
        )));
        items.append(&mut self.lw.m.extra_items);
        let (decls, stmts) = tb.unwrap_or_default();
        let mut body = decls;
        body.extend(stmts);
        body.push(expr_stmt(sys("$finish", vec![])));
        items.push(initial(block(body)));
        items
    }

    fn is_ctor_param(&self, n: &str) -> bool {
        self.ifaces
            .get(&self.lw.m.name)
            .is_some_and(|i| i.ctor_params.iter().any(|p| p == n))
    }

    /// A generated clock (IEEE 1666-2023 §6.7): `sc_clock("clk", period, unit
    /// [, duty, start, start_unit, posedge_first])` or with `sc_time`s.
    fn clock_gen(&mut self, clk: &str, args: &[sc::Expr], span: ScSpan) -> R<ModuleItem> {
        let a = args.get(1..).unwrap_or(&[]);
        let ps = |lw: &mut Lw, e: &[sc::Expr]| -> R<(u64, usize)> {
            if e.len() >= 2 && is_time_unit(&e[1]) {
                let x = lw.time_value(&e[0], &e[1], span)?;
                return expr_int(&x)
                    .map(|v| (v as u64, 2))
                    .ok_or(())
                    .or_else(|_| lw.err(span, "clock times must be constant"));
            }
            match e.first() {
                Some(x) => {
                    let (v, t) = lw.expr(x)?;
                    if !matches!(t, Ty::Time) {
                        // The deprecated double form is in the default time unit (ns).
                        if let Some(n) = lw.const_eval(x) {
                            return Ok(((n * 1000) as u64, 1));
                        }
                        if let sc::ExprKind::FloatLit { text } = &x.kind
                            && let Ok(f) = text.trim_end_matches(['f', 'F']).parse::<f64>()
                        {
                            return Ok(((f * 1000.0).round() as u64, 1));
                        }
                    }
                    expr_int(&v)
                        .map(|v| (v as u64, 1))
                        .ok_or(())
                        .or_else(|_| lw.err(span, "clock times must be constant"))
                }
                None => Ok((1000, 0)),
            }
        };
        let (period, used) = ps(self.lw, a)?;
        let rest = &a[used.min(a.len())..];
        let duty = match rest.first() {
            Some(sc::Expr {
                kind: sc::ExprKind::FloatLit { text },
                ..
            }) => text
                .trim_end_matches(['f', 'F'])
                .parse::<f64>()
                .unwrap_or(0.5),
            Some(e) if self.lw.const_eval(e).is_some() => self.lw.const_eval(e).unwrap_or(0) as f64,
            _ => 0.5,
        };
        let rest = rest.get(1..).unwrap_or(&[]);
        let (start, used) = if rest.is_empty() {
            (0, 0)
        } else {
            ps(self.lw, rest)?
        };
        let rest = &rest[used.min(rest.len())..];
        let posedge_first = match rest.first() {
            Some(sc::Expr {
                kind: sc::ExprKind::BoolLit(b),
                ..
            }) => *b,
            _ => true,
        };
        let high = (period as f64 * duty).round() as u64;
        let low = period - high;
        let (first, t1, t2) = if posedge_first {
            (1, high, low)
        } else {
            (0, low, high)
        };
        if let Some(sym) = self.lw.m.syms.get_mut(clk) {
            sym.kind = SymKind::Clock;
        }
        self.clock_init.insert(clk.to_string(), 1 - first);
        // Toggles are deferred with #0 so that writes sc_main makes at the
        // same time instant are applied first (SystemC's update phase).
        let mut body = vec![wait(ident("scrt_started"))];
        if start > 0 {
            body.push(delay(u64_lit(start), null_stmt()));
        }
        body.push(forever(block(vec![
            delay(int(0), null_stmt()),
            assign(ident(clk), sized(1, first)),
            delay(u64_lit(t1), null_stmt()),
            delay(int(0), null_stmt()),
            assign(ident(clk), sized(1, 1 - first)),
            delay(u64_lit(t2), null_stmt()),
        ])));
        Ok(initial(block(body)))
    }

    /// The `initial` block running one process.
    fn proc_wrapper(
        &mut self,
        p: &ProcCtx,
        func: &str,
        dont_init: bool,
        flags: &BTreeSet<(usize, String)>,
    ) -> Vec<ModuleItem> {
        let mut items = Vec::new();
        let call = expr_stmt(call_fn(func, vec![]));
        let my_flags: Vec<String> = flags
            .iter()
            .filter(|(i, _)| *i == p.index)
            .map(|(_, s)| s.clone())
            .collect();
        for f in &my_flags {
            items.push(data_decl(
                bit_t(1, false),
                &edge_flag_name(p.index, f),
                Vec::new(),
                None,
            ));
        }
        let wait_sens = || -> Statement {
            if my_flags.is_empty() {
                return at(
                    p.sens
                        .iter()
                        .map(|(e, x, _)| event_expr(*e, x.clone()))
                        .collect(),
                    null_stmt(),
                );
            }
            let branches = p
                .sens
                .iter()
                .map(|(e, x, s)| {
                    let mut v = vec![at(vec![event_expr(*e, x.clone())], null_stmt())];
                    if my_flags.contains(s) {
                        v.push(assign(ident(&edge_flag_name(p.index, s)), sized(1, 1)));
                    }
                    block(v)
                })
                .collect();
            block(vec![fork(JoinType::JoinAny, branches), disable_fork()])
        };
        let clear_flags: Vec<Statement> = my_flags
            .iter()
            .map(|s| assign(ident(&edge_flag_name(p.index, s)), sized(1, 0)))
            .collect();
        let mut body = vec![wait(ident("scrt_started"))];
        match p.kind {
            sc::ProcessKind::Method => {
                if !dont_init {
                    body.push(call.clone());
                }
                if !p.sens.is_empty() {
                    let mut lp = vec![wait_sens(), call];
                    lp.extend(clear_flags);
                    body.push(forever(block(lp)));
                }
            }
            sc::ProcessKind::Thread | sc::ProcessKind::CThread => {
                if let Some((edge, clk)) = &p.clock {
                    // A clocked thread first runs at its first clock edge.
                    body.push(at(vec![event_expr(Some(*edge), clk.clone())], null_stmt()));
                } else if dont_init {
                    if p.sens.is_empty() {
                        return items;
                    }
                    body.push(wait_sens());
                }
                if p.reset.is_some() {
                    let flag = reset_flag_name(p.index);
                    items.push(data_decl(bit_t(1, false), &flag, Vec::new(), None));
                    let async_resets: Vec<(Expression, Expression)> =
                        self.async_resets.get(p.index).cloned().unwrap_or_default();
                    let run = if async_resets.is_empty() {
                        call
                    } else {
                        let mut branches = vec![call];
                        for (sig, lvl) in async_resets {
                            let edge = if expr_int(&lvl) == Some(0) {
                                Edge::Negedge
                            } else {
                                Edge::Posedge
                            };
                            branches.push(block(vec![
                                at(vec![event_expr(Some(edge), sig)], null_stmt()),
                                assign(ident(&flag), sized(1, 1)),
                            ]));
                        }
                        block(vec![fork(JoinType::JoinAny, branches), disable_fork()])
                    };
                    body.push(forever(block(vec![
                        assign(ident(&flag), sized(1, 0)),
                        run,
                        if_(
                            unary(UnaryOp::LogNot, ident(&flag)),
                            st(StatementKind::Break),
                            None,
                        ),
                    ])));
                } else {
                    body.push(call);
                }
            }
        }
        items.push(initial(block(body)));
        items
    }
}

fn is_time_unit(e: &sc::Expr) -> bool {
    e.as_name().is_some_and(|q| {
        matches!(
            q.last_name(),
            "SC_FS" | "SC_PS" | "SC_NS" | "SC_US" | "SC_MS" | "SC_SEC"
        )
    })
}

fn is_structural_loop(s: &sc::Stmt) -> bool {
    fn any(s: &sc::Stmt) -> bool {
        match s {
            sc::Stmt::Sensitive { .. } | sc::Stmt::ScProcess { .. } => true,
            sc::Stmt::Block(b) => b.stmts.iter().any(any),
            sc::Stmt::For { body, .. } => any(body),
            sc::Stmt::Expr(sc::Expr {
                kind: sc::ExprKind::Call { callee, .. },
                ..
            }) => {
                matches!(&callee.kind, sc::ExprKind::Member { name, .. } if name.ident.name == "bind")
            }
            _ => false,
        }
    }
    matches!(s, sc::Stmt::For { body, .. } if any(body))
}

/// Member function → member functions it calls (by name).
fn call_graph(lw: &Lw, class: &sc::ClassDecl, name: &str) -> BTreeMap<String, BTreeSet<String>> {
    let mut g = BTreeMap::new();
    let mut add = |f: &sc::FunctionDecl| {
        let mut callees = BTreeSet::new();
        if let Some(b) = &f.body {
            for s in &b.stmts {
                stmt_calls(s, &mut callees);
            }
        }
        g.insert(f.base_name().to_string(), callees);
    };
    for m in &class.members {
        if let sc::Member::Method(f) = m {
            add(f);
        }
    }
    if let Some(ool) = lw.prog.out_of_class.get(name) {
        for (_, f) in ool {
            add(f);
        }
    }
    g
}

fn stmt_calls(s: &sc::Stmt, out: &mut BTreeSet<String>) {
    visit_stmt_exprs(s, &mut |e| {
        if let sc::ExprKind::Call { callee, .. } = &e.kind
            && let Some(q) = callee.as_name()
            && q.segments.len() == 1
        {
            out.insert(q.last_name().to_string());
        }
    });
}

/// Every expression of a statement tree.
pub fn visit_stmt_exprs(s: &sc::Stmt, f: &mut dyn FnMut(&sc::Expr)) {
    use sc::Stmt as S;
    let cond = |c: &sc::Condition, f: &mut dyn FnMut(&sc::Expr)| {
        if let sc::Condition::Expr(e) = c {
            visit_expr(e, f);
        }
    };
    match s {
        S::Block(b) => b.stmts.iter().for_each(|s| visit_stmt_exprs(s, f)),
        S::Expr(e) | S::Return(Some(e), _) => visit_expr(e, f),
        S::Decl(v) => {
            for d in &v.declarators {
                match &d.init {
                    Some(sc::Initializer::Assign(e)) => visit_expr(e, f),
                    Some(sc::Initializer::Paren(a) | sc::Initializer::Brace(a)) => {
                        a.iter().for_each(|e| visit_expr(e, f))
                    }
                    None => {}
                }
            }
        }
        S::If {
            init,
            cond: c,
            then_branch,
            else_branch,
            ..
        } => {
            if let Some(i) = init {
                visit_stmt_exprs(i, f);
            }
            cond(c, f);
            visit_stmt_exprs(then_branch, f);
            if let Some(e) = else_branch {
                visit_stmt_exprs(e, f);
            }
        }
        S::Switch { cond: c, arms, .. } => {
            cond(c, f);
            for a in arms {
                a.body.iter().for_each(|s| visit_stmt_exprs(s, f));
            }
        }
        S::For {
            init,
            cond: c,
            step,
            body,
            ..
        } => {
            if let Some(i) = init {
                visit_stmt_exprs(i, f);
            }
            if let Some(c) = c {
                cond(c, f);
            }
            if let Some(s) = step {
                visit_expr(s, f);
            }
            visit_stmt_exprs(body, f);
        }
        S::RangeFor { range, body, .. } => {
            visit_expr(range, f);
            visit_stmt_exprs(body, f);
        }
        S::While { cond: c, body, .. } => {
            cond(c, f);
            visit_stmt_exprs(body, f);
        }
        S::DoWhile { body, cond: c, .. } => {
            visit_stmt_exprs(body, f);
            visit_expr(c, f);
        }
        _ => {}
    }
}

pub fn visit_expr(e: &sc::Expr, f: &mut dyn FnMut(&sc::Expr)) {
    use sc::ExprKind as K;
    f(e);
    match &e.kind {
        K::Call { callee, args } => {
            visit_expr(callee, f);
            args.iter().for_each(|a| visit_expr(a, f));
        }
        K::Binary { lhs, rhs, .. } | K::Assign { lhs, rhs, .. } => {
            visit_expr(lhs, f);
            visit_expr(rhs, f);
        }
        K::Unary { operand, .. } | K::Postfix { operand, .. } => visit_expr(operand, f),
        K::Conditional {
            cond,
            then_expr,
            else_expr,
        } => {
            visit_expr(cond, f);
            visit_expr(then_expr, f);
            visit_expr(else_expr, f);
        }
        K::Index { base, index } => {
            visit_expr(base, f);
            visit_expr(index, f);
        }
        K::Member { base, .. } => visit_expr(base, f),
        K::Cast { expr, .. } | K::Paren(expr) => visit_expr(expr, f),
        _ => {}
    }
}

/// The member functions that may block (wait, FIFO access, blocking
/// transport, or a call to one that does) — lowered as tasks.
fn blocking_functions(lw: &Lw, defs: &[(usize, &sc::FunctionDecl)]) -> BTreeSet<String> {
    let mut direct = BTreeSet::new();
    let mut calls: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (_, f) in defs {
        let name = f.base_name().to_string();
        let mut blocks = false;
        let mut callees = BTreeSet::new();
        if let Some(b) = &f.body {
            for s in &b.stmts {
                visit_stmt_exprs(s, &mut |e| {
                    let sc::ExprKind::Call { callee, args } = &e.kind else {
                        return;
                    };
                    match &callee.kind {
                        sc::ExprKind::Name(q) => {
                            let n = q.last_name();
                            if matches!(n, "wait" | "sc_start") {
                                blocks = true;
                            }
                            callees.insert(n.to_string());
                        }
                        sc::ExprKind::Member { base, name, .. } => {
                            let m = name.ident.name.as_str();
                            let sym = base.as_name().and_then(|q| lw.m.syms.get(q.last_name()));
                            match sym.map(|s| &s.kind) {
                                Some(SymKind::Fifo | SymKind::FifoIn | SymKind::FifoOut)
                                    if matches!(m, "read" | "write") =>
                                {
                                    blocks = true
                                }
                                Some(SymKind::InitSocket) if m == "b_transport" => blocks = true,
                                _ => {}
                            }
                            let _ = args;
                        }
                        _ => {}
                    }
                });
            }
        }
        if blocks {
            direct.insert(name.clone());
        }
        calls.insert(name, callees);
    }
    let mut out = direct;
    loop {
        let before = out.len();
        for (f, cs) in &calls {
            if cs.iter().any(|c| out.contains(c)) {
                out.insert(f.clone());
            }
        }
        if out.len() == before {
            break;
        }
    }
    // A void function is a task when it blocks; registered transport
    // methods with an `sc_time&` are tasks too (they may wait).
    for (_, f) in defs {
        if f.base_name() == "b_transport" {
            out.insert("b_transport".to_string());
        }
    }
    out
}
