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
use crate::ast::expr::{BinaryOp, ExprKind, Expression, NumberLiteral, UnaryOp};
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
    /// Members that are `sc_buffer`s.
    pub buffers: BTreeSet<String>,
    /// Resolved signals and the resolved out/inout ports: member → width.
    pub resolved: BTreeMap<String, u32>,
    /// SystemC basenames of the member objects (§5.17).
    pub sc_names: BTreeMap<String, String>,
    /// Ports some instance binds to an sc_buffer (§6.9): input port → the
    /// hidden input that carries the buffer's write count, and output port
    /// → the hidden output that counts the writes made through it.
    pub port_counters: BTreeMap<String, String>,
    pub port_wcounters: BTreeMap<String, String>,
    /// The interfaces a channel implements (their SV classes, §5.15).
    pub implements: Vec<String>,
}

/// A registered process before lowering.
struct ProcSpec {
    kind: sc::ProcessKind,
    func: String,
    span: ScSpan,
    sens: Vec<SensTerm>,
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
    /// sc_main: the testbench statements from this index on follow the
    /// last, unbounded `sc_start()` and run in a `final` block.
    tb_tail: Option<usize>,
    /// Names of the objects sc_main creates (top level, §5.17).
    tb_names: NameGen,
    /// The interfaces the module being lowered implements (a channel).
    implements: Vec<String>,
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
            tb_tail: None,
            tb_names: NameGen::default(),
            implements: Vec::new(),
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

/// SystemC object names within one parent (§5.17): the name an object is
/// constructed with — `s{"s"}`, `s("s")`, `SC_NAMED(s)`, or the
/// constructor's initializer `s("s")` — else `sc_gen_unique_name`'s
/// `<kind>_<n>`, numbered per kind in construction (declaration) order.
#[derive(Default)]
pub struct NameGen {
    counters: BTreeMap<&'static str, u32>,
}

impl NameGen {
    pub fn name(
        &mut self,
        v: &sc::VarDecl,
        d: &sc::Declarator,
        ctor_inits: &[&sc::MemInit],
    ) -> Option<String> {
        let q = v.ty.name()?;
        let kind = default_basename(q)?;
        let lit = |args: &[sc::Expr]| match args.first().map(|a| &a.kind) {
            Some(sc::ExprKind::StringLit { value, .. }) => Some(value.clone()),
            _ => None,
        };
        let given = match &d.init {
            Some(sc::Initializer::Brace(a) | sc::Initializer::Paren(a)) => lit(a),
            _ => None,
        }
        .or_else(|| {
            ctor_inits
                .iter()
                .find(|mi| mi.name.last_name() == d.name.name)
                .and_then(|mi| lit(&mi.args))
        });
        Some(given.unwrap_or_else(|| {
            let n = self.counters.entry(kind).or_insert(0);
            *n += 1;
            format!("{}_{}", kind, *n - 1)
        }))
    }
}

/// The width of a resolved signal or port, which picks its nettype.
fn resolved_width(lw: &Lw, ty: &Ty, span: ScSpan) -> R<u32> {
    match ty {
        Ty::Vec4 { w } => match w.n {
            Some(n) => Ok(n),
            None => lw.err(span, "the width of a resolved signal must be a constant"),
        },
        _ => lw.err(span, "a resolved signal carries sc_logic values"),
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
        // A channel: the interfaces it implements (its bases deriving from
        // sc_interface).
        for b in &class.bases {
            let consts = |e: &sc::Expr| self.lw.const_eval(e);
            let t = ty_of_name(&b.name, &self.lw.env, &consts).ok();
            if let Some(c) = t.as_ref().and_then(|t| self.lw.user_class(t))
                && self
                    .lw
                    .prog
                    .user_classes
                    .borrow()
                    .get(&c)
                    .is_some_and(|s| s.is_interface)
            {
                iface.implements.push(c);
            }
        }
        let mut name_gen = NameGen::default();
        for m in &class.members {
            let sc::Member::Field(v) = m else { continue };
            if v.specifiers.is_static {
                continue;
            }
            for d in &v.declarators {
                if let Some(n) = name_gen.name(v, d, &self.ctor_inits) {
                    iface.sc_names.insert(d.name.name.clone(), n);
                }
                let sym = self.member_sym(v, d)?;
                if let Some(sym) = sym {
                    if matches!(ScObjectKind::of(&v.ty), ScObjectKind::Buffer) {
                        iface.buffers.insert(sym.sv.clone());
                    }
                    if v.ty.name().is_some_and(drives_resolved) {
                        iface
                            .resolved
                            .insert(sym.sv.clone(), resolved_width(self.lw, &sym.ty, d.span)?);
                    }
                    if port_dir(&sym.kind).is_some() {
                        iface.ports.push((d.name.name.clone(), sym.kind.clone()));
                    }
                    iface.members.insert(d.name.name.clone(), sym);
                }
            }
        }
        // §6.9: a port bound to an sc_buffer passes on every write of it,
        // not only value changes — a write count travels beside the value.
        let int_t = Ty::int32();
        for (p, kind) in iface.ports.clone() {
            if !self.lw.prog.buffer_ports.contains(&(name.clone(), p.clone())) {
                continue;
            }
            let mut hidden = Vec::new();
            if matches!(kind, SymKind::InPort | SymKind::InOutPort) {
                let c = format!("__sc_bc_{}", p);
                iface.port_counters.insert(p.clone(), c.clone());
                hidden.push((c, SymKind::InPort));
            }
            if matches!(kind, SymKind::OutPort | SymKind::InOutPort) {
                let c = format!("__sc_bw_{}", p);
                iface.port_wcounters.insert(p.clone(), c.clone());
                hidden.push((c, SymKind::OutPort));
            }
            for (c, k) in hidden {
                iface.members.insert(
                    c.clone(),
                    Sym {
                        kind: k.clone(),
                        ty: int_t.clone(),
                        sv: c.clone(),
                    },
                );
                iface.ports.push((c, k));
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
        // An array of signals or ports (`sc_signal<T> s[N]`) is an array
        // of their values.
        let payload = |lw: &Lw| -> R<Ty> {
            let q = q.expect("library object has a name");
            let t = payload_ty(q, &lw.env, &consts).or_else(|m| lw.err(d.span, m))?;
            lw.with_dims(t, d)
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
            ScObjectKind::Port | ScObjectKind::Export => {
                let is_export = kind == ScObjectKind::Export;
                let arg = q
                    .and_then(|q| q.last_args())
                    .and_then(|a| a.first())
                    .and_then(|a| match a {
                        sc::TemplateArg::Type(t) => t.name().cloned(),
                        _ => None,
                    });
                let Some(iq) = arg else {
                    return self.lw.err(d.span, "the interface of a port is missing");
                };
                // The standard signal and FIFO interfaces: the port is the
                // matching specialized port (§6.8–§6.11, §6.24, §6.25).
                let std_kind = match iq.last_name() {
                    "sc_signal_in_if" => Some(SymKind::InPort),
                    "sc_signal_inout_if" | "sc_signal_write_if" => Some(SymKind::InOutPort),
                    "sc_fifo_in_if" => Some(SymKind::FifoIn),
                    "sc_fifo_out_if" => Some(SymKind::FifoOut),
                    _ => None,
                };
                if let Some(k) = std_kind {
                    if is_export {
                        return self.lw.err(
                            d.span,
                            "an sc_export of a signal or FIFO interface is not supported in simulation",
                        );
                    }
                    let t = payload_ty(&iq, &self.lw.env, &consts).or_else(|m| self.lw.err(d.span, m))?;
                    let t = match k {
                        SymKind::FifoIn | SymKind::FifoOut => Ty::Mailbox(Box::new(t)),
                        _ => t,
                    };
                    let t = self.lw.with_dims(t, d)?;
                    return Ok(Some(Sym { kind: k, ty: t, sv: name }));
                }
                let t = ty_of_name(&iq, &self.lw.env, &consts).ok();
                let iface = t.as_ref().and_then(|t| self.lw.user_class(t)).filter(|c| {
                    self.lw
                        .prog
                        .user_classes
                        .borrow()
                        .get(c)
                        .is_some_and(|s| s.is_interface)
                });
                let Some(iface) = iface else {
                    return self.lw.err(
                        d.span,
                        format!("'{}' is not an interface (a class derived from sc_interface)", iq.last_name()),
                    );
                };
                let pc = super::classes::port_class_name(&iface);
                let k = if is_export {
                    SymKind::Export(iface)
                } else {
                    SymKind::Port(iface)
                };
                (k, Ty::Class(pc))
            }
            ScObjectKind::AnalysisPort => {
                return self.lw.err(
                    d.span,
                    "analysis ports are not supported in simulation yet",
                );
            }
            ScObjectKind::Other => {
                if let Some(q) = q {
                    if let Some(module) = self.lw.module_of(q) {
                        return Ok(Some(Sym {
                            kind: SymKind::Instance(module),
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
            resolved: iface.resolved.clone(),
            sc_names: iface.sc_names.clone(),
            port_counters: iface.port_counters.clone(),
            port_wcounters: iface.port_wcounters.clone(),
            ..Default::default()
        };
        for b in &iface.buffers {
            self.add_buffer(b);
        }
        self.implements = iface.implements.clone();
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
            let inits: Vec<&sc::MemInit> = c.initializers.iter().collect();
            if let Err(e) = self.construct_members(class, &inits, &mut s) {
                self.lw.record(e);
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
        } else if let Err(e) = self.construct_members(class, &[], &mut s) {
            self.lw.record(e);
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
        self.event_mirrors()?;
        let mut funcs = self.lower_bodies(defs)?;
        funcs.push(self.destructor(class, name)?);
        funcs.extend(self.callback_functions(&s, false));
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

    /// Construct the module's member objects of user classes, in
    /// declaration order, from the constructor's initializer list or their
    /// own initializer (C++ builds members before the constructor body).
    fn construct_members(
        &mut self,
        class: &sc::ClassDecl,
        inits: &[&sc::MemInit],
        s: &mut Structure,
    ) -> R<()> {
        for m in &class.members {
            let sc::Member::Field(v) = m else { continue };
            if v.specifiers.is_static {
                continue;
            }
            for d in &v.declarators {
                let Some(sym) = self.lw.lookup(&d.name.name) else {
                    continue;
                };
                let Ty::Class(cls) = &sym.ty else { continue };
                if sym.kind != SymKind::Var {
                    continue;
                }
                let is_lib = is_lib_class(cls);
                if self.lw.user_class(&sym.ty).is_none() && !is_lib {
                    continue;
                }
                let args: Vec<sc::Expr> = match inits
                    .iter()
                    .find(|mi| mi.name.last_name() == d.name.name)
                {
                    Some(mi) => mi.args.clone(),
                    None => match &d.init {
                        Some(sc::Initializer::Assign(e)) => vec![e.clone()],
                        Some(sc::Initializer::Paren(a) | sc::Initializer::Brace(a)) => a.clone(),
                        None => Vec::new(),
                    },
                };
                if is_lib {
                    let x = self.lw.lib_object_new(&sym.ty, &args)?.expect("library object");
                    s.elab.push(assign(ident(&sym.sv), x));
                    continue;
                }
                let stmts = super::classes::construct_into(
                    self.lw,
                    ident(&sym.sv),
                    cls,
                    &args,
                    d.span,
                )?;
                s.elab.extend(stmts);
            }
        }
        Ok(())
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
        if matches!(n, "sc_module" | "sc_channel" | "sc_behavior" | "sc_prim_channel") {
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
                if let Some(sc::ExprKind::StringLit { value, .. }) = mi.args.first().map(|a| &a.kind) {
                    self.lw.m.inst_names.insert(n.to_string(), value.clone());
                }
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
            // Member objects were constructed by construct_members.
            SymKind::Var
                if self.lw.user_class(&sym.ty).is_some()
                    || matches!(&sym.ty, Ty::Class(c) if is_lib_class(c)) => {}
            SymKind::Var | SymKind::Boxed => {
                if let [a] = mi.args.as_slice() {
                    let (x, _) = self.lw.expr(a)?;
                    let target = self.lw.sym_target(&sym);
                    s.elab.push(assign(target, x));
                }
            }
            SymKind::Fifo => {
                if let Some(size) = fifo_size_arg(&mi.args) {
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
            if let Some(n) = self.runtime_name_in(a) {
                return self.lw.err(
                    a.span,
                    format!(
                        "a module constructor argument must be known before simulation ('{}' is computed at run time)",
                        n
                    ),
                );
            }
            out.push((p.clone(), self.lw.expr(a)?.0));
        }
        Ok(out)
    }

    /// A name in a module constructor argument whose value only exists at
    /// run time (the arguments become SystemVerilog parameters): anything
    /// but a constant, the enclosing module's own constructor parameters and
    /// template parameters.
    fn runtime_name_in(&self, a: &sc::Expr) -> Option<String> {
        let own = self
            .ifaces
            .get(&self.lw.m.name)
            .map(|i| i.ctor_params.clone())
            .unwrap_or_default();
        let mut bad = None;
        visit_expr(a, &mut |x| {
            if let sc::ExprKind::Name(q) = &x.kind
                && bad.is_none()
            {
                let n = q.last_name();
                let known = self.lw.const_eval(x).is_some()
                    || (!self.lw.m.tb && own.iter().any(|p| p == n))
                    || self.lw.env.tparams.contains_key(n)
                    || self.lw.lookup(n).is_none();
                if !known {
                    bad = Some(n.to_string());
                }
            }
        });
        bad
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
                let forced = match edge {
                    sc::SensitivityEdge::Pos => Some(Edge::Posedge),
                    sc::SensitivityEdge::Neg => Some(Edge::Negedge),
                    sc::SensitivityEdge::Any => None,
                };
                for it in items {
                    let entries = self.sens_item(it, forced)?;
                    match s.procs.last_mut() {
                        Some(p) => p.sens.extend(entries),
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

    /// One `sensitive << x` item; `forced` is the edge of a
    /// `sensitive_pos`/`sensitive_neg` list.
    fn sens_item(&mut self, e: &sc::Expr, forced: Option<Edge>) -> R<Vec<SensTerm>> {
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
        // A port or export of a user interface: the channel's default event,
        // or the event function named (`p->data_written_event()`).
        let (pt, pev) = match &e.kind {
            sc::ExprKind::Call { callee, args } if args.is_empty() => match &callee.kind {
                sc::ExprKind::Member { base, name, .. } => (base.as_ref(), name.ident.name.clone()),
                _ => (e, "default_event".to_string()),
            },
            _ => (e, "default_event".to_string()),
        };
        if let Some((obj, ifc, idx)) = self.lw.port_ref(pt) {
            let has = self
                .lw
                .prog
                .user_classes
                .borrow()
                .get(&ifc)
                .is_some_and(|s| s.events.contains(&pev));
            if !has {
                return self.lw.err(
                    e.span,
                    format!("the port's interface has no event function '{}'", pev),
                );
            }
            let snap = self.lw.module_var("__sc_ps", &Ty::Handle(ifc));
            let ch = self.lw.port_channel(&obj, idx.as_ref())?;
            let mut t = SensTerm::new(
                None,
                member(ident(&snap), &format!("__sc_ev_{}", pev)),
                base_name(pt),
            );
            t.setup = Some(assign(ident(&snap), ch));
            return Ok(vec![t]);
        }
        let (target, edge) = if let sc::ExprKind::Call { callee, args } = &e.kind
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
            (base.as_ref(), edge)
        } else {
            (e, None)
        };
        let edge = forced.or(edge);
        let name = base_name(target);
        let counter = if edge.is_none() {
            self.lw.buffer_counter_of(target)
        } else {
            None
        };
        if let Some((ev, false)) = &counter {
            return Ok(vec![SensTerm::new(None, ident(ev), name)]);
        }
        let (x, t) = self.lw.expr(target)?;
        // An sc_fifo's data events (§6.23.4): written by default.
        if let Ty::Mailbox(_) = t {
            let ev = match &e.kind {
                sc::ExprKind::Call { callee, .. }
                    if matches!(&callee.kind, sc::ExprKind::Member { name, .. } if name.ident.name == "data_read_event") =>
                {
                    "read_ev"
                }
                _ => "written_ev",
            };
            return Ok(vec![SensTerm::new(None, member(x, ev), name)]);
        }
        // An sc_event_queue's event (§5.11).
        if matches!(&t, Ty::Class(c) if c == "scrt_event_queue") {
            return Ok(vec![SensTerm::new(None, member(x, "ev"), name)]);
        }
        let mut v = vec![match edge {
            // §6.8.4: an sc_logic's edge is a change to '1' / '0'.
            Some(ed) if matches!(t, Ty::Vec4 { .. }) => SensTerm::logic_edge(ed, x, name.clone()),
            _ => SensTerm::new(edge, x, name.clone()),
        }];
        // A port some instance binds to an sc_buffer also wakes on its
        // writes (§6.9).
        if let Some((ev, true)) = counter {
            v.push(SensTerm::new(None, ident(&ev), name));
        }
        Ok(v)
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
                if let Some(sc::ExprKind::StringLit { value, .. }) = cargs.first().map(|a| &a.kind) {
                    self.lw.m.inst_names.insert(q.last_name().to_string(), value.clone());
                }
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
        // The module's own port or export: `exp(chan)`, `p.bind(x)`.
        let own = match &callee.kind {
            K::Name(q) if q.segments.len() == 1 => self.lw.lookup(q.last_name()),
            K::Member { base, name, .. } if name.ident.name == "bind" => base
                .as_name()
                .filter(|q| q.segments.len() == 1)
                .and_then(|q| self.lw.lookup(q.last_name())),
            _ => None,
        };
        if let Some(sym) = own
            && let SymKind::Port(ifc) | SymKind::Export(ifc) = &sym.kind
            && let [a] = args.as_slice()
        {
            let stmt = self.bind_port_object(ident(&sym.sv), ifc, a, e.span)?;
            s.elab.push(stmt);
            return Ok(true);
        }
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
                    let x = self.port_actual(a, module, p)?;
                    self.connect(s, &sym.sv, p, x);
                    self.bind_buffer_counts(s, &sym.sv, module, p, a)?;
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

    /// A process or clock first waits for sc_main's first `sc_start`; with
    /// no sc_main (a SystemVerilog top), it starts at time 0.
    fn start_wait(&self) -> Vec<Statement> {
        if self.lw.prog.sc_main.is_some() {
            vec![wait(ident("scrt_started"))]
        } else {
            Vec::new()
        }
    }

    /// Register an `sc_buffer` of the module being lowered and declare its
    /// write counter.
    fn add_buffer(&mut self, sv: &str) {
        if self.lw.m.buffers.insert(sv.to_string()) {
            self.lw.m.extra_items.push(data_decl(
                atom_t(crate::ast::types::IntegerAtomType::Int, false),
                &buffer_counter(sv),
                Vec::new(),
                None,
            ));
        }
    }

    /// Bind the port or export object `target` of interface `ifc` (§5.12.7,
    /// §5.14.5): to a channel (its adapter for the interface), to `*this`
    /// (the channel being lowered), or to another port or export, which the
    /// port then follows.
    fn bind_port_object(
        &mut self,
        target: Expression,
        ifc: &str,
        a: &sc::Expr,
        span: ScSpan,
    ) -> R<Statement> {
        let a = match &a.kind {
            sc::ExprKind::Unary {
                op: sc::UnaryOp::Deref,
                operand,
            } => operand.as_ref(),
            _ => a,
        };
        let compatible = |lw: &Lw, impls: &[String]| -> Option<String> {
            impls.iter().find(|x| lw.is_same_or_derived(x, ifc)).cloned()
        };
        let bind_ch = |x: Expression| expr_stmt(method(target.clone(), "bind_ch", vec![x]));
        let bind_up = |x: Expression| expr_stmt(method(target.clone(), "bind_up", vec![x]));
        match &a.kind {
            sc::ExprKind::This => {
                let Some(x) = compatible(self.lw, &self.implements) else {
                    return self.lw.err(span, "this module does not implement the port's interface");
                };
                return Ok(bind_ch(ident(&adapter_object(&x))));
            }
            sc::ExprKind::Name(q) if q.segments.len() == 1 => {
                if let Some(sym) = self.lw.lookup(q.last_name()) {
                    match &sym.kind {
                        SymKind::Instance(module) => {
                            let impls = self
                                .ifaces
                                .get(module)
                                .map(|i| i.implements.clone())
                                .unwrap_or_default();
                            let Some(x) = compatible(self.lw, &impls) else {
                                return self.lw.err(
                                    span,
                                    format!("'{}' does not implement the port's interface", q.last_name()),
                                );
                            };
                            return Ok(bind_ch(member(ident(&sym.sv), &adapter_object(&x))));
                        }
                        SymKind::Port(_) | SymKind::Export(_) => {
                            return Ok(bind_up(ident(&sym.sv)));
                        }
                        _ => {}
                    }
                }
            }
            sc::ExprKind::Member { base, name, .. } => {
                if let Some((inst, module)) = self.instance_of(base) {
                    let kind = self
                        .ifaces
                        .get(&module)
                        .and_then(|i| i.members.get(&name.ident.name))
                        .map(|m| m.kind.clone());
                    if matches!(kind, Some(SymKind::Port(_) | SymKind::Export(_))) {
                        return Ok(bind_up(member(ident(&inst), &name.ident.name)));
                    }
                }
            }
            _ => {}
        }
        self.lw.err(
            span,
            "a port or export binds to a channel, `*this`, or another port or export",
        )
    }

    /// The actual of a port binding. A resolved out/inout port connects to
    /// the resolved net itself (it drives it); any other port to the value.
    fn port_actual(&mut self, a: &sc::Expr, module: &str, port: &str) -> R<Expression> {
        let child_resolved = self
            .ifaces
            .get(module)
            .is_some_and(|i| i.resolved.contains_key(port));
        let net = a
            .as_name()
            .and_then(|q| self.lw.lookup(q.last_name()))
            .filter(|sym| sym.is_signal_like() && self.lw.m.resolved.contains_key(&sym.sv));
        match (child_resolved, net) {
            (true, Some(sym)) => Ok(ident(&sym.sv)),
            (true, None) => self.lw.err(
                a.span,
                format!(
                    "port '{}' of '{}' drives a resolved signal: bind it to an sc_signal_resolved, an sc_signal_rv or a resolved port",
                    port, module
                ),
            ),
            (false, Some(_))
                if self
                    .ifaces
                    .get(module)
                    .and_then(|i| i.members.get(port))
                    .is_some_and(|m| m.kind != SymKind::InPort) =>
            {
                self.lw.err(
                    a.span,
                    format!(
                        "binding the output port '{}' of '{}' to a resolved signal is not supported in simulation; declare it sc_out_resolved or sc_out_rv",
                        port, module
                    ),
                )
            }
            _ => Ok(self.lw.expr(a)?.0),
        }
    }

    /// §6.9: binding a port to an sc_buffer (or to a parent port bound to
    /// one) also connects its hidden write count — the buffer's event count
    /// into an input port, the port's own write count out of an output.
    fn bind_buffer_counts(
        &mut self,
        s: &mut Structure,
        inst: &str,
        module: &str,
        port: &str,
        a: &sc::Expr,
    ) -> R<()> {
        let Some((ev, value_too)) = self.lw.buffer_counter_of(a) else {
            return Ok(());
        };
        let (cin, cout) = match self.ifaces.get(module) {
            Some(i) => (i.port_counters.get(port).cloned(), i.port_wcounters.get(port).cloned()),
            None => (None, None),
        };
        if cin.is_none() && cout.is_none() {
            return self.lw.err(
                a.span,
                "binding an sc_buffer to a port this way is not supported in simulation",
            );
        }
        if let Some(c) = cin {
            self.connect(s, inst, &c, ident(&ev));
        }
        if let Some(c) = cout {
            // Only a buffer itself sums its writers; a parent's port passes
            // its own write count up instead.
            let Some(buf) = a
                .as_name()
                .map(|q| q.last_name().to_string())
                .filter(|_| !value_too)
            else {
                return self.lw.err(
                    a.span,
                    "an output port bound to a port that leads to an sc_buffer is not supported in simulation",
                );
            };
            let v = format!("__sc_bw_{}_{}", inst, port);
            self.lw.m.extra_items.push(data_decl(
                atom_t(crate::ast::types::IntegerAtomType::Int, false),
                &v,
                Vec::new(),
                None,
            ));
            self.connect(s, inst, &c, ident(&v));
            self.lw.m.buffer_sources.entry(buf).or_default().push(v);
        }
        Ok(())
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
                let x = self.port_actual(a, module, port)?;
                self.connect(s, inst, port, x);
                self.bind_buffer_counts(s, inst, module, port, a)
            }
            Some(SymKind::FifoIn | SymKind::FifoOut) => {
                let (x, _) = self.lw.expr(a)?;
                s.elab.push(assign(member(ident(inst), port), x));
                Ok(())
            }
            Some(SymKind::Port(ifc) | SymKind::Export(ifc)) => {
                let stmt = self.bind_port_object(member(ident(inst), port), &ifc, a, span)?;
                s.elab.push(stmt);
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
        let writes = write_sets(self.lw, class, name);
        let mut writers: BTreeMap<String, BTreeSet<usize>> = BTreeMap::new();
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
                for w in writes.get(&f).into_iter().flatten() {
                    writers.entry(w.clone()).or_default().insert(i);
                }
                if let Some(callees) = graph.get(&f) {
                    stack.extend(callees.iter().cloned());
                }
            }
        }
        // §6.4.4: the signals and ports two processes may write, with the
        // default SC_ONE_WRITER policy, check their writer at every write.
        let relaxed: BTreeSet<String> = class
            .members
            .iter()
            .filter_map(|m| match m {
                sc::Member::Field(v) if many_writers(&v.ty) => Some(v),
                _ => None,
            })
            .flat_map(|v| v.declarators.iter().map(|d| d.name.name.clone()))
            .collect();
        self.lw.m.one_writer = writers
            .into_iter()
            .filter(|(sig, ps)| {
                ps.len() >= 2
                    && !relaxed.contains(sig)
                    && !self.lw.m.resolved.contains_key(sig)
                    && self.lw.m.syms.get(sig).is_some_and(|s| {
                        matches!(
                            s.kind,
                            SymKind::Signal | SymKind::OutPort | SymKind::InOutPort
                        )
                    })
            })
            .map(|(sig, _)| sig)
            .collect();
        self.lw.m.proc_names = s.procs.iter().map(|p| (p.func.clone(), p.kind)).collect();
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

    /// `function void __sc_dtor()`: the module's destructor body, then its
    /// child modules held by value, in reverse declaration order (C++
    /// destroys members after the body, last first). sc_main destroys its
    /// modules when it returns.
    fn destructor(&mut self, class: &'a sc::ClassDecl, name: &str) -> R<ModuleItem> {
        let cpp = class.name_str().unwrap_or(name).to_string();
        let def = class
            .members
            .iter()
            .find_map(|m| match m {
                sc::Member::Destructor(f) if f.body.is_some() => Some((self.lw.tu, f)),
                _ => None,
            })
            .or_else(|| {
                self.lw
                    .prog
                    .out_of_class
                    .get(&cpp)
                    .and_then(|v| v.iter().find(|(_, f)| f.base_name().starts_with('~')))
                    .map(|(t, f)| (*t, *f))
            });
        let mut body = Vec::new();
        if let Some((tu, f)) = def
            && let Some(b) = &f.body
        {
            let saved = self.lw.tu;
            self.lw.tu = tu;
            self.lw.f = FnCtx {
                scopes: vec![BTreeMap::new()],
                ret: Some(Ty::Void),
                ..Default::default()
            };
            let stmts = self.lw.block(&b.stmts);
            if self.lw.f.is_task {
                let span = f.span;
                self.lw.tu = saved;
                return self.lw.err(span, "a destructor cannot wait");
            }
            body.extend(std::mem::take(&mut self.lw.f.decls));
            body.extend(stmts);
            self.lw.tu = saved;
        }
        let children = self.value_children(class);
        for c in children.into_iter().rev() {
            body.push(expr_stmt(call(member(ident(&c), "__sc_dtor"), Vec::new())));
        }
        Ok(ModuleItem::FunctionDeclaration(function_decl(
            "__sc_dtor",
            void_t(),
            Vec::new(),
            body,
        )))
    }

    /// The child modules a module holds by value (not through a pointer),
    /// in declaration order, that are SystemC modules (with `__sc_dtor`).
    fn value_children(&self, class: &sc::ClassDecl) -> Vec<String> {
        let mut out = Vec::new();
        for m in &class.members {
            let sc::Member::Field(v) = m else { continue };
            for d in &v.declarators {
                if !d.ptr_ops.is_empty() || !v.ty.ptr_ops.is_empty() {
                    continue;
                }
                if let Some(sym) = self.lw.lookup(&d.name.name)
                    && let SymKind::Instance(module) = &sym.kind
                    && !self.lw.prog.foreign.contains_key(module)
                {
                    out.push(sym.sv);
                }
            }
        }
        out
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
                    let ty = self.lw.ty(&p.ty, p.span);
                    // An event is always the caller's (`sc_event&`, const too).
                    matches!(ty, Ok(Ty::Event))
                        || p.ty.ptr_ops.contains(&sc::PtrOp::LRef)
                            && !p.ty.is_const
                            && !matches!(ty, Ok(Ty::Class(_)))
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
            shared: matches!(self.lw.m.fn_proc.get(&name), Some(None)),
            ret_copy: super::classes::returns_copy(f, &sig.ret),
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
            // An object passed by value is the callee's own copy.
            if self.lw.user_class(&ty).is_some()
                && matches!(ty, Ty::Class(_))
                && !p
                    .ty
                    .ptr_ops
                    .iter()
                    .any(|o| matches!(o, sc::PtrOp::LRef | sc::PtrOp::RRef))
            {
                prologue.push(assign(ident(&pname), method(ident(&pname), "__sc_copy", vec![])));
            }
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
                    kind: if matches!(ty, Ty::Event) { SymKind::Event } else { SymKind::Var },
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
        if !self.lw.prog.user_classes.borrow().is_empty() {
            items.insert(1, import_all("sc_user"));
        }
        let mut ports = Vec::new();
        let mut clock_items = Vec::new();
        for (clk, args, span) in &s.clocks {
            clock_items.push(self.clock_gen(clk, args, *span)?);
        }
        let syms = self.lw.m.syms.clone();
        let resolved = self.lw.m.resolved.clone();
        for (pname, kind) in port_order {
            let sym = &syms[pname];
            // A resolved out/inout port is an inout net its processes drive.
            if let Some(w) = resolved.get(pname) {
                self.lw.rv_widths.insert(*w);
                ports.push(ansi_port(
                    PortDirection::Inout,
                    named_t(&rv_nettype(*w), Vec::new()),
                    pname,
                    Vec::new(),
                ));
                continue;
            }
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
            if let Some(w) = resolved.get(n) {
                self.lw.rv_widths.insert(*w);
                items.push(data_decl(
                    named_t(&rv_nettype(*w), Vec::new()),
                    &sym.sv,
                    Vec::new(),
                    None,
                ));
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
                // A port or export of a user interface: an object of its
                // port class, named for diagnostics.
                SymKind::Port(_) | SymKind::Export(_) => {
                    let (dt, dims) = sv_type(&sym.ty);
                    let base = self
                        .lw
                        .m
                        .sc_names
                        .get(n)
                        .cloned()
                        .unwrap_or_else(|| n.clone());
                    let is_export = matches!(sym.kind, SymKind::Export(_));
                    (
                        dt,
                        dims,
                        Some(new_obj(Some(vec![string(&base), sized(1, is_export as u64)]))),
                    )
                }
                SymKind::Clock => (
                    bit_t(1, false),
                    Vec::new(),
                    Some(sized(1, self.clock_init.get(n).copied().unwrap_or(0))),
                ),
                // A member object of a user class (constructed at
                // elaboration); a signal of one holds a default-built value.
                _ if matches!(sym.ty, Ty::Class(_)) && self.lw.user_class(&sym.ty).is_some() => {
                    let (dt, dims) = sv_type(&sym.ty);
                    let init = match sym.kind {
                        SymKind::Var => new_obj(None),
                        _ => self.default_object(&sym.ty)?,
                    };
                    (dt, dims, Some(init))
                }
                _ => {
                    let (dt, dims) = sv_type(&sym.ty);
                    (dt, dims, None)
                }
            };
            items.push(data_decl(dt, &sym.sv, dims, init));
        }
        items.append(&mut self.lw.m.extra_items);
        items.extend(self.kernel_items());
        // Children.
        for inst in &s.insts {
            items.push(instance(
                self.lw.prog.sv_module_name(&inst.module),
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
        // A channel: an adapter object per interface it implements.
        let (chan_items, chan_elab) = self.channel_items()?;
        items.extend(chan_items);
        // Elaboration code: output ports of a user class start with a
        // default-built value (the bound signal's), as SystemC's.
        let mut elab = elab_decls;
        // Port and export objects learn their hierarchical names.
        if !self.lw.m.tb {
            for (n, sym) in &syms {
                if matches!(sym.kind, SymKind::Port(_) | SymKind::Export(_)) {
                    let base = self.lw.m.sc_names.get(n).cloned().unwrap_or_else(|| n.clone());
                    elab.push(assign(
                        member(ident(&sym.sv), "name"),
                        concat(vec![ident("__sc_path"), string(&format!(".{}", base))]),
                    ));
                }
            }
        }
        for (pname, kind) in port_order {
            let sym = &syms[pname];
            if matches!(kind, SymKind::OutPort | SymKind::InOutPort)
                && matches!(sym.ty, Ty::Class(_))
                && self.lw.user_class(&sym.ty).is_some()
            {
                elab.push(assign(ident(pname), self.default_object(&sym.ty)?));
            }
        }
        elab.extend(fw_assigns);
        elab.extend(chan_elab);
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

    /// Module items the kernel model needs: the instance's SystemC name, the
    /// drivers of resolved nets, the writer check of one-writer signals and
    /// the running process's identity.
    fn kernel_items(&mut self) -> Vec<ModuleItem> {
        use crate::ast::types::{IntegerAtomType, SimpleType};
        let mut items = Vec::new();
        let int_t = || atom_t(IntegerAtomType::Int, false);
        let str_t = || simple_t(SimpleType::String);
        if !self.lw.m.tb {
            // §5.17: `name()` is the instance path, sc_main's root removed.
            items.push(data_decl(
                str_t(),
                "__sc_path",
                Vec::new(),
                Some(call_fn(
                    "scrt_name",
                    vec![sys("$sformatf", vec![string("%m")])],
                )),
            ));
        }
        // §6.13.4: every writer of a resolved net drives {written, value};
        // the nettype resolves the written ones.
        for ((net, _), drv) in self.lw.m.drivers.clone() {
            let w = self.lw.m.resolved[&net];
            items.push(data_decl(
                sv_scalar_type(&Ty::Vec4 {
                    w: Width::known(w + 1),
                }),
                &drv,
                Vec::new(),
                Some(concat(vec![
                    sized(1, 0),
                    size_cast(w, ex(ExprKind::Number(NumberLiteral::UnbasedUnsized('z')))),
                ])),
            ));
            items.push(cont_assign(ident(&net), ident(&drv)));
        }
        // §6.9: an sc_buffer's event count — its own writes and those made
        // through the output ports bound to it.
        for b in self.lw.m.buffers.clone() {
            let ev = buffer_event(&b);
            let sum = self
                .lw
                .m
                .buffer_sources
                .get(&b)
                .into_iter()
                .flatten()
                .fold(ident(&buffer_counter(&b)), |acc, v| {
                    bin(BinaryOp::Add, acc, ident(v))
                });
            items.push(data_decl(int_t(), &ev, Vec::new(), None));
            items.push(cont_assign(ident(&ev), sum));
        }
        // §5.15.6 update phase of a primitive channel: request_update() arms
        // a nonblocking trigger (the NBA region, SystemC's update phase);
        // update() then runs once.
        if self.lw.m.uses_update {
            items.push(data_decl(bit_t(1, false), "__sc_upd", Vec::new(), None));
            items.push(data_decl(
                simple_t(crate::ast::types::SimpleType::Event),
                "__sc_upd_ev",
                Vec::new(),
                None,
            ));
            items.push(ModuleItem::FunctionDeclaration(function_decl(
                "__sc_request_update",
                void_t(),
                Vec::new(),
                vec![if_(
                    unary(UnaryOp::LogNot, ident("__sc_upd")),
                    block(vec![assign(ident("__sc_upd"), sized(1, 1)), trigger_nb("__sc_upd_ev")]),
                    None,
                )],
            )));
            items.push(initial(forever(block(vec![
                at(vec![event_expr(None, ident("__sc_upd_ev"))], null_stmt()),
                assign(ident("__sc_upd"), sized(1, 0)),
                expr_stmt(call_fn("update", vec![])),
            ]))));
        }
        let procs = self.lw.m.proc_names.clone();
        if !self.lw.m.one_writer.is_empty() {
            for sig in self.lw.m.one_writer.clone() {
                items.push(data_decl(int_t(), &one_writer_var(&sig), Vec::new(), Some(int(0))));
            }
            let table = |f: &dyn Fn(&(String, sc::ProcessKind)) -> String| -> Vec<Statement> {
                vec![case_(
                    ident("p"),
                    procs
                        .iter()
                        .enumerate()
                        .map(|(i, p)| (int(i as i64 + 1), ret(Some(string(&f(p))))))
                        .collect(),
                    Some(ret(Some(string("")))),
                )]
            };
            items.push(ModuleItem::FunctionDeclaration(function_decl(
                "__sc_proc_name",
                str_t(),
                vec![fport(PortDirection::Input, int_t(), "p")],
                table(&|p| p.0.clone()),
            )));
            items.push(ModuleItem::FunctionDeclaration(function_decl(
                "__sc_proc_kind",
                str_t(),
                vec![fport(PortDirection::Input, int_t(), "p")],
                table(&|p| {
                    match p.1 {
                        sc::ProcessKind::Method => "sc_method_process",
                        sc::ProcessKind::Thread => "sc_thread_process",
                        sc::ProcessKind::CThread => "sc_cthread_process",
                    }
                    .to_string()
                }),
            )));
            // The first process to write the signal owns it; another one
            // writing it is E115 (writes outside processes are not checked).
            let full = |p: &str| {
                concat(vec![
                    ident("__sc_path"),
                    string("."),
                    call_fn("__sc_proc_name", vec![ident(p)]),
                ])
            };
            items.push(ModuleItem::FunctionDeclaration(function_decl(
                "__sc_one_writer",
                bit_t(1, false),
                vec![
                    fport(PortDirection::Inout, int_t(), "w"),
                    fport(PortDirection::Input, int_t(), "pid"),
                    fport(PortDirection::Input, str_t(), "sig"),
                ],
                vec![
                    if_(
                        bin(
                            BinaryOp::LogOr,
                            bin(BinaryOp::Eq, ident("pid"), int(0)),
                            bin(BinaryOp::Eq, ident("w"), ident("pid")),
                        ),
                        ret(Some(sized(1, 1))),
                        None,
                    ),
                    if_(
                        bin(BinaryOp::Eq, ident("w"), int(0)),
                        block(vec![assign(ident("w"), ident("pid")), ret(Some(sized(1, 1)))]),
                        None,
                    ),
                    expr_stmt(call_fn(
                        "scrt_e115",
                        vec![
                            ident("sig"),
                            full("w"),
                            call_fn("__sc_proc_kind", vec![ident("w")]),
                            full("pid"),
                            call_fn("__sc_proc_kind", vec![ident("pid")]),
                        ],
                    )),
                    ret(Some(sized(1, 0))),
                ],
            )));
        }
        if self.lw.m.needs_pid {
            // The process running a shared function: each process wrapper
            // records its handle (§9.7 process::self()).
            items.push(data_decl(
                named_t("process", Vec::new()),
                "__sc_ph",
                vec![unpacked(int(procs.len().max(1) as i64))],
                None,
            ));
            let mut body = Vec::new();
            for i in 0..procs.len() {
                body.push(if_(
                    bin(
                        BinaryOp::Eq,
                        index(ident("__sc_ph"), int(i as i64)),
                        process_self(),
                    ),
                    ret(Some(int(i as i64 + 1))),
                    None,
                ));
            }
            body.push(ret(Some(int(0))));
            items.push(ModuleItem::FunctionDeclaration(function_decl(
                "__sc_pid",
                int_t(),
                Vec::new(),
                body,
            )));
        }
        items
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
        // `argc`/`argv`: the program name, then the values of
        // `+sc_args=a,b,…` (scrt_args).
        for p in &f.params {
            let Some(n) = &p.name else { continue };
            if p.ty.ptr_ops.is_empty() && p.array_dims.is_empty() {
                self.lw
                    .declare_local(&n.name, Ty::int32(), SymKind::Var, Some(call_fn("scrt_argc", vec![])));
            } else {
                self.lw.declare_local(
                    &n.name,
                    Ty::Queue(Box::new(Ty::Str)),
                    SymKind::Var,
                    Some(call_fn("scrt_args", vec![])),
                );
            }
        }
        // Free functions sc_main calls, lowered into the testbench module.
        let mut defs = vec![(self.lw.tu, f)];
        self.add_free_functions(&mut defs);
        defs.remove(0);
        self.register_sigs(&defs)?;
        if let Some(b) = &f.body {
            match unbounded_start_tail(&b.stmts) {
                Some(i) => {
                    self.walk(&b.stmts[..i], &mut s);
                    self.tb_tail = Some(s.elab.len());
                    self.walk(&b.stmts[i..], &mut s);
                }
                None => self.walk(&b.stmts, &mut s),
            }
        }
        let decls = std::mem::take(&mut self.lw.f.decls);
        let stmts = std::mem::take(&mut s.elab);
        self.lw.m.procs.clear();
        let saved = std::mem::take(&mut self.lw.f);
        let mut funcs = self.lower_bodies(defs)?;
        funcs.extend(self.callback_functions(&s, true));
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
        let module = v.ty.name().and_then(|q| self.lw.module_of(q));
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
                    if let Some(n) = self.tb_names.name(v, d, &[]) {
                        self.lw.m.sc_names.insert(d.name.name.clone(), n);
                    }
                    let Some(sym) = self.member_sym(v, d)? else {
                        continue;
                    };
                    if v.ty.name().is_some_and(drives_resolved) {
                        let w = resolved_width(self.lw, &sym.ty, d.span)?;
                        self.lw.m.resolved.insert(sym.sv.clone(), w);
                    }
                    let args = match &d.init {
                        Some(sc::Initializer::Paren(a) | sc::Initializer::Brace(a)) => a.clone(),
                        _ => Vec::new(),
                    };
                    match sym.kind {
                        SymKind::Clock => s.clocks.push((d.name.name.clone(), args, d.span)),
                        SymKind::Fifo => {
                            if let Some(n) = fifo_size_arg(&args) {
                                let (x, _) = self.lw.expr(n)?;
                                self.fifo_size.insert(d.name.name.clone(), x);
                            }
                        }
                        _ => {}
                    }
                    if matches!(kind, ScObjectKind::Buffer) {
                        self.add_buffer(&sym.sv);
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
                    if let Some(sc::ExprKind::StringLit { value, .. }) = args.first().map(|a| &a.kind) {
                        self.lw.m.inst_names.insert(d.name.name.clone(), value.clone());
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
                    // A module object of sc_main (not one made with `new`)
                    // is destroyed when sc_main returns.
                    let by_value = d.ptr_ops.is_empty()
                        && !matches!(&d.init, Some(sc::Initializer::Assign(sc::Expr { kind: sc::ExprKind::New { .. }, .. })))
                        && !self.lw.prog.foreign.contains_key(&module);
                    if by_value {
                        self.lw.m.tb_values.push(sv.clone());
                    }
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
                body: Box::new(if self.lw.m.buffers.contains(sig) {
                    let n = buffer_counter(sig);
                    block(vec![
                        assign(target, index(ident(slot), ident("k"))),
                        assign(ident(&n), bin(BinaryOp::Add, ident(&n), int(1))),
                    ])
                } else {
                    assign(target, index(ident(slot), ident("k")))
                }),
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
        // sc_main's module objects are destroyed when it returns, last
        // declared first.
        let mut destroy: Vec<Statement> = vec![
            if_(ident("__sc_destroyed"), ret(None), None),
            assign(ident("__sc_destroyed"), sized(1, 1)),
        ];
        destroy.extend(
            self.lw
                .m
                .tb_values
                .iter()
                .rev()
                .map(|v| expr_stmt(call(member(ident(v), "__sc_dtor"), Vec::new()))),
        );
        items.push(data_decl(bit_t(1, false), "__sc_destroyed", Vec::new(), None));
        items.push(ModuleItem::FunctionDeclaration(function_decl(
            "__sc_destroy",
            void_t(),
            Vec::new(),
            destroy,
        )));
        items.append(&mut self.lw.m.extra_items);
        let (decls, mut stmts) = tb.unwrap_or_default();
        let Some(at) = self.tb_tail.take() else {
            let mut body = decls;
            body.extend(stmts);
            body.push(expr_stmt(call_fn("__sc_destroy", vec![])));
            body.push(expr_stmt(sys("$finish", vec![])));
            items.push(initial(block(body)));
            return items;
        };
        // An unbounded sc_start() also returns when no events are left
        // (IEEE 1666-2023 §4.5.7), where SystemVerilog simulation simply
        // ends; the statements after it run in a `final` block, which
        // both ends reach. sc_main's locals move to the module so the
        // final block sees them.
        let mut tail = vec![assign(ident("scrt_tb_now"), sys("$time", vec![]))];
        tail.extend(stmts.split_off(at));
        tail.push(expr_stmt(call_fn("__sc_destroy", vec![])));
        let mut body = Vec::new();
        for d in decls {
            let StatementKind::VarDecl {
                data_type,
                declarators,
                ..
            } = d.kind
            else {
                body.push(d);
                continue;
            };
            for v in declarators {
                items.push(data_decl(
                    data_type.clone(),
                    &v.name.name,
                    v.dimensions,
                    None,
                ));
                if let Some(init) = v.init {
                    body.push(assign(ident(&v.name.name), init));
                }
            }
        }
        body.extend(stmts);
        body.push(expr_stmt(sys("$finish", vec![])));
        items.push(initial(block(body)));
        items.push(ModuleItem::FinalConstruct(
            crate::ast::decl::FinalConstruct {
                stmt: block(tail),
                span: sp(),
            },
        ));
        items
    }

    /// The adapters of a channel (§5.15): for each interface it implements,
    /// a class extending the interface whose methods call the channel's
    /// member functions (through module-level aliases: inside the class a
    /// method's own name would name itself), and an object of it that the
    /// ports bound to the channel hold. The interface's events alias the
    /// events the channel's event functions return.
    fn channel_items(&mut self) -> R<(Vec<ModuleItem>, Vec<Statement>)> {
        let mut items = Vec::new();
        let elab = Vec::new();
        for ifc in self.implements.clone() {
            let Some(isig) = self.lw.prog.user_classes.borrow().get(&ifc).cloned() else {
                continue;
            };
            let cls = format!("__sc_ifc_{}", ifc.trim_start_matches("sc_c_"));
            let obj = adapter_object(&ifc);
            let mut citems = Vec::new();
            for (mname, overloads) in &isig.methods {
                if isig.events.contains(mname) {
                    continue;
                }
                for ms in overloads {
                    let Some(fsig) = self.lw.m.funcs.get(mname).cloned() else {
                        return self.lw.err(
                            ScSpan::default(),
                            format!(
                                "channel '{}' does not implement '{}' of '{}'",
                                self.lw.m.name,
                                mname,
                                isig.cpp
                            ),
                        );
                    };
                    let alias = format!("__sc_chm_{}_{}", ifc.trim_start_matches("sc_c_"), ms.sv);
                    let mut ports = Vec::new();
                    let mut args = Vec::new();
                    for (i, t) in ms.params.iter().enumerate() {
                        let by_ref = ms.sig.by_ref.get(i).copied().unwrap_or(false);
                        let dir = if by_ref {
                            PortDirection::Ref
                        } else {
                            PortDirection::Input
                        };
                        // An override keeps the interface's argument names.
                        let n = &ms.pnames[i];
                        ports.push(fport(dir, sv_scalar_type(t), n));
                        args.push(ident(n));
                    }
                    let returns = !matches!(ms.sig.ret, Ty::Void);
                    if returns {
                        ports.push(fport(PortDirection::Output, sv_scalar_type(&ms.sig.ret), "__sc_ret"));
                    }
                    // The class method calls the module alias.
                    let mut call_args = args.clone();
                    if returns {
                        call_args.push(ident("__sc_ret"));
                    }
                    citems.push(class_task(
                        task_decl(&ms.sv, ports.clone(), vec![expr_stmt(call_fn(&alias, call_args))]),
                        true,
                    ));
                    // The alias calls the member function.
                    let body = if fsig.is_task && returns {
                        let mut a = args.clone();
                        a.push(ident("__sc_ret"));
                        vec![expr_stmt(call_fn(mname, a))]
                    } else if returns {
                        vec![assign(ident("__sc_ret"), call_fn(mname, args.clone()))]
                    } else {
                        vec![expr_stmt(call_fn(mname, args.clone()))]
                    };
                    items.push(ModuleItem::TaskDeclaration(task_decl(&alias, ports, body)));
                }
            }
            items.push(ModuleItem::ClassDeclaration(class_decl(&cls, Some(&ifc), citems)));
            items.push(data_decl(named_t(&cls, Vec::new()), &obj, Vec::new(), Some(new_obj(None))));
            // Its events are triggered with the channel's (event_mirrors).
        }
        Ok((items, elab))
    }

    /// The interface objects' events to trigger with each channel event an
    /// interface event function returns (`ModCtx::ev_mirrors`).
    fn event_mirrors(&mut self) -> R<()> {
        for ifc in self.implements.clone() {
            let Some(isig) = self.lw.prog.user_classes.borrow().get(&ifc).cloned() else {
                continue;
            };
            let obj = adapter_object(&ifc);
            for e in &isig.events {
                if e == "default_event" && !self.defines_member_function(e) {
                    continue;
                }
                let ev = self.event_function_target(e)?;
                let ExprKind::Ident(h) = &ev.kind else {
                    return self.lw.err(
                        ScSpan::default(),
                        format!("'{}' must return an sc_event member of the channel", e),
                    );
                };
                let Some(seg) = h.path.last() else { continue };
                self.lw
                    .m
                    .ev_mirrors
                    .entry(seg.name.name.clone())
                    .or_default()
                    .push(member(ident(&obj), &format!("__sc_ev_{}", e)));
            }
        }
        Ok(())
    }

    /// §4.4 callbacks: `__sc_cb_<k>()` calls the module's own callback, then
    /// those of its child modules in construction order (sc_main's calls
    /// its top modules'): the kernel's hierarchy order.
    fn callback_functions(&self, s: &Structure, tb: bool) -> Vec<ModuleItem> {
        if !self.lw.prog.has_callbacks() {
            return Vec::new();
        }
        let foreign: BTreeSet<&String> = self.lw.prog.foreign.values().collect();
        let mut out = Vec::new();
        for (k, cb) in super::program::CALLBACKS {
            let mut body = Vec::new();
            if !tb && self.defines_member_function(cb) {
                body.push(expr_stmt(call_fn(cb, vec![])));
            }
            for i in &s.insts {
                if !foreign.contains(&i.module) {
                    body.push(expr_stmt(call(member(ident(&i.sv), &format!("__sc_cb_{}", k)), Vec::new())));
                }
            }
            out.push(ModuleItem::FunctionDeclaration(function_decl(
                &format!("__sc_cb_{}", k),
                void_t(),
                Vec::new(),
                body,
            )));
        }
        out
    }

    /// Whether the module being lowered defines member function `f`.
    fn defines_member_function(&self, f: &str) -> bool {
        let in_class = self.lw.prog.classes.get(&self.lw.m.name).is_some_and(|(_, c, _)| {
            c.members
                .iter()
                .any(|m| matches!(m, sc::Member::Method(fd) if fd.base_name() == f && fd.body.is_some()))
        });
        in_class
            || self
                .lw
                .prog
                .out_of_class
                .get(&self.lw.m.name)
                .is_some_and(|v| v.iter().any(|(_, fd)| fd.base_name() == f))
    }

    /// The event a channel's `const sc_event& f() const { return ev; }`
    /// returns.
    fn event_function_target(&mut self, f: &str) -> R<Expression> {
        let class = self.lw.prog.classes.get(&self.lw.m.name).map(|(_, c, _)| *c);
        let def = class.and_then(|c| {
            c.members.iter().find_map(|m| match m {
                sc::Member::Method(fd) if fd.base_name() == f && fd.body.is_some() => Some(fd),
                _ => None,
            })
        });
        let def = def.or_else(|| {
            self.lw
                .prog
                .out_of_class
                .get(&self.lw.m.name)
                .and_then(|v| v.iter().find(|(_, fd)| fd.base_name() == f).map(|(_, fd)| *fd))
        });
        let ret_expr = def
            .and_then(|fd| fd.body.as_ref())
            .and_then(|b| match b.stmts.as_slice() {
                [sc::Stmt::Return(Some(e), _)] => Some(e.clone()),
                _ => None,
            });
        match ret_expr {
            Some(e) => match self.lw.expr(&e)? {
                (x, Ty::Event) => Ok(x),
                _ => self.lw.err(e.span, format!("'{}' must return an sc_event of the channel", f)),
            },
            None => self.lw.err(
                ScSpan::default(),
                format!("'{}' of channel '{}' must be `return <event>;`", f, self.lw.m.name),
            ),
        }
    }

    /// A default-constructed object of a user class (a signal's or port's
    /// initial value: `sc_signal<T>` default-constructs its `T`).
    fn default_object(&self, ty: &Ty) -> R<Expression> {
        let Ty::Class(cls) = ty else {
            unreachable!("an object type")
        };
        let k = self
            .lw
            .prog
            .user_classes
            .borrow()
            .get(cls)
            .and_then(|s| s.ctor(0));
        match k {
            Some(k) => Ok(call(member(ident(cls), &format!("__sc_make{}", k)), Vec::new())),
            None => self.lw.err(
                ScSpan::default(),
                format!("'{}' needs a default constructor to be a signal or port value", cls.trim_start_matches("sc_c_")),
            ),
        }
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
        let mut body = self.start_wait();
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
                return at(p.sens.iter().map(SensTerm::event).collect(), null_stmt());
            }
            let branches = p
                .sens
                .iter()
                .map(|t| {
                    let mut v = vec![at(vec![t.event()], null_stmt())];
                    if my_flags.contains(&t.name) {
                        v.push(assign(ident(&edge_flag_name(p.index, &t.name)), sized(1, 1)));
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
        let mut body = self.start_wait();
        // Port sensitivities find their channel's event.
        body.extend(p.sens.iter().filter_map(|t| t.setup.clone()));
        if self.lw.m.needs_pid {
            body.insert(
                0,
                assign(index(ident("__sc_ph"), int(p.index as i64)), process_self()),
            );
        }
        match p.kind {
            sc::ProcessKind::Method if self.lw.m.next_triggers.iter().any(|(i, _)| *i == p.index) => {
                // §5.2.17: each activation waits for what next_trigger()
                // set during the previous one, else the static sensitivity.
                let kind = next_trigger_kind(p.index);
                items.push(data_decl(atom_t(crate::ast::types::IntegerAtomType::Int, false), &kind, Vec::new(), None));
                items.push(data_decl(
                    atom_t(crate::ast::types::IntegerAtomType::LongInt, true),
                    &next_trigger_time(p.index),
                    Vec::new(),
                    None,
                ));
                if !dont_init {
                    body.push(call.clone());
                }
                let arms: Vec<(Expression, Statement)> = self
                    .lw
                    .m
                    .next_triggers
                    .iter()
                    .enumerate()
                    .filter(|(_, (i, _))| *i == p.index)
                    .map(|(k, (_, w))| (int(k as i64 + 1), w.clone()))
                    .collect();
                let fallback = if p.sens.is_empty() {
                    wait(sized(1, 0))
                } else {
                    wait_sens()
                };
                let mut lp = vec![
                    case_(ident(&kind), arms, Some(fallback)),
                    assign(ident(&kind), int(0)),
                    call,
                ];
                lp.extend(clear_flags);
                body.push(forever(block(lp)));
            }
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

/// The adapter object a channel holds for interface `ifc` (SV class).
pub fn adapter_object(ifc: &str) -> String {
    format!("__sc_ifo_{}", ifc.trim_start_matches("sc_c_"))
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

/// Member function → the member names it writes as signals or ports
/// (`s.write(v)`, `s->write(v)`, `s[i].write(v)`, `s = v`).
fn write_sets(lw: &Lw, class: &sc::ClassDecl, name: &str) -> BTreeMap<String, BTreeSet<String>> {
    fn target(e: &sc::Expr) -> Option<String> {
        let e = match &e.kind {
            sc::ExprKind::Index { base, .. } => base.as_ref(),
            _ => e,
        };
        e.as_name()
            .filter(|q| q.segments.len() == 1)
            .map(|q| q.last_name().to_string())
    }
    let mut g = BTreeMap::new();
    let mut add = |f: &sc::FunctionDecl| {
        let mut out = BTreeSet::new();
        if let Some(b) = &f.body {
            for s in &b.stmts {
                visit_stmt_exprs(s, &mut |e| match &e.kind {
                    sc::ExprKind::Call { callee, .. } => {
                        if let sc::ExprKind::Member { base, name, .. } = &callee.kind
                            && name.ident.name == "write"
                            && let Some(t) = target(base)
                        {
                            out.insert(t);
                        }
                    }
                    sc::ExprKind::Assign { lhs, .. } => {
                        if let Some(t) = target(lhs) {
                            out.insert(t);
                        }
                    }
                    _ => {}
                });
            }
        }
        g.entry(f.base_name().to_string())
            .or_insert_with(BTreeSet::new)
            .extend(out);
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

/// Whether a signal type names a writer policy other than SC_ONE_WRITER
/// (`sc_signal<T, SC_MANY_WRITERS>`, §6.4.4).
fn many_writers(ty: &sc::Type) -> bool {
    ty.name()
        .and_then(|q| q.last_args())
        .and_then(|a| a.get(1))
        .is_some_and(|a| {
            let n = match a {
                sc::TemplateArg::Type(t) => t.name().map(|q| q.last_name().to_string()),
                sc::TemplateArg::Expr(e) => e.as_name().map(|q| q.last_name().to_string()),
            };
            matches!(n.as_deref(), Some("SC_MANY_WRITERS" | "SC_UNCHECKED_WRITERS"))
        })
}

fn stmt_calls(s: &sc::Stmt, out: &mut BTreeSet<String>) {
    visit_stmt_exprs(s, &mut |e| {
        if let sc::ExprKind::Call { callee, args } = &e.kind
            && let Some(q) = callee.as_name()
            && q.segments.len() == 1
        {
            out.insert(q.last_name().to_string());
            // `sc_bind(&f, …)` (§5.5) calls `f` in the spawned thread.
            if q.last_name() == "sc_bind"
                && let Some(f) = args.first()
            {
                let f = match &f.kind {
                    sc::ExprKind::Unary {
                        op: sc::UnaryOp::AddrOf,
                        operand,
                    } => operand.as_ref(),
                    _ => f,
                };
                if let Some(q) = f.as_name()
                    && q.segments.len() == 1
                {
                    out.insert(q.last_name().to_string());
                }
            }
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
        S::ScFork { spawns, .. } => spawns.iter().for_each(|e| visit_expr(e, f)),
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
                            let target = match &base.kind {
                                sc::ExprKind::Index { base: b, .. } => b.as_ref(),
                                _ => base.as_ref(),
                            };
                            let sym = target.as_name().and_then(|q| lw.m.syms.get(q.last_name()));
                            match sym.map(|s| &s.kind) {
                                Some(SymKind::Fifo | SymKind::FifoIn | SymKind::FifoOut)
                                    if matches!(m, "read" | "write") =>
                                {
                                    blocks = true
                                }
                                Some(SymKind::InitSocket) if m == "b_transport" => blocks = true,
                                // Interface methods are tasks (§5.12).
                                Some(SymKind::Port(_) | SymKind::Export(_))
                                    if !matches!(m, "size" | "bind") =>
                                {
                                    blocks = true
                                }
                                _ => {}
                            }
                            // sc_mutex::lock, sc_semaphore::wait.
                            if let Some(sym) = sym
                                && matches!((&sym.ty, m), (Ty::Class(c), "lock") if c == "scrt_mutex")
                                    | matches!((&sym.ty, m), (Ty::Class(c), "wait") if c == "scrt_semaphore")
                            {
                                blocks = true;
                            }
                            // A member function of a user-class object that
                            // may block.
                            if lw.prog.blocking_methods.borrow().contains(m) {
                                blocks = true;
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

/// The depth argument of `sc_fifo(size)` / `sc_fifo(name, size)` (§6.23.3).
fn fifo_size_arg(args: &[sc::Expr]) -> Option<&sc::Expr> {
    match args {
        [a] if !matches!(a.kind, sc::ExprKind::StringLit { .. }) => Some(a),
        [_, size, ..] => Some(size),
        _ => None,
    }
}

/// The index after sc_main's last top-level unbounded `sc_start()`, when the
/// statements after it need no simulation time.
fn unbounded_start_tail(stmts: &[sc::Stmt]) -> Option<usize> {
    let i = stmts.iter().rposition(|s| {
        matches!(s, sc::Stmt::Expr(sc::Expr { kind: sc::ExprKind::Call { callee, args }, .. })
            if args.is_empty() && callee.as_name().is_some_and(|q| q.last_name() == "sc_start"))
    })?;
    let tail = &stmts[i + 1..];
    (!tail.is_empty() && !super::program::calls_any(tail, &["sc_start", "wait"])).then_some(i + 1)
}
