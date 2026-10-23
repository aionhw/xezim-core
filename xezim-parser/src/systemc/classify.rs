//! What a SystemC design declares, read off the syntax tree: which members
//! are ports, channels or TLM sockets (by their library type), and which
//! processes a module registers with which sensitivity.
//!
//! This is classification by spelling — `sc_core::sc_in<bool>` and
//! `sc_in<bool>` are both input ports — not name resolution: a design
//! that defines its own `sc_in` is classified as if it were the library's.

use super::ast::*;
use super::parser::for_each_class as visit_classes;
use super::token::ScSpan;

/// The kind of SystemC object a declaration's type makes it.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ScObjectKind {
    /// `sc_in<T>`, `sc_in_clk`, `sc_in_rv<W>`, `sc_in_resolved` (§6.8)
    InPort,
    /// `sc_out<T>` and its clock/resolved forms (§6.10)
    OutPort,
    /// `sc_inout<T>` and its resolved forms (§6.10)
    InOutPort,
    /// `sc_fifo_in<T>` (§6.24)
    FifoIn,
    /// `sc_fifo_out<T>` (§6.25)
    FifoOut,
    /// `sc_port<IF, N, P>` (§5.12)
    Port,
    /// `sc_export<IF>` (§5.13)
    Export,
    /// `sc_signal<T>`, `sc_signal_rv<W>`, `sc_signal_resolved` (§6.4)
    Signal,
    /// `sc_buffer<T>` (§6.6)
    Buffer,
    /// `sc_clock` (§6.7)
    Clock,
    /// `sc_fifo<T>`, `tlm_fifo<T>`, `tlm_analysis_fifo<T>`
    Fifo,
    /// `sc_event` (§5.10)
    Event,
    /// `sc_vector<T>` of the element kind (§8.5)
    Vector(Box<ScObjectKind>),
    /// A TLM-2.0 initiator socket, including the `tlm_utils` convenience
    /// sockets (§13.2, §16.1)
    InitiatorSocket,
    /// A TLM-2.0 target socket, including the `tlm_utils` convenience
    /// sockets (§13.2, §16.1)
    TargetSocket,
    /// `tlm_analysis_port<T>` (§17.3)
    AnalysisPort,
    /// Anything else.
    Other,
}

/// Namespaces the SystemC and TLM-2.0 names live in.
const LIBRARY_NAMESPACES: &[&str] = &["sc_core", "sc_dt", "tlm", "tlm_utils", "sc_ams"];

impl ScObjectKind {
    pub fn of(ty: &Type) -> Self {
        match ty.name() {
            Some(q) => Self::of_name(q),
            None => ScObjectKind::Other,
        }
    }

    pub fn of_name(q: &QualifiedName) -> Self {
        if !q.qualifiers().all(|n| LIBRARY_NAMESPACES.contains(&n)) {
            return ScObjectKind::Other;
        }
        use ScObjectKind::*;
        match q.last_name() {
            "sc_in" | "sc_in_clk" | "sc_in_rv" | "sc_in_resolved" => InPort,
            "sc_out" | "sc_out_clk" | "sc_out_rv" | "sc_out_resolved" => OutPort,
            "sc_inout" | "sc_inout_clk" | "sc_inout_rv" | "sc_inout_resolved" => InOutPort,
            "sc_fifo_in" => FifoIn,
            "sc_fifo_out" => FifoOut,
            "sc_port" => Port,
            "sc_export" => Export,
            "sc_signal" | "sc_signal_rv" | "sc_signal_resolved" => Signal,
            "sc_buffer" => Buffer,
            "sc_clock" => Clock,
            "sc_fifo" | "tlm_fifo" | "tlm_analysis_fifo" => Fifo,
            "sc_event" => Event,
            "sc_vector" => {
                let elem = q
                    .last_args()
                    .and_then(|a| a.first())
                    .and_then(|a| match a {
                        TemplateArg::Type(t) => Some(Self::of(t)),
                        TemplateArg::Expr(_) => None,
                    })
                    .unwrap_or(Other);
                Vector(Box::new(elem))
            }
            "tlm_initiator_socket"
            | "tlm_base_initiator_socket"
            | "simple_initiator_socket"
            | "simple_initiator_socket_tagged"
            | "multi_passthrough_initiator_socket" => InitiatorSocket,
            "tlm_target_socket"
            | "tlm_base_target_socket"
            | "simple_target_socket"
            | "simple_target_socket_tagged"
            | "passthrough_target_socket"
            | "passthrough_target_socket_tagged"
            | "multi_passthrough_target_socket" => TargetSocket,
            "tlm_analysis_port" => AnalysisPort,
            _ => Other,
        }
    }

    /// The element kind of a vector, else `self`.
    pub fn element(&self) -> &ScObjectKind {
        match self {
            ScObjectKind::Vector(inner) => inner.element(),
            other => other,
        }
    }

    pub fn is_port(&self) -> bool {
        use ScObjectKind::*;
        matches!(
            self.element(),
            InPort | OutPort | InOutPort | FifoIn | FifoOut | Port | Export
        )
    }

    pub fn is_channel(&self) -> bool {
        use ScObjectKind::*;
        matches!(self.element(), Signal | Buffer | Clock | Fifo)
    }

    pub fn is_socket(&self) -> bool {
        use ScObjectKind::*;
        matches!(
            self.element(),
            InitiatorSocket | TargetSocket | AnalysisPort
        )
    }
}

/// A data member of a class with its SystemC classification.
#[derive(Debug, Clone)]
pub struct ScMember<'a> {
    pub name: &'a Ident,
    pub kind: ScObjectKind,
    /// The member's declared type (the specifier part; pointer parts are on
    /// `declarator`).
    pub ty: &'a Type,
    pub declarator: &'a Declarator,
}

impl ScMember<'_> {
    /// Declared through a pointer (`sc_signal<bool>* s;`).
    pub fn is_pointer(&self) -> bool {
        !self.declarator.ptr_ops.is_empty()
    }
}

/// A static-sensitivity entry: `sensitive << clk.pos()` gives
/// `(Any, clk.pos())`; `sensitive_pos << clk` gives `(Pos, clk)`.
#[derive(Debug, Clone)]
pub struct Sensitivity<'a> {
    pub edge: SensitivityEdge,
    pub expr: &'a Expr,
}

#[derive(Debug, Clone)]
pub struct ResetSpec<'a> {
    pub is_async: bool,
    pub signal: &'a Expr,
    pub level: &'a Expr,
}

/// A process a module registers, with the static configuration statements
/// that follow its registration (IEEE 1666-2023 §5.2.9–§5.2.16).
#[derive(Debug, Clone)]
pub struct ProcessInfo<'a> {
    pub kind: ProcessKind,
    pub func: &'a Ident,
    /// The clock edge expression of an `SC_CTHREAD`.
    pub clock: Option<&'a Expr>,
    pub sensitivity: Vec<Sensitivity<'a>>,
    pub dont_initialize: bool,
    pub resets: Vec<ResetSpec<'a>>,
    pub span: ScSpan,
}

/// Walk `stmts` in source order, nested statements included, collecting
/// process registrations and attaching each configuration statement to the
/// process registered most recently before it.
fn collect_processes<'a>(stmts: &'a [Stmt], out: &mut Vec<ProcessInfo<'a>>) {
    for s in stmts {
        match s {
            Stmt::ScProcess {
                kind,
                func,
                clock,
                span,
            } => out.push(ProcessInfo {
                kind: *kind,
                func,
                clock: clock.as_ref(),
                sensitivity: Vec::new(),
                dont_initialize: false,
                resets: Vec::new(),
                span: *span,
            }),
            Stmt::Sensitive { edge, items, .. } => {
                if let Some(p) = out.last_mut() {
                    p.sensitivity
                        .extend(items.iter().map(|expr| Sensitivity { edge: *edge, expr }));
                }
            }
            Stmt::DontInitialize(_) => {
                if let Some(p) = out.last_mut() {
                    p.dont_initialize = true;
                }
            }
            Stmt::ResetSignalIs {
                is_async,
                signal,
                level,
                ..
            } => {
                if let Some(p) = out.last_mut() {
                    p.resets.push(ResetSpec {
                        is_async: *is_async,
                        signal,
                        level,
                    });
                }
            }
            Stmt::Block(b) => collect_processes(&b.stmts, out),
            Stmt::If {
                then_branch,
                else_branch,
                ..
            } => {
                collect_processes(std::slice::from_ref(then_branch.as_ref()), out);
                if let Some(e) = else_branch {
                    collect_processes(std::slice::from_ref(e.as_ref()), out);
                }
            }
            Stmt::For { body, .. }
            | Stmt::RangeFor { body, .. }
            | Stmt::While { body, .. }
            | Stmt::DoWhile { body, .. } => {
                collect_processes(std::slice::from_ref(body.as_ref()), out)
            }
            Stmt::Labeled { stmt, .. } => {
                collect_processes(std::slice::from_ref(stmt.as_ref()), out)
            }
            Stmt::Switch { arms, .. } => {
                for a in arms {
                    collect_processes(&a.body, out);
                }
            }
            Stmt::Try { body, handlers, .. } => {
                collect_processes(&body.stmts, out);
                for h in handlers {
                    collect_processes(&h.body.stmts, out);
                }
            }
            _ => {}
        }
    }
}

impl ClassDecl {
    /// Every named data member, with its classification.
    pub fn objects(&self) -> Vec<ScMember<'_>> {
        let mut out = Vec::new();
        for m in &self.members {
            if let Member::Field(v) = m {
                if v.specifiers.is_static {
                    continue;
                }
                let kind = ScObjectKind::of(&v.ty);
                for d in &v.declarators {
                    out.push(ScMember {
                        name: &d.name,
                        kind: kind.clone(),
                        ty: &v.ty,
                        declarator: d,
                    });
                }
            }
        }
        out
    }

    /// Ports and exports (§5.12–§5.13, §6.8–§6.25).
    pub fn ports(&self) -> Vec<ScMember<'_>> {
        self.objects()
            .into_iter()
            .filter(|m| m.kind.is_port())
            .collect()
    }

    /// Primitive channels: signals, buffers, clocks, FIFOs.
    pub fn signals(&self) -> Vec<ScMember<'_>> {
        self.objects()
            .into_iter()
            .filter(|m| m.kind.is_channel())
            .collect()
    }

    /// TLM-2.0 sockets and analysis ports.
    pub fn sockets(&self) -> Vec<ScMember<'_>> {
        self.objects()
            .into_iter()
            .filter(|m| m.kind.is_socket())
            .collect()
    }

    pub fn constructors(&self) -> impl Iterator<Item = &FunctionDecl> {
        self.members.iter().filter_map(|m| match m {
            Member::Constructor(f) => Some(f),
            _ => None,
        })
    }

    pub fn methods(&self) -> impl Iterator<Item = &FunctionDecl> {
        self.members.iter().filter_map(|m| match m {
            Member::Method(f) => Some(f),
            _ => None,
        })
    }

    pub fn find_method(&self, name: &str) -> Option<&FunctionDecl> {
        self.methods().find(|f| f.base_name() == name)
    }

    /// Processes registered by member functions defined inside the class
    /// body, constructors first. Use [`TranslationUnit::processes`] to
    /// include out-of-class definitions (`top::top(…) { SC_METHOD(…); }`).
    pub fn processes(&self) -> Vec<ProcessInfo<'_>> {
        let mut out = Vec::new();
        // SystemC 3.0 in-class initializers run during construction, in
        // declaration order, before the constructor body.
        for m in &self.members {
            match m {
                Member::ScProcessImp {
                    kind,
                    clock,
                    init,
                    method,
                    span,
                } => {
                    out.push(ProcessInfo {
                        kind: *kind,
                        func: &method.name.segments[0].ident,
                        clock: clock.as_ref(),
                        sensitivity: Vec::new(),
                        dont_initialize: false,
                        resets: Vec::new(),
                        span: *span,
                    });
                    collect_processes(init, &mut out);
                }
                Member::ScInit { body, .. } => collect_processes(&body.stmts, &mut out),
                _ => {}
            }
        }
        let others = self.members.iter().filter_map(|m| match m {
            Member::Method(f) | Member::Destructor(f) => Some(f),
            _ => None,
        });
        for f in self.constructors().chain(others) {
            if let Some(b) = &f.body {
                collect_processes(&b.stmts, &mut out);
            }
        }
        out
    }
}

fn visit_functions<'a>(items: &'a [Item], f: &mut impl FnMut(&'a FunctionDecl)) {
    for i in items {
        match i {
            Item::Function(func) => f(func),
            Item::Namespace { items, .. } | Item::ExternBlock { items, .. } => {
                visit_functions(items, f)
            }
            Item::Template { item, .. } => visit_functions(std::slice::from_ref(item.as_ref()), f),
            _ => {}
        }
    }
}

impl TranslationUnit {
    /// Every class, struct and union, nested ones and those inside
    /// namespaces and templates included.
    pub fn classes(&self) -> Vec<&ClassDecl> {
        let mut out = Vec::new();
        visit_classes(&self.items, &mut |c| out.push(c));
        out
    }

    /// Every SystemC module class.
    pub fn modules(&self) -> Vec<&ClassDecl> {
        self.classes().into_iter().filter(|c| c.sc_module).collect()
    }

    pub fn find_class(&self, name: &str) -> Option<&ClassDecl> {
        self.classes()
            .into_iter()
            .find(|c| c.name_str() == Some(name))
    }

    /// Namespace-scope functions, out-of-class member definitions included.
    pub fn functions(&self) -> Vec<&FunctionDecl> {
        let mut out = Vec::new();
        visit_functions(&self.items, &mut |f| out.push(f));
        out
    }

    /// The `sc_main` entry point (§4.3), if defined.
    pub fn sc_main(&self) -> Option<&FunctionDecl> {
        self.functions()
            .into_iter()
            .find(|f| f.name.segments.len() == 1 && f.base_name() == "sc_main" && f.body.is_some())
    }

    /// Member functions of class `class` defined outside its body
    /// (`void top::run() {…}`).
    pub fn out_of_class_members(&self, class: &str) -> Vec<&FunctionDecl> {
        self.functions()
            .into_iter()
            .filter(|f| f.name.qualifiers().last() == Some(class))
            .collect()
    }

    /// The processes `class` registers, in its body and in out-of-class
    /// member definitions (constructors first).
    pub fn processes<'a>(&'a self, class: &'a ClassDecl) -> Vec<ProcessInfo<'a>> {
        let mut out = class.processes();
        let Some(name) = class.name_str() else {
            return out;
        };
        let defs = self.out_of_class_members(name);
        let (ctors, others): (Vec<&FunctionDecl>, Vec<&FunctionDecl>) =
            defs.into_iter().partition(|f| f.base_name() == name);
        for f in ctors.into_iter().chain(others) {
            if let Some(b) = &f.body {
                collect_processes(&b.stmts, &mut out);
            }
        }
        out
    }
}
