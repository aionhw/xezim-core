//! Lowering of SystemC member-function bodies: statements and expressions
//! (C++ semantics onto IEEE 1800-2017 procedural code, with the SystemC
//! kernel calls of IEEE 1666-2023 mapped onto SV timing controls).

use std::collections::{BTreeMap, BTreeSet};

use super::build::*;
use super::program::Program;
use super::types::*;
use crate::ast::expr::{BinaryOp, ExprKind, Expression, NumberBase, UnaryOp};
use crate::ast::stmt::{CaseItem, CaseKind, Edge, EventExpr, JoinType, Statement, StatementKind};
use crate::sv_parser::systemc::ast as sc;
use crate::sv_parser::systemc::token::ScSpan;

/// A lowering failure at a C++ location.
#[derive(Debug, Clone)]
pub struct LowerError {
    pub tu: usize,
    pub span: ScSpan,
    pub msg: String,
}

pub type R<T> = Result<T, LowerError>;

/// What a name in scope is.
#[derive(Debug, Clone, PartialEq)]
pub enum SymKind {
    Var,
    Signal,
    InPort,
    OutPort,
    InOutPort,
    Clock,
    Event,
    Fifo,
    FifoIn,
    FifoOut,
    /// A child module instance: its module name.
    Instance(String),
    InitSocket,
    TargetSocket,
    /// A scalar whose address is taken: an `scrt_boxN` object (`.v`).
    Boxed,
    /// An array whose element address is taken: an `scrt_arrN` object (`.a`).
    BoxedArr,
    /// A loop variable unrolled at elaboration: a constant.
    Const(i64),
    /// A `sc_trace_file*`: tracing maps onto `$dumpvars`.
    TraceFile,
    /// `sc_port<IF>` / `sc_export<IF>` of a user interface (its SV class):
    /// an object of the interface's port class (§5.12, §5.14).
    Port(String),
    Export(String),
}

#[derive(Debug, Clone)]
pub struct Sym {
    pub kind: SymKind,
    pub ty: Ty,
    /// The SV name.
    pub sv: String,
}

impl Sym {
    pub fn is_signal_like(&self) -> bool {
        matches!(
            self.kind,
            SymKind::Signal
                | SymKind::InPort
                | SymKind::OutPort
                | SymKind::InOutPort
                | SymKind::Clock
        )
    }
}

/// A member function's lowered signature.
#[derive(Debug, Clone)]
pub struct FnSig {
    pub ret: Ty,
    /// Lowered as a task (it may block).
    pub is_task: bool,
    /// Per parameter: passed by non-const reference.
    pub by_ref: Vec<bool>,
}

/// One term of a process's static sensitivity: the event, and the C++
/// name of the signal it watches.
#[derive(Debug, Clone)]
pub struct SensTerm {
    pub edge: Option<Edge>,
    pub expr: Expression,
    /// A guard on the event: SystemC's edge of an sc_logic is a change TO
    /// '1' or '0' (§6.8.4), not SystemVerilog's 0→z or 1→x as well.
    pub iff: Option<Expression>,
    pub name: String,
    /// Run when the process starts, before it first waits: a port's
    /// channel is known once the bindings are made.
    pub setup: Option<Statement>,
}

impl SensTerm {
    pub fn new(edge: Option<Edge>, expr: Expression, name: String) -> Self {
        SensTerm {
            edge,
            expr,
            iff: None,
            name,
            setup: None,
        }
    }

    /// The edge of an sc_logic value: SystemC's posedge is any change to
    /// '1', its negedge any change to '0'.
    pub fn logic_edge(edge: Edge, expr: Expression, name: String) -> Self {
        let lvl = sized(1, matches!(edge, Edge::Posedge) as u64);
        SensTerm {
            edge: None,
            iff: Some(bin(BinaryOp::CaseEq, expr.clone(), lvl)),
            expr,
            name,
            setup: None,
        }
    }

    pub fn event(&self) -> EventExpr {
        EventExpr {
            edge: self.edge,
            expr: self.expr.clone(),
            iff: self.iff.clone(),
            span: sp(),
        }
    }
}

/// A registered process, as the bodies it runs see it.
#[derive(Debug, Clone)]
pub struct ProcCtx {
    pub index: usize,
    pub kind: sc::ProcessKind,
    /// Static sensitivity (`wait()` waits on it).
    pub sens: Vec<SensTerm>,
    /// Clock edge of an SC_CTHREAD.
    pub clock: Option<(Edge, Expression)>,
    /// Synchronous reset condition (lowered), checked after every wait.
    pub reset: Option<Expression>,
}

/// Per-module lowering state.
#[derive(Default)]
pub struct ModCtx {
    pub name: String,
    pub syms: BTreeMap<String, Sym>,
    pub funcs: BTreeMap<String, FnSig>,
    /// Member function → process that runs it (for `wait()` and
    /// `posedge()`), or `None` when several processes share it.
    pub fn_proc: BTreeMap<String, Option<usize>>,
    pub procs: Vec<ProcCtx>,
    /// Signals whose `posedge()/negedge()/event()` a process asks about:
    /// (process, signal SV name).
    pub edge_flags: BTreeSet<(usize, String)>,
    /// The sc_main testbench (writes are deferred to the next sc_start).
    pub tb: bool,
    /// Testbench write sites: (target signal SV name, value queue, whether
    /// an element is written).
    pub pending: Vec<(String, String, bool)>,
    /// Extra module items the bodies needed (temporaries, flags).
    pub extra_items: Vec<crate::ast::decl::ModuleItem>,
    /// `sc_buffer` channels (SV names): each write also bumps their
    /// `buffer_counter`.
    pub buffers: BTreeSet<String>,
    /// Resolved signals and the resolved ports the module drives (§6.13–
    /// §6.18), SV name → width: nets of the `scrt_rv<W>_t` nettype whose
    /// drivers are the writing processes.
    pub resolved: BTreeMap<String, u32>,
    /// Driver variables of resolved nets: (net, writer) → variable.
    pub drivers: BTreeMap<(String, Writer), String>,
    /// SystemC object names of the module's members (§5.17): the name given
    /// at construction, else the generated `signal_0`, `port_0`, ….
    pub sc_names: BTreeMap<String, String>,
    /// Child instances: member → SystemC instance name.
    pub inst_names: BTreeMap<String, String>,
    /// Signals two or more of the module's processes write, with the
    /// default writer policy (§6.4.4): each write checks its writer (E115).
    pub one_writer: BTreeSet<String>,
    /// A channel's events that an interface event function returns: the
    /// interface objects' events triggered with each (an event property
    /// cannot alias a module event).
    pub ev_mirrors: BTreeMap<String, Vec<Expression>>,
    /// Registered processes: (function name, kind).
    pub proc_names: Vec<(String, sc::ProcessKind)>,
    /// Whether a write site needed the running process's identity at run
    /// time (a function several processes share).
    pub needs_pid: bool,
    /// Lowering a user class's member functions: its SV name (`this`).
    pub class: Option<String>,
    /// sc_main's module objects held by value (destroyed when it returns).
    pub tb_values: Vec<String>,
    /// A primitive channel requested its update phase (`request_update()`).
    pub uses_update: bool,
    /// Input ports some instance binds to an sc_buffer: port → the hidden
    /// input carrying the buffer's write count (§6.9).
    pub port_counters: BTreeMap<String, String>,
    /// Output ports bound to an sc_buffer in some instance: port → the
    /// hidden output counting the writes through it.
    pub port_wcounters: BTreeMap<String, String>,
    /// sc_buffer → the write counters of the child output ports bound to
    /// it; with its own counter they make up its event count.
    pub buffer_sources: BTreeMap<String, Vec<String>>,
}

/// Who writes a resolved net: a process of the module, or code outside any
/// process (elaboration, sc_main).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Writer {
    Process(usize),
    Outside,
}

/// Per-function lowering state.
#[derive(Default)]
pub struct FnCtx {
    pub scopes: Vec<BTreeMap<String, Sym>>,
    /// Local declarations, hoisted to the top of the SV body (SV requires
    /// declarations before statements).
    pub decls: Vec<Statement>,
    pub used: BTreeSet<String>,
    pub proc: Option<usize>,
    pub ret: Option<Ty>,
    pub cout_hex: bool,
    /// The function may block (a task).
    pub is_task: bool,
    /// A value-returning task returns through this output argument.
    pub ret_var: Option<String>,
    /// Statements to run before every return (copy-back of boxed
    /// reference parameters).
    pub epilogue: Vec<Statement>,
    /// The function runs in several processes (its process is known only
    /// at run time).
    pub shared: bool,
    /// The function returns an object by value: `return x;` returns a copy.
    pub ret_copy: bool,
}

pub struct Lw<'a> {
    pub prog: &'a Program<'a>,
    pub errors: Vec<LowerError>,
    pub tu: usize,
    pub env: TyEnv,
    /// Enumerators: C++ name (and `Enum::name`) → value.
    pub enum_consts: BTreeMap<String, i64>,
    pub m: ModCtx,
    pub f: FnCtx,
    /// Statements an expression needs run before the statement using it
    /// (a FIFO read becomes `get` into a temporary).
    pub pre: Vec<Statement>,
    tmp: usize,
    /// Widths of the resolved nets lowered so far (each needs its nettype).
    pub rv_widths: BTreeSet<u32>,
}

const TIME_UNITS: &[(&str, f64)] = &[
    ("SC_FS", 0.001),
    ("SC_PS", 1.0),
    ("SC_NS", 1e3),
    ("SC_US", 1e6),
    ("SC_MS", 1e9),
    ("SC_SEC", 1e12),
];

/// The operands of an event AND-list `e1 & e2 & …` (at least two).
fn and_list(e: &sc::Expr) -> Option<Vec<&sc::Expr>> {
    fn flat<'a>(e: &'a sc::Expr, out: &mut Vec<&'a sc::Expr>) {
        match &e.kind {
            sc::ExprKind::Binary {
                op: sc::BinaryOp::BitAnd,
                lhs,
                rhs,
            } => {
                flat(lhs, out);
                flat(rhs, out);
            }
            _ => out.push(e),
        }
    }
    let mut v = Vec::new();
    flat(e, &mut v);
    (v.len() > 1).then_some(v)
}

fn time_unit(e: &sc::Expr) -> Option<f64> {
    let q = e.as_name()?;
    TIME_UNITS
        .iter()
        .find(|(n, _)| *n == q.last_name())
        .map(|(_, f)| *f)
}

/// The library-namespace-free path of a name (`std::cout` → `cout`).
fn short_path(q: &sc::QualifiedName) -> String {
    let mut parts: Vec<&str> = q.segments.iter().map(|s| s.ident.name.as_str()).collect();
    while parts.len() > 1 && is_library_ns(parts[0]) {
        parts.remove(0);
    }
    parts.join("::")
}

fn is_stream(e: &sc::Expr) -> bool {
    e.as_name()
        .is_some_and(|q| matches!(short_path(q).as_str(), "cout" | "cerr" | "clog"))
}

fn sv_binop(op: sc::BinaryOp) -> Option<BinaryOp> {
    use sc::BinaryOp as B;
    Some(match op {
        B::Mul => BinaryOp::Mul,
        B::Div => BinaryOp::Div,
        B::Rem => BinaryOp::Mod,
        B::Add => BinaryOp::Add,
        B::Sub => BinaryOp::Sub,
        B::Shl => BinaryOp::ShiftLeft,
        B::Shr => BinaryOp::ShiftRight,
        B::Lt => BinaryOp::Lt,
        B::Gt => BinaryOp::Gt,
        B::Le => BinaryOp::Leq,
        B::Ge => BinaryOp::Geq,
        B::Eq => BinaryOp::Eq,
        B::Ne => BinaryOp::Neq,
        B::BitAnd => BinaryOp::BitAnd,
        B::BitXor => BinaryOp::BitXor,
        B::BitOr => BinaryOp::BitOr,
        B::LogAnd => BinaryOp::LogAnd,
        B::LogOr => BinaryOp::LogOr,
        _ => return None,
    })
}

/// C++ `>>` of a signed value shifts in the sign bit (an arithmetic shift).
fn signed_shift(op: BinaryOp, lhs: &Ty) -> BinaryOp {
    match (op, lhs) {
        (BinaryOp::ShiftRight, Ty::Vec2 { signed: true, .. } | Ty::Int { signed: true, .. }) => {
            BinaryOp::ArithShiftRight
        }
        _ => op,
    }
}

/// The binary operator of a compound assignment (`+=` → `+`).
fn compound_binop(op: sc::AssignOp) -> sc::BinaryOp {
    use sc::AssignOp as A;
    use sc::BinaryOp as B;
    match op {
        A::Add => B::Add,
        A::Sub => B::Sub,
        A::Mul => B::Mul,
        A::Div => B::Div,
        A::Rem => B::Rem,
        A::And => B::BitAnd,
        A::Or => B::BitOr,
        A::Xor => B::BitXor,
        A::Shl => B::Shl,
        A::Shr => B::Shr,
        A::Assign => B::Comma,
    }
}

fn sv_assignop(op: sc::AssignOp) -> Option<BinaryOp> {
    use sc::AssignOp as A;
    Some(match op {
        A::Assign => return None,
        A::Mul => BinaryOp::Mul,
        A::Div => BinaryOp::Div,
        A::Rem => BinaryOp::Mod,
        A::Add => BinaryOp::Add,
        A::Sub => BinaryOp::Sub,
        A::Shl => BinaryOp::ShiftLeft,
        A::Shr => BinaryOp::ShiftRight,
        A::And => BinaryOp::BitAnd,
        A::Xor => BinaryOp::BitXor,
        A::Or => BinaryOp::BitOr,
    })
}

/// Decode a C++ character literal's value.
fn char_value(text: &str) -> Option<i64> {
    let start = text.find('\'')?;
    let body = &text[start + 1..text.rfind('\'')?];
    let mut chars = body.chars();
    let c = chars.next()?;
    if c != '\\' {
        return Some(c as i64);
    }
    Some(match chars.next()? {
        'n' => 10,
        't' => 9,
        'r' => 13,
        '0' => 0,
        'a' => 7,
        'b' => 8,
        'f' => 12,
        'v' => 11,
        'x' => i64::from_str_radix(chars.as_str(), 16).ok()?,
        other => other as i64,
    })
}

/// A C printf format as SV `$write` understands it: `%d` → `%0d` (SV pads
/// to the value's width), `%x` → `%0h`, length modifiers dropped.
pub fn printf_to_sv(fmt: &str) -> String {
    let mut out = String::new();
    let mut chars = fmt.chars().peekable();
    while let Some(c) = chars.next() {
        if c != '%' {
            out.push(c);
            continue;
        }
        if chars.peek() == Some(&'%') {
            chars.next();
            out.push_str("%%");
            continue;
        }
        let mut spec = String::new();
        while let Some(&d) = chars.peek() {
            if matches!(d, '-' | '+' | ' ' | '#' | '0'..='9' | '.') {
                spec.push(d);
                chars.next();
            } else {
                break;
            }
        }
        while matches!(chars.peek(), Some('l' | 'h' | 'z' | 'j' | 't' | 'L')) {
            chars.next();
        }
        let conv = chars.next().unwrap_or('d');
        let sv_conv = match conv {
            'd' | 'i' | 'u' => 'd',
            'x' | 'X' | 'p' => 'h',
            'o' => 'o',
            other => other,
        };
        out.push('%');
        if spec.is_empty() && matches!(sv_conv, 'd' | 'h' | 'o') {
            out.push('0');
        }
        out.push_str(&spec);
        out.push(sv_conv);
    }
    out
}

impl<'a> Lw<'a> {
    pub fn new(prog: &'a Program<'a>, env: TyEnv, enum_consts: BTreeMap<String, i64>) -> Self {
        Lw {
            prog,
            errors: Vec::new(),
            tu: 0,
            env,
            enum_consts,
            m: ModCtx::default(),
            f: FnCtx::default(),
            pre: Vec::new(),
            tmp: 0,
            rv_widths: BTreeSet::new(),
        }
    }

    pub fn err<T>(&self, span: ScSpan, msg: impl Into<String>) -> R<T> {
        Err(LowerError {
            tu: self.tu,
            span,
            msg: msg.into(),
        })
    }

    pub fn record(&mut self, e: LowerError) {
        self.errors.push(e);
    }

    /// The lowering type of a C++ type.
    pub fn ty(&self, t: &sc::Type, span: ScSpan) -> R<Ty> {
        let consts = |e: &sc::Expr| self.const_eval(e);
        ty_of(t, &self.env, &consts).or_else(|m| self.err(span, m))
    }

    /// The type of a declarator: the specifier type with the declarator's own
    /// pointer parts and array dimensions.
    pub fn decl_ty(&self, base: &sc::Type, d: &sc::Declarator) -> R<Ty> {
        let mut t = base.clone();
        t.ptr_ops.extend(d.ptr_ops.iter().copied());
        let ty = self.ty(&t, d.span)?;
        self.with_dims(ty, d)
    }

    /// `ty` as the type of declarator `d`, with its array dimensions.
    pub fn with_dims(&self, mut ty: Ty, d: &sc::Declarator) -> R<Ty> {
        for dim in d.array_dims.iter().rev() {
            let n = match dim {
                Some(e) => self.const_eval(e).map(int).or_else(|| self.tparam_value(e)),
                None => None,
            };
            let Some(n) = n else {
                return self.err(d.span, "array dimensions must be constant");
            };
            ty = Ty::Array(Box::new(ty), n);
        }
        Ok(ty)
    }

    fn tparam_value(&self, e: &sc::Expr) -> Option<Expression> {
        let q = e.as_name()?;
        match self.env.tparams.get(q.last_name())? {
            TParam::Value(sv) => Some(ident(sv)),
            TParam::Const(v) => Some(int(*v)),
            TParam::Type(_) => None,
        }
    }

    /// The value of a constant integer expression, when it has one.
    pub fn const_eval(&self, e: &sc::Expr) -> Option<i64> {
        use sc::ExprKind as K;
        Some(match &e.kind {
            K::IntLit { value, .. } => (*value)? as i64,
            K::CharLit { text } => char_value(text)?,
            K::BoolLit(b) => *b as i64,
            K::Paren(inner) => self.const_eval(inner)?,
            K::Unary { op, operand } => {
                let v = self.const_eval(operand)?;
                match op {
                    sc::UnaryOp::Neg => -v,
                    sc::UnaryOp::Plus => v,
                    sc::UnaryOp::Not => (v == 0) as i64,
                    sc::UnaryOp::BitNot => !v,
                    _ => return None,
                }
            }
            K::Binary { op, lhs, rhs } => {
                let (a, b) = (self.const_eval(lhs)?, self.const_eval(rhs)?);
                use sc::BinaryOp as B;
                match op {
                    B::Add => a.wrapping_add(b),
                    B::Sub => a.wrapping_sub(b),
                    B::Mul => a.wrapping_mul(b),
                    B::Div if b != 0 => a / b,
                    B::Rem if b != 0 => a % b,
                    B::Shl => a.wrapping_shl(b as u32),
                    B::Shr => a >> b,
                    B::BitAnd => a & b,
                    B::BitOr => a | b,
                    B::BitXor => a ^ b,
                    B::Lt => (a < b) as i64,
                    B::Gt => (a > b) as i64,
                    B::Le => (a <= b) as i64,
                    B::Ge => (a >= b) as i64,
                    B::Eq => (a == b) as i64,
                    B::Ne => (a != b) as i64,
                    B::LogAnd => (a != 0 && b != 0) as i64,
                    B::LogOr => (a != 0 || b != 0) as i64,
                    _ => return None,
                }
            }
            K::Conditional {
                cond,
                then_expr,
                else_expr,
            } => {
                if self.const_eval(cond)? != 0 {
                    self.const_eval(then_expr)?
                } else {
                    self.const_eval(else_expr)?
                }
            }
            K::Name(q) => {
                let path = short_path(q);
                if let Some(v) = self.enum_consts.get(&path) {
                    return Some(*v);
                }
                if q.segments.len() == 1 {
                    if let Some(sym) = self.lookup(q.last_name())
                        && let SymKind::Const(v) = sym.kind
                    {
                        return Some(v);
                    }
                    if let Some(v) = self.prog.global_consts.get(q.last_name()) {
                        return Some(*v);
                    }
                    if let Some(TParam::Const(v)) = self.env.tparams.get(q.last_name()) {
                        return Some(*v);
                    }
                }
                return None;
            }
            K::Call { callee, args } if args.is_empty() => {
                // `vec.size()` of an sc_vector with a known size.
                if let K::Member { base, name, .. } = &callee.kind
                    && name.ident.name == "size"
                {
                    let q = base.as_name()?;
                    let sym = self.lookup(q.last_name())?;
                    if let Ty::Array(_, n) = &sym.ty {
                        return expr_int(n);
                    }
                }
                return None;
            }
            K::Cast { expr, .. } => self.const_eval(expr)?,
            _ => return None,
        })
    }

    // ---- scopes -----------------------------------------------------------

    pub fn lookup(&self, name: &str) -> Option<Sym> {
        for s in self.f.scopes.iter().rev() {
            if let Some(sym) = s.get(name) {
                return Some(sym.clone());
            }
        }
        self.m.syms.get(name).cloned()
    }

    /// A unique SV name for a new local `name`.
    pub fn fresh_local(&mut self, name: &str) -> String {
        let mut sv = name.to_string();
        let mut k = 1;
        while self.f.used.contains(&sv)
            || self.m.syms.contains_key(&sv) && self.f.used.contains(name)
        {
            sv = format!("{}__{}", name, k);
            k += 1;
        }
        self.f.used.insert(sv.clone());
        sv
    }

    pub fn temp(&mut self, ty: &Ty) -> String {
        self.tmp += 1;
        let name = format!("__sc_t{}", self.tmp);
        let (dt, dims) = sv_type(ty);
        self.f.decls.push(st(StatementKind::VarDecl {
            data_type: dt,
            lifetime: None,
            declarators: vec![var_declarator(&name, dims, None)],
        }));
        name
    }

    /// A module-level variable (for testbench pending writes and flags).
    pub fn module_var(&mut self, prefix: &str, ty: &Ty) -> String {
        self.tmp += 1;
        let name = format!("{}{}", prefix, self.tmp);
        let (dt, dims) = sv_type(ty);
        self.m.extra_items.push(data_decl(dt, &name, dims, None));
        name
    }

    /// Declare a local variable in the current function scope.
    pub fn declare_local(
        &mut self,
        name: &str,
        ty: Ty,
        kind: SymKind,
        init_new: Option<Expression>,
    ) -> String {
        let sv = self.fresh_local(name);
        let (dt, dims) = match &kind {
            SymKind::Boxed => (named_t(box_class(&ty), Vec::new()), Vec::new()),
            SymKind::BoxedArr => (named_t(arr_class(&ty), Vec::new()), Vec::new()),
            _ => sv_type(&ty),
        };
        self.f.decls.push(st(StatementKind::VarDecl {
            data_type: dt,
            lifetime: None,
            declarators: vec![var_declarator(&sv, dims, init_new)],
        }));
        self.f.scopes.last_mut().expect("function scope").insert(
            name.to_string(),
            Sym {
                kind,
                ty,
                sv: sv.clone(),
            },
        );
        sv
    }

    // ---- expressions --------------------------------------------------------

    /// Read access to a symbol.
    pub fn sym_read(&self, sym: &Sym) -> Expression {
        match sym.kind {
            SymKind::Boxed => member(ident(&sym.sv), "v"),
            SymKind::Const(v) => int(v),
            // A resolved net is {written, value}: its value bits.
            _ if sym.is_signal_like() && self.m.resolved.contains_key(&sym.sv) => {
                match self.m.resolved[&sym.sv] {
                    1 => index(ident(&sym.sv), int(0)),
                    w => range(ident(&sym.sv), int(w as i64 - 1), int(0)),
                }
            }
            _ => ident(&sym.sv),
        }
    }

    /// The SystemC name of a member object (`t.signal_0`), or of the module
    /// itself: the instance path (`__sc_path`, empty in sc_main) and the
    /// object's basename.
    pub fn obj_name(&self, member: Option<&str>) -> Expression {
        let base = member.map(|m| {
            self.m
                .sc_names
                .get(m)
                .cloned()
                .unwrap_or_else(|| m.to_string())
        });
        match (base, self.m.tb) {
            (Some(b), true) => string(&b),
            (None, true) => string(""),
            (Some(b), false) => concat(vec![ident("__sc_path"), string(&format!(".{}", b))]),
            (None, false) => ident("__sc_path"),
        }
    }

    /// `x.name()` / `x.basename()` (§5.17) of a member object, a child
    /// instance or a child's member (`u.clk`): the hierarchical name, or the
    /// last part of it.
    fn object_name(&self, base: &sc::Expr, basename: bool) -> Option<Expression> {
        let strip = |e: &sc::Expr| -> sc::Expr {
            match &e.kind {
                sc::ExprKind::Unary {
                    op: sc::UnaryOp::Deref,
                    operand,
                } => (**operand).clone(),
                _ => e.clone(),
            }
        };
        let base = strip(base);
        let inst_path = |lw: &Self, inst: &str| -> Option<Expression> {
            let n = lw.m.inst_names.get(inst)?;
            Some(if lw.m.tb {
                string(n)
            } else {
                concat(vec![ident("__sc_path"), string(&format!(".{}", n))])
            })
        };
        match &base.kind {
            sc::ExprKind::Name(q) if q.segments.len() == 1 => {
                let sym = self.lookup(q.last_name())?;
                match &sym.kind {
                    SymKind::Instance(_) => {
                        if basename {
                            return self.m.inst_names.get(&sym.sv).map(|n| string(n));
                        }
                        inst_path(self, q.last_name())
                    }
                    _ => {
                        let b = self.m.sc_names.get(q.last_name())?;
                        Some(if basename {
                            string(b)
                        } else {
                            self.obj_name(Some(q.last_name()))
                        })
                    }
                }
            }
            sc::ExprKind::Member { base: inner, name, .. } => {
                let inner = strip(inner);
                let q = inner.as_name()?;
                let sym = self.lookup(q.last_name())?;
                let SymKind::Instance(module) = &sym.kind else {
                    return None;
                };
                let b = self
                    .prog
                    .module_names
                    .borrow()
                    .get(module)?
                    .get(&name.ident.name)?
                    .clone();
                if basename {
                    return Some(string(&b));
                }
                let p = inst_path(self, q.last_name())?;
                Some(concat(vec![p, string(&format!(".{}", b))]))
            }
            _ => None,
        }
    }

    /// Whether the class `a` (SV name) is `b` or derives from it.
    pub fn is_same_or_derived(&self, a: &str, b: &str) -> bool {
        let classes = self.prog.user_classes.borrow();
        let mut cur = Some(a.to_string());
        while let Some(c) = cur {
            if c == b {
                return true;
            }
            cur = classes.get(&c).and_then(|s| s.base.clone());
        }
        false
    }

    /// The module a type names: its class, or for a module template with
    /// a type parameter, the instantiation.
    pub fn module_of(&self, q: &sc::QualifiedName) -> Option<String> {
        let n = q.last_name();
        if !self.prog.is_module(n) {
            return None;
        }
        if self.env.templates.contains_key(n) {
            return instantiate(q, &self.env, &|e| self.const_eval(e)).ok().flatten();
        }
        Some(n.to_string())
    }

    /// The user class (SV name) of an object or pointer type.
    pub fn user_class(&self, t: &Ty) -> Option<String> {
        match t {
            Ty::Class(c) | Ty::Handle(c) if self.prog.user_classes.borrow().contains_key(c) => {
                Some(c.clone())
            }
            _ => None,
        }
    }

    /// A library channel object (`sc_mutex`, `sc_semaphore`,
    /// `sc_event_queue`, §6.27–§6.29) built from its declaration's
    /// arguments: a name, and a semaphore's count.
    pub fn lib_object_new(&mut self, ty: &Ty, args: &[sc::Expr]) -> R<Option<Expression>> {
        let Ty::Class(c) = ty else { return Ok(None) };
        match c.as_str() {
            "scrt_mutex" | "scrt_event_queue" => Ok(Some(new_obj(None))),
            "scrt_semaphore" => {
                let n = args
                    .iter()
                    .rev()
                    .find(|a| !matches!(a.kind, sc::ExprKind::StringLit { .. }));
                let Some(n) = n else {
                    return self.err(
                        args.first().map_or(ScSpan::default(), |a| a.span),
                        "an sc_semaphore needs its initial count",
                    );
                };
                let x = self.expr(n)?.0;
                Ok(Some(new_obj(Some(vec![x]))))
            }
            _ => Ok(None),
        }
    }

    /// Member functions of the library channels.
    fn lib_channel_call(
        &mut self,
        b: Expression,
        c: &str,
        m: &str,
        args: &[sc::Expr],
        span: ScSpan,
    ) -> R<(Expression, Ty)> {
        let task = |lw: &mut Self, sv: &str| -> (Expression, Ty) {
            lw.f.is_task = true;
            let t = lw.temp(&Ty::int32());
            lw.pre.push(expr_stmt(method(b.clone(), sv, vec![ident(&t)])));
            (ident(&t), Ty::int32())
        };
        Ok(match (c, m, args.len()) {
            ("scrt_mutex", "lock", 0) => task(self, "lock"),
            ("scrt_mutex", "trylock" | "unlock", 0) => (method(b, m, vec![]), Ty::int32()),
            ("scrt_semaphore", "wait", 0) => task(self, "wait_"),
            ("scrt_semaphore", "trywait" | "post" | "get_value", 0) => (method(b, m, vec![]), Ty::int32()),
            ("scrt_event_queue", "notify", _) => {
                let t = match args {
                    [t] => self.expr(t)?.0,
                    [v, u] => self.time_value(v, u, span)?,
                    _ => return self.err(span, "notify(time) or notify(value, unit) expected"),
                };
                (method(b, "notify", vec![t]), Ty::Void)
            }
            ("scrt_event_queue", "cancel_all", 0) => (method(b, "cancel_all", vec![]), Ty::Void),
            ("scrt_event_queue", "default_event", 0) => (member(b, "ev"), Ty::Event),
            _ => return self.err(span, format!("'{}' is not a member function of this channel", m)),
        })
    }

    /// `obj.m(args)` on an object of the user class `cls`; a member function
    /// that may block is a task returning through an output argument.
    pub fn object_call(
        &mut self,
        obj: Expression,
        cls: &str,
        m: &str,
        mut xs: Vec<Expression>,
        span: ScSpan,
    ) -> R<(Expression, Ty)> {
        let sig = self.prog.user_classes.borrow().get(cls).cloned();
        let Some(sig) = sig else {
            return self.err(span, "not a class");
        };
        let Some(ms) = sig.method(m, xs.len()).cloned() else {
            return self.err(
                span,
                format!(
                    "'{}' has no member function '{}' taking {} arguments",
                    sig.cpp,
                    m,
                    xs.len()
                ),
            );
        };
        if ms.sig.is_task {
            self.f.is_task = true;
            if !matches!(ms.sig.ret, Ty::Void) {
                let t = self.temp(&ms.sig.ret);
                xs.push(ident(&t));
                self.pre.push(expr_stmt(method(obj, &ms.sv, xs)));
                return Ok((ident(&t), ms.sig.ret.clone()));
            }
        }
        Ok((method(obj, &ms.sv, xs), ms.sig.ret.clone()))
    }

    /// A port or export of a user interface `e` names (`p`, `p[i]`): the
    /// SV object, the interface and the index of the channel.
    pub fn port_ref(&self, e: &sc::Expr) -> Option<(Expression, String, Option<sc::Expr>)> {
        let (e, idx) = match &e.kind {
            sc::ExprKind::Index { base, index } => (base.as_ref(), Some((**index).clone())),
            _ => (e, None),
        };
        match &e.kind {
            sc::ExprKind::Name(q) if q.segments.len() == 1 => {
                let sym = self.lookup(q.last_name())?;
                match sym.kind {
                    SymKind::Port(i) | SymKind::Export(i) => Some((ident(&sym.sv), i, idx)),
                    _ => None,
                }
            }
            // A child's port or export (`top.exp->f()` in sc_main).
            sc::ExprKind::Member { base, name, .. } => {
                let q = base.as_name()?;
                let sym = self.lookup(q.last_name())?;
                let SymKind::Instance(module) = &sym.kind else {
                    return None;
                };
                let Some(Ty::Class(pc)) = self.prog.module_member_ty(module, &name.ident.name) else {
                    return None;
                };
                let ifc = format!("sc_c_{}", pc.strip_prefix("__sc_port__")?);
                Some((member(ident(&sym.sv), &name.ident.name), ifc, idx))
            }
            _ => None,
        }
    }

    /// The channel interface a port or export reaches: `p.get(i)`.
    pub fn port_channel(&mut self, obj: &Expression, idx: Option<&sc::Expr>) -> R<Expression> {
        let i = match idx {
            Some(e) => self.expr(e)?.0,
            None => int(0),
        };
        Ok(method(obj.clone(), "get", vec![i]))
    }

    /// `T::__sc_make<k>(args)`: a new object of the user class `cls`.
    pub fn make_object(&mut self, cls: &str, args: &[sc::Expr], span: ScSpan) -> R<Expression> {
        let sig = self.prog.user_classes.borrow().get(cls).cloned();
        let Some(sig) = sig else {
            return self.err(span, "not a class");
        };
        let Some(k) = sig.ctor(args.len()) else {
            return self.err(
                span,
                format!("'{}' has no constructor taking {} arguments", sig.cpp, args.len()),
            );
        };
        let mut xs = Vec::new();
        for a in args {
            xs.push(self.expr(a)?.0);
        }
        Ok(call(member(ident(cls), &format!("__sc_make{}", k)), xs))
    }

    /// The writer a write site stands for: the process running this
    /// function, code outside processes, or — in a function several
    /// processes share — whichever runs it (`None`: decided at run time).
    pub fn writer(&self) -> Option<Writer> {
        match (self.f.proc, self.f.shared) {
            (Some(p), _) => Some(Writer::Process(p)),
            (None, true) => None,
            (None, false) => Some(Writer::Outside),
        }
    }

    /// The driver variable of `writer` on the resolved net `net`.
    pub fn driver_var(&mut self, net: &str, writer: Writer) -> String {
        let key = (net.to_string(), writer);
        if let Some(v) = self.m.drivers.get(&key) {
            return v.clone();
        }
        let v = match writer {
            Writer::Process(p) => format!("__sc_drv{}_{}", p, net),
            Writer::Outside => format!("__sc_drvx_{}", net),
        };
        self.m.drivers.insert(key, v.clone());
        v
    }

    /// A write of `value` to the resolved net `net` (width `w`): the writer's
    /// driver becomes {written, value} in the update phase (§6.13.4).
    fn resolved_write(&mut self, net: &str, w: u32, value: Expression) -> Statement {
        let word = concat(vec![sized(1, 1), size_cast(w, paren(value))]);
        match self.writer() {
            Some(wr) => nba(ident(&self.driver_var(net, wr)), word),
            None => {
                // The writing process is known only at run time.
                self.m.needs_pid = true;
                let n = self.m.procs.len();
                let mut stmt = None;
                for p in (0..n).rev() {
                    let d = self.driver_var(net, Writer::Process(p));
                    let w_ = nba(ident(&d), word.clone());
                    stmt = Some(match stmt {
                        None => w_,
                        Some(rest) => if_(
                            bin(BinaryOp::Eq, call_fn("__sc_pid", vec![]), int(p as i64 + 1)),
                            w_,
                            Some(rest),
                        ),
                    });
                }
                stmt.unwrap_or_else(null_stmt)
            }
        }
    }

    pub fn expr(&mut self, e: &sc::Expr) -> R<(Expression, Ty)> {
        use sc::ExprKind as K;
        let span = e.span;
        match &e.kind {
            K::IntLit { text, value } => {
                let v = value.ok_or(()).or_else(|_| {
                    self.err(span, format!("integer literal '{}' is too large", text))
                })?;
                let unsigned = text.to_ascii_lowercase().contains('u');
                let long = text.to_ascii_lowercase().contains('l') || v > i32::MAX as u64;
                if v > i32::MAX as u64 || unsigned && long {
                    Ok((
                        u64_lit(v),
                        Ty::Int {
                            bits: 64,
                            signed: !unsigned,
                            ch: false,
                        },
                    ))
                } else if unsigned {
                    Ok((
                        sized(32, v),
                        Ty::Int {
                            bits: 32,
                            signed: false,
                            ch: false,
                        },
                    ))
                } else {
                    Ok((int(v as i64), Ty::int32()))
                }
            }
            K::FloatLit { text } => {
                let t = text
                    .trim_end_matches(['f', 'F', 'l', 'L'])
                    .replace('\'', "");
                let v: f64 = t
                    .parse()
                    .or_else(|_| self.err(span, "bad floating literal"))?;
                Ok((real(v), Ty::Real { single: false }))
            }
            K::CharLit { text } => {
                let v = char_value(text)
                    .ok_or(())
                    .or_else(|_| self.err(span, "bad character literal"))?;
                Ok((
                    sized(8, v as u64),
                    Ty::Int {
                        bits: 8,
                        signed: true,
                        ch: true,
                    },
                ))
            }
            K::StringLit { value, .. } => Ok((string(value), Ty::Str)),
            K::BoolLit(b) => Ok((sized(1, *b as u64), Ty::Bool)),
            K::Nullptr => Ok((null(), Ty::Ptr { elem: 1 })),
            // In a user class's member function `this` points to the object.
            K::This => match &self.m.class {
                Some(c) => Ok((ex(ExprKind::This), Ty::Handle(c.clone()))),
                None => self.err(
                    span,
                    "'this' is only supported in member functions of classes, register_b_transport and socket binding",
                ),
            },
            K::Name(q) => self.name(q, span),
            K::Paren(inner) => {
                if let K::Binary {
                    op: sc::BinaryOp::Comma,
                    ..
                } = &inner.kind
                {
                    return self.concat(inner);
                }
                let (x, t) = self.expr(inner)?;
                Ok((paren(x), t))
            }
            K::Unary { op, operand } => self.unary(*op, operand, span),
            K::Postfix { op, operand } => {
                let (x, t) = self.expr(operand)?;
                let op = match op {
                    sc::PostfixOp::Inc => UnaryOp::PostIncr,
                    sc::PostfixOp::Dec => UnaryOp::PostDecr,
                };
                Ok((unary(op, x), t))
            }
            K::Binary { op, lhs, rhs } => self.binary(*op, lhs, rhs, span),
            K::Conditional {
                cond: c,
                then_expr,
                else_expr,
            } => {
                let (c, _) = self.expr(c)?;
                let (t, tt) = self.expr(then_expr)?;
                let (f, _) = self.expr(else_expr)?;
                Ok((cond(c, t, f), tt))
            }
            K::Call { callee, args } => self.call(callee, args, span),
            K::Index { base, index: i } => self.index_expr(base, i, span),
            K::Member { base, name, .. } => self.member_expr(base, name, span),
            K::Cast { kind, ty, expr } => self.cast(*kind, ty, expr, span),
            K::Construct { ty, args, .. } => {
                let t = self.ty(ty, span)?;
                match args.as_slice() {
                    [] => Ok((int(0), t)),
                    [a] => {
                        let (x, _) = self.expr(a)?;
                        Ok((type_cast(sv_scalar_type(&t), x), t))
                    }
                    _ => self.err(
                        span,
                        "a constructor call with several arguments is not supported here",
                    ),
                }
            }
            K::SizeofType(t) => {
                let ty = self.ty(t, span)?;
                match ty.byte_size() {
                    Some(n) => Ok((
                        int(n as i64),
                        Ty::Int {
                            bits: 64,
                            signed: false,
                            ch: false,
                        },
                    )),
                    None => self.err(span, "sizeof of this type is not supported"),
                }
            }
            K::SizeofExpr(x) => {
                let (_, t) = self.expr(x)?;
                let n = match &t {
                    Ty::Array(elem, n) => {
                        elem.byte_size().zip(expr_int(n)).map(|(a, b)| a as i64 * b)
                    }
                    other => other.byte_size().map(|v| v as i64),
                };
                match n {
                    Some(n) => Ok((
                        int(n),
                        Ty::Int {
                            bits: 64,
                            signed: false,
                            ch: false,
                        },
                    )),
                    None => self.err(span, "sizeof of this expression is not supported"),
                }
            }
            K::InitList(items) => {
                let mut parts = Vec::new();
                for it in items {
                    parts.push(crate::ast::expr::AssignmentPatternItem::Ordered(
                        self.expr(it)?.0,
                    ));
                }
                Ok((ex(ExprKind::AssignmentPattern(parts)), Ty::int32()))
            }
            // `new T(args)`: a new object of a user class (a pointer to it).
            K::New {
                ty,
                args,
                array_size: None,
                ..
            } if self
                .ty(ty, span)
                .ok()
                .and_then(|t| self.user_class(&t))
                .is_some() =>
            {
                let cls = self
                    .ty(ty, span)
                    .ok()
                    .and_then(|t| self.user_class(&t))
                    .expect("checked");
                let x = self.make_object(&cls, args.as_deref().unwrap_or(&[]), span)?;
                Ok((x, Ty::Handle(cls)))
            }
            // `new T[n]` of a scalar type: a data pointer to a new array.
            K::New {
                ty,
                array_size: Some(n),
                ..
            } => {
                let elem = self.ty(ty, span)?;
                let Some(bytes) = elem.byte_size().filter(|_| elem.is_scalar_bits() || matches!(elem, Ty::Bool)) else {
                    return self.err(span, "'new[]' of this type is not supported");
                };
                let (n, _) = self.expr(n)?;
                Ok((
                    call_fn("scrt_new_array", vec![int(bytes as i64), n]),
                    Ty::Ptr { elem: bytes as u32 },
                ))
            }
            // `new tlm_generic_payload`: an object of a runtime class.
            K::New {
                ty,
                args: None | Some(_),
                array_size: None,
                ..
            } if matches!(self.ty(ty, span), Ok(Ty::Class(_))) => {
                let Ok(Ty::Class(c)) = self.ty(ty, span) else {
                    unreachable!("checked")
                };
                Ok((new_obj(None), Ty::Handle(c)))
            }
            K::New { .. } => self.err(
                span,
                "'new' is supported only to create a child module or initialize a declared object",
            ),
            K::Lambda(_) => self.err(span, "lambdas are not supported in simulation"),
            K::Throw(_) => self.err(span, "exceptions are not supported in simulation"),
            _ => self.err(span, "this expression is not supported in simulation"),
        }
    }

    fn name(&mut self, q: &sc::QualifiedName, span: ScSpan) -> R<(Expression, Ty)> {
        let path = short_path(q);
        if !path.contains("::")
            && let Some(sym) = self.lookup(&path)
        {
            return Ok((self.sym_read(&sym), sym.ty.clone()));
        }
        if let Some(v) = self.enum_consts.get(&path) {
            return Ok((int(*v), Ty::int32()));
        }
        match path.as_str() {
            "SC_ZERO_TIME" => return Ok((u64_lit(0), Ty::Time)),
            // glibc's.
            "RAND_MAX" => return Ok((int(2147483647), Ty::int32())),
            "NULL" => return Ok((null(), Ty::Ptr { elem: 1 })),
            "SC_LOGIC_0" => return Ok((sized(1, 0), Ty::Vec4 { w: Width::known(1) })),
            "SC_LOGIC_1" => return Ok((sized(1, 1), Ty::Vec4 { w: Width::known(1) })),
            "SC_LOGIC_X" => {
                return Ok((
                    ex(ExprKind::Number(
                        crate::ast::expr::NumberLiteral::UnbasedUnsized('x'),
                    )),
                    Ty::Vec4 { w: Width::known(1) },
                ));
            }
            "SC_LOGIC_Z" => {
                return Ok((
                    ex(ExprKind::Number(
                        crate::ast::expr::NumberLiteral::UnbasedUnsized('z'),
                    )),
                    Ty::Vec4 { w: Width::known(1) },
                ));
            }
            _ => {}
        }
        let last = q.last_name();
        // `T::m`: a static member of a user class.
        if q.segments.len() >= 2 {
            let cls = super::classes::class_sv(&q.segments[q.segments.len() - 2].ident.name);
            if let Some(t) = self.prog.class_field_ty(&cls, last) {
                return Ok((member(ident(&cls), &super::classes::escape_sv(last)), t));
            }
        }
        if last.starts_with("TLM_")
            || matches!(
                last,
                "BEGIN_REQ" | "END_REQ" | "BEGIN_RESP" | "END_RESP" | "UNINITIALIZED_PHASE"
            )
        {
            return Ok((ident(last), Ty::int32()));
        }
        if let Some(v) = self.prog.global_consts.get(last) {
            return Ok((int(*v), Ty::int32()));
        }
        match self.env.tparams.get(last) {
            Some(TParam::Value(sv)) => return Ok((ident(sv), Ty::int32())),
            Some(TParam::Const(v)) => return Ok((int(*v), Ty::int32())),
            _ => {}
        }
        self.err(span, format!("unknown name '{}'", path))
    }

    /// `(a, b, …)` as a SystemC concatenation.
    fn concat(&mut self, e: &sc::Expr) -> R<(Expression, Ty)> {
        let mut parts = Vec::new();
        flatten_comma(e, &mut parts);
        let mut out = Vec::new();
        let mut width = Some(0u32);
        for p in parts {
            let (x, t) = self.expr(p)?;
            let w = match &t {
                Ty::Bool => Some(1),
                Ty::Vec2 { w, .. } | Ty::Vec4 { w, .. } => w.n,
                _ => {
                    return self.err(p.span, "the comma operator is supported only as a SystemC concatenation of bit vectors");
                }
            };
            width = width.zip(w).map(|(a, b)| a + b);
            out.push(x);
        }
        let w = width.unwrap_or(64);
        Ok((
            concat(out),
            Ty::Vec2 {
                w: Width::known(w),
                signed: false,
                bv: false,
            },
        ))
    }

    fn unary(&mut self, op: sc::UnaryOp, operand: &sc::Expr, span: ScSpan) -> R<(Expression, Ty)> {
        use sc::UnaryOp as U;
        match op {
            U::AddrOf => self.address_of(operand, span),
            U::Deref => {
                // `*s++` on a C string (`const char*`): its first character,
                // and the string then starts one later.
                let ch = Ty::Int {
                    bits: 8,
                    signed: true,
                    ch: true,
                };
                if let sc::ExprKind::Postfix {
                    op: sc::PostfixOp::Inc,
                    operand: inner,
                } = &operand.kind
                {
                    let saved = self.pre.len();
                    if let Ok((sx, Ty::Str)) = self.expr(inner) {
                        let t = self.temp(&ch);
                        self.pre.push(assign(ident(&t), index(sx.clone(), int(0))));
                        let rest = method(
                            sx.clone(),
                            "substr",
                            vec![int(1), bin(BinaryOp::Sub, method(sx, "len", vec![]), int(1))],
                        );
                        let store = self.store(inner, rest, span)?;
                        self.pre.extend(store);
                        return Ok((ident(&t), ch));
                    }
                    self.pre.truncate(saved);
                }
                // `*reinterpret_cast<T*>(p)` / `*p`: read through a data pointer.
                let (p, t) = self.expr(operand)?;
                if matches!(t, Ty::Str) {
                    return Ok((index(p, int(0)), ch));
                }
                match t {
                    Ty::Ptr { elem } => Ok((ptr_get(p, int(0), elem), ptr_elem_ty(elem))),
                    // `*p` is the object the pointer points to.
                    Ty::Handle(c) => Ok((p, Ty::Class(c))),
                    Ty::Class(_) => Ok((p, t)),
                    _ => self.err(span, "dereferencing this pointer is not supported"),
                }
            }
            _ => {
                let (x, t) = self.expr(operand)?;
                let (sv, rt) = match op {
                    U::Plus => (UnaryOp::Plus, t),
                    U::Neg => (UnaryOp::Minus, t),
                    U::Not => (UnaryOp::LogNot, Ty::Bool),
                    U::BitNot => (UnaryOp::BitNot, t),
                    U::PreInc => (UnaryOp::PreIncr, t),
                    U::PreDec => (UnaryOp::PreDecr, t),
                    _ => unreachable!("handled above"),
                };
                Ok((unary(sv, x), rt))
            }
        }
    }

    /// `&x` / `&arr[i]`: a data pointer into a boxed object.
    fn address_of(&mut self, operand: &sc::Expr, span: ScSpan) -> R<(Expression, Ty)> {
        use sc::ExprKind as K;
        // The address of an object is a pointer to it: its handle.
        let saved = self.pre.len();
        if let Ok((x, Ty::Class(c))) = self.expr(operand) {
            return Ok((x, Ty::Handle(c)));
        }
        self.pre.truncate(saved);
        match &operand.kind {
            K::Name(q) if q.segments.len() == 1 => {
                let Some(sym) = self.lookup(q.last_name()) else {
                    return self.err(span, format!("unknown name '{}'", q.last_name()));
                };
                match sym.kind {
                    SymKind::Boxed => {
                        let elem = sym.ty.byte_size().unwrap_or(1) as u32;
                        Ok((ptr_mk(ident(&sym.sv), int(0)), Ty::Ptr { elem }))
                    }
                    SymKind::BoxedArr => {
                        let elem = arr_elem_bytes(&sym.ty);
                        Ok((ptr_mk(ident(&sym.sv), int(0)), Ty::Ptr { elem }))
                    }
                    _ => self.err(
                        span,
                        format!("taking the address of '{}' is not supported", q.last_name()),
                    ),
                }
            }
            K::Index { base, index: i } => {
                let Some(q) = base.as_name() else {
                    return self.err(span, "taking this address is not supported");
                };
                let Some(sym) = self.lookup(q.last_name()) else {
                    return self.err(span, format!("unknown name '{}'", q.last_name()));
                };
                if sym.kind != SymKind::BoxedArr {
                    return self.err(
                        span,
                        format!(
                            "taking the address of an element of '{}' is not supported",
                            q.last_name()
                        ),
                    );
                }
                let elem = arr_elem_bytes(&sym.ty);
                let (i, _) = self.expr(i)?;
                let off = if elem == 1 {
                    i
                } else {
                    bin(BinaryOp::Mul, paren(i), int(elem as i64))
                };
                Ok((ptr_mk(ident(&sym.sv), off), Ty::Ptr { elem }))
            }
            _ => self.err(span, "taking this address is not supported"),
        }
    }

    fn binary(
        &mut self,
        op: sc::BinaryOp,
        lhs: &sc::Expr,
        rhs: &sc::Expr,
        span: ScSpan,
    ) -> R<(Expression, Ty)> {
        if op == sc::BinaryOp::Shl && (is_stream(lhs) || stream_base(lhs)) {
            return self.err(span, "stream output is supported only as a statement");
        }
        if op == sc::BinaryOp::Comma {
            return self.err(
                span,
                "the comma operator is supported only as a parenthesized SystemC concatenation",
            );
        }
        let (l, lt) = self.expr(lhs)?;
        let (r, rt) = self.expr(rhs)?;
        // Operators on objects are the class's operator functions; `!=`
        // without one is the negated `==`.
        if let Ty::Class(c) = &lt
            && self.user_class(&lt).is_some()
        {
            let spelling = super::classes::op_spelling(op);
            if let Some(e) = super::classes::object_op(self, c, spelling, l.clone(), r.clone()) {
                return Ok(e);
            }
            if op == sc::BinaryOp::Ne
                && let Some((e, _)) = super::classes::object_op(self, c, "==", l, r)
            {
                return Ok((super::classes::not(e), Ty::Bool));
            }
            return self.err(
                span,
                format!("this class has no operator{}", spelling),
            );
        }
        // Pointer arithmetic and null tests.
        if let Ty::Ptr { elem } = lt {
            match op {
                sc::BinaryOp::Add | sc::BinaryOp::Sub => {
                    let n = if elem == 1 {
                        r
                    } else {
                        bin(BinaryOp::Mul, paren(r), int(elem as i64))
                    };
                    let n = if op == sc::BinaryOp::Sub {
                        unary(UnaryOp::Minus, paren(n))
                    } else {
                        n
                    };
                    return Ok((method(l, "add", vec![n]), Ty::Ptr { elem }));
                }
                sc::BinaryOp::Eq | sc::BinaryOp::Ne => {
                    let op = if op == sc::BinaryOp::Eq {
                        BinaryOp::Eq
                    } else {
                        BinaryOp::Neq
                    };
                    return Ok((bin(op, l, null()), Ty::Bool));
                }
                _ => {}
            }
        }
        if let (
            Ty::Ptr { .. } | Ty::Class(_) | Ty::Handle(_),
            sc::BinaryOp::Eq | sc::BinaryOp::Ne,
        ) = (&rt, op)
        {
            let op = if op == sc::BinaryOp::Eq {
                BinaryOp::Eq
            } else {
                BinaryOp::Neq
            };
            return Ok((bin(op, null(), r), Ty::Bool));
        }
        let Some(sv) = sv_binop(op) else {
            return self.err(span, "this operator is not supported");
        };
        let sv = signed_shift(sv, &lt);
        let ty = match op {
            sc::BinaryOp::Lt
            | sc::BinaryOp::Gt
            | sc::BinaryOp::Le
            | sc::BinaryOp::Ge
            | sc::BinaryOp::Eq
            | sc::BinaryOp::Ne
            | sc::BinaryOp::LogAnd
            | sc::BinaryOp::LogOr => Ty::Bool,
            _ => arith_ty(&lt, &rt, op),
        };
        if matches!(lt, Ty::Str) && op == sc::BinaryOp::Add {
            return Ok((concat(vec![l, r]), Ty::Str));
        }
        // Integer division of two reals stays real; mixed SystemC arithmetic
        // is 64-bit in C++ (sc_uint promotes to uint64).
        Ok((bin(sv, l, r), ty))
    }

    /// `e` as a value of type `target`: a string literal assigned to an
    /// `sc_bv`/`sc_lv`/`sc_uint` is a bit string (IEEE 1666-2023 §7.9.8,
    /// `"01XZ"`, `"0b…"`, `"0x…"`), zero-extended to the width.
    pub fn expr_for(&mut self, e: &sc::Expr, target: &Ty) -> R<Expression> {
        let (sc::ExprKind::StringLit { value, .. }, Ty::Vec2 { w, .. } | Ty::Vec4 { w }) =
            (&e.kind, target)
        else {
            return Ok(self.expr(e)?.0);
        };
        let Some(n) = w.n else {
            return self.err(e.span, "a bit-string literal needs a constant width");
        };
        let four = matches!(target, Ty::Vec4 { .. });
        let (base, digits, per) = match value.get(..2) {
            Some("0x" | "0X") => (NumberBase::Hex, &value[2..], 4),
            Some("0b" | "0B") => (NumberBase::Binary, &value[2..], 1),
            _ => (NumberBase::Binary, value.as_str(), 1),
        };
        let ok = |c: char| match base {
            NumberBase::Hex => c.is_ascii_hexdigit(),
            _ => matches!(c, '0' | '1') || (four && matches!(c, 'x' | 'X' | 'z' | 'Z')),
        };
        if digits.is_empty() || !digits.chars().all(ok) {
            return self.err(
                e.span,
                format!("\"{}\" is not a bit string for this type", value),
            );
        }
        let mut d = digits.to_ascii_lowercase();
        let need = (n as usize).div_ceil(per);
        if d.len() > need {
            d = d[d.len() - need..].to_string();
        }
        while d.len() < need {
            d.insert(0, '0');
        }
        Ok(based_lit(n, base, d))
    }

    fn index_expr(&mut self, base: &sc::Expr, i: &sc::Expr, span: ScSpan) -> R<(Expression, Ty)> {
        if let Some(q) = base.as_name()
            && let Some(sym) = self.lookup(q.last_name())
            && sym.kind == SymKind::BoxedArr
        {
            let (iv, _) = self.expr(i)?;
            let elem = match &sym.ty {
                Ty::Array(e, _) => (**e).clone(),
                _ => Ty::int32(),
            };
            return Ok((index(member(ident(&sym.sv), "a"), iv), elem));
        }
        let (b, bt) = self.expr(base)?;
        let (iv, _) = self.expr(i)?;
        match bt {
            Ty::Array(elem, _) | Ty::Queue(elem) => Ok((index(b, iv), *elem)),
            Ty::Ptr { elem } => Ok((ptr_get(b, ptr_offset(iv, elem), elem), ptr_elem_ty(elem))),
            Ty::Vec2 { .. } | Ty::Vec4 { .. } | Ty::Int { .. } => Ok((index(b, iv), Ty::Bool)),
            Ty::Str => Ok((
                method(b, "getc", vec![iv]),
                Ty::Int {
                    bits: 8,
                    signed: true,
                    ch: true,
                },
            )),
            _ => self.err(span, "indexing this value is not supported"),
        }
    }

    fn member_expr(
        &mut self,
        base: &sc::Expr,
        name: &sc::NameSegment,
        span: ScSpan,
    ) -> R<(Expression, Ty)> {
        let field = name.ident.name.as_str();
        // `inst.signal` (sc_main / parent reading a child's member).
        if let Some(q) = base.as_name()
            && let Some(sym) = self.lookup(q.last_name())
            && let SymKind::Instance(module) = &sym.kind
        {
            let child = self.prog.module_member_ty(module, field);
            let resolved = self
                .prog
                .module_resolved
                .borrow()
                .get(module)
                .and_then(|r| r.get(field).copied());
            let x = member(ident(&sym.sv), field);
            return match child {
                // A child's resolved net reads its value bits.
                Some(t) => Ok((
                    match resolved {
                        Some(1) => index(x, int(0)),
                        Some(w) => range(x, int(w as i64 - 1), int(0)),
                        None => x,
                    },
                    t,
                )),
                None => self.err(span, format!("'{}' has no member '{}'", module, field)),
            };
        }
        let (b, bt) = self.expr(base)?;
        match bt {
            Ty::Class(c) | Ty::Handle(c) => {
                let t = self.prog.class_field_ty(&c, field);
                match t {
                    Some(t) => Ok((member(b, &super::classes::escape_sv(field)), t)),
                    None => self.err(span, format!("unknown member '{}'", field)),
                }
            }
            _ => self.err(
                span,
                format!("member '{}' access on this value is not supported", field),
            ),
        }
    }

    fn cast(
        &mut self,
        kind: sc::CastKind,
        ty: &sc::Type,
        e: &sc::Expr,
        span: ScSpan,
    ) -> R<(Expression, Ty)> {
        let t = self.ty(ty, span)?;
        let (x, xt) = self.expr(e)?;
        match (&t, &xt) {
            (Ty::Void, _) => Ok((x, Ty::Void)),
            // Reinterpreting a data pointer only changes its element size.
            (Ty::Ptr { elem }, Ty::Ptr { .. }) => Ok((x, Ty::Ptr { elem: *elem })),
            // Casts between objects or pointers of related classes keep
            // the handle (`static_cast<T*>(p)`, `dynamic_cast<T&>(o)`).
            (Ty::Class(_) | Ty::Handle(_), Ty::Class(_) | Ty::Handle(_)) => Ok((x, t)),
            _ if kind == sc::CastKind::Reinterpret => {
                self.err(span, "this reinterpret_cast is not supported")
            }
            // C++ converts floating to integer by truncation; an SV cast rounds.
            (Ty::Int { .. } | Ty::Vec2 { .. } | Ty::Bool, Ty::Real { .. }) => {
                Ok((type_cast(sv_scalar_type(&t), sys("$rtoi", vec![x])), t))
            }
            _ => Ok((type_cast(sv_scalar_type(&t), x), t)),
        }
    }

    /// The type of a member function call's result, for user classes.
    pub fn call(
        &mut self,
        callee: &sc::Expr,
        args: &[sc::Expr],
        span: ScSpan,
    ) -> R<(Expression, Ty)> {
        use sc::ExprKind as K;
        match &callee.kind {
            K::Name(q) if matches!(q.last_name(), "sc_spawn" | "sc_spawn_options") => self.err(
                span,
                "dynamic processes (sc_spawn) are not supported in simulation",
            ),
            K::Name(q) => self.call_name(q, args, span),
            K::Member { base, name, .. } => {
                self.call_method(base, &name.ident.name, name, args, span)
            }
            _ => self.err(span, "this call is not supported"),
        }
    }

    fn args(&mut self, args: &[sc::Expr]) -> R<Vec<(Expression, Ty)>> {
        args.iter().map(|a| self.expr(a)).collect()
    }

    /// `sc_time(v, unit)` and `wait(v, unit)` time values, in ps.
    pub fn time_value(&mut self, v: &sc::Expr, unit: &sc::Expr, span: ScSpan) -> R<Expression> {
        let Some(factor) = time_unit(unit) else {
            return self.err(span, "expected a time unit (SC_NS, …)");
        };
        if let Some(c) = self.const_eval(v) {
            return Ok(u64_lit((c as f64 * factor).round() as u64));
        }
        if let sc::ExprKind::FloatLit { text } = &v.kind
            && let Ok(f) = text.trim_end_matches(['f', 'F']).parse::<f64>()
        {
            return Ok(u64_lit((f * factor).round() as u64));
        }
        let (x, t) = self.expr(v)?;
        let prod = if matches!(t, Ty::Real { .. }) || factor < 1.0 {
            bin(BinaryOp::Mul, paren(x), real(factor))
        } else {
            bin(
                BinaryOp::Mul,
                type_cast(atom_t(crate::ast::types::IntegerAtomType::LongInt, true), x),
                u64_lit(factor as u64),
            )
        };
        Ok(type_cast(
            atom_t(crate::ast::types::IntegerAtomType::LongInt, true),
            prod,
        ))
    }

    fn call_name(
        &mut self,
        q: &sc::QualifiedName,
        args: &[sc::Expr],
        span: ScSpan,
    ) -> R<(Expression, Ty)> {
        let path = short_path(q);
        let name = path.as_str();
        // `T(args)` / `box<int>(args)`: a temporary object of a user class.
        {
            let consts = |e: &sc::Expr| self.const_eval(e);
            if let Ok(t @ Ty::Class(_)) = ty_of_name(q, &self.env, &consts)
                && let Some(cls) = self.user_class(&t)
            {
                let x = self.make_object(&cls, args, span)?;
                return Ok((x, Ty::Class(cls)));
            }
        }
        // Template-id constructors: `sc_uint<8>(x)`.
        if q.last_args().is_some() || matches!(name, "sc_time" | "int" | "unsigned") {
            if name == "sc_time" {
                return match args {
                    [v, u] => Ok((self.time_value(v, u, span)?, Ty::Time)),
                    [] => Ok((u64_lit(0), Ty::Time)),
                    _ => self.err(span, "sc_time(value, unit) expected"),
                };
            }
            let consts = |e: &sc::Expr| self.const_eval(e);
            if let Ok(t) = ty_of_name(q, &self.env, &consts) {
                let [a] = args else {
                    return self.err(span, "a conversion takes one argument");
                };
                let (x, _) = self.expr(a)?;
                return Ok((type_cast(sv_scalar_type(&t), x), t));
            }
        }
        // `T::f(args)`: a static member function of a user class.
        if q.segments.len() >= 2 {
            let cls = super::classes::class_sv(&q.segments[q.segments.len() - 2].ident.name);
            let ms = self
                .prog
                .user_classes
                .borrow()
                .get(&cls)
                .and_then(|s| s.method(q.last_name(), args.len()).cloned());
            if let Some(ms) = ms {
                let xs = self.args(args)?.into_iter().map(|a| a.0).collect();
                return Ok((call(member(ident(&cls), &ms.sv), xs), ms.sig.ret.clone()));
            }
        }
        // An overloaded member function, by its number of arguments.
        let overload = format!("{}__{}", name, args.len());
        let name = if !self.m.funcs.contains_key(name) && self.m.funcs.contains_key(&overload) {
            overload.as_str()
        } else {
            name
        };
        if let Some(sig) = self.m.funcs.get(name).cloned() {
            let mut lowered = Vec::new();
            for (i, a) in args.iter().enumerate() {
                if sig.by_ref.get(i).copied().unwrap_or(false) {
                    lowered.push(self.lvalue_ref(a)?);
                } else {
                    lowered.push(self.expr(a)?.0);
                }
            }
            if sig.is_task {
                self.f.is_task = true;
                if !matches!(sig.ret, Ty::Void) {
                    // A blocking function returns through an output argument.
                    let t = self.temp(&sig.ret);
                    lowered.push(ident(&t));
                    self.pre.push(expr_stmt(call_fn(name, lowered)));
                    return Ok((ident(&t), sig.ret.clone()));
                }
            }
            return Ok((call_fn(name, lowered), sig.ret.clone()));
        }
        // A functional cast to a named type: `sc_dt::uint64(x)`, `T(x)`.
        if args.len() == 1 {
            let consts = |e: &sc::Expr| self.const_eval(e);
            if let Ok(t) = ty_of_name(q, &self.env, &consts)
                && (t.is_scalar_bits() || matches!(t, Ty::Real { .. } | Ty::Time))
            {
                let (x, xt) = self.expr(&args[0])?;
                let x = if matches!(xt, Ty::Real { .. }) && !matches!(t, Ty::Real { .. }) {
                    sys("$rtoi", vec![x])
                } else {
                    x
                };
                return Ok((type_cast(sv_scalar_type(&t), x), t));
            }
        }
        if let Some(f) = self.prog.free_fn_sig(name) {
            let lowered: Vec<Expression> = self.args(args)?.into_iter().map(|a| a.0).collect();
            return Ok((call_fn(&format!("sc_f_{}", name), lowered), f));
        }
        let a = self.args(args)?;
        let first = |i: usize| a.get(i).map(|x| x.0.clone());
        Ok(match (name, a.len()) {
            // §5.17 the module's own name.
            ("name", 0) if !self.m.tb => (ident("__sc_path"), Ty::Str),
            ("basename", 0) if !self.m.tb => (
                call_fn("scrt_basename", vec![ident("__sc_path")]),
                Ty::Str,
            ),
            ("sc_time_stamp", 0) => {
                if self.m.tb {
                    (ident("scrt_tb_now"), Ty::Time)
                } else {
                    (call_fn("scrt_now", vec![]), Ty::Time)
                }
            }
            ("sc_simulation_time", 0) => (
                bin(
                    BinaryOp::Div,
                    type_cast(
                        real_t(crate::ast::types::RealType::Real),
                        sys("$time", vec![]),
                    ),
                    real(1000.0),
                ),
                Ty::Real { single: false },
            ),
            ("sc_delta_count", 0) => (
                u64_lit(0),
                Ty::Int {
                    bits: 64,
                    signed: false,
                    ch: false,
                },
            ),
            ("memcpy", 3) => (
                call_fn(
                    "scrt_memcpy",
                    vec![
                        self.ptr_arg(&args[0], &a[0])?,
                        self.ptr_arg(&args[1], &a[1])?,
                        a[2].0.clone(),
                    ],
                ),
                Ty::Void,
            ),
            ("memset", 3) => (
                call_fn(
                    "scrt_memset",
                    vec![
                        self.ptr_arg(&args[0], &a[0])?,
                        a[1].0.clone(),
                        a[2].0.clone(),
                    ],
                ),
                Ty::Void,
            ),
            ("memcmp", 3) => (
                call_fn(
                    "scrt_memcmp",
                    vec![
                        self.ptr_arg(&args[0], &a[0])?,
                        self.ptr_arg(&args[1], &a[1])?,
                        a[2].0.clone(),
                    ],
                ),
                Ty::int32(),
            ),
            // C's rand()/srand(): glibc's sequence, as the C program has.
            ("rand", 0) => (call_fn("scrt_rand", vec![]), Ty::int32()),
            ("srand", 1) => (call_fn("scrt_srand", vec![a[0].0.clone()]), Ty::Void),
            ("abs" | "labs" | "llabs", 1) => {
                let x = first(0).expect("one arg");
                (
                    cond(
                        bin(BinaryOp::Lt, x.clone(), int(0)),
                        unary(UnaryOp::Minus, x.clone()),
                        x,
                    ),
                    a[0].1.clone(),
                )
            }
            ("min", 2) => (
                cond(
                    bin(BinaryOp::Lt, a[0].0.clone(), a[1].0.clone()),
                    a[0].0.clone(),
                    a[1].0.clone(),
                ),
                a[0].1.clone(),
            ),
            ("max", 2) => (
                cond(
                    bin(BinaryOp::Gt, a[0].0.clone(), a[1].0.clone()),
                    a[0].0.clone(),
                    a[1].0.clone(),
                ),
                a[0].1.clone(),
            ),
            ("to_string", 1) => {
                let f = if matches!(a[0].1, Ty::Real { .. }) {
                    "%f"
                } else {
                    "%0d"
                };
                (sys("$sformatf", vec![string(f), a[0].0.clone()]), Ty::Str)
            }
            // <cmath>: the IEEE 1800-2017 §20.8.2 real math functions.
            (f, 1) if math1(f).is_some() => (
                sys(math1(f).expect("checked"), vec![a[0].0.clone()]),
                Ty::Real { single: false },
            ),
            ("pow" | "powf", 2) => (
                sys("$pow", vec![a[0].0.clone(), a[1].0.clone()]),
                Ty::Real { single: false },
            ),
            ("atan2" | "atan2f", 2) => (
                sys("$atan2", vec![a[0].0.clone(), a[1].0.clone()]),
                Ty::Real { single: false },
            ),
            ("fabs" | "fabsf", 1) => {
                let x = a[0].0.clone();
                (
                    cond(
                        bin(BinaryOp::Lt, x.clone(), real(0.0)),
                        unary(UnaryOp::Minus, x.clone()),
                        x,
                    ),
                    Ty::Real { single: false },
                )
            }
            ("sc_create_vcd_trace_file", 1) => (
                sys(
                    "$dumpfile",
                    vec![bin(BinaryOp::Add, a[0].0.clone(), string(""))],
                ),
                Ty::Void,
            ),
            _ => {
                return self.err(
                    span,
                    format!("call to '{}' is not supported in simulation", path),
                );
            }
        })
    }

    /// A `memcpy`-style pointer argument; an array name decays to a pointer.
    fn ptr_arg(&mut self, e: &sc::Expr, lowered: &(Expression, Ty)) -> R<Expression> {
        if let Some(q) = e.as_name()
            && let Some(sym) = self.lookup(q.last_name())
            && sym.kind == SymKind::BoxedArr
        {
            return Ok(ptr_mk(ident(&sym.sv), int(0)));
        }
        match lowered.1 {
            Ty::Ptr { .. } => Ok(lowered.0.clone()),
            _ => self.err(
                e.span,
                "expected a pointer to an object whose address is taken",
            ),
        }
    }

    /// An argument passed to a non-const reference parameter (`ref`).
    fn lvalue_ref(&mut self, e: &sc::Expr) -> R<Expression> {
        if let Some(q) = e.as_name()
            && let Some(sym) = self.lookup(q.last_name())
            && sym.kind == SymKind::Boxed
        {
            return Ok(member(ident(&sym.sv), "v"));
        }
        if let sc::ExprKind::Unary {
            op: sc::UnaryOp::Deref,
            operand,
        } = &e.kind
        {
            return Ok(self.expr(operand)?.0);
        }
        Ok(self.expr(e)?.0)
    }

    fn call_method(
        &mut self,
        base: &sc::Expr,
        m: &str,
        seg: &sc::NameSegment,
        args: &[sc::Expr],
        span: ScSpan,
    ) -> R<(Expression, Ty)> {
        if matches!(m, "name" | "basename")
            && args.is_empty()
            && let Some(n) = self.object_name(base, m == "basename")
        {
            return Ok((n, Ty::Str));
        }
        // A port or export of a user interface (§5.12): `p->m(args)` calls
        // the channel; `size()` and `get_interface()` are the port's own.
        if let Some((obj, ifc, idx)) = self.port_ref(base) {
            match (m, args.len()) {
                ("size", 0) => return Ok((method(obj, "size", vec![]), Ty::int32())),
                ("get_interface", 0) | ("operator->", 0) => {
                    let ch = self.port_channel(&obj, idx.as_ref())?;
                    return Ok((ch, Ty::Handle(ifc)));
                }
                _ => {}
            }
            let ch = self.port_channel(&obj, idx.as_ref())?;
            let is_event = self
                .prog
                .user_classes
                .borrow()
                .get(&ifc)
                .is_some_and(|s| s.events.contains(m));
            if is_event {
                return Ok((member(ch, &format!("__sc_ev_{}", m)), Ty::Event));
            }
            let mut xs = Vec::new();
            for a in args {
                xs.push(self.expr(a)?.0);
            }
            return self.object_call(ch, &ifc, m, xs, span);
        }
        // `inst.sig.read()`: a child's signal or port, read from its parent.
        if matches!(m, "read" | "get_new_value")
            && args.is_empty()
            && let sc::ExprKind::Member { base: inner, .. } = &base.kind
            && inner
                .as_name()
                .and_then(|q| self.lookup(q.last_name()))
                .is_some_and(|s| matches!(s.kind, SymKind::Instance(_)))
        {
            return self.expr(base);
        }
        // Objects by symbol kind first.
        let sym = base.as_name().and_then(|q| {
            if q.segments.len() == 1 {
                self.lookup(q.last_name())
            } else {
                None
            }
        });
        let sym = match (&sym, &base.kind) {
            (None, sc::ExprKind::Index { base: b, .. }) => b
                .as_name()
                .and_then(|q| self.lookup(q.last_name()))
                .filter(|s| s.is_signal_like()),
            _ => sym,
        };
        if let Some(sym) = &sym {
            match sym.kind {
                SymKind::Signal
                | SymKind::InPort
                | SymKind::OutPort
                | SymKind::InOutPort
                | SymKind::Clock => {
                    let (x, t) = self.expr(base)?;
                    let elem_t = match &t {
                        Ty::Array(e, _) => (**e).clone(),
                        other => other.clone(),
                    };
                    return match m {
                        "read" | "get_new_value" => Ok((x, elem_t)),
                        "posedge" | "negedge" | "event" => {
                            let flag = self.edge_flag(&sym.sv, span)?;
                            let f = ident(&flag);
                            Ok(match m {
                                "posedge" => (
                                    bin(BinaryOp::LogAnd, f, bin(BinaryOp::Eq, x, sized(1, 1))),
                                    Ty::Bool,
                                ),
                                "negedge" => (
                                    bin(BinaryOp::LogAnd, f, bin(BinaryOp::Eq, x, sized(1, 0))),
                                    Ty::Bool,
                                ),
                                _ => (f, Ty::Bool),
                            })
                        }
                        "name" | "basename" => Ok((string(&sym.sv), Ty::Str)),
                        "write" => self.err(span, "write() is supported only as a statement"),
                        _ => self.err(
                            span,
                            format!("'{}' on a signal or port is not supported", m),
                        ),
                    };
                }
                SymKind::Fifo | SymKind::FifoIn | SymKind::FifoOut => {
                    let elem = match &sym.ty {
                        Ty::Mailbox(e) => (**e).clone(),
                        _ => Ty::int32(),
                    };
                    let h = ident(&sym.sv);
                    return match m {
                        "read" if args.is_empty() => {
                            let t = self.temp(&elem);
                            self.pre.push(expr_stmt(method(h, "get", vec![ident(&t)])));
                            self.f.is_task = true;
                            Ok((ident(&t), elem))
                        }
                        "num_available" => Ok((method(h, "num", vec![]), Ty::int32())),
                        "num_free" => Ok((method(h, "num_free", vec![]), Ty::int32())),
                        "data_written_event" | "default_event" => Ok((member(h, "written_ev"), Ty::Event)),
                        "data_read_event" => Ok((member(h, "read_ev"), Ty::Event)),
                        "nb_read" => {
                            let target = self.lvalue_ref(&args[0])?;
                            Ok((method(h, "try_get", vec![target]), Ty::Bool))
                        }
                        "nb_write" => {
                            let (v, _) = self.expr(&args[0])?;
                            Ok((method(h, "try_put", vec![v]), Ty::Bool))
                        }
                        _ => self.err(
                            span,
                            format!("'{}' on a FIFO is supported only as a statement", m),
                        ),
                    };
                }
                SymKind::InitSocket => {
                    let s = ident(&sym.sv);
                    return match m {
                        "transport_dbg" => {
                            let (t, _) = self.expr(&args[0])?;
                            Ok((
                                method(s, "transport_dbg", vec![t]),
                                Ty::Int {
                                    bits: 32,
                                    signed: false,
                                    ch: false,
                                },
                            ))
                        }
                        "get_direct_mem_ptr" => {
                            let (t, _) = self.expr(&args[0])?;
                            Ok((method(s, "get_direct_mem_ptr", vec![t]), Ty::Bool))
                        }
                        _ => self.err(
                            span,
                            format!("'{}' on a socket is supported only as a statement", m),
                        ),
                    };
                }
                _ => {}
            }
        }
        let _ = seg;
        let (b, bt) = self.expr(base)?;
        // Library channels lower their own arguments (`notify(5, SC_NS)`).
        if let Ty::Class(c) | Ty::Handle(c) = &bt
            && matches!(c.as_str(), "scrt_mutex" | "scrt_semaphore" | "scrt_event_queue")
        {
            let c = c.clone();
            return self.lib_channel_call(b, &c, m, args, span);
        }
        let a = self.args(args)?;
        let arg = |i: usize| a[i].0.clone();
        match &bt {
            Ty::Bool | Ty::Vec2 { .. } | Ty::Vec4 { .. } | Ty::Int { .. } => {
                let wide = Ty::Int {
                    bits: 64,
                    signed: false,
                    ch: false,
                };
                Ok(match (m, a.len()) {
                    ("range", 2) => {
                        let w = self
                            .const_eval(&args[0])
                            .zip(self.const_eval(&args[1]))
                            .map(|(h, l)| (h - l).unsigned_abs() as u32 + 1);
                        let t = Ty::Vec2 {
                            w: Width::known(w.unwrap_or(64)),
                            signed: false,
                            bv: matches!(bt, Ty::Vec2 { bv: true, .. }),
                        };
                        (range(b, arg(0), arg(1)), t)
                    }
                    ("bit" | "get_bit", 1) => (index(b, arg(0)), Ty::Bool),
                    ("to_uint" | "to_ulong" | "to_uint64" | "value", 0) => {
                        (type_cast(sv_scalar_type(&wide), b), wide)
                    }
                    ("to_int" | "to_long" | "to_int64", 0) => {
                        let t = Ty::Int {
                            bits: 64,
                            signed: true,
                            ch: false,
                        };
                        (type_cast(sv_scalar_type(&t), b), t)
                    }
                    ("to_bool", 0) => (bin(BinaryOp::Neq, b, int(0)), Ty::Bool),
                    ("to_double", 0) => (
                        type_cast(real_t(crate::ast::types::RealType::Real), b),
                        Ty::Real { single: false },
                    ),
                    ("and_reduce", 0) => (unary(UnaryOp::BitAnd, b), Ty::Bool),
                    ("or_reduce", 0) => (unary(UnaryOp::BitOr, b), Ty::Bool),
                    ("xor_reduce", 0) => (unary(UnaryOp::BitXor, b), Ty::Bool),
                    ("nand_reduce", 0) => (unary(UnaryOp::BitNand, b), Ty::Bool),
                    ("nor_reduce", 0) => (unary(UnaryOp::BitNor, b), Ty::Bool),
                    ("xnor_reduce", 0) => (unary(UnaryOp::BitXnor, b), Ty::Bool),
                    ("length", 0) => (sys("$bits", vec![b]), Ty::int32()),
                    ("to_string", _) => (sys("$sformatf", vec![string("%b"), b]), Ty::Str),
                    _ => {
                        return self
                            .err(span, format!("'{}' on a SystemC value is not supported", m));
                    }
                })
            }
            Ty::Time => Ok(match m {
                "to_seconds" => (
                    bin(
                        BinaryOp::Div,
                        type_cast(real_t(crate::ast::types::RealType::Real), b),
                        real(1e12),
                    ),
                    Ty::Real { single: false },
                ),
                "to_double" | "value" => (b, Ty::Real { single: false }),
                "to_string" => (call_fn("scrt_time_str", vec![b]), Ty::Str),
                _ => return self.err(span, format!("'{}' on sc_time is not supported", m)),
            }),
            Ty::Str => Ok(match m {
                "c_str" | "data" | "str" => (b, Ty::Str),
                "length" | "size" => (method(b, "len", vec![]), Ty::int32()),
                "empty" => (
                    bin(BinaryOp::Eq, method(b, "len", vec![]), int(0)),
                    Ty::Bool,
                ),
                _ => return self.err(span, format!("'{}' on std::string is not supported", m)),
            }),
            Ty::Queue(elem) => Ok(match (m, a.len()) {
                ("size", 0) => (method(b, "size", vec![]), Ty::int32()),
                ("empty", 0) => (
                    bin(BinaryOp::Eq, method(b, "size", vec![]), int(0)),
                    Ty::Bool,
                ),
                ("back", 0) => (index(b, ex(ExprKind::Dollar)), (**elem).clone()),
                ("front", 0) => (index(b, int(0)), (**elem).clone()),
                ("at", 1) => (index(b, arg(0)), (**elem).clone()),
                _ => {
                    return self.err(
                        span,
                        format!("'{}' on std::vector is supported only as a statement", m),
                    );
                }
            }),
            Ty::Array(_, n) if m == "size" => Ok((n.clone(), Ty::int32())),
            Ty::Ptr { .. } => self.err(span, "methods on a data pointer are not supported"),
            // `os.str()`: what an output string stream holds.
            Ty::OStream if m == "str" && a.is_empty() => Ok((b, Ty::Str)),
            Ty::Class(c) | Ty::Handle(c) if self.user_class(&bt).is_some() => {
                let xs: Vec<Expression> = a.iter().map(|x| x.0.clone()).collect();
                self.object_call(b, c, m, xs, span)
            }
            Ty::Class(c) | Ty::Handle(c) => {
                let sv_m = if m == "release" { "release_" } else { m };
                let ret = self.prog.class_method_ret(c, m);
                let mut xs = Vec::new();
                for (e, x) in args.iter().zip(&a) {
                    // A data pointer argument may be an array (it decays).
                    let decays = matches!(m, "set_data_ptr" | "set_byte_enable_ptr")
                        && e.as_name()
                            .and_then(|q| self.lookup(q.last_name()))
                            .is_some_and(|sym| sym.kind == SymKind::BoxedArr);
                    xs.push(if decays {
                        self.ptr_arg(e, x)?
                    } else {
                        x.0.clone()
                    });
                }
                match ret {
                    Some(r) => Ok((method(b, sv_m, xs), r)),
                    None => self.err(span, format!("unknown method '{}'", m)),
                }
            }
            _ => self.err(span, format!("'{}' is not supported on this value", m)),
        }
    }

    /// The flag a process's wait wrapper sets when `sig` changed (for
    /// `posedge()`/`negedge()`/`event()`).
    fn edge_flag(&mut self, sig: &str, span: ScSpan) -> R<String> {
        let Some(p) = self.f.proc else {
            return self.err(
                span,
                "posedge()/negedge()/event() is supported only in a process body",
            );
        };
        let in_sens = self.m.procs[p].sens.iter().any(|t| t.name == sig);
        if !in_sens {
            return self.err(
                span,
                format!(
                    "'{}' must be in the process's sensitivity list to test its edge",
                    sig
                ),
            );
        }
        self.m.edge_flags.insert((p, sig.to_string()));
        Ok(edge_flag_name(p, sig))
    }

    // ---- statements ---------------------------------------------------------

    pub fn block(&mut self, stmts: &[sc::Stmt]) -> Vec<Statement> {
        self.f.scopes.push(BTreeMap::new());
        let mut out = Vec::new();
        for s in stmts {
            match self.stmt(s) {
                Ok(v) => out.extend(v),
                Err(e) => self.record(e),
            }
        }
        self.f.scopes.pop();
        out
    }

    fn take_pre(&mut self, mut v: Vec<Statement>) -> Vec<Statement> {
        let mut out = std::mem::take(&mut self.pre);
        out.append(&mut v);
        out
    }

    fn sub(&mut self, s: &sc::Stmt) -> R<Statement> {
        self.f.scopes.push(BTreeMap::new());
        let r = self.stmt(s);
        self.f.scopes.pop();
        let v = r?;
        Ok(if v.len() == 1 {
            v.into_iter().next().expect("one")
        } else {
            block(v)
        })
    }

    pub fn stmt(&mut self, s: &sc::Stmt) -> R<Vec<Statement>> {
        use sc::Stmt as S;
        let out = match s {
            S::Block(b) => vec![block(self.block(&b.stmts))],
            S::Empty(_) | S::Typedef(_) | S::Using(_) | S::StaticAssert(_) => Vec::new(),
            S::Decl(v) => self.local_decl(v)?,
            S::Expr(e) => self.expr_stmt(e)?,
            S::If {
                init,
                cond: c,
                then_branch,
                else_branch,
                ..
            } => {
                let mut v = Vec::new();
                if let Some(i) = init {
                    v.extend(self.stmt(i)?);
                }
                // What the condition needs computed first (a blocking call's
                // result) comes before the `if`, not inside a branch.
                let c = self.condition(c)?;
                v.append(&mut self.pre);
                let t = self.sub(then_branch)?;
                let f = match else_branch {
                    Some(e) => Some(self.sub(e)?),
                    None => None,
                };
                v.push(if_(c, t, f));
                v
            }
            S::While { cond: c, body, .. } => {
                let c = self.condition(c)?;
                let pre = std::mem::take(&mut self.pre);
                if pre.is_empty() {
                    vec![while_(c, self.sub(body)?)]
                } else {
                    // A condition with statements to run first is tested at
                    // the top of each iteration.
                    let mut b = pre;
                    b.push(if_(unary(UnaryOp::LogNot, paren(c)), st(StatementKind::Break), None));
                    b.push(self.sub(body)?);
                    vec![while_(sized(1, 1), block(b))]
                }
            }
            S::DoWhile { body, cond: c, .. } => {
                let b = self.sub(body)?;
                let (c, _) = self.expr(c)?;
                let pre = std::mem::take(&mut self.pre);
                if pre.is_empty() {
                    vec![do_while(b, c)]
                } else {
                    let mut bb = vec![b];
                    bb.extend(pre);
                    vec![do_while(block(bb), c)]
                }
            }
            S::For {
                init,
                cond: c,
                step,
                body,
                ..
            } => {
                self.f.scopes.push(BTreeMap::new());
                let r = (|| -> R<Vec<Statement>> {
                    let mut v = Vec::new();
                    if let Some(i) = init {
                        v.extend(self.stmt(i)?);
                    }
                    let mut c = match c {
                        Some(c) => Some(self.condition(c)?),
                        None => None,
                    };
                    // A condition with statements to run first is tested at
                    // the top of the body.
                    let cpre = std::mem::take(&mut self.pre);
                    let steps = match step {
                        Some(e) => self.step_exprs(e)?,
                        None => Vec::new(),
                    };
                    let mut b = self.sub(body)?;
                    if !cpre.is_empty() {
                        let mut bb = cpre;
                        if let Some(cc) = c.take() {
                            bb.push(if_(unary(UnaryOp::LogNot, paren(cc)), st(StatementKind::Break), None));
                        }
                        bb.push(b);
                        b = block(bb);
                    }
                    v.push(st(StatementKind::For {
                        init: Vec::new(),
                        condition: c,
                        step: steps,
                        body: Box::new(b),
                    }));
                    Ok(v)
                })();
                self.f.scopes.pop();
                vec![block(r?)]
            }
            S::RangeFor {
                decl,
                range: rng,
                body,
                ..
            } => {
                // for (T& x : v) → foreach over the queue, `x` aliasing v[i].
                let (r, rt) = self.expr(rng)?;
                let (Ty::Queue(elem) | Ty::Array(elem, _)) = rt else {
                    return self.err(
                        decl.span,
                        "range-for is supported over std::vector and arrays",
                    );
                };
                let Some(name) = &decl.name else {
                    return self.err(decl.span, "range-for needs a variable");
                };
                let idx = self.fresh_local("__sc_i");
                self.f.decls.push(var_decl(
                    atom_t(crate::ast::types::IntegerAtomType::Int, false),
                    &idx,
                    None,
                ));
                // The loop variable is a copy of the element, written back
                // after each iteration when bound by reference.
                let alias = self.fresh_local(&name.name);
                let (dt, dims) = sv_type(&elem);
                self.f.decls.push(st(StatementKind::VarDecl {
                    data_type: dt,
                    lifetime: None,
                    declarators: vec![var_declarator(&alias, dims, None)],
                }));
                self.f.scopes.push(BTreeMap::new());
                self.f.scopes.last_mut().expect("scope").insert(
                    name.name.clone(),
                    Sym {
                        kind: SymKind::Var,
                        ty: (*elem).clone(),
                        sv: alias.clone(),
                    },
                );
                let b = self.sub(body);
                self.f.scopes.pop();
                let b = b?;
                let by_ref = decl.ty.ptr_ops.contains(&sc::PtrOp::LRef);
                let mut body_stmts = vec![assign(ident(&alias), index(r.clone(), ident(&idx))), b];
                if by_ref {
                    body_stmts.push(assign(index(r.clone(), ident(&idx)), ident(&alias)));
                }
                vec![
                    assign(ident(&idx), int(0)),
                    while_(
                        bin(BinaryOp::Lt, ident(&idx), sys("$size", vec![r])),
                        block({
                            let mut v = body_stmts;
                            v.push(expr_stmt(unary(UnaryOp::PostIncr, ident(&idx))));
                            v
                        }),
                    ),
                ]
            }
            S::Switch {
                init,
                cond: c,
                arms,
                ..
            } => {
                let mut v = Vec::new();
                if let Some(i) = init {
                    v.extend(self.stmt(i)?);
                }
                let c = self.condition(c)?;
                v.push(self.switch(c, arms)?);
                v
            }
            S::Break(sp_) => {
                let _ = sp_;
                vec![st(StatementKind::Break)]
            }
            S::Continue(_) => vec![st(StatementKind::Continue)],
            S::Return(v, span) => {
                // `return n;` in sc_main ends the program with status n.
                if self.m.tb && self.f.ret.is_none() {
                    let code = match v {
                        Some(e) => self.expr(e)?.0,
                        None => int(0),
                    };
                    return Ok(vec![
                        expr_stmt(call_fn("__sc_destroy", vec![])),
                        expr_stmt(sys("$__sc_exit", vec![code])),
                    ]);
                }
                let _ = span;
                let mut out = match v {
                    Some(e) if !matches!(self.f.ret, Some(Ty::Void) | None) => {
                        let (x, t) = self.expr(e)?;
                        // An object returned by value is a copy of it.
                        let x = if self.f.ret_copy && matches!(t, Ty::Class(_)) {
                            method(x, "__sc_copy", vec![])
                        } else {
                            x
                        };
                        match self.f.ret_var.clone() {
                            Some(rv) => vec![assign(ident(&rv), x)],
                            None => {
                                let mut o = self.f.epilogue.clone();
                                o.push(ret(Some(x)));
                                return Ok(self.take_pre(o));
                            }
                        }
                    }
                    Some(e) => self.expr_stmt(e)?,
                    None => Vec::new(),
                };
                out.extend(self.f.epilogue.clone());
                out.push(ret(None));
                out
            }
            S::Class(c) => {
                return self.err(c.span, "local classes are not supported in simulation");
            }
            S::Enum(e) => {
                return self.err(
                    e.span,
                    "local enums are not supported in simulation; declare it at namespace scope",
                );
            }
            S::Try { span, .. } => {
                return self.err(*span, "exceptions are not supported in simulation");
            }
            S::Labeled { span, .. } => {
                return self.err(*span, "labels are not supported in simulation");
            }
            S::ScFork { span, .. } => {
                return self.err(*span, "SC_FORK/SC_JOIN is not supported in simulation yet");
            }
            S::ScProcess { span, .. }
            | S::Sensitive { span, .. }
            | S::DontInitialize(span)
            | S::ResetSignalIs { span, .. } => {
                return self.err(
                    *span,
                    "process registration is supported only in the module constructor body",
                );
            }
        };
        Ok(self.take_pre(out))
    }

    fn condition(&mut self, c: &sc::Condition) -> R<Expression> {
        match c {
            sc::Condition::Expr(e) => Ok(self.expr(e)?.0),
            sc::Condition::Decl(v) => {
                let stmts = self.local_decl(v)?;
                self.pre.extend(stmts);
                let d = &v.declarators[0];
                let sym = self.lookup(&d.name.name).expect("just declared");
                Ok(self.sym_read(&sym))
            }
        }
    }

    fn step_exprs(&mut self, e: &sc::Expr) -> R<Vec<Expression>> {
        let mut parts = Vec::new();
        flatten_comma(e, &mut parts);
        let mut out = Vec::new();
        for p in parts {
            out.push(match &p.kind {
                sc::ExprKind::Assign { op, lhs, rhs } => {
                    let (l, _) = self.expr(lhs)?;
                    let (r, _) = self.expr(rhs)?;
                    let r = match sv_assignop(*op) {
                        Some(b) => bin(b, l.clone(), r),
                        None => r,
                    };
                    ex(ExprKind::AssignExpr {
                        lvalue: Box::new(l),
                        rvalue: Box::new(r),
                    })
                }
                _ => self.expr(p)?.0,
            });
        }
        Ok(out)
    }

    /// `switch` with C fall-through: an arm that does not end in `break`
    /// (or `return`/`continue`) runs the following arms' bodies too.
    fn switch(&mut self, c: Expression, arms: &[sc::SwitchArm]) -> R<Statement> {
        let mut bodies: Vec<(Vec<Statement>, bool)> = Vec::new();
        for arm in arms {
            let mut stmts = arm.body.as_slice();
            let mut terminated = false;
            if let Some(last) = stmts.last() {
                match last {
                    sc::Stmt::Break(_) => {
                        stmts = &stmts[..stmts.len() - 1];
                        terminated = true;
                    }
                    sc::Stmt::Return(..) | sc::Stmt::Continue(_) => terminated = true,
                    _ => {}
                }
            }
            for s in stmts {
                if contains_switch_break(s) {
                    return self.err(
                        stmt_span(s),
                        "'break' out of a switch from inside a nested statement is not supported",
                    );
                }
            }
            let lowered = self.block(stmts);
            bodies.push((lowered, terminated));
        }
        let mut items = Vec::new();
        for (i, arm) in arms.iter().enumerate() {
            let mut body = Vec::new();
            for (b, term) in &bodies[i..] {
                body.extend(b.iter().cloned());
                if *term {
                    break;
                }
            }
            let mut patterns = Vec::new();
            let mut is_default = false;
            for l in &arm.labels {
                match l {
                    Some(e) => patterns.push(self.expr(e)?.0),
                    None => is_default = true,
                }
            }
            if is_default && !patterns.is_empty() {
                // `case X: default:` — the default item covers it.
                patterns.clear();
            }
            items.push(CaseItem {
                patterns,
                is_default,
                stmt: block(body),
                span: sp(),
                pattern: None,
                guard: None,
            });
        }
        Ok(st(StatementKind::Case {
            unique_priority: None,
            kind: CaseKind::Case,
            expr: c,
            items,
        }))
    }

    /// A local declaration: hoisted declaration plus initializing statements.
    pub fn local_decl(&mut self, v: &sc::VarDecl) -> R<Vec<Statement>> {
        let mut out = Vec::new();
        for d in &v.declarators {
            let ty = self.decl_ty(&v.ty, d)?;
            if d.name.name.is_empty() {
                continue;
            }
            // A static local keeps its value across calls: a module variable
            // initialized once.
            if v.specifiers.is_static {
                let init = match &d.init {
                    Some(sc::Initializer::Assign(e)) => Some(self.expr(e)?.0),
                    Some(sc::Initializer::Paren(a) | sc::Initializer::Brace(a)) if a.len() == 1 => {
                        Some(self.expr(&a[0])?.0)
                    }
                    _ => None,
                };
                self.tmp += 1;
                let sv = format!("__sc_static{}_{}", self.tmp, d.name.name);
                let (dt, dims) = sv_type(&ty);
                self.m.extra_items.push(data_decl(dt, &sv, dims, init));
                self.f.scopes.last_mut().expect("scope").insert(
                    d.name.name.clone(),
                    Sym {
                        kind: SymKind::Var,
                        ty,
                        sv,
                    },
                );
                continue;
            }
            // A library channel object.
            if matches!(&ty, Ty::Class(c) if matches!(c.as_str(), "scrt_mutex" | "scrt_semaphore" | "scrt_event_queue"))
            {
                let args: Vec<sc::Expr> = match &d.init {
                    Some(sc::Initializer::Paren(a) | sc::Initializer::Brace(a)) => a.clone(),
                    _ => Vec::new(),
                };
                let init = self.lib_object_new(&ty, &args)?.expect("library object");
                let sv = self.declare_local(&d.name.name, ty.clone(), SymKind::Var, None);
                out.push(assign(ident(&sv), init));
                continue;
            }
            // A user-class object: allocated where declared and built by
            // its constructor, a copy, or a temporary (a reference names
            // the object it is bound to).
            if let Some(cls) = self.user_class(&ty).filter(|_| matches!(ty, Ty::Class(_))) {
                let is_ref = d
                    .ptr_ops
                    .iter()
                    .chain(v.ty.ptr_ops.iter())
                    .any(|o| matches!(o, sc::PtrOp::LRef | sc::PtrOp::RRef));
                let sv = self.declare_local(&d.name.name, ty.clone(), SymKind::Var, None);
                let init_args: Vec<sc::Expr> = match &d.init {
                    Some(sc::Initializer::Paren(a) | sc::Initializer::Brace(a)) => a.clone(),
                    Some(sc::Initializer::Assign(e)) => vec![e.clone()],
                    None => Vec::new(),
                };
                if is_ref {
                    if let [e] = init_args.as_slice() {
                        let (x, _) = self.expr(e)?;
                        out.push(assign(ident(&sv), x));
                    }
                    continue;
                }
                // A temporary (`T x = T(1, 2);`) is the object itself.
                if let [e] = init_args.as_slice()
                    && let sc::ExprKind::Call { callee, .. } = &e.kind
                    && callee
                        .as_name()
                        .is_some_and(|q| super::classes::class_sv(q.last_name()) == cls)
                {
                    let (x, _) = self.expr(e)?;
                    out.push(assign(ident(&sv), x));
                    continue;
                }
                out.push(assign(ident(&sv), new_obj(None)));
                out.extend(super::classes::construct_into(
                    self,
                    ident(&sv),
                    &cls,
                    &init_args,
                    d.span,
                )?);
                continue;
            }
            if let Ty::Array(elem, _) = &ty
                && let Some(cls) = self.user_class(elem)
                && matches!(**elem, Ty::Class(_))
            {
                // An array of objects: each element default-constructed.
                let sv = self.declare_local(&d.name.name, ty.clone(), SymKind::Var, None);
                let k = self
                    .prog
                    .user_classes
                    .borrow()
                    .get(&cls)
                    .and_then(|s| s.ctor(0));
                let Some(k) = k else {
                    return self.err(d.span, "an array of objects needs a default constructor");
                };
                out.push(st(StatementKind::Foreach {
                    array: ident(&sv),
                    vars: vec![Some(id("__sc_i"))],
                    body: Box::new(assign(
                        index(ident(&sv), ident("__sc_i")),
                        call(member(ident(&cls), &format!("__sc_make{}", k)), Vec::new()),
                    )),
                }));
                continue;
            }
            let boxed = self.prog.address_taken(&d.name.name, self.tu);
            let kind = match (&ty, boxed) {
                (Ty::Array(..), true) => SymKind::BoxedArr,
                (_, true) if ty.is_scalar_bits() || matches!(ty, Ty::Bool) => SymKind::Boxed,
                _ => SymKind::Var,
            };
            // Objects of class type are created where declared.
            let init_new = match (&kind, &ty) {
                (SymKind::Boxed, _) => Some(new_obj(None)),
                (SymKind::BoxedArr, Ty::Array(_, n)) => Some(new_obj(Some(vec![n.clone()]))),
                (SymKind::Var, Ty::Class(_))
                    if d.init.is_none() && v.ty.name().is_some() && d.ptr_ops.is_empty() =>
                {
                    Some(new_obj(None))
                }
                _ => None,
            };
            let is_obj_new = init_new.is_some();
            let sv = self.declare_local(&d.name.name, ty.clone(), kind.clone(), None);
            if is_obj_new {
                out.push(assign(ident(&sv), init_new.expect("checked")));
            }
            let target = match kind {
                SymKind::Boxed => member(ident(&sv), "v"),
                _ => ident(&sv),
            };
            match &d.init {
                None => {}
                Some(_) if matches!(ty, Ty::Class(_)) => match d.init.as_ref() {
                    Some(sc::Initializer::Assign(e))
                        if matches!(e.kind, sc::ExprKind::New { .. }) =>
                    {
                        out.push(assign(target, new_obj(None)));
                    }
                    Some(sc::Initializer::Assign(e)) => {
                        let (x, _) = self.expr(e)?;
                        out.push(assign(target, x));
                    }
                    _ => out.push(assign(target, new_obj(None))),
                },
                Some(sc::Initializer::Assign(e)) => {
                    if let sc::ExprKind::Call { callee, args } = &e.kind
                        && callee
                            .as_name()
                            .is_some_and(|q| short_path(q) == "sc_create_vcd_trace_file")
                    {
                        let (x, _) = self.call(callee, args, e.span)?;
                        out.push(expr_stmt(x));
                        let sc_ = self.f.scopes.last_mut().expect("scope");
                        if let Some(s) = sc_.get_mut(&d.name.name) {
                            s.kind = SymKind::TraceFile;
                        }
                        continue;
                    }
                    let x = self.expr_for(e, &ty)?;
                    out.push(assign(target, x));
                }
                Some(sc::Initializer::Paren(args)) | Some(sc::Initializer::Brace(args)) => {
                    match args.as_slice() {
                        [] => {}
                        [a] => {
                            let x = self.expr_for(a, &ty)?;
                            out.push(assign(target, x));
                        }
                        [v_, u] if matches!(ty, Ty::Time) => {
                            let x = self.time_value(v_, u, d.span)?;
                            out.push(assign(target, x));
                        }
                        _ => return self.err(d.span, "this initializer is not supported"),
                    }
                }
            }
        }
        Ok(out)
    }

    /// A statement-level expression: assignments, kernel calls, stream
    /// output and the statement-only object methods.
    pub fn expr_stmt(&mut self, e: &sc::Expr) -> R<Vec<Statement>> {
        use sc::ExprKind as K;
        let span = e.span;
        // `os << …` into a string stream (an `operator<<`'s ostream, an
        // ostringstream): the text is appended to it.
        if let K::Binary {
            op: sc::BinaryOp::Shl,
            ..
        } = &e.kind
            && let Some(sym) = leftmost_shl(e)
                .as_name()
                .and_then(|q| self.lookup(q.last_name()))
            && matches!(sym.ty, Ty::OStream)
        {
            return self.stream_out(e, Some(sym.sv.clone()));
        }
        match &e.kind {
            K::Assign { op, lhs, rhs } => return self.assign_stmt(*op, lhs, rhs, span),
            K::Binary {
                op: sc::BinaryOp::Shl,
                ..
            } if stream_base(e) => return self.cout(e),
            K::Binary {
                op: sc::BinaryOp::Comma,
                lhs,
                rhs,
            } => {
                let mut v = self.expr_stmt(lhs)?;
                v.extend(self.expr_stmt(rhs)?);
                return Ok(v);
            }
            K::Postfix { operand, .. } | K::Unary { operand, .. }
                if matches!(e.kind, K::Postfix { .. }) || is_incdec(&e.kind) =>
            {
                let inc = match &e.kind {
                    K::Postfix { op, .. } => *op == sc::PostfixOp::Inc,
                    K::Unary { op, .. } => *op == sc::UnaryOp::PreInc,
                    _ => true,
                };
                let one = sc::Expr {
                    kind: K::IntLit {
                        text: "1".into(),
                        value: Some(1),
                    },
                    span,
                };
                return self.assign_stmt(
                    if inc {
                        sc::AssignOp::Add
                    } else {
                        sc::AssignOp::Sub
                    },
                    operand,
                    &one,
                    span,
                );
            }
            K::Cast { expr, .. } => {
                // `(void)x;`
                if matches!(expr.kind, K::Call { .. }) {
                    return self.expr_stmt(expr);
                }
                return Ok(Vec::new());
            }
            K::Delete { .. } => return Ok(Vec::new()),
            K::Paren(inner) => return self.expr_stmt(inner),
            K::Call { callee, args } => {
                if let Some(v) = self.kernel_call(callee, args, span)? {
                    return Ok(v);
                }
            }
            _ => {}
        }
        let (x, _) = self.expr(e)?;
        match x.kind {
            ExprKind::Call { .. } | ExprKind::SystemCall { .. } => Ok(vec![expr_stmt(x)]),
            // A value computed for nothing (C++ allows it).
            _ => Ok(Vec::new()),
        }
    }

    fn assign_stmt(
        &mut self,
        op: sc::AssignOp,
        lhs: &sc::Expr,
        rhs: &sc::Expr,
        span: ScSpan,
    ) -> R<Vec<Statement>> {
        use sc::ExprKind as K;
        // `a = b = v;`: the inner assignment, then the outer from its target.
        if let K::Assign {
            op: inner_op,
            lhs: inner_lhs,
            rhs: inner_rhs,
        } = &rhs.kind
        {
            let mut v = self.assign_stmt(*inner_op, inner_lhs, inner_rhs, span)?;
            v.extend(self.assign_stmt(op, lhs, inner_lhs, span)?);
            return Ok(v);
        }
        // `p = new T[n]`: a data pointer to a new array.
        if let K::New {
            array_size: Some(_),
            ..
        } = &rhs.kind
        {
            let (r, _) = self.expr(rhs)?;
            return self.store(lhs, r, span);
        }
        // `x = new T` for a class handle.
        if let K::New { .. } = &rhs.kind {
            let (l, lt) = self.expr(lhs)?;
            if self.user_class(&lt).is_some() {
                let (r, _) = self.expr(rhs)?;
                return Ok(vec![assign(l, r)]);
            }
            if matches!(lt, Ty::Class(_) | Ty::Handle(_)) {
                return Ok(vec![assign(l, new_obj(None))]);
            }
            return self.err(span, "'new' of this type is not supported");
        }
        // An object (not a signal of one): C++ copies into it, or applies
        // the class's compound operator.
        let lhs_signal = lhs
            .as_name()
            .and_then(|q| self.lookup(q.last_name()))
            .is_some_and(|s| s.is_signal_like());
        if !lhs_signal {
            let saved = self.pre.len();
            let peek = self.expr(lhs);
            if let Ok((l, Ty::Class(c))) = peek
                && self.prog.user_classes.borrow().contains_key(&c)
            {
                let (r, _) = self.expr(rhs)?;
                if op == sc::AssignOp::Assign {
                    return Ok(vec![expr_stmt(method(l, "__sc_set", vec![r]))]);
                }
                let spelling = format!("{}=", super::classes::op_spelling(compound_binop(op)));
                let m = self
                    .prog
                    .user_classes
                    .borrow()
                    .get(&c)
                    .and_then(|s| s.method(&format!("operator{}", spelling), 1).cloned());
                return match m {
                    Some(m) => Ok(vec![expr_stmt(method(l, &m.sv, vec![r]))]),
                    None => self.err(span, format!("this class has no operator{}", spelling)),
                };
            }
            self.pre.truncate(saved);
        }
        let (mut r, _) = if let K::StringLit { .. } = &rhs.kind {
            let (_, lt) = self.expr(lhs)?;
            (self.expr_for(rhs, &lt)?, lt)
        } else {
            self.expr(rhs)?
        };
        if let Some(b) = sv_assignop(op) {
            let (cur, ct) = self.expr(lhs)?;
            r = bin(signed_shift(b, &ct), cur, paren(r));
        }
        self.store(lhs, r, span)
    }

    /// Store `value` into the C++ lvalue `lhs`.
    pub fn store(&mut self, lhs: &sc::Expr, value: Expression, span: ScSpan) -> R<Vec<Statement>> {
        use sc::ExprKind as K;
        match &lhs.kind {
            K::Name(q) if q.segments.len() == 1 => {
                let Some(sym) = self.lookup(q.last_name()) else {
                    return self.err(span, format!("unknown name '{}'", q.last_name()));
                };
                Ok(vec![self.store_sym(&sym, None, value, span)?])
            }
            K::Index { base, index: i } => {
                if let Some(q) = base.as_name()
                    && let Some(sym) = self.lookup(q.last_name())
                {
                    if sym.kind == SymKind::BoxedArr {
                        let (iv, _) = self.expr(i)?;
                        return Ok(vec![assign(index(member(ident(&sym.sv), "a"), iv), value)]);
                    }
                    if sym.is_signal_like() {
                        let (iv, _) = self.expr(i)?;
                        return Ok(vec![self.store_sym(&sym, Some(iv), value, span)?]);
                    }
                }
                let (b, bt) = self.expr(base)?;
                let (iv, _) = self.expr(i)?;
                match bt {
                    Ty::Ptr { elem } => Ok(vec![expr_stmt(ptr_set(
                        b,
                        ptr_offset(iv, elem),
                        elem,
                        value,
                    ))]),
                    _ => Ok(vec![assign(index(b, iv), value)]),
                }
            }
            K::Unary {
                op: sc::UnaryOp::Deref,
                operand,
            } => {
                let (p, t) = self.expr(operand)?;
                match t {
                    Ty::Ptr { elem } => Ok(vec![expr_stmt(ptr_set(p, int(0), elem, value))]),
                    _ => self.err(span, "storing through this pointer is not supported"),
                }
            }
            K::Paren(inner) => {
                if let K::Binary {
                    op: sc::BinaryOp::Comma,
                    ..
                } = &inner.kind
                {
                    let (c, _) = self.concat(inner)?;
                    return Ok(vec![assign(c, value)]);
                }
                self.store(inner, value, span)
            }
            K::Call { callee, args } => {
                // `x.range(h, l) = v`, `x.bit(i) = v`, `s.write(v)` handled
                // as statements elsewhere.
                if let K::Member { base, name, .. } = &callee.kind {
                    let (b, _) = self.expr(base)?;
                    match (name.ident.name.as_str(), args.as_slice()) {
                        ("range", [h, l]) => {
                            let (h, _) = self.expr(h)?;
                            let (l, _) = self.expr(l)?;
                            return Ok(vec![assign(range(b, h, l), value)]);
                        }
                        ("bit", [i]) => {
                            let (i, _) = self.expr(i)?;
                            return Ok(vec![assign(index(b, i), value)]);
                        }
                        _ => {}
                    }
                }
                self.err(span, "assignment to this expression is not supported")
            }
            _ => {
                let (l, _) = self.expr(lhs)?;
                Ok(vec![assign(l, value)])
            }
        }
    }

    /// Store into a symbol (optionally an element of it): signals and output
    /// ports update in the update phase — a nonblocking assignment; in the
    /// sc_main testbench, at the next sc_start.
    fn store_sym(
        &mut self,
        sym: &Sym,
        elem: Option<Expression>,
        value: Expression,
        span: ScSpan,
    ) -> R<Statement> {
        let target = |base: Expression| match &elem {
            Some(i) => index(base, i.clone()),
            None => base,
        };
        match sym.kind {
            SymKind::Signal | SymKind::OutPort | SymKind::InOutPort | SymKind::Clock => {
                let resolved = self.m.resolved.get(&sym.sv).copied();
                if resolved.is_some() && elem.is_some() {
                    return self.err(span, "an element of a resolved signal cannot be written");
                }
                if self.m.tb && self.f.proc.is_none() {
                    let mut elem_ty = match (&sym.ty, &elem) {
                        (Ty::Array(e, _), Some(_)) => (**e).clone(),
                        (t, _) => t.clone(),
                    };
                    // sc_main drives a resolved net through its own driver.
                    // sc_main writes an object signal a copy.
                    let value = if matches!(elem_ty, Ty::Class(_)) && self.user_class(&elem_ty).is_some() {
                        method(value, "__sc_copy", vec![])
                    } else {
                        value
                    };
                    let (target_sig, value) = match resolved {
                        Some(w) => {
                            elem_ty = Ty::Vec4 {
                                w: Width::known(w + 1),
                            };
                            (
                                self.driver_var(&sym.sv, Writer::Outside),
                                concat(vec![sized(1, 1), size_cast(w, paren(value))]),
                            )
                        }
                        None => (sym.sv.clone(), value),
                    };
                    // Queued (value, element index) per write site, applied
                    // in order at the next sc_start.
                    let slot = self.module_var("__sc_pw", &Ty::Queue(Box::new(elem_ty)));
                    let idx = format!("{}_i", slot);
                    self.m.extra_items.push(data_decl(
                        atom_t(crate::ast::types::IntegerAtomType::Int, false),
                        &idx,
                        vec![crate::ast::types::UnpackedDimension::Queue {
                            max_size: None,
                            span: sp(),
                        }],
                        None,
                    ));
                    self.m
                        .pending
                        .push((target_sig, slot.clone(), elem.is_some()));
                    return Ok(block(vec![
                        expr_stmt(method(ident(&slot), "push_back", vec![value])),
                        expr_stmt(method(
                            ident(&idx),
                            "push_back",
                            vec![elem.unwrap_or_else(|| int(0))],
                        )),
                    ]));
                }
                if let Some(w) = resolved {
                    return Ok(self.resolved_write(&sym.sv, w, value));
                }
                // A signal of objects takes a copy, and changes only when
                // the class's operator== says the value differs (§6.4.4).
                let elem_ty = match (&sym.ty, &elem) {
                    (Ty::Array(e, _), Some(_)) => (**e).clone(),
                    (t, _) => t.clone(),
                };
                if let Some(cls) = self.user_class(&elem_ty).filter(|_| matches!(elem_ty, Ty::Class(_))) {
                    let t = self.temp(&elem_ty);
                    let cur = target(ident(&sym.sv));
                    let changed = match super::classes::object_op(self, &cls, "==", cur.clone(), ident(&t)) {
                        Some((eq, _)) => super::classes::not(eq),
                        None => sized(1, 1),
                    };
                    return Ok(block(vec![
                        assign(ident(&t), value),
                        if_(
                            changed,
                            nba(cur, method(ident(&t), "__sc_copy", vec![])),
                            None,
                        ),
                    ]));
                }
                let w = nba(target(ident(&sym.sv)), value);
                // §6.4.4 SC_ONE_WRITER: a second process writing the signal is
                // an error at that write (E115), and the write does not happen.
                let w = if self.m.one_writer.contains(&sym.sv) {
                    let pid = match self.writer() {
                        Some(Writer::Process(p)) => int(p as i64 + 1),
                        Some(Writer::Outside) => int(0),
                        None => {
                            self.m.needs_pid = true;
                            call_fn("__sc_pid", vec![])
                        }
                    };
                    if_(
                        call_fn(
                            "__sc_one_writer",
                            vec![
                                ident(&one_writer_var(&sym.sv)),
                                pid,
                                self.obj_name(Some(&sym.sv)),
                            ],
                        ),
                        w,
                        None,
                    )
                } else {
                    w
                };
                if self.m.buffers.contains(&sym.sv) {
                    // §6.9: an sc_buffer notifies on every write, changed or
                    // not; its write counter changes in the same update.
                    let n = buffer_counter(&sym.sv);
                    return Ok(block(vec![
                        w,
                        nba(ident(&n), bin(BinaryOp::Add, ident(&n), int(1))),
                    ]));
                }
                if let Some(n) = self.m.port_wcounters.get(&sym.sv).cloned() {
                    // A write through a port bound to an sc_buffer is a write
                    // of the buffer, counted beside the value.
                    return Ok(block(vec![
                        w,
                        nba(ident(&n), bin(BinaryOp::Add, ident(&n), int(1))),
                    ]));
                }
                Ok(w)
            }
            SymKind::InPort => self.err(span, "an input port cannot be written"),
            SymKind::Boxed => Ok(assign(target(member(ident(&sym.sv), "v")), value)),
            SymKind::Var => Ok(assign(target(ident(&sym.sv)), value)),
            SymKind::Const(_) => self.err(
                span,
                "a loop variable unrolled at elaboration cannot be written",
            ),
            _ => self.err(span, "assignment to this object is not supported"),
        }
    }

    /// Statement-only calls: the kernel (`wait`, `sc_start`, `sc_stop`),
    /// signal/FIFO/event/socket methods, `printf`, `SC_REPORT_*`.
    fn kernel_call(
        &mut self,
        callee: &sc::Expr,
        args: &[sc::Expr],
        span: ScSpan,
    ) -> R<Option<Vec<Statement>>> {
        use sc::ExprKind as K;
        if let K::Name(q) = &callee.kind {
            let path = short_path(q);
            match path.as_str() {
                "wait" => return Ok(Some(self.wait(args, span)?)),
                "sc_start" => return Ok(Some(self.sc_start(args, span)?)),
                "sc_stop" => {
                    let f = if self.m.tb {
                        "scrt_stop"
                    } else {
                        "scrt_stop_request"
                    };
                    return Ok(Some(vec![expr_stmt(call_fn(f, vec![]))]));
                }
                "printf" => {
                    let Some((fmt, rest)) = args.split_first() else {
                        return self.err(span, "printf needs a format");
                    };
                    let sc::ExprKind::StringLit { value, .. } = &fmt.kind else {
                        return self.err(span, "printf needs a literal format");
                    };
                    let mut a = vec![string(&printf_to_sv(value))];
                    for x in rest {
                        a.push(self.expr(x)?.0);
                    }
                    return Ok(Some(vec![expr_stmt(sys("$write", a))]));
                }
                "SC_REPORT_INFO" | "SC_REPORT_WARNING" | "SC_REPORT_ERROR" | "SC_REPORT_FATAL" => {
                    let [id_, msg] = args else {
                        return self.err(span, format!("{}(id, message) expected", path));
                    };
                    let (i, _) = self.expr(id_)?;
                    let (m, _) = self.expr(msg)?;
                    let (sev, fin) = match path.as_str() {
                        "SC_REPORT_INFO" => ("Info", false),
                        "SC_REPORT_WARNING" => ("Warning", false),
                        "SC_REPORT_ERROR" => ("Error", true),
                        _ => ("Fatal", true),
                    };
                    // SystemC 2.3's report format: warnings and errors name
                    // the C++ source line and, inside a process, the process.
                    let mut v = vec![expr_stmt(sys(
                        "$write",
                        vec![string(&format!("\n{}: %s: %s\n", sev)), i, m],
                    ))];
                    if sev != "Info" {
                        let loc = self.prog.results[self.tu].locate(span);
                        v.push(expr_stmt(sys(
                            "$write",
                            vec![string(&format!("In file: {}:{}\n", loc.file, loc.line))],
                        )));
                        if !self.m.tb {
                            v.push(expr_stmt(sys(
                                "$write",
                                vec![
                                    string("In process: %s @ %s\n"),
                                    call_fn(
                                        "scrt_name",
                                        vec![sys("$sformatf", vec![string("%m")])],
                                    ),
                                    call_fn("scrt_time_str", vec![sys("$time", vec![])]),
                                ],
                            )));
                        }
                    }
                    // An error report ends the run with exit status 1 (the
                    // kernel's exception); a fatal one aborts it (status 134,
                    // SIGABRT) after the kernel's own note.
                    if sev == "Fatal" {
                        v.push(expr_stmt(sys(
                            "$write",
                            vec![string("\nInfo: (I99) simulation aborted\n")],
                        )));
                        v.push(expr_stmt(sys("$__sc_exit", vec![int(134)])));
                    } else if fin {
                        v.push(expr_stmt(sys("$__sc_exit", vec![int(1)])));
                    }
                    return Ok(Some(v));
                }
                "sc_trace" => {
                    let Some(obj) = args.get(1) else {
                        return self.err(span, "sc_trace(file, object, name) expected");
                    };
                    let (x, _) = self.expr(obj)?;
                    return Ok(Some(vec![expr_stmt(sys("$dumpvars", vec![int(1), x]))]));
                }
                "sc_close_vcd_trace_file" => {
                    return Ok(Some(vec![expr_stmt(sys("$dumpflush", vec![]))]));
                }
                // §5.15.6: the channel's update() runs in the update phase,
                // once however often it was requested.
                "request_update" | "async_request_update" if args.is_empty() => {
                    self.m.uses_update = true;
                    return Ok(Some(vec![expr_stmt(call_fn("__sc_request_update", vec![]))]));
                }
                "next_trigger" => {
                    return self.err(span, "next_trigger() is not supported in simulation");
                }
                _ => return Ok(None),
            }
        }
        let K::Member { base, name, .. } = &callee.kind else {
            return Ok(None);
        };
        let m = name.ident.name.as_str();
        let sym = base
            .as_name()
            .filter(|q| q.segments.len() == 1)
            .and_then(|q| self.lookup(q.last_name()))
            .or_else(|| match &base.kind {
                K::Index { base: b, .. } => b.as_name().and_then(|q| self.lookup(q.last_name())),
                _ => None,
            });
        let Some(sym) = sym else {
            // Queue (std::vector) mutators on any expression.
            if matches!(
                m,
                "push_back" | "pop_back" | "clear" | "push_front" | "pop_front"
            ) {
                let (b, bt) = self.expr(base)?;
                if let Ty::Queue(_) = bt {
                    return Ok(Some(self.queue_op(b, m, args)?));
                }
            }
            return Ok(None);
        };
        match sym.kind {
            SymKind::Signal | SymKind::OutPort | SymKind::InOutPort | SymKind::Clock
                if m == "write" =>
            {
                let [v] = args else {
                    return self.err(span, "write(value) expected");
                };
                let elem_ty = match (&sym.ty, &base.kind) {
                    (Ty::Array(e, _), K::Index { .. }) => (**e).clone(),
                    (t, _) => t.clone(),
                };
                let x = self.expr_for(v, &elem_ty)?;
                let elem = match &base.kind {
                    K::Index { index: i, .. } => Some(self.expr(i)?.0),
                    _ => None,
                };
                Ok(Some(vec![self.store_sym(&sym, elem, x, span)?]))
            }
            SymKind::Fifo | SymKind::FifoOut if m == "write" => {
                let (x, xt) = self.expr(&args[0])?;
                // A FIFO of objects holds copies.
                let x = if matches!(xt, Ty::Class(_)) && self.user_class(&xt).is_some() {
                    method(x, "__sc_copy", vec![])
                } else {
                    x
                };
                self.f.is_task = true;
                Ok(Some(vec![expr_stmt(method(
                    ident(&sym.sv),
                    "put",
                    vec![x],
                ))]))
            }
            SymKind::Fifo | SymKind::FifoIn if m == "read" && args.len() == 1 => {
                let target = self.lvalue_ref(&args[0])?;
                self.f.is_task = true;
                Ok(Some(vec![expr_stmt(method(
                    ident(&sym.sv),
                    "get",
                    vec![target],
                ))]))
            }
            SymKind::Event => match m {
                "notify" => Ok(Some(self.notify(&sym.sv, args, span)?)),
                "cancel" => Ok(Some(Vec::new())),
                _ => self.err(span, format!("'{}' on sc_event is not supported", m)),
            },
            SymKind::InitSocket if m == "b_transport" => {
                let [t, d] = args else {
                    return self.err(span, "b_transport(trans, delay) expected");
                };
                let (t, _) = self.expr(&deref_inner(t).clone())?;
                let d = self.lvalue_ref(d)?;
                self.f.is_task = true;
                Ok(Some(vec![expr_stmt(method(
                    ident(&sym.sv),
                    "b_transport",
                    vec![t, d],
                ))]))
            }
            SymKind::Var if matches!(sym.ty, Ty::Queue(_)) => {
                Ok(Some(self.queue_op(ident(&sym.sv), m, args)?))
            }
            SymKind::TraceFile => Ok(Some(Vec::new())),
            _ => Ok(None),
        }
    }

    fn queue_op(&mut self, q: Expression, m: &str, args: &[sc::Expr]) -> R<Vec<Statement>> {
        let a: Vec<Expression> = self.args(args)?.into_iter().map(|x| x.0).collect();
        let call = match m {
            "push_back" => method(q, "push_back", a),
            "push_front" => method(q, "push_front", a),
            "pop_back" => method(q, "pop_back", vec![]),
            "pop_front" => method(q, "pop_front", vec![]),
            "clear" => method(q, "delete", vec![]),
            _ => unreachable!("caller filters"),
        };
        Ok(vec![expr_stmt(call)])
    }

    /// `e.notify()` (immediate), `e.notify(t)` / `e.notify(v, unit)` (timed;
    /// `SC_ZERO_TIME` is a delta notification).
    fn notify(&mut self, ev: &str, args: &[sc::Expr], span: ScSpan) -> R<Vec<Statement>> {
        let mirrors = self.m.ev_mirrors.get(ev).cloned().unwrap_or_default();
        let fire = |nb: bool| -> Statement {
            let mut v = vec![if nb { trigger_nb(ev) } else { trigger(ev) }];
            for m in &mirrors {
                v.push(st(StatementKind::EventTrigger {
                    nonblocking: nb,
                    name: id(ev),
                    target: Some(Box::new(m.clone())),
                    span: sp(),
                }));
            }
            if v.len() == 1 { v.pop().expect("one") } else { block(v) }
        };
        let (t, c) = match args {
            [] => return Ok(vec![fire(false)]),
            [t] => (
                self.expr(t)?.0,
                if self.zero_time(t) { Some(0) } else { self.const_eval(t) },
            ),
            [v, u] => (self.time_value(v, u, span)?, self.const_eval(v)),
            _ => return self.err(span, "notify() takes a time or (value, unit)"),
        };
        // §4.2.1.3: a delta notification triggers after the update phase.
        match c {
            Some(0) => return Ok(vec![fire(true)]),
            Some(_) => return Ok(vec![fork(JoinType::JoinNone, vec![delay(t, fire(false))])]),
            None => {}
        }
        Ok(vec![fork(
            JoinType::JoinNone,
            vec![if_(
                bin(BinaryOp::Eq, t.clone(), int(0)),
                fire(true),
                Some(delay(t, fire(false))),
            )],
        )])
    }

    /// `wait(...)` in a thread (IEEE 1666-2023 §5.2.17).
    fn wait(&mut self, args: &[sc::Expr], span: ScSpan) -> R<Vec<Statement>> {
        self.f.is_task = true;
        let proc = self.f.proc.map(|p| self.m.procs[p].clone());
        let reset_check = |proc: &Option<ProcCtx>| -> Vec<Statement> {
            match proc {
                Some(p) if p.reset.is_some() => vec![if_(
                    p.reset.clone().expect("checked"),
                    block(vec![
                        assign(ident(&reset_flag_name(p.index)), sized(1, 1)),
                        ret(None),
                    ]),
                    None,
                )],
                _ => Vec::new(),
            }
        };
        let mut out = match args {
            [] => {
                let Some(p) = &proc else {
                    return self.err(span, "wait() with no arguments is supported only in a process with static sensitivity");
                };
                let events: Vec<EventExpr> = match &p.clock {
                    Some((edge, clk)) => vec![event_expr(Some(*edge), clk.clone())],
                    None => p.sens.iter().map(SensTerm::event).collect(),
                };
                if events.is_empty() {
                    return self.err(
                        span,
                        "wait() in a process without static sensitivity never returns",
                    );
                }
                vec![at(events, null_stmt())]
            }
            [n] if self.expr_is_int(n) => {
                let Some(p) = &proc else {
                    return self.err(span, "wait(n) is supported only in a clocked thread");
                };
                let Some((edge, clk)) = &p.clock else {
                    return self.err(span, "wait(n) is supported only in a clocked thread");
                };
                let (n, _) = self.expr(n)?;
                let mut body = vec![at(vec![event_expr(Some(*edge), clk.clone())], null_stmt())];
                body.extend(reset_check(&proc));
                return Ok(vec![repeat(n, block(body))]);
            }
            [v, u] if time_unit(u).is_some() => {
                let t = self.time_value(v, u, span)?;
                self.wait_time(t, self.const_eval(v))
            }
            [v, u, e] if time_unit(u).is_some() => {
                let t = self.time_value(v, u, span)?;
                let on_events = self.event_wait(e)?;
                vec![
                    fork(JoinType::JoinAny, vec![delay(t, null_stmt()), on_events]),
                    disable_fork(),
                ]
            }
            [t, e] => {
                // wait(timeout, event): whichever comes first.
                let (t, _) = self.expr(t)?;
                let on_events = self.event_wait(e)?;
                vec![
                    fork(JoinType::JoinAny, vec![delay(t, null_stmt()), on_events]),
                    disable_fork(),
                ]
            }
            [x] if and_list(x).is_some() => vec![self.event_wait(x)?],
            [x] => {
                let (_, t) = self.peek_ty(x)?;
                if matches!(t, Ty::Time | Ty::Int { .. }) && !self.is_event_expr(x) {
                    let (d, _) = self.expr(x)?;
                    let c = if self.zero_time(x) { Some(0) } else { self.const_eval(x) };
                    self.wait_time(d, c)
                } else {
                    let ev = self.event_list(x)?;
                    vec![at(ev, null_stmt())]
                }
            }
            _ => return self.err(span, "this form of wait() is not supported"),
        };
        out.extend(reset_check(&proc));
        Ok(out)
    }

    /// Waiting on an event list: `e1 | e2` resumes on any of them; `e1 & e2`
    /// (§5.10.7) once each has been notified, in any order (a fork of one
    /// event control per event, joined).
    fn event_wait(&mut self, e: &sc::Expr) -> R<Statement> {
        if let Some(evs) = and_list(e) {
            let mut branches = Vec::new();
            for x in evs {
                branches.push(at(self.event_list(x)?, null_stmt()));
            }
            return Ok(fork(JoinType::Join, branches));
        }
        Ok(at(self.event_list(e)?, null_stmt()))
    }

    /// A wait for time `t` (`c` when constant): zero is the next delta
    /// cycle, after the update phase (§4.2.1.3), as `scrt_wait` does it.
    fn wait_time(&mut self, t: Expression, c: Option<i64>) -> Vec<Statement> {
        match c {
            Some(0) => vec![trigger_nb("scrt_delta_ev"), at(vec![event_expr(None, ident("scrt_delta_ev"))], null_stmt())],
            Some(_) => vec![delay(t, null_stmt())],
            None => vec![expr_stmt(call_fn("scrt_wait", vec![t]))],
        }
    }

    /// `SC_ZERO_TIME`.
    fn zero_time(&self, e: &sc::Expr) -> bool {
        matches!(&e.kind, sc::ExprKind::Name(q) if q.last_name() == "SC_ZERO_TIME")
    }

    fn expr_is_int(&self, e: &sc::Expr) -> bool {
        matches!(e.kind, sc::ExprKind::IntLit { .. })
            && self.f.proc.is_some_and(|p| self.m.procs[p].clock.is_some())
            || self.const_eval(e).is_some()
                && self.f.proc.is_some_and(|p| self.m.procs[p].clock.is_some())
    }

    fn is_event_expr(&self, e: &sc::Expr) -> bool {
        match &e.kind {
            sc::ExprKind::Name(q) => self
                .lookup(q.last_name())
                .is_some_and(|s| s.kind == SymKind::Event),
            sc::ExprKind::Call { callee, .. } => {
                matches!(&callee.kind, sc::ExprKind::Member { name, .. } if name.ident.name.ends_with("_event"))
            }
            sc::ExprKind::Binary {
                op: sc::BinaryOp::BitOr | sc::BinaryOp::BitAnd,
                ..
            } => true,
            _ => false,
        }
    }

    /// The type of an expression without keeping its lowering.
    fn peek_ty(&mut self, e: &sc::Expr) -> R<(Expression, Ty)> {
        if self.is_event_expr(e) {
            return Ok((null(), Ty::Event));
        }
        let saved = self.pre.len();
        let r = self.expr(e);
        self.pre.truncate(saved);
        r
    }

    /// An event expression: `e`, `e1 | e2`, `s.posedge_event()`,
    /// `s.value_changed_event()`, `s.default_event()`.
    pub fn event_list(&mut self, e: &sc::Expr) -> R<Vec<EventExpr>> {
        use sc::ExprKind as K;
        match &e.kind {
            K::Binary {
                op: sc::BinaryOp::BitOr,
                lhs,
                rhs,
            } => {
                let mut v = self.event_list(lhs)?;
                v.extend(self.event_list(rhs)?);
                Ok(v)
            }
            K::Binary {
                op: sc::BinaryOp::BitAnd,
                ..
            } => self.err(e.span, "an event AND-list cannot be mixed with '|'"),
            K::Call { callee, args } if args.is_empty() => {
                // An event function of a port's channel (§5.12).
                if let K::Member { base, name, .. } = &callee.kind
                    && let Some((obj, ifc, idx)) = self.port_ref(base)
                {
                    let ev = name.ident.name.clone();
                    let has = self
                        .prog
                        .user_classes
                        .borrow()
                        .get(&ifc)
                        .is_some_and(|s| s.events.contains(&ev));
                    if !has {
                        return self.err(e.span, format!("the port's interface has no event function '{}'", ev));
                    }
                    let ch = self.port_channel(&obj, idx.as_ref())?;
                    let t = self.temp(&Ty::Handle(ifc));
                    self.pre.push(assign(ident(&t), ch));
                    return Ok(vec![event_expr(None, member(ident(&t), &format!("__sc_ev_{}", ev)))]);
                }
                if let K::Member { base, name, .. } = &callee.kind {
                    let (x, t) = self.expr(base)?;
                    let edge = match name.ident.name.as_str() {
                        "posedge_event" | "pos" => Some(Edge::Posedge),
                        "negedge_event" | "neg" => Some(Edge::Negedge),
                        "value_changed_event" | "default_event" | "value_changed" => None,
                        other => return self.err(e.span, format!("'{}' is not an event", other)),
                    };
                    // An sc_event_queue's event.
                    if matches!(&t, Ty::Class(c) if c == "scrt_event_queue") {
                        return Ok(vec![event_expr(None, member(x, "ev"))]);
                    }
                    // An sc_fifo's data events (§6.23.4).
                    if matches!(t, Ty::Mailbox(_)) {
                        let ev = match name.ident.name.as_str() {
                            "data_read_event" => "read_ev",
                            _ => "written_ev",
                        };
                        return Ok(vec![event_expr(None, member(x, ev))]);
                    }
                    if edge.is_none()
                        && let Some((ev, value_too)) = self.buffer_counter_of(base)
                    {
                        let mut v = vec![event_expr(None, ident(&ev))];
                        if value_too {
                            v.push(event_expr(None, x));
                        }
                        return Ok(v);
                    }
                    return Ok(vec![match edge {
                        // §6.8.4: an sc_logic's edge is a change to '1' / '0'.
                        Some(ed) if matches!(t, Ty::Vec4 { .. }) => {
                            SensTerm::logic_edge(ed, x, String::new()).event()
                        }
                        _ => event_expr(edge, x),
                    }]);
                }
                self.err(e.span, "expected an event")
            }
            _ => {
                let counter = self.buffer_counter_of(e);
                if let Some((ev, false)) = &counter {
                    return Ok(vec![event_expr(None, ident(ev))]);
                }
                let (x, _) = self.expr(e)?;
                let mut v = vec![event_expr(None, x)];
                if let Some((ev, true)) = counter {
                    v.push(event_expr(None, ident(&ev)));
                }
                Ok(v)
            }
        }
    }

    /// The write counter of the `sc_buffer` `e` names.
    /// A port bound to a buffer in some instances (`true`): its events are
    /// value changes or writes, as the instance's channel decides.
    pub fn buffer_counter_of(&self, e: &sc::Expr) -> Option<(String, bool)> {
        let q = e.as_name()?;
        let sym = self.lookup(q.last_name())?;
        if let Some(c) = self.m.port_counters.get(&sym.sv) {
            return Some((c.clone(), true));
        }
        (sym.kind == SymKind::Signal && self.m.buffers.contains(&sym.sv))
            .then(|| (buffer_event(&sym.sv), false))
    }

    /// `sc_start(...)` in sc_main (see mod.rs: the testbench pauses 1 ps
    /// before the end time so events AT the end time run in the next
    /// sc_start, as in SystemC).
    fn sc_start(&mut self, args: &[sc::Expr], span: ScSpan) -> R<Vec<Statement>> {
        if !self.m.tb {
            return self.err(span, "sc_start() is supported only in sc_main");
        }
        let dur = match args {
            [] => None,
            [t] => Some(self.expr(t)?.0),
            [v, u] => Some(self.time_value(v, u, span)?),
            _ => {
                return self.err(
                    span,
                    "sc_start(), sc_start(time) or sc_start(value, unit) expected",
                );
            }
        };
        // §5.12.7: the end of elaboration checks every port and export is
        // bound (before the first sc_start runs anything).
        let mut v = vec![if_(
            unary(UnaryOp::LogNot, ident("scrt_started")),
            expr_stmt(call_fn("scrt_check_bindings", vec![])),
            None,
        )];
        v.push(if_(
            ident("scrt_started"),
            delay(int(1), null_stmt()),
            Some(delay(int(0), null_stmt())),
        ));
        v.push(expr_stmt(call_fn("__sc_apply_pending", vec![])));
        v.push(assign(ident("scrt_started"), sized(1, 1)));
        v.push(assign(ident("scrt_paused"), sized(1, 0)));
        match dur {
            Some(d) => {
                let d_var = "__sc_dur";
                v.push(assign(ident(d_var), d));
                v.push(if_(
                    bin(BinaryOp::Gt, ident(d_var), u64_lit(0)),
                    block(vec![
                        fork(
                            JoinType::JoinAny,
                            vec![
                                delay(bin(BinaryOp::Sub, ident(d_var), u64_lit(1)), null_stmt()),
                                wait(ident("scrt_stop_req")),
                            ],
                        ),
                        disable_fork(),
                        stop_at_delta_end(),
                        assign(
                            ident("scrt_tb_now"),
                            cond(
                                ident("scrt_stopped"),
                                sys("$time", vec![]),
                                bin(BinaryOp::Add, sys("$time", vec![]), u64_lit(1)),
                            ),
                        ),
                    ]),
                    Some(assign(ident("scrt_tb_now"), sys("$time", vec![]))),
                ));
            }
            None => {
                v.push(wait(ident("scrt_stop_req")));
                v.push(stop_at_delta_end());
                v.push(assign(ident("scrt_tb_now"), sys("$time", vec![])));
            }
        }
        v.push(assign(ident("scrt_paused"), sized(1, 1)));
        Ok(v)
    }

    /// `std::cout << a << b << std::endl;` → `$write(fmt, …)`.
    fn cout(&mut self, e: &sc::Expr) -> R<Vec<Statement>> {
        self.stream_out(e, None)
    }

    /// `stream << a << b …`: to standard output, or appended to the string
    /// `sink`.
    fn stream_out(&mut self, e: &sc::Expr, sink: Option<String>) -> R<Vec<Statement>> {
        let mut items = Vec::new();
        flatten_shl(e, &mut items);
        let mut fmt = String::new();
        let mut args = Vec::new();
        let mut width: Option<i64> = None;
        let mut fill_zero = false;
        for it in items.into_iter().skip(1) {
            if let Some(q) = it.as_name() {
                match short_path(q).as_str() {
                    "endl" => {
                        fmt.push('\n');
                        continue;
                    }
                    "hex" => {
                        self.f.cout_hex = true;
                        continue;
                    }
                    "dec" => {
                        self.f.cout_hex = false;
                        continue;
                    }
                    "flush" | "showbase" | "noshowbase" | "boolalpha" | "fixed" | "oct"
                    | "left" | "right" => continue,
                    _ => {}
                }
            }
            if let sc::ExprKind::Call { callee, args: a } = &it.kind
                && let Some(q) = callee.as_name()
            {
                match short_path(q).as_str() {
                    "setw" => {
                        width = a.first().and_then(|x| self.const_eval(x));
                        continue;
                    }
                    "setfill" => {
                        fill_zero = a.first().and_then(|x| self.const_eval(x)) == Some('0' as i64);
                        continue;
                    }
                    "setprecision" => continue,
                    _ => {}
                }
            }
            if let sc::ExprKind::StringLit { value, .. } = &it.kind
                && width.is_none()
            {
                fmt.push_str(&value.replace('%', "%%"));
                continue;
            }
            let (x, t) = self.expr(it)?;
            // An object prints with its class's `operator<<`.
            if let Ty::Class(c) = &t
                && let Some(f) = self
                    .prog
                    .user_classes
                    .borrow()
                    .get(c)
                    .and_then(|s| s.fmt.clone())
            {
                args.push(call_fn(&f, vec![x]));
                fmt.push_str("%s");
                continue;
            }
            let w = width
                .take()
                .map(|w| format!("{}{}", if fill_zero { "0" } else { "" }, w));
            let pad = w.clone().unwrap_or_else(|| "0".to_string());
            let spec = match &t {
                Ty::Int { ch: true, .. } => format!("%{}c", w.unwrap_or_default()),
                Ty::Str => format!("%{}s", w.unwrap_or_default()),
                Ty::Real { .. } => "%g".to_string(),
                Ty::Time => {
                    args.push(call_fn("scrt_time_str", vec![x]));
                    fmt.push_str("%s");
                    continue;
                }
                Ty::Vec2 { bv: true, .. } => "%b".to_string(),
                Ty::Vec4 { .. } => {
                    args.push(call_fn(
                        "scrt_upper",
                        vec![sys("$sformatf", vec![string("%b"), x])],
                    ));
                    fmt.push_str("%s");
                    continue;
                }
                // SystemC prints sc_uint in hex with ceil((W+1)/4) digits (a
                // leading sign digit), sc_int with ceil(W/4), zero-padded.
                Ty::Vec2 { w, signed, .. } if self.f.cout_hex && w.n.is_some() => {
                    let wn = w.n.expect("checked");
                    let digits = if *signed {
                        wn.div_ceil(4)
                    } else {
                        (wn + 1).div_ceil(4)
                    };
                    args.push(size_cast(digits * 4, x));
                    fmt.push_str("%h");
                    continue;
                }
                Ty::Bool | Ty::Vec2 { .. } | Ty::Int { .. } => {
                    if self.f.cout_hex {
                        format!("%{}h", pad)
                    } else {
                        format!("%{}d", pad)
                    }
                }
                Ty::OStream => "%s".to_string(),
                Ty::Ptr { .. } | Ty::Class(_) | Ty::Handle(_) => {
                    return self.err(it.span, "printing this object is not supported");
                }
                _ => return self.err(it.span, "printing this value is not supported"),
            };
            fmt.push_str(&spec);
            args.push(x);
        }
        let mut a = vec![string(&fmt)];
        a.extend(args);
        Ok(vec![match sink {
            None => expr_stmt(sys("$write", a)),
            Some(v) => assign(ident(&v), concat(vec![ident(&v), sys("$sformatf", a)])),
        }])
    }
}

fn math1(f: &str) -> Option<&'static str> {
    Some(match f.trim_end_matches('f') {
        "sqrt" => "$sqrt",
        "floor" => "$floor",
        "ceil" => "$ceil",
        "sin" => "$sin",
        "cos" => "$cos",
        "tan" => "$tan",
        "asin" => "$asin",
        "acos" => "$acos",
        "atan" => "$atan",
        "sinh" => "$sinh",
        "cosh" => "$cosh",
        "tanh" => "$tanh",
        "exp" => "$exp",
        "log" => "$ln",
        "log10" => "$log10",
        _ => return None,
    })
}

/// The write counter of an `sc_buffer`: it changes on every write, so a
/// process sensitive to it wakes like one sensitive to a changed signal.
/// The writer-process slot of a one-writer signal (E115 check).
pub fn one_writer_var(sig: &str) -> String {
    format!("__sc_w_{}", sig)
}

/// The nettype of a resolved net of width `w` (runtime package): a driver
/// word {written, value[w-1:0]}.
pub fn rv_nettype(w: u32) -> String {
    format!("scrt_rv{}_t", w)
}

/// The event count of an sc_buffer: its own writes plus those made through
/// the output ports bound to it (a continuous sum).
pub fn buffer_event(buffer: &str) -> String {
    format!("__sc_be_{}", buffer)
}

pub fn buffer_counter(buffer: &str) -> String {
    format!("__sc_wr_{}", buffer)
}

/// After a process's sc_stop(): let the processes of the current delta
/// cycle finish, then report the stop.
fn stop_at_delta_end() -> Statement {
    if_(
        bin(
            BinaryOp::LogAnd,
            ident("scrt_stop_req"),
            unary(UnaryOp::LogNot, ident("scrt_stopped")),
        ),
        block(vec![
            delay(int(0), null_stmt()),
            expr_stmt(call_fn("scrt_stop", vec![])),
        ]),
        None,
    )
}

/// `scrt_ptr::mk(obj, off)`.
pub fn ptr_mk(obj: Expression, off: Expression) -> Expression {
    method(ident("scrt_ptr"), "mk", vec![obj, off])
}

fn ptr_offset(i: Expression, elem: u32) -> Expression {
    if elem == 1 {
        i
    } else {
        bin(BinaryOp::Mul, paren(i), int(elem as i64))
    }
}

fn ptr_get(p: Expression, off: Expression, elem: u32) -> Expression {
    let m = match elem {
        2 => "get16",
        4 => "get32",
        8 => "get64",
        _ => "get8",
    };
    method(p, m, vec![off])
}

fn ptr_set(p: Expression, off: Expression, elem: u32, v: Expression) -> Expression {
    let m = match elem {
        2 => "set16",
        4 => "set32",
        8 => "set64",
        _ => "set8",
    };
    method(p, m, vec![off, v])
}

fn ptr_elem_ty(elem: u32) -> Ty {
    Ty::Int {
        bits: (elem * 8).max(8),
        signed: false,
        ch: elem == 1,
    }
}

pub fn box_class(ty: &Ty) -> &'static str {
    match ty.byte_size().unwrap_or(4) {
        1 => "scrt_box8",
        2 => "scrt_box16",
        8 => "scrt_box64",
        _ => "scrt_box32",
    }
}

pub fn arr_class(ty: &Ty) -> &'static str {
    match arr_elem_bytes(ty) {
        1 => "scrt_arr8",
        2 => "scrt_arr16",
        8 => "scrt_arr64",
        _ => "scrt_arr32",
    }
}

pub fn arr_elem_bytes(ty: &Ty) -> u32 {
    match ty {
        Ty::Array(e, _) => e.byte_size().unwrap_or(4) as u32,
        _ => 4,
    }
}

pub fn edge_flag_name(p: usize, sig: &str) -> String {
    format!("__sc_p{}_ev_{}", p, sig)
}

pub fn reset_flag_name(p: usize) -> String {
    format!("__sc_p{}_reset", p)
}

/// The integer value of a literal SV expression.
pub fn expr_int(e: &Expression) -> Option<i64> {
    match &e.kind {
        ExprKind::Number(crate::ast::expr::NumberLiteral::Integer { value, .. }) => {
            value.parse().ok()
        }
        _ => None,
    }
}

fn flatten_comma<'e>(e: &'e sc::Expr, out: &mut Vec<&'e sc::Expr>) {
    match &e.kind {
        sc::ExprKind::Binary {
            op: sc::BinaryOp::Comma,
            lhs,
            rhs,
        } => {
            flatten_comma(lhs, out);
            flatten_comma(rhs, out);
        }
        sc::ExprKind::Paren(inner)
            if matches!(
                inner.kind,
                sc::ExprKind::Binary {
                    op: sc::BinaryOp::Comma,
                    ..
                }
            ) =>
        {
            flatten_comma(inner, out)
        }
        _ => out.push(e),
    }
}

fn flatten_shl<'e>(e: &'e sc::Expr, out: &mut Vec<&'e sc::Expr>) {
    match &e.kind {
        sc::ExprKind::Binary {
            op: sc::BinaryOp::Shl,
            lhs,
            rhs,
        } => {
            flatten_shl(lhs, out);
            out.push(rhs);
        }
        _ => out.push(e),
    }
}

/// Whether a `<<` chain starts at a stream (`std::cout << …`).
/// The first operand of a `<<` chain (the stream).
fn leftmost_shl(e: &sc::Expr) -> &sc::Expr {
    match &e.kind {
        sc::ExprKind::Binary {
            op: sc::BinaryOp::Shl,
            lhs,
            ..
        } => leftmost_shl(lhs),
        _ => e,
    }
}

fn stream_base(e: &sc::Expr) -> bool {
    match &e.kind {
        sc::ExprKind::Binary {
            op: sc::BinaryOp::Shl,
            lhs,
            ..
        } => stream_base(lhs),
        _ => is_stream(e),
    }
}

fn is_incdec(k: &sc::ExprKind) -> bool {
    matches!(
        k,
        sc::ExprKind::Unary {
            op: sc::UnaryOp::PreInc | sc::UnaryOp::PreDec,
            ..
        }
    )
}

fn deref_inner(e: &sc::Expr) -> &sc::Expr {
    match &e.kind {
        sc::ExprKind::Unary {
            op: sc::UnaryOp::Deref,
            operand,
        } => operand,
        _ => e,
    }
}

/// The result type of arithmetic on `a` and `b`.
fn arith_ty(a: &Ty, b: &Ty, op: sc::BinaryOp) -> Ty {
    match (a, b) {
        (Ty::Real { .. }, _) | (_, Ty::Real { .. }) => Ty::Real { single: false },
        (Ty::Time, Ty::Time) if op == sc::BinaryOp::Div => Ty::Real { single: false },
        (Ty::Time, _) | (_, Ty::Time) => Ty::Time,
        (Ty::Vec2 { .. } | Ty::Vec4 { .. }, _)
            if matches!(
                op,
                sc::BinaryOp::BitAnd
                    | sc::BinaryOp::BitOr
                    | sc::BinaryOp::BitXor
                    | sc::BinaryOp::Shl
                    | sc::BinaryOp::Shr
            ) =>
        {
            a.clone()
        }
        (Ty::Vec2 { signed, .. }, _) => Ty::Int {
            bits: 64,
            signed: *signed,
            ch: false,
        },
        (
            Ty::Int {
                bits: ab,
                signed: asg,
                ..
            },
            Ty::Int {
                bits: bb,
                signed: bsg,
                ..
            },
        ) => Ty::Int {
            bits: (*ab).max(*bb).max(32),
            signed: *asg && *bsg,
            ch: false,
        },
        (Ty::Int { bits, signed, .. }, _) => Ty::Int {
            bits: (*bits).max(32),
            signed: *signed,
            ch: false,
        },
        _ => Ty::int32(),
    }
}

fn contains_switch_break(s: &sc::Stmt) -> bool {
    match s {
        sc::Stmt::Break(_) => true,
        sc::Stmt::Block(b) => b.stmts.iter().any(contains_switch_break),
        sc::Stmt::If {
            then_branch,
            else_branch,
            ..
        } => {
            contains_switch_break(then_branch)
                || else_branch
                    .as_ref()
                    .is_some_and(|e| contains_switch_break(e))
        }
        // A break inside a loop or nested switch belongs to it.
        _ => false,
    }
}

pub fn stmt_span(s: &sc::Stmt) -> ScSpan {
    use sc::Stmt as S;
    match s {
        S::Block(b) => b.span,
        S::Decl(v) => v.span,
        S::Expr(e) => e.span,
        S::If { span, .. }
        | S::Switch { span, .. }
        | S::For { span, .. }
        | S::RangeFor { span, .. }
        | S::While { span, .. }
        | S::DoWhile { span, .. }
        | S::Try { span, .. }
        | S::Labeled { span, .. }
        | S::ScProcess { span, .. }
        | S::Sensitive { span, .. }
        | S::ResetSignalIs { span, .. }
        | S::ScFork { span, .. } => *span,
        S::Break(s) | S::Continue(s) | S::Empty(s) | S::DontInitialize(s) | S::Return(_, s) => *s,
        S::Typedef(t) => t.span,
        S::Using(_) | S::Class(_) | S::Enum(_) | S::StaticAssert(_) => ScSpan::default(),
    }
}

#[cfg(test)]
mod tests {
    use super::printf_to_sv;

    #[test]
    fn printf_formats() {
        assert_eq!(
            printf_to_sv("%d %5d %x %llu %s %c %% %f\n"),
            "%0d %5d %0h %0d %s %c %% %f\n"
        );
        assert_eq!(printf_to_sv("%08x|%-4d"), "%08h|%-4d");
    }
}
