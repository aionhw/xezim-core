//! User C++ classes and structs → SystemVerilog classes in the package
//! `sc_user`, which every generated module imports: objects in process
//! bodies, signal and FIFO payloads (IEEE 1666-2023 §6.4.2, §6.23).
//!
//! A C++ class `T` is the SV class `sc_c_T`. A pointer is a handle to an
//! object (shared, `Ty::Handle`); an object itself — a variable, a member,
//! a by-value parameter — is a handle to its own object (`Ty::Class`), and
//! C++'s copies of it are explicit: `__sc_set(o)` copies `o`'s members into
//! the object (assignment), `__sc_copy()` makes a new copy (initialization,
//! by-value parameters and returns, signal and FIFO writes). Copying uses
//! the static type, as C++ slices.
//!
//! Construction: `new` only allocates (member objects included); each C++
//! constructor is a method `__sc_init<k>` (base class, members, body) and
//! a static factory `__sc_make<k>`, so overloaded and base-class
//! constructors keep their meaning. Operators become methods or package
//! functions (`__sc_op_eq`, …); `operator<<` on an ostream becomes a
//! function returning the text (`__sc_fmt__T`).

use std::collections::{BTreeMap, BTreeSet};

use super::build::*;
use super::lower::*;
use super::module::visit_stmt_exprs;
use super::program::Program;
use super::types::*;
use crate::ast::Description;
use crate::ast::decl::{
    ClassItem, ClassProperty, ClassQualifier, ImportDeclaration, ImportItem, PackageItem,
    TypedefDeclaration,
};
use crate::ast::expr::Expression;
use crate::ast::module::PackageDeclaration;
use crate::ast::stmt::{Statement, StatementKind};
use crate::ast::types::PortDirection;
use crate::sv_parser::systemc::ast as sc;
use crate::sv_parser::systemc::token::ScSpan;

/// The SV class of a C++ class.
pub fn class_sv(name: &str) -> String {
    format!("sc_c_{}", name)
}

/// A member of a user class.
#[derive(Debug, Clone)]
pub struct FieldSig {
    pub ty: Ty,
    pub is_static: bool,
}

/// One overload of a member function.
#[derive(Debug, Clone)]
pub struct MethodSig {
    /// The SV method name (overloads are told apart by arity).
    pub sv: String,
    pub sig: FnSig,
    /// The parameter types and whether each is passed by (non-const)
    /// reference.
    pub params: Vec<Ty>,
    /// Their SV names (as the lowered method declares them).
    pub pnames: Vec<String>,
    /// Parameters without and with their defaults.
    pub min_args: usize,
    pub max_args: usize,
    pub is_static: bool,
    /// The class declaring it (SV name).
    pub owner: String,
}

/// How `a == b` (or another operator) on objects of the class is computed.
#[derive(Debug, Clone)]
pub enum OpImpl {
    /// A method of the left operand, and what it returns.
    Method(String, Ty),
    /// A package function of both operands, and what it returns.
    Function(String, Ty),
}

/// What the lowering knows of a user class.
#[derive(Debug, Clone, Default)]
pub struct ClassSig {
    pub cpp: String,
    pub sv: String,
    /// The base class (SV name).
    pub base: Option<String>,
    /// Members, own and inherited, by C++ name.
    pub fields: BTreeMap<String, FieldSig>,
    /// Own members in declaration order.
    pub own_fields: Vec<String>,
    /// Member functions, own and inherited: C++ name → overloads.
    pub methods: BTreeMap<String, Vec<MethodSig>>,
    /// Constructors: (fewest, most arguments) per `__sc_init<k>`.
    pub ctors: Vec<(usize, usize)>,
    /// Binary operators on objects: C++ operator spelling → implementation.
    pub ops: BTreeMap<String, OpImpl>,
    /// `operator<<(ostream&, const T&)`: the package function formatting it.
    pub fmt: Option<String>,
    /// An interface (§5.13, derived from `sc_interface`): its methods are
    /// tasks (an implementation may block), and ports of it are objects of
    /// the class `__sc_port__<name>`.
    pub is_interface: bool,
    /// Member functions returning an event (`const sc_event&
    /// default_event()`): an interface holds each as an event property
    /// (`__sc_ev_<name>`) its channel aliases to the event it returns.
    pub events: BTreeSet<String>,
}

impl ClassSig {
    /// The overload of `name` that takes `n` arguments.
    pub fn method(&self, name: &str, n: usize) -> Option<&MethodSig> {
        self.methods
            .get(name)?
            .iter()
            .find(|m| m.min_args <= n && n <= m.max_args)
    }

    /// The constructor taking `n` arguments.
    pub fn ctor(&self, n: usize) -> Option<usize> {
        self.ctors.iter().position(|(lo, hi)| *lo <= n && n <= *hi)
    }
}

/// The SV name of a C++ operator function (`operator==` → `__sc_op_eq`).
pub fn operator_sv(name: &str) -> Option<&'static str> {
    Some(match name.strip_prefix("operator")?.trim() {
        "==" => "__sc_op_eq",
        "!=" => "__sc_op_ne",
        "<" => "__sc_op_lt",
        ">" => "__sc_op_gt",
        "<=" => "__sc_op_le",
        ">=" => "__sc_op_ge",
        "+" => "__sc_op_add",
        "-" => "__sc_op_sub",
        "*" => "__sc_op_mul",
        "/" => "__sc_op_div",
        "%" => "__sc_op_mod",
        "&" => "__sc_op_and",
        "|" => "__sc_op_or",
        "^" => "__sc_op_xor",
        "+=" => "__sc_op_add_assign",
        "-=" => "__sc_op_sub_assign",
        "=" => "__sc_op_assign",
        "[]" => "__sc_op_index",
        "()" => "__sc_op_call",
        "<<" => "__sc_op_shl",
        ">>" => "__sc_op_shr",
        _ => return None,
    })
}

/// Library base classes: a class deriving from one is a channel, an
/// interface or a TLM object, not plain data.
fn library_class(n: &str) -> bool {
    n.starts_with("sc_") || n.starts_with("tlm_") || n.starts_with("peq_")
}

/// `sc_interface`, the root of every interface (§5.13): an interface class
/// derives from it (virtually).
fn is_sc_interface(n: &str) -> bool {
    n == "sc_interface"
}

/// A user class to lower: a plain class, or an instantiation of a class
/// template.
#[derive(Debug, Clone)]
pub struct UserClass<'a> {
    /// The lowered name: the class's, or the instantiation's
    /// (`box__int32`); the SV class is `sc_c_<name>`.
    pub name: String,
    /// The C++ class (template) as declared.
    pub cpp: String,
    pub tu: usize,
    pub decl: &'a sc::ClassDecl,
    /// The template parameters' bindings (empty for a plain class).
    pub bindings: BTreeMap<String, TParam>,
    /// The base class's lowered name.
    pub base: Option<String>,
}

/// Whether a class is plain data or behaviour: not a module, and not
/// derived from a library class.
pub fn is_plain(c: &sc::ClassDecl) -> bool {
    !c.sc_module
        && !c.bases.iter().any(|b| {
            library_class(b.name.last_name()) && !is_sc_interface(b.name.last_name())
        })
}

/// The user classes to lower: plain classes and structs (not foreign
/// modules), and the instantiations of plain class templates; bases come
/// before the classes deriving from them.
pub fn user_classes<'a>(lw: &mut Lw<'a>) -> Vec<UserClass<'a>> {
    let prog = lw.prog;
    let plain = is_plain;
    let mut cands: BTreeMap<String, UserClass<'a>> = BTreeMap::new();
    for (n, (tu, c, tps)) in &prog.classes {
        if tps.is_empty() && !prog.foreign.contains_key(n) && plain(c) {
            cands.insert(
                n.clone(),
                UserClass {
                    name: n.clone(),
                    cpp: n.clone(),
                    tu: *tu,
                    decl: c,
                    bindings: BTreeMap::new(),
                    base: None,
                },
            );
        }
    }
    let instances = lw.env.instances.borrow().clone();
    for (inst, i) in instances {
        if let Some((tu, c, _)) = prog.classes.get(&i.template)
            && plain(c)
        {
            cands.insert(
                inst.clone(),
                UserClass {
                    name: inst.clone(),
                    cpp: i.template.clone(),
                    tu: *tu,
                    decl: c,
                    bindings: super::templates::bindings(lw, &inst),
                    base: None,
                },
            );
        }
    }
    // Base classes, resolved in each class's own bindings.
    let saved = std::mem::take(&mut lw.env.tparams);
    for uc in cands.values_mut() {
        lw.env.tparams = uc.bindings.clone();
        // `sc_interface` is no base of the SV class.
        uc.base = uc
            .decl
            .bases
            .iter()
            .find(|b| !is_sc_interface(b.name.last_name()))
            .map(|b| {
                instantiate(&b.name, &lw.env, &|e| lw.const_eval(e))
                    .ok()
                    .flatten()
                    .unwrap_or_else(|| b.name.last_name().to_string())
            });
    }
    lw.env.tparams = saved;
    // Drop classes whose bases are not lowered themselves.
    loop {
        let drop: Vec<String> = cands
            .iter()
            .filter(|(_, uc)| uc.base.as_ref().is_some_and(|b| !cands.contains_key(b)))
            .map(|(n, _)| n.clone())
            .collect();
        if drop.is_empty() {
            break;
        }
        for n in drop {
            cands.remove(&n);
        }
    }
    let mut out = Vec::new();
    let mut done: BTreeSet<String> = BTreeSet::new();
    while out.len() < cands.len() {
        let before = out.len();
        for (n, uc) in &cands {
            if done.contains(n) {
                continue;
            }
            if uc.base.as_ref().is_none_or(|b| done.contains(b)) {
                done.insert(n.clone());
                out.push(uc.clone());
            }
        }
        if out.len() == before {
            break; // a base cycle; cannot happen in C++
        }
    }
    out
}

/// Every definition of the class's member functions: in the class body and
/// out of it (`T::f`), with their translation units.
fn member_defs<'a>(
    prog: &Program<'a>,
    name: &str,
    tu: usize,
    c: &'a sc::ClassDecl,
) -> Vec<(usize, &'a sc::FunctionDecl)> {
    let mut out = Vec::new();
    for m in &c.members {
        if let sc::Member::Method(f) = m
            && !f.specifiers.is_friend
        {
            out.push((tu, f));
        }
    }
    for &(t, f) in prog.out_of_class.get(name).into_iter().flatten() {
        let f: &'a sc::FunctionDecl = f;
        if f.base_name() != name && !f.base_name().starts_with('~') {
            out.push((t, f));
        }
    }
    out
}

fn ctor_defs<'a>(
    prog: &Program<'a>,
    name: &str,
    tu: usize,
    c: &'a sc::ClassDecl,
) -> Vec<(usize, &'a sc::FunctionDecl)> {
    let mut out: Vec<(usize, &'a sc::FunctionDecl)> = Vec::new();
    for m in &c.members {
        if let sc::Member::Constructor(f) = m {
            out.push((tu, f));
        }
    }
    // An out-of-class definition replaces its in-class declaration.
    for &(t, f) in prog.out_of_class.get(name).into_iter().flatten() {
        let f: &'a sc::FunctionDecl = f;
        if f.base_name() != name {
            continue;
        }
        if let Some(slot) = out
            .iter_mut()
            .find(|(_, d)| d.body.is_none() && d.params.len() == f.params.len())
        {
            *slot = (t, f);
        } else {
            out.push((t, f));
        }
    }
    out.retain(|(_, f)| f.special_body.is_none() || f.body.is_some());
    out
}

/// Free (and friend) operator functions of the program by their first
/// class operand: (C++ class, operator spelling) → definition.
fn free_operators<'a>(
    prog: &Program<'a>,
    classes: &BTreeSet<String>,
) -> Vec<(String, String, usize, &'a sc::FunctionDecl)> {
    fn walk<'a>(
        tu: usize,
        items: &'a [sc::Item],
        out: &mut Vec<(usize, &'a sc::FunctionDecl)>,
    ) {
        for item in items {
            match item {
                sc::Item::Function(f) => out.push((tu, f)),
                sc::Item::Namespace { items, .. } | sc::Item::ExternBlock { items, .. } => {
                    walk(tu, items, out)
                }
                sc::Item::Class(c) => {
                    for m in &c.members {
                        if let sc::Member::Method(f) = m
                            && f.specifiers.is_friend
                        {
                            out.push((tu, f));
                        }
                    }
                }
                _ => {}
            }
        }
    }
    let mut fns = Vec::new();
    for (tu, r) in prog.results.iter().enumerate() {
        walk(tu, &r.unit.items, &mut fns);
    }
    let mut out = Vec::new();
    for (tu, f) in fns {
        let n = f.base_name();
        if !n.starts_with("operator") || f.body.is_none() {
            continue;
        }
        // The class operand: the first parameter of a user class, or the
        // second of `operator<<(std::ostream&, const T&)`.
        let class_of = |p: &sc::Param| {
            p.ty.name()
                .map(|q| q.last_name().to_string())
                .filter(|c| classes.contains(c))
        };
        let class = f.params.iter().find_map(class_of);
        if let Some(c) = class {
            out.push((c, n.to_string(), tu, f));
        }
    }
    out
}

/// Whether a parameter is an ostream (`std::ostream& os`).
fn is_ostream(t: &sc::Type) -> bool {
    t.name()
        .is_some_and(|q| matches!(q.last_name(), "ostream" | "basic_ostream"))
}

/// Compute every user class's signature (members, methods, constructors,
/// operators) and record it in the program; the names become types.
pub fn signatures(lw: &mut Lw, classes: &[UserClass]) -> R<()> {
    for uc in classes {
        lw.env.classes.insert(uc.name.clone());
    }
    // Free operator functions of the plain classes.
    let names: BTreeSet<String> = classes
        .iter()
        .filter(|uc| uc.bindings.is_empty())
        .map(|uc| uc.cpp.clone())
        .collect();
    let blocking = blocking_methods(lw, classes);
    let ops = free_operators(lw.prog, &names);
    let saved = std::mem::take(&mut lw.env.tparams);
    for uc in classes {
        lw.env.tparams = uc.bindings.clone();
        if let Err(e) = class_signature(lw, uc, &blocking, &ops) {
            lw.record(e);
        }
    }
    lw.env.tparams = saved;
    Ok(())
}

fn class_signature(
    lw: &mut Lw,
    uc: &UserClass,
    blocking: &BTreeSet<(String, String)>,
    ops: &[(String, String, usize, &sc::FunctionDecl)],
) -> R<()> {
    {
        let (name, tu, c) = (&uc.name, &uc.tu, uc.decl);
        lw.tu = *tu;
        let sv = class_sv(name);
        let base = uc.base.clone();
        let mut sig = match &base {
            Some(b) => {
                let inherited = lw
                    .prog
                    .user_classes
                    .borrow()
                    .get(&class_sv(b))
                    .cloned()
                    .unwrap_or_default();
                ClassSig {
                    fields: inherited.fields,
                    methods: inherited.methods,
                    ops: inherited.ops,
                    fmt: inherited.fmt,
                    is_interface: inherited.is_interface,
                    events: inherited.events,
                    ..Default::default()
                }
            }
            None => ClassSig::default(),
        };
        sig.is_interface |= c.bases.iter().any(|b| is_sc_interface(b.name.last_name()));
        // sc_interface::default_event() (§5.13): every interface has it; a
        // channel defining it sets the event.
        if sig.is_interface {
            sig.events.insert("default_event".to_string());
        }
        sig.cpp = name.clone();
        sig.sv = sv.clone();
        sig.base = base.as_deref().map(class_sv);
        for m in &c.members {
            let sc::Member::Field(v) = m else { continue };
            for d in &v.declarators {
                let ty = lw.decl_ty(&v.ty, d)?;
                sig.fields.insert(
                    d.name.name.clone(),
                    FieldSig {
                        ty,
                        is_static: v.specifiers.is_static,
                    },
                );
                sig.own_fields.push(d.name.name.clone());
            }
        }
        // Member functions, overloads told apart by arity.
        let defs = member_defs(lw.prog, &uc.cpp, *tu, c);
        let mut by_name: BTreeMap<String, Vec<&sc::FunctionDecl>> = BTreeMap::new();
        for (_, f) in &defs {
            let entry = by_name.entry(f.base_name().to_string()).or_default();
            // An out-of-class definition repeats its in-class declaration.
            if !entry.iter().any(|g| g.params.len() == f.params.len()) {
                entry.push(f);
            }
        }
        for (mname, fs) in by_name {
            let mut overloads = Vec::new();
            for f in &fs {
                let base_sv = operator_sv(&mname)
                    .map(str::to_string)
                    .unwrap_or_else(|| escape_sv(&mname));
                let sv_name = if fs.len() > 1 {
                    format!("{}__{}", base_sv, f.params.len())
                } else {
                    base_sv
                };
                let mut fsig =
                    fn_sig(lw, f, blocking.contains(&(name.clone(), mname.clone())))?;
                if sig.is_interface {
                    // An implementation may block: interface methods are
                    // tasks; one returning an event is an event property.
                    fsig.is_task = true;
                    if matches!(fsig.ret, Ty::Event) {
                        sig.events.insert(mname.clone());
                    }
                }
                let mut ptys = Vec::new();
                let mut pnames = Vec::new();
                for (i, p) in f.params.iter().enumerate() {
                    if !is_ostream(&p.ty) {
                        ptys.push(lw.ty(&p.ty, p.span)?);
                        pnames.push(
                            p.name
                                .as_ref()
                                .map_or_else(|| format!("__sc_arg{}", i), |n| escape_sv(&n.name)),
                        );
                    }
                }
                overloads.push(MethodSig {
                    sv: sv_name,
                    sig: fsig,
                    params: ptys,
                    pnames,
                    min_args: f.params.iter().filter(|p| p.default.is_none()).count(),
                    max_args: f.params.len(),
                    is_static: f.specifiers.is_static,
                    owner: sv.clone(),
                });
            }
            if let Some(op) = operator_sv(&mname)
                && fs.iter().any(|f| f.params.len() == 1)
            {
                let (sv_m, ret) = overloads
                    .iter()
                    .find(|o| o.max_args == 1)
                    .map(|o| (o.sv.clone(), o.sig.ret.clone()))
                    .unwrap_or_else(|| (op.to_string(), Ty::Bool));
                sig.ops.insert(
                    mname.trim_start_matches("operator").trim().to_string(),
                    OpImpl::Method(sv_m, ret),
                );
            }
            sig.methods.insert(mname, overloads);
        }
        let ctors = ctor_defs(lw.prog, &uc.cpp, *tu, c);
        sig.ctors = if ctors.is_empty() {
            vec![(0, 0)]
        } else {
            ctors
                .iter()
                .map(|(_, f)| {
                    (
                        f.params.iter().filter(|p| p.default.is_none()).count(),
                        f.params.len(),
                    )
                })
                .collect()
        };
        for (cls, op, _, f) in ops {
            if !uc.bindings.is_empty() || cls != &uc.cpp {
                continue;
            }
            let spelling = op.trim_start_matches("operator").trim().to_string();
            if spelling == "<<" && f.params.first().is_some_and(|p| is_ostream(&p.ty)) {
                sig.fmt = Some(format!("__sc_fmt__{}", name));
            } else if let Some(o) = operator_sv(op) {
                let ret = fn_sig(lw, f, false)?.ret;
                sig.ops
                    .insert(spelling, OpImpl::Function(format!("{}__{}", o, name), ret));
            }
        }
        lw.prog.user_classes.borrow_mut().insert(sv.clone(), sig);
    }
    Ok(())
}

/// SV keywords a C++ member may be named (`release`, `new`, …) get an `_`.
pub fn escape_sv(n: &str) -> String {
    const KW: &[&str] = &[
        "release", "new", "type", "string", "event", "input", "output", "begin", "end",
        "module", "logic", "reg", "wire", "bit", "byte", "time", "real", "class", "task",
        "function", "virtual", "static", "extends", "this", "super", "null", "local",
        "protected", "rand", "constraint", "property", "sequence", "assert", "cover", "fork",
        "join", "wait", "disable", "repeat", "forever", "initial", "always", "final", "package",
        "import", "export", "interface", "program", "config", "default", "unique", "priority",
        "inside", "dist", "with", "foreach", "randomize", "process", "semaphore", "mailbox",
        "edge", "posedge", "negedge", "or", "and", "not", "xor", "buf", "table", "int",
        "shortint", "longint", "integer", "signed", "unsigned", "void", "enum", "struct",
        "union", "packed", "ref", "const", "var", "alias", "assign", "deassign", "force",
        "case", "casex", "casez", "endcase", "if", "else", "for", "while", "do", "return",
        "break", "continue", "global", "chandle", "context", "pure", "extern", "bind",
        "parameter", "localparam", "specify", "generate", "genvar", "tri", "supply0",
        "supply1", "begin_keywords", "first_match", "matches", "tagged", "covergroup",
        "coverpoint", "bins", "illegal_bins", "ignore_bins", "expect", "let", "checker",
        "randcase", "randsequence", "solve", "before", "iff", "intersect", "throughout",
        "within", "nexttime", "until", "implies", "accept_on", "reject_on", "s_always",
        "eventually", "strong", "weak", "soft", "untyped", "interconnect", "nettype",
        "implements", "restrict", "assume", "uwire", "trireg", "small", "medium", "large",
        "highz0", "highz1", "strong0", "strong1", "pull0", "pull1", "weak0", "weak1",
        "pullup", "pulldown", "cmos", "rcmos", "nmos", "pmos", "rnmos", "rpmos", "tran",
        "rtran", "tranif0", "tranif1", "rtranif0", "rtranif1", "bufif0", "bufif1",
        "notif0", "notif1", "nand", "nor", "xnor", "join_any", "join_none", "shortreal",
        "realtime", "timeunit", "timeprecision", "primitive", "macromodule", "library",
        "incdir", "include", "design", "instance", "cell", "liblist", "use", "noshowcancelled",
        "showcancelled", "pulsestyle_onevent", "pulsestyle_ondetect", "automatic",
        "endfunction", "endtask", "endclass", "endmodule", "endpackage",
    ];
    if KW.contains(&n) {
        format!("{}_", n)
    } else {
        n.to_string()
    }
}

/// The lowered signature of a member function.
fn fn_sig(lw: &Lw, f: &sc::FunctionDecl, blocks: bool) -> R<FnSig> {
    let ret = match &f.return_type {
        Some(rt) => {
            let mut rt = rt.clone();
            rt.ptr_ops.extend(f.return_ptr_ops.iter().copied());
            lw.ty(&rt, f.span)?
        }
        None => Ty::Void,
    };
    let by_ref = f
        .params
        .iter()
        .map(|p| {
            p.ty.ptr_ops.contains(&sc::PtrOp::LRef)
                && !p.ty.is_const
                && !matches!(lw.ty(&p.ty, p.span), Ok(Ty::Class(_) | Ty::Handle(_)))
        })
        .collect();
    Ok(FnSig {
        ret,
        is_task: blocks,
        by_ref,
        defaults: Vec::new(),
    })
}

/// The member functions that may block (`wait`, a blocking FIFO access, or
/// a call of one): they become tasks. Calls on other objects count by name.
fn blocking_methods(lw: &Lw, classes: &[UserClass]) -> BTreeSet<(String, String)> {
    let mut direct = BTreeSet::new();
    let mut calls: BTreeMap<(String, String), (BTreeSet<String>, BTreeSet<String>)> =
        BTreeMap::new();
    for uc in classes {
        for (_, f) in member_defs(lw.prog, &uc.cpp, uc.tu, uc.decl) {
            let key = (uc.name.clone(), f.base_name().to_string());
            let mut own = BTreeSet::new();
            let mut other = BTreeSet::new();
            let mut blocks = false;
            if let Some(b) = &f.body {
                for s in &b.stmts {
                    visit_stmt_exprs(s, &mut |e| {
                        let sc::ExprKind::Call { callee, .. } = &e.kind else {
                            return;
                        };
                        match &callee.kind {
                            sc::ExprKind::Name(q) => {
                                let n = q.last_name();
                                if matches!(n, "wait" | "sc_start") {
                                    blocks = true;
                                }
                                own.insert(n.to_string());
                            }
                            sc::ExprKind::Member { name, .. } => {
                                other.insert(name.ident.name.clone());
                            }
                            _ => {}
                        }
                    });
                }
            }
            if blocks {
                direct.insert(key.clone());
            }
            let e = calls.entry(key).or_default();
            e.0.extend(own);
            e.1.extend(other);
        }
    }
    let mut out = direct;
    loop {
        let before = out.len();
        let names: BTreeSet<String> = out.iter().map(|(_, m)| m.clone()).collect();
        for ((c, m), (own, other)) in &calls {
            if own.iter().any(|f| out.contains(&(c.clone(), f.clone())))
                || other.iter().any(|f| names.contains(f))
            {
                out.insert((c.clone(), m.clone()));
            }
        }
        if out.len() == before {
            break;
        }
    }
    *lw.prog.blocking_methods.borrow_mut() = out.iter().map(|(_, m)| m.clone()).collect();
    out
}

/// The package `sc_user` holding the lowered user classes (`None` when the
/// design has none).
pub fn package(lw: &mut Lw, classes: &[UserClass]) -> Option<Description> {
    if classes.is_empty() {
        return None;
    }
    let mut items: Vec<PackageItem> = vec![PackageItem::Import(ImportDeclaration {
        items: vec![ImportItem {
            package: id("sc_rt"),
            item: None,
            span: sp(),
        }],
        span: sp(),
    })];
    // Forward declarations: classes refer to each other freely.
    for uc in classes {
        items.push(PackageItem::Typedef(TypedefDeclaration {
            data_type: void_t(),
            name: id(&class_sv(&uc.name)),
            dimensions: Vec::new(),
            span: sp(),
            forward: false,
        }));
    }
    let statics = static_definitions(lw);
    let names: BTreeSet<String> = classes
        .iter()
        .filter(|uc| uc.bindings.is_empty())
        .map(|uc| uc.cpp.clone())
        .collect();
    let saved = std::mem::take(&mut lw.env.tparams);
    for uc in classes {
        // A class whose signature failed was reported already.
        if !lw.prog.user_classes.borrow().contains_key(&class_sv(&uc.name)) {
            continue;
        }
        lw.tu = uc.tu;
        lw.env.tparams = uc.bindings.clone();
        match lower_class(lw, uc, &statics) {
            Ok(cd) => {
                items.push(PackageItem::Class(cd));
                let is_if = lw
                    .prog
                    .user_classes
                    .borrow()
                    .get(&class_sv(&uc.name))
                    .is_some_and(|s| s.is_interface);
                if is_if {
                    match super::package_items(&port_class(&class_sv(&uc.name))) {
                        Ok(v) => items.extend(v),
                        Err(m) => lw.record(LowerError {
                            tu: uc.tu,
                            span: uc.decl.span,
                            msg: m,
                        }),
                    }
                }
            }
            Err(e) => lw.record(e),
        }
    }
    lw.env.tparams = saved;
    for (cls, op, tu, f) in free_operators(lw.prog, &names) {
        lw.tu = tu;
        let r = if op.trim_start_matches("operator").trim() == "<<"
            && f.params.first().is_some_and(|p| is_ostream(&p.ty))
        {
            lower_formatter(lw, &cls, f)
        } else {
            match operator_sv(&op) {
                Some(o) => lower_free_function(lw, &format!("{}__{}", o, cls), f),
                None => continue,
            }
        };
        match r {
            Ok(fd) => items.push(PackageItem::Function(fd)),
            Err(e) => lw.record(e),
        }
    }
    Some(Description::Package(PackageDeclaration {
        attrs: Vec::new(),
        lifetime: None,
        name: id("sc_user"),
        items,
        endlabel: None,
        span: sp(),
    }))
}

/// The port class of an interface: `sc_port<IF, N>` and `sc_export<IF>`
/// are objects of it (§5.12, §5.14). A binding names a channel (its
/// adapter object for the interface) or another port or export, followed
/// when the port is used, so bindings may be made in any order.
pub fn port_class_name(iface: &str) -> String {
    format!("__sc_port__{}", iface.trim_start_matches("sc_c_"))
}

#[cfg(test)]
pub fn port_class_for_test(iface: &str) -> String {
    port_class(iface)
}

fn port_class(iface: &str) -> String {
    let p = port_class_name(iface);
    format!(
        "class {p} extends scrt_port_base;
  {iface} ch[$];
  {p} up[$];
  int order[$];
  {iface} res[$];
  bit done;
  function new(string n = \"\", bit ex = 0); name = n; is_export = ex; scrt_ports.push_back(this); endfunction
  virtual function int nbound(); return order.size(); endfunction
  function void bind_ch({iface} c); order.push_back(ch.size()); ch.push_back(c); done = 0; endfunction
  function void bind_up({p} q); order.push_back(-(up.size() + 1)); up.push_back(q); done = 0; endfunction
  function void all(ref {iface} out[$]);
    foreach (order[k])
      if (order[k] >= 0) out.push_back(ch[order[k]]);
      else up[-order[k] - 1].all(out);
  endfunction
  function {iface} get(int i = 0);
    if (!done) begin res.delete(); all(res); done = 1; end
    if (i < 0 || i >= res.size()) begin
      $write(\"\\nError: (E112) get interface failed: port is not bound: port '%s' (sc_port)\\n\", name);
      $__sc_exit(1);
      return null;
    end
    return res[i];
  endfunction
  function int size();
    if (!done) begin res.delete(); all(res); done = 1; end
    return res.size();
  endfunction
endclass
"
    )
}

/// `int T::count = 0;` — the initial values of static members.
fn static_definitions(lw: &Lw) -> BTreeMap<(String, String), sc::Expr> {
    fn walk(items: &[sc::Item], out: &mut BTreeMap<(String, String), sc::Expr>) {
        for item in items {
            match item {
                sc::Item::Var(v) => {
                    for d in &v.declarators {
                        let Some((c, m)) = d.name.name.rsplit_once("::") else {
                            continue;
                        };
                        let init = match &d.init {
                            Some(sc::Initializer::Assign(e)) => Some(e.clone()),
                            Some(sc::Initializer::Paren(a) | sc::Initializer::Brace(a)) => {
                                a.first().cloned()
                            }
                            None => None,
                        };
                        if let Some(e) = init {
                            let c = c.rsplit("::").next().unwrap_or(c);
                            out.insert((c.to_string(), m.to_string()), e);
                        }
                    }
                }
                sc::Item::Namespace { items, .. } | sc::Item::ExternBlock { items, .. } => {
                    walk(items, out)
                }
                _ => {}
            }
        }
    }
    let mut out = BTreeMap::new();
    for r in lw.prog.results {
        walk(&r.unit.items, &mut out);
    }
    out
}

/// Enter a class's scope: its members are names, its member functions
/// callable by name.
fn enter_class(lw: &mut Lw, sig: &ClassSig) {
    let mut syms = BTreeMap::new();
    for (n, f) in &sig.fields {
        syms.insert(
            n.clone(),
            Sym {
                // An sc_event member is an event (notify, wait).
                kind: if matches!(f.ty, Ty::Event) {
                    SymKind::Event
                } else {
                    SymKind::Var
                },
                ty: f.ty.clone(),
                sv: escape_sv(n),
            },
        );
    }
    let mut funcs = BTreeMap::new();
    for (n, overloads) in &sig.methods {
        for o in overloads {
            funcs.insert(o.sv.clone(), o.sig.clone());
            if overloads.len() == 1 {
                funcs.insert(n.clone(), o.sig.clone());
            }
        }
    }
    lw.m = ModCtx {
        name: sig.cpp.clone(),
        syms,
        funcs,
        class: Some(sig.sv.clone()),
        ..Default::default()
    };
}

fn lower_class(
    lw: &mut Lw,
    uc: &UserClass,
    statics: &BTreeMap<(String, String), sc::Expr>,
) -> R<crate::ast::decl::ClassDeclaration> {
    let (name, cpp, tu, c) = (uc.name.as_str(), uc.cpp.as_str(), uc.tu, uc.decl);
    // C++ runs destructors at `delete` and at the end of every object's
    // lifetime; only one that does nothing can be left out.
    let dtors = c
        .members
        .iter()
        .filter_map(|m| match m {
            sc::Member::Destructor(f) => Some((tu, f)),
            _ => None,
        })
        .chain(
            lw.prog
                .out_of_class
                .get(cpp)
                .into_iter()
                .flatten()
                .filter(|(_, f)| f.base_name().starts_with('~'))
                .map(|(t, f)| (*t, *f)),
        )
        .collect::<Vec<_>>();
    for (t, f) in dtors {
        if f.body.as_ref().is_some_and(|b| !b.stmts.is_empty()) {
            lw.tu = t;
            return lw.err(
                f.span,
                format!("the destructor of '{}' has statements; destructors are not run in simulation", name),
            );
        }
    }
    lw.tu = tu;
    let Some(sig) = lw.prog.user_classes.borrow().get(&class_sv(name)).cloned() else {
        return lw.err(c.span, format!("class '{}' could not be lowered", name));
    };
    enter_class(lw, &sig);
    let mut items: Vec<ClassItem> = Vec::new();
    // Members.
    for f in &sig.own_fields {
        let fs = &sig.fields[f];
        let (dt, dims) = sv_type(&fs.ty);
        let init = if fs.is_static {
            match statics.get(&(cpp.to_string(), f.clone())) {
                Some(e) => Some(lw.expr_for(e, &fs.ty)?),
                None => {
                    // `static const int N = 4;` in the class body.
                    in_class_init(c, f).map(|e| lw.expr_for(&e, &fs.ty)).transpose()?
                }
            }
        } else {
            None
        };
        items.push(ClassItem::Property(ClassProperty {
            qualifiers: if fs.is_static {
                vec![ClassQualifier::Static]
            } else {
                Vec::new()
            },
            data_type: dt,
            declarators: vec![var_declarator(&escape_sv(f), dims, init)],
            span: sp(),
        }));
    }
    // An interface's events, aliased by the channel implementing it.
    for e in &sig.events {
        let inherited = sig
            .base
            .as_ref()
            .and_then(|b| lw.prog.user_classes.borrow().get(b).map(|bs| bs.events.contains(e)))
            .unwrap_or(false);
        if !inherited {
            items.push(ClassItem::Property(ClassProperty {
                qualifiers: Vec::new(),
                data_type: simple_t(crate::ast::types::SimpleType::Event),
                declarators: vec![var_declarator(&format!("__sc_ev_{}", e), Vec::new(), None)],
                span: sp(),
            }));
        }
    }
    // `new` allocates the member objects (construction is __sc_init).
    let mut alloc = Vec::new();
    for f in &sig.own_fields {
        let fs = &sig.fields[f];
        if !fs.is_static {
            alloc.extend(allocate(
                member(ex(crate::ast::expr::ExprKind::This), &escape_sv(f)),
                &fs.ty,
            ));
        }
    }
    items.push(class_function(function_decl("new", void_t(), Vec::new(), alloc), false));
    // Constructors.
    let ctors = ctor_defs(lw.prog, cpp, tu, c);
    if ctors.is_empty() {
        items.push(class_function(lower_ctor(lw, &sig, c, 0, None)?, false));
    }
    for (k, (t, f)) in ctors.iter().enumerate() {
        let saved = lw.tu;
        lw.tu = *t;
        let r = lower_ctor(lw, &sig, c, k, Some(f));
        lw.tu = saved;
        items.push(class_function(r?, false));
    }
    for k in 0..sig.ctors.len() {
        items.push(factory(&sig, k, ctors.get(k).map(|(_, f)| *f), lw)?);
    }
    // Copies: member-wise, as C++'s implicit copy (or the user's
    // operator= / copy constructor).
    items.push(class_function(copy_set(&sig, lw), false));
    items.push(class_function(
        function_decl(
            "__sc_copy",
            named_t(&sig.sv, Vec::new()),
            Vec::new(),
            vec![
                var_decl(named_t(&sig.sv, Vec::new()), "__sc_c", Some(new_obj(None))),
                expr_stmt(method(
                    ident("__sc_c"),
                    "__sc_set",
                    vec![ex(crate::ast::expr::ExprKind::This)],
                )),
                ret(Some(ident("__sc_c"))),
            ],
        ),
        false,
    ));
    // Member functions.
    for (t, f) in member_defs(lw.prog, cpp, tu, c) {
        if sig.events.contains(f.base_name()) {
            continue;
        }
        if f.body.is_none() {
            // Pure virtual or declared only: a virtual method that does
            // nothing (C++ cannot call it).
            if f.specifiers.is_virtual {
                let Some(ms) = sig.method(f.base_name(), f.params.len()).cloned() else {
                    continue;
                };
                if ms.owner != sig.sv {
                    continue;
                }
                items.push(abstract_method(lw, &ms, f)?);
            }
            continue;
        }
        let saved = lw.tu;
        lw.tu = t;
        let Some(ms) = sig.method(f.base_name(), f.params.len()).cloned() else {
            lw.tu = saved;
            continue;
        };
        let r = lower_method(lw, &ms, f);
        lw.tu = saved;
        match r {
            Ok(item) => items.push(item),
            Err(e) => lw.record(e),
        }
    }
    Ok(class_decl(&sig.sv, sig.base.as_deref(), items))
}

/// The in-class initializer of a member (`int n = 3;`, `T x{1, 2};`).
fn in_class_init(c: &sc::ClassDecl, field: &str) -> Option<sc::Expr> {
    c.members.iter().find_map(|m| match m {
        sc::Member::Field(v) => v.declarators.iter().find_map(|d| {
            if d.name.name != field {
                return None;
            }
            match &d.init {
                Some(sc::Initializer::Assign(e)) => Some(e.clone()),
                Some(sc::Initializer::Paren(a) | sc::Initializer::Brace(a)) if a.len() == 1 => {
                    Some(a[0].clone())
                }
                _ => None,
            }
        }),
        _ => None,
    })
}

/// Statements allocating the object(s) a member of type `ty` holds.
pub fn allocate(target: Expression, ty: &Ty) -> Vec<Statement> {
    match ty {
        Ty::Class(_) => vec![assign(target, new_obj(None))],
        Ty::Array(elem, _) if matches!(**elem, Ty::Class(_)) => vec![st(StatementKind::Foreach {
            array: target.clone(),
            vars: vec![Some(id("__sc_i"))],
            body: Box::new(assign(index(target, ident("__sc_i")), new_obj(None))),
        })],
        _ => Vec::new(),
    }
}

/// `function void __sc_init<k>(params)`: base class, members, body.
fn lower_ctor(
    lw: &mut Lw,
    sig: &ClassSig,
    c: &sc::ClassDecl,
    k: usize,
    f: Option<&sc::FunctionDecl>,
) -> R<crate::ast::decl::FunctionDeclaration> {
    lw.f = FnCtx {
        scopes: vec![BTreeMap::new()],
        ret: Some(Ty::Void),
        ..Default::default()
    };
    let mut ports = Vec::new();
    let mut prologue = Vec::new();
    if let Some(f) = f {
        params(lw, f, &mut ports, &mut prologue)?;
    }
    let inits: &[sc::MemInit] = f.map(|f| f.initializers.as_slice()).unwrap_or(&[]);
    let mut body = Vec::new();
    // The base class first.
    if let Some(b) = &sig.base {
        let base_cpp = b.trim_start_matches("sc_c_");
        let mi = inits.iter().find(|mi| mi.name.last_name() == base_cpp);
        let args = mi.map(|m| m.args.as_slice()).unwrap_or(&[]);
        let bsig = lw.prog.user_classes.borrow().get(b).cloned().unwrap_or_default();
        let Some(bk) = bsig.ctor(args.len()) else {
            return lw.err(c.span, format!("'{}' has no constructor taking {} arguments", base_cpp, args.len()));
        };
        let xs = lower_args(lw, args)?;
        body.push(expr_stmt(method(
            ident("super"),
            &format!("__sc_init{}", bk),
            xs,
        )));
    }
    // Members in declaration order.
    for field in &sig.own_fields {
        let fs = sig.fields[field].clone();
        if fs.is_static {
            continue;
        }
        // `this.m`: a constructor parameter may share the member's name
        // (`w(w)`).
        let target = || member(ex(crate::ast::expr::ExprKind::This), &escape_sv(field));
        let mi = inits.iter().find(|mi| mi.name.last_name() == field.as_str());
        let given: Option<Vec<sc::Expr>> = mi
            .map(|m| m.args.clone())
            .or_else(|| in_class_init(c, field).map(|e| vec![e]));
        match (&fs.ty, given) {
            (Ty::Class(cls), args) => {
                let args = args.unwrap_or_default();
                body.extend(construct_into(lw, target(), cls, &args, c.span)?);
            }
            (_, Some(args)) => match args.as_slice() {
                [] => {}
                [a] => {
                    let x = lw.expr_for(a, &fs.ty)?;
                    body.push(assign(target(), x));
                }
                [v, u] if matches!(fs.ty, Ty::Time) => {
                    let x = lw.time_value(v, u, c.span)?;
                    body.push(assign(target(), x));
                }
                _ => return lw.err(c.span, format!("initializer of '{}' is not supported", field)),
            },
            (_, None) => {}
        }
    }
    let stmts = match f.and_then(|f| f.body.as_ref()) {
        Some(b) => lw.block(&b.stmts),
        None => Vec::new(),
    };
    let mut items = std::mem::take(&mut lw.f.decls);
    items.extend(prologue);
    items.extend(body);
    items.extend(stmts);
    Ok(function_decl(
        &format!("__sc_init{}", k),
        void_t(),
        ports,
        items,
    ))
}

/// Construct the (allocated) object `target` of class `cls` from `args`:
/// a copy for one argument of the class itself, else the constructor
/// taking that many.
pub fn construct_into(
    lw: &mut Lw,
    target: Expression,
    cls: &str,
    args: &[sc::Expr],
    span: ScSpan,
) -> R<Vec<Statement>> {
    let csig = lw.prog.user_classes.borrow().get(cls).cloned();
    let Some(csig) = csig else {
        // A runtime class (the TLM payload): nothing to construct.
        return Ok(Vec::new());
    };
    if let [a] = args {
        let (x, t) = lw.expr(a)?;
        if matches!(&t, Ty::Class(c2) | Ty::Handle(c2) if lw.is_same_or_derived(c2, cls)) {
            return Ok(vec![expr_stmt(method(target, "__sc_set", vec![x]))]);
        }
    }
    let Some(k) = csig.ctor(args.len()) else {
        return lw.err(
            span,
            format!("'{}' has no constructor taking {} arguments", csig.cpp, args.len()),
        );
    };
    let xs = lower_args(lw, args)?;
    Ok(vec![expr_stmt(method(target, &format!("__sc_init{}", k), xs))])
}

fn lower_args(lw: &mut Lw, args: &[sc::Expr]) -> R<Vec<Expression>> {
    let mut out = Vec::new();
    for a in args {
        out.push(lw.expr(a)?.0);
    }
    Ok(out)
}

/// `static function T __sc_make<k>(params)`: allocate and construct.
fn factory(
    sig: &ClassSig,
    k: usize,
    f: Option<&sc::FunctionDecl>,
    lw: &mut Lw,
) -> R<ClassItem> {
    let t = || named_t(&sig.sv, Vec::new());
    let mut ports = Vec::new();
    let mut names = Vec::new();
    if let Some(f) = f {
        lw.f = FnCtx {
            scopes: vec![BTreeMap::new()],
            ..Default::default()
        };
        for (i, p) in f.params.iter().enumerate() {
            let ty = lw.ty(&p.ty, p.span)?;
            let n = format!("a{}", i);
            ports.push(fport(PortDirection::Input, sv_scalar_type(&ty), &n));
            names.push(ident(&n));
        }
    }
    let fd = function_decl(
        &format!("__sc_make{}", k),
        t(),
        ports,
        vec![
            var_decl(t(), "o", Some(new_obj(None))),
            expr_stmt(method(ident("o"), &format!("__sc_init{}", k), names)),
            ret(Some(ident("o"))),
        ],
    );
    Ok(ClassItem::Method(crate::ast::decl::ClassMethod {
        qualifiers: vec![ClassQualifier::Static],
        kind: crate::ast::decl::ClassMethodKind::Function(fd),
        span: sp(),
    }))
}

/// `function void __sc_set(T o)`: C++ copy assignment — the user's
/// `operator=` if declared, else member-wise.
fn copy_set(sig: &ClassSig, lw: &Lw) -> crate::ast::decl::FunctionDeclaration {
    let o = || ident("__sc_o");
    let this = || ex(crate::ast::expr::ExprKind::This);
    let mut body = Vec::new();
    if let Some(m) = sig
        .methods
        .get("operator=")
        .and_then(|v| v.iter().find(|m| m.owner == sig.sv))
    {
        body.push(expr_stmt(call_fn(&m.sv, vec![o()])));
    } else {
        if sig.base.is_some() {
            body.push(expr_stmt(method(ident("super"), "__sc_set", vec![o()])));
        }
        for f in &sig.own_fields {
            let fs = &sig.fields[f];
            if fs.is_static {
                continue;
            }
            let n = escape_sv(f);
            body.extend(copy_member(member(this(), &n), member(o(), &n), &fs.ty));
        }
    }
    let _ = lw;
    function_decl(
        "__sc_set",
        void_t(),
        vec![fport(PortDirection::Input, named_t(&sig.sv, Vec::new()), "__sc_o")],
        body,
    )
}

/// Copy one member value: objects into their own object, arrays of objects
/// element by element, anything else by assignment.
fn copy_member(dst: Expression, src: Expression, ty: &Ty) -> Vec<Statement> {
    match ty {
        Ty::Class(_) => vec![expr_stmt(method(dst, "__sc_set", vec![src]))],
        Ty::Array(elem, _) if matches!(**elem, Ty::Class(_)) => {
            vec![st(StatementKind::Foreach {
                array: dst.clone(),
                vars: vec![Some(id("__sc_i"))],
                body: Box::new(expr_stmt(method(
                    index(dst, ident("__sc_i")),
                    "__sc_set",
                    vec![index(src, ident("__sc_i"))],
                ))),
            })]
        }
        _ => vec![assign(dst, src)],
    }
}

/// The parameters of a member function: ports, and a prologue copying the
/// by-value objects (C++ passes a copy).
pub fn params(
    lw: &mut Lw,
    f: &sc::FunctionDecl,
    ports: &mut Vec<crate::ast::decl::FunctionPort>,
    prologue: &mut Vec<Statement>,
) -> R<()> {
    for (i, p) in f.params.iter().enumerate() {
        if is_ostream(&p.ty) {
            continue;
        }
        let ty = lw.ty(&p.ty, p.span)?;
        let pname = p
            .name
            .as_ref()
            .map_or_else(|| format!("__sc_arg{}", i), |n| escape_sv(&n.name));
        let by_ref = p.ty.ptr_ops.contains(&sc::PtrOp::LRef)
            && !p.ty.is_const
            && !matches!(ty, Ty::Class(_) | Ty::Handle(_));
        let dir = if by_ref {
            PortDirection::Ref
        } else {
            PortDirection::Input
        };
        ports.push(fport(dir, sv_scalar_type(&ty), &pname));
        if matches!(ty, Ty::Class(_))
            && !p.ty.ptr_ops.iter().any(|o| matches!(o, sc::PtrOp::LRef | sc::PtrOp::RRef))
        {
            prologue.push(assign(ident(&pname), method(ident(&pname), "__sc_copy", vec![])));
        }
        lw.f.used.insert(pname.clone());
        lw.f.scopes[0].insert(
            p.name.as_ref().map_or_else(|| pname.clone(), |n| n.name.clone()),
            Sym {
                kind: SymKind::Var,
                ty,
                sv: pname,
            },
        );
    }
    Ok(())
}

/// A member function → a class method (a task when it may block).
fn lower_method(lw: &mut Lw, ms: &MethodSig, f: &sc::FunctionDecl) -> R<ClassItem> {
    lw.f = FnCtx {
        scopes: vec![BTreeMap::new()],
        ret: Some(ms.sig.ret.clone()),
        ret_copy: returns_copy(f, &ms.sig.ret),
        is_task: ms.sig.is_task,
        ..Default::default()
    };
    let mut ports = Vec::new();
    let mut prologue = Vec::new();
    params(lw, f, &mut ports, &mut prologue)?;
    if ms.sig.is_task && !matches!(ms.sig.ret, Ty::Void) {
        lw.f.ret_var = Some("__sc_ret".to_string());
        ports.push(fport(
            PortDirection::Output,
            sv_scalar_type(&ms.sig.ret),
            "__sc_ret",
        ));
    }
    let body = f.body.as_ref().expect("defined");
    let stmts = lw.block(&body.stmts);
    let mut items = std::mem::take(&mut lw.f.decls);
    items.extend(prologue);
    items.extend(stmts);
    let mut quals = Vec::new();
    if f.specifiers.is_virtual {
        quals.push(ClassQualifier::Virtual);
    }
    if ms.is_static {
        quals.push(ClassQualifier::Static);
    }
    let kind = if ms.sig.is_task {
        crate::ast::decl::ClassMethodKind::Task(task_decl(&ms.sv, ports, items))
    } else {
        crate::ast::decl::ClassMethodKind::Function(function_decl(
            &ms.sv,
            sv_scalar_type(&ms.sig.ret),
            ports,
            items,
        ))
    };
    Ok(ClassItem::Method(crate::ast::decl::ClassMethod {
        qualifiers: quals,
        kind,
        span: sp(),
    }))
}

/// A pure virtual (or body-less virtual) member function: a virtual method
/// that returns the type's default.
fn abstract_method(lw: &mut Lw, ms: &MethodSig, f: &sc::FunctionDecl) -> R<ClassItem> {
    lw.f = FnCtx {
        scopes: vec![BTreeMap::new()],
        ..Default::default()
    };
    let mut ports = Vec::new();
    let mut prologue = Vec::new();
    params(lw, f, &mut ports, &mut prologue)?;
    if ms.sig.is_task && !matches!(ms.sig.ret, Ty::Void) {
        ports.push(fport(
            PortDirection::Output,
            sv_scalar_type(&ms.sig.ret),
            "__sc_ret",
        ));
    }
    let kind = if ms.sig.is_task {
        crate::ast::decl::ClassMethodKind::Task(task_decl(&ms.sv, ports, Vec::new()))
    } else {
        crate::ast::decl::ClassMethodKind::Function(function_decl(
            &ms.sv,
            sv_scalar_type(&ms.sig.ret),
            ports,
            Vec::new(),
        ))
    };
    Ok(ClassItem::Method(crate::ast::decl::ClassMethod {
        qualifiers: vec![ClassQualifier::Virtual],
        kind,
        span: sp(),
    }))
}

/// Whether a function returning an object by value returns a copy of it.
pub fn returns_copy(f: &sc::FunctionDecl, ret: &Ty) -> bool {
    matches!(ret, Ty::Class(_))
        && !f
            .return_ptr_ops
            .iter()
            .chain(f.return_type.iter().flat_map(|t| t.ptr_ops.iter()))
            .any(|o| matches!(o, sc::PtrOp::LRef | sc::PtrOp::RRef))
}

/// A free operator function of a class → a package function.
fn lower_free_function(
    lw: &mut Lw,
    sv_name: &str,
    f: &sc::FunctionDecl,
) -> R<crate::ast::decl::FunctionDeclaration> {
    lw.m = ModCtx::default();
    let sig = fn_sig(lw, f, false)?;
    lw.f = FnCtx {
        scopes: vec![BTreeMap::new()],
        ret: Some(sig.ret.clone()),
        ret_copy: returns_copy(f, &sig.ret),
        ..Default::default()
    };
    let mut ports = Vec::new();
    let mut prologue = Vec::new();
    params(lw, f, &mut ports, &mut prologue)?;
    let stmts = lw.block(&f.body.as_ref().expect("defined").stmts);
    let mut items = std::mem::take(&mut lw.f.decls);
    items.extend(prologue);
    items.extend(stmts);
    Ok(function_decl(sv_name, sv_scalar_type(&sig.ret), ports, items))
}

/// `std::ostream& operator<<(std::ostream& os, const T& v)` → `string
/// __sc_fmt__T(T v)`: what the function streams into `os`, as text.
fn lower_formatter(
    lw: &mut Lw,
    class: &str,
    f: &sc::FunctionDecl,
) -> R<crate::ast::decl::FunctionDeclaration> {
    lw.m = ModCtx::default();
    lw.f = FnCtx {
        scopes: vec![BTreeMap::new()],
        ret: Some(Ty::Str),
        ..Default::default()
    };
    let os = f
        .params
        .first()
        .and_then(|p| p.name.as_ref())
        .map(|n| n.name.clone())
        .unwrap_or_default();
    let sink = lw.declare_local(&os, Ty::OStream, SymKind::Var, Some(string("")));
    let _ = sink;
    let mut ports = Vec::new();
    let mut prologue = Vec::new();
    params(lw, f, &mut ports, &mut prologue)?;
    let stmts = lw.block(&f.body.as_ref().expect("defined").stmts);
    let mut items = std::mem::take(&mut lw.f.decls);
    items.extend(prologue);
    items.extend(stmts);
    Ok(function_decl(
        &format!("__sc_fmt__{}", class),
        simple_t(crate::ast::types::SimpleType::String),
        ports,
        items,
    ))
}

/// `a == b` and friends on objects: the class's operator, if it has one.
pub fn object_op(
    lw: &Lw,
    cls: &str,
    op: &str,
    a: Expression,
    b: Expression,
) -> Option<(Expression, Ty)> {
    let sig = lw.prog.user_classes.borrow().get(cls).cloned()?;
    match sig.ops.get(op)? {
        OpImpl::Method(m, t) => Some((method(a, m, vec![b]), t.clone())),
        OpImpl::Function(f, t) => Some((call_fn(f, vec![a, b]), t.clone())),
    }
}

/// The C++ spelling of a binary operator.
pub fn op_spelling(op: sc::BinaryOp) -> &'static str {
    use sc::BinaryOp as B;
    match op {
        B::Eq => "==",
        B::Ne => "!=",
        B::Lt => "<",
        B::Gt => ">",
        B::Le => "<=",
        B::Ge => ">=",
        B::Add => "+",
        B::Sub => "-",
        B::Mul => "*",
        B::Div => "/",
        B::Rem => "%",
        B::BitAnd => "&",
        B::BitOr => "|",
        B::BitXor => "^",
        B::Shl => "<<",
        B::Shr => ">>",
        _ => "",
    }
}

/// Logical negation, for `!=` from `==`.
pub fn not(e: Expression) -> Expression {
    unary(crate::ast::expr::UnaryOp::LogNot, paren(e))
}

