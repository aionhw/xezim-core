//! The design as the lowering sees it: every class, out-of-class member
//! definition, enum and constant of all translation units, merged by name
//! (a header included by several `.cpp` files defines its classes once).

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};

use super::types::Ty;
use crate::sv_parser::systemc::classify::ScObjectKind;
use crate::sv_parser::systemc::ScParseResult;
use crate::sv_parser::systemc::ast::*;

/// The elaboration and simulation callbacks (§4.4), in the order the
/// kernel calls them: (suffix of the hierarchy function, member function).
pub const CALLBACKS: [(&str, &str); 4] = [
    ("bee", "before_end_of_elaboration"),
    ("eoe", "end_of_elaboration"),
    ("sos", "start_of_simulation"),
    ("eos", "end_of_simulation"),
];

pub struct Program<'a> {
    pub results: &'a [ScParseResult],
    /// Classes by name: (translation unit, declaration, template parameters).
    pub classes: BTreeMap<String, (usize, &'a ClassDecl, Vec<TemplateParam>)>,
    /// `T::f` definitions outside class `T`.
    pub out_of_class: BTreeMap<String, Vec<(usize, &'a FunctionDecl)>>,
    pub sc_main: Option<(usize, &'a FunctionDecl)>,
    pub free_fns: BTreeMap<String, (usize, &'a FunctionDecl)>,
    pub enums: Vec<(usize, &'a EnumDecl)>,
    pub typedefs: Vec<(usize, &'a TypedefDecl)>,
    /// Namespace-scope integer constants (`const int N = 4;`).
    pub global_consts: BTreeMap<String, i64>,
    /// Per translation unit: names whose address the code takes.
    address_taken: BTreeSet<(usize, String)>,
    /// Lowered member types of each module (for `inst.member` references).
    pub module_members: RefCell<BTreeMap<String, BTreeMap<String, Ty>>>,
    /// SystemC basenames of each module's member objects (`u.clk.name()`).
    pub module_names: RefCell<BTreeMap<String, BTreeMap<String, String>>>,
    /// Each module's resolved signals and ports (member → width).
    pub module_resolved: RefCell<BTreeMap<String, BTreeMap<String, u32>>>,
    /// The user classes lowered to SV classes, by SV name (`sc_c_T`).
    pub user_classes: RefCell<BTreeMap<String, super::classes::ClassSig>>,
    /// Names of the user-class member functions that may block (tasks).
    pub blocking_methods: RefCell<BTreeSet<String>>,
    /// Classes deriving from `sc_foreign_module`: declarations of modules
    /// written in SystemVerilog, by C++ class → SV module name.
    pub foreign: BTreeMap<String, String>,
    /// Input ports some instance binds to an `sc_buffer` (directly or
    /// through a parent's port): (module class, port). Such a port also
    /// carries the buffer's write count, so it sees every write (§6.9).
    pub buffer_ports: BTreeSet<(String, String)>,
}

impl<'a> Program<'a> {
    /// Whether some module defines an elaboration or simulation callback
    /// (§4.4: `before_end_of_elaboration`, …).
    pub fn has_callbacks(&self) -> bool {
        let is_cb = |n: &str| CALLBACKS.iter().any(|(_, c)| *c == n);
        self.classes.iter().any(|(n, (_, c, _))| {
            c.members.iter().any(|m| {
                matches!(m, Member::Method(fd) if fd.body.is_some() && is_cb(fd.base_name()))
            }) || self
                .out_of_class
                .get(n)
                .is_some_and(|v| v.iter().any(|(_, fd)| is_cb(fd.base_name())))
        })
    }

    pub fn new(results: &'a [ScParseResult]) -> Self {
        let mut p = Program {
            results,
            classes: BTreeMap::new(),
            out_of_class: BTreeMap::new(),
            sc_main: None,
            free_fns: BTreeMap::new(),
            enums: Vec::new(),
            typedefs: Vec::new(),
            global_consts: BTreeMap::new(),
            address_taken: BTreeSet::new(),
            module_members: RefCell::new(BTreeMap::new()),
            module_names: RefCell::new(BTreeMap::new()),
            module_resolved: RefCell::new(BTreeMap::new()),
            user_classes: RefCell::new(BTreeMap::new()),
            blocking_methods: RefCell::new(BTreeSet::new()),
            foreign: BTreeMap::new(),
            buffer_ports: BTreeSet::new(),
        };
        for (tu, r) in results.iter().enumerate() {
            p.collect(tu, &r.unit.items, &[]);
            let mut names = BTreeSet::new();
            for item in &r.unit.items {
                scan_item(item, &mut names);
            }
            for n in names {
                p.address_taken.insert((tu, n));
            }
        }
        let foreign: Vec<(String, String)> = p
            .classes
            .iter()
            .filter(|(_, (_, c, _))| {
                c.bases
                    .iter()
                    .any(|b| b.name.last_name() == "sc_foreign_module")
            })
            .map(|(n, (_, c, _))| (n.clone(), p.hdl_name(n, c)))
            .collect();
        p.foreign.extend(foreign);
        p.scan_buffer_ports();
        p
    }

    /// Find the ports bound to an `sc_buffer`: `x.port(buf)`,
    /// `x->port.bind(buf)`, or to a port of the parent that is itself one
    /// (until no more are found).
    fn scan_buffer_ports(&mut self) {
        // Per binding scope: (own module class or None for sc_main, its
        // object declarations, the statements that bind).
        let mut scopes: Vec<(Option<String>, Vec<&'a VarDecl>, Vec<&'a Stmt>)> = Vec::new();
        for (name, entry) in &self.classes {
            let c: &'a ClassDecl = entry.1;
            if !c.sc_module {
                continue;
            }
            let decls: Vec<&VarDecl> = c
                .members
                .iter()
                .filter_map(|m| match m {
                    Member::Field(v) => Some(v),
                    _ => None,
                })
                .collect();
            let mut stmts: Vec<&Stmt> = Vec::new();
            for m in &c.members {
                if let Member::Constructor(f) = m
                    && let Some(b) = &f.body
                {
                    stmts.extend(b.stmts.iter());
                }
            }
            for &(_, f) in self.out_of_class.get(name).into_iter().flatten() {
                let f: &'a FunctionDecl = f;
                if f.base_name() == name
                    && let Some(b) = &f.body
                {
                    stmts.extend(b.stmts.iter());
                }
            }
            scopes.push((Some(name.clone()), decls, stmts));
        }
        if let Some((_, f)) = self.sc_main
            && let Some(b) = &f.body
        {
            let decls = b
                .stmts
                .iter()
                .filter_map(|s| match s {
                    Stmt::Decl(v) => Some(v),
                    _ => None,
                })
                .collect();
            scopes.push((None, decls, b.stmts.iter().collect()));
        }
        loop {
            let mut found = Vec::new();
            for (own, decls, stmts) in &scopes {
                let class_of = |n: &str| -> Option<String> {
                    decls
                        .iter()
                        .find(|v| v.declarators.iter().any(|d| d.name.name == n))
                        .and_then(|v| v.ty.name())
                        .map(|q| q.last_name().to_string())
                };
                let is_buffer = |n: &str| {
                    decls.iter().any(|v| {
                        ScObjectKind::of(&v.ty) == ScObjectKind::Buffer
                            && v.declarators.iter().any(|d| d.name.name == n)
                    }) || own
                        .as_ref()
                        .is_some_and(|o| self.buffer_ports.contains(&(o.clone(), n.to_string())))
                };
                let inst = |e: &Expr| -> Option<String> {
                    let e = match &e.kind {
                        ExprKind::Unary {
                            op: UnaryOp::Deref,
                            operand,
                        } => operand.as_ref(),
                        _ => e,
                    };
                    class_of(e.as_name()?.last_name())
                };
                for s in stmts {
                    visit_stmt(s, &mut |e| {
                        let ExprKind::Call { callee, args } = &e.kind else {
                            return;
                        };
                        let [a] = args.as_slice() else { return };
                        let Some(arg) = a.as_name().map(|q| q.last_name().to_string()) else {
                            return;
                        };
                        if !is_buffer(&arg) {
                            return;
                        }
                        let ExprKind::Member { base, name, .. } = &callee.kind else {
                            return;
                        };
                        let bound = if name.ident.name == "bind"
                            && let ExprKind::Member {
                                base: b2, name: port, ..
                            } = &base.kind
                        {
                            inst(b2).map(|c| (c, port.ident.name.clone()))
                        } else {
                            inst(base).map(|c| (c, name.ident.name.clone()))
                        };
                        if let Some(b) = bound {
                            found.push(b);
                        }
                    });
                }
            }
            let before = self.buffer_ports.len();
            self.buffer_ports.extend(found);
            if self.buffer_ports.len() == before {
                break;
            }
        }
    }

    /// The SV module a foreign-module class stands for: the name given to
    /// `sc_foreign_module(nm, "name", …)` or returned by `hdl_name()`, else
    /// the class name.
    fn hdl_name(&self, class: &str, c: &ClassDecl) -> String {
        let lit = |e: &Expr| match &e.kind {
            ExprKind::StringLit { value, .. } => Some(value.clone()),
            _ => None,
        };
        let ctors = c
            .members
            .iter()
            .filter_map(|m| match m {
                Member::Constructor(f) => Some(f),
                _ => None,
            })
            .chain(
                self.out_of_class
                    .get(class)
                    .into_iter()
                    .flatten()
                    .map(|(_, f)| *f)
                    .filter(|f| f.base_name() == class),
            );
        for f in ctors {
            for mi in &f.initializers {
                if mi.name.last_name() == "sc_foreign_module"
                    && let Some(n) = mi.args.get(1).and_then(lit)
                {
                    return n;
                }
            }
        }
        for m in &c.members {
            if let Member::Method(f) = m
                && f.base_name() == "hdl_name"
                && let Some(b) = &f.body
                && let [Stmt::Return(Some(e), _)] = b.stmts.as_slice()
                && let Some(n) = lit(e)
            {
                return n;
            }
        }
        class.to_string()
    }

    /// The SV module an instance of class `module` instantiates.
    pub fn sv_module_name<'s>(&'s self, module: &'s str) -> &'s str {
        self.foreign.get(module).map_or(module, |s| s.as_str())
    }

    fn collect(&mut self, tu: usize, items: &'a [Item], tparams: &[TemplateParam]) {
        for item in items {
            match item {
                Item::Class(c) => self.add_class(tu, c, tparams.to_vec()),
                Item::Template { params, item, .. } => {
                    self.collect(tu, std::slice::from_ref(item.as_ref()), params)
                }
                Item::Namespace { items, .. } | Item::ExternBlock { items, .. } => {
                    self.collect(tu, items, &[])
                }
                Item::Function(f) => {
                    let n = f.name.segments.len();
                    if n >= 2 {
                        let class = f.name.segments[n - 2].ident.name.clone();
                        if f.body.is_some() {
                            self.out_of_class.entry(class).or_default().push((tu, f));
                        }
                    } else if f.base_name() == "sc_main" && f.body.is_some() {
                        self.sc_main = Some((tu, f));
                    } else if f.body.is_some() {
                        self.free_fns
                            .entry(f.base_name().to_string())
                            .or_insert((tu, f));
                    }
                }
                Item::Enum(e) => self.enums.push((tu, e)),
                Item::Typedef(t) => self.typedefs.push((tu, t)),
                Item::Var(v) if v.ty.is_const || v.specifiers.is_constexpr => {
                    for d in &v.declarators {
                        if let Some(Initializer::Assign(Expr {
                            kind: ExprKind::IntLit { value: Some(x), .. },
                            ..
                        })) = &d.init
                        {
                            self.global_consts.insert(d.name.name.clone(), *x as i64);
                        }
                    }
                }
                _ => {}
            }
        }
    }

    fn add_class(&mut self, tu: usize, c: &'a ClassDecl, tparams: Vec<TemplateParam>) {
        if let Some(n) = c.name_str() {
            self.classes
                .entry(n.to_string())
                .or_insert((tu, c, tparams));
        }
        for m in &c.members {
            if let Member::NestedClass(n) = m {
                self.add_class(tu, n, Vec::new());
            }
        }
    }

    pub fn is_module(&self, name: &str) -> bool {
        self.classes.get(name).is_some_and(|(_, c, _)| c.sc_module)
            || self.foreign.contains_key(name)
            || self.is_prim_channel(name)
    }

    /// A primitive channel (§5.15): derived from `sc_prim_channel`, lowered
    /// like a module (it has members, an update phase and is bound to).
    pub fn is_prim_channel(&self, name: &str) -> bool {
        let mut cur = name.to_string();
        for _ in 0..32 {
            let Some((_, c, _)) = self.classes.get(&cur) else {
                return false;
            };
            if c.bases.iter().any(|b| b.name.last_name() == "sc_prim_channel") {
                return true;
            }
            match c.bases.first() {
                Some(b) => cur = b.name.last_name().to_string(),
                None => return false,
            }
        }
        false
    }

    pub fn address_taken(&self, name: &str, tu: usize) -> bool {
        self.address_taken.contains(&(tu, name.to_string()))
    }

    pub fn module_member_ty(&self, module: &str, member: &str) -> Option<Ty> {
        self.module_members
            .borrow()
            .get(module)?
            .get(member)
            .cloned()
    }

    /// The return type of a runtime class method (`scrt_tlm_gp`).
    pub fn class_method_ret(&self, class: &str, m: &str) -> Option<Ty> {
        if class != "scrt_tlm_gp" {
            return None;
        }
        let u32_ = Ty::Int {
            bits: 32,
            signed: false,
            ch: false,
        };
        Some(match m {
            "get_command" | "get_response_status" => Ty::int32(),
            "get_address" => Ty::Int {
                bits: 64,
                signed: false,
                ch: false,
            },
            "get_data_ptr" | "get_byte_enable_ptr" => Ty::Ptr { elem: 1 },
            "get_data_length" | "get_streaming_width" | "get_byte_enable_length" => u32_,
            "is_dmi_allowed" | "is_response_ok" | "is_response_error" | "is_read" | "is_write"
            | "has_mm" => Ty::Bool,
            "get_response_string" => Ty::Str,
            "set_command"
            | "set_address"
            | "set_data_ptr"
            | "set_data_length"
            | "set_streaming_width"
            | "set_byte_enable_ptr"
            | "set_byte_enable_length"
            | "set_dmi_allowed"
            | "set_response_status"
            | "set_read"
            | "set_write"
            | "acquire"
            | "release"
            | "reset" => Ty::Void,
            _ => return None,
        })
    }

    /// The type of a user class's member.
    pub fn class_field_ty(&self, class: &str, field: &str) -> Option<Ty> {
        self.user_classes
            .borrow()
            .get(class)?
            .fields
            .get(field)
            .map(|f| f.ty.clone())
    }

    pub fn free_fn_sig(&self, _name: &str) -> Option<Ty> {
        None
    }
}

// ---- address-taken scan ------------------------------------------------------

fn scan_item(item: &Item, out: &mut BTreeSet<String>) {
    match item {
        Item::Class(c) => scan_class(c, out),
        Item::Function(f) => scan_fn(f, out),
        Item::Template { item, .. } => scan_item(item, out),
        Item::Namespace { items, .. } | Item::ExternBlock { items, .. } => {
            for i in items {
                scan_item(i, out);
            }
        }
        _ => {}
    }
}

fn scan_class(c: &ClassDecl, out: &mut BTreeSet<String>) {
    for m in &c.members {
        match m {
            Member::Method(f) | Member::Constructor(f) | Member::Destructor(f) => scan_fn(f, out),
            Member::NestedClass(n) => scan_class(n, out),
            Member::ScProcessImp { method, .. } => scan_fn(method, out),
            _ => {}
        }
    }
}

fn scan_fn(f: &FunctionDecl, out: &mut BTreeSet<String>) {
    if let Some(b) = &f.body {
        for s in &b.stmts {
            visit_stmt(s, &mut |e| scan_expr(e, out));
        }
    }
}

/// Names whose address an expression takes (not recursive: `visit_*` calls
/// this on every subexpression).
fn scan_expr(e: &Expr, out: &mut BTreeSet<String>) {
    use ExprKind as K;
    match &e.kind {
        K::Unary {
            op: UnaryOp::AddrOf,
            operand,
        } => match &operand.kind {
            K::Name(q) if q.segments.len() == 1 => {
                out.insert(q.last_name().to_string());
            }
            K::Index { base, .. } => {
                if let Some(q) = base.as_name() {
                    out.insert(q.last_name().to_string());
                }
            }
            _ => {}
        },
        K::Call { callee, args } => {
            // Arrays passed to the C memory functions decay to pointers.
            if let Some(q) = callee.as_name()
                && matches!(q.last_name(), "memcpy" | "memset" | "memcmp")
            {
                for a in args.iter().take(2) {
                    if let Some(n) = a.as_name() {
                        out.insert(n.last_name().to_string());
                    }
                }
            }
        }
        _ => {}
    }
}

/// Whether the statements call any of `names` (unqualified).
pub fn calls_any(stmts: &[Stmt], names: &[&str]) -> bool {
    let mut found = false;
    for s in stmts {
        visit_stmt(s, &mut |e| {
            if let ExprKind::Call { callee, .. } = &e.kind
                && let Some(q) = callee.as_name()
                && names.contains(&q.last_name())
            {
                found = true;
            }
        });
    }
    found
}

/// Calls `f` on every expression of a statement, subexpressions included.
fn visit_stmt(s: &Stmt, f: &mut dyn FnMut(&Expr)) {
    let cond = |c: &Condition, f: &mut dyn FnMut(&Expr)| {
        if let Condition::Expr(e) = c {
            visit_expr(e, f);
        }
    };
    match s {
        Stmt::Block(b) => b.stmts.iter().for_each(|s| visit_stmt(s, f)),
        Stmt::Decl(v) => {
            for d in &v.declarators {
                match &d.init {
                    Some(Initializer::Assign(e)) => visit_expr(e, f),
                    Some(Initializer::Paren(a) | Initializer::Brace(a)) => {
                        a.iter().for_each(|e| visit_expr(e, f))
                    }
                    _ => {}
                }
            }
        }
        Stmt::Expr(e) => visit_expr(e, f),
        Stmt::If {
            init,
            cond: c,
            then_branch,
            else_branch,
            ..
        } => {
            if let Some(i) = init {
                visit_stmt(i, f);
            }
            cond(c, f);
            visit_stmt(then_branch, f);
            if let Some(e) = else_branch {
                visit_stmt(e, f);
            }
        }
        Stmt::Switch { arms, cond: c, .. } => {
            cond(c, f);
            for a in arms {
                a.body.iter().for_each(|s| visit_stmt(s, f));
            }
        }
        Stmt::For {
            init,
            cond: c,
            step,
            body,
            ..
        } => {
            if let Some(i) = init {
                visit_stmt(i, f);
            }
            if let Some(c) = c {
                cond(c, f);
            }
            if let Some(s) = step {
                visit_expr(s, f);
            }
            visit_stmt(body, f);
        }
        Stmt::RangeFor { range, body, .. } => {
            visit_expr(range, f);
            visit_stmt(body, f);
        }
        Stmt::While { cond: c, body, .. } => {
            cond(c, f);
            visit_stmt(body, f);
        }
        Stmt::DoWhile { body, cond, .. } => {
            visit_stmt(body, f);
            visit_expr(cond, f);
        }
        Stmt::Return(Some(e), _) => visit_expr(e, f),
        _ => {}
    }
}

fn visit_expr(e: &Expr, f: &mut dyn FnMut(&Expr)) {
    use ExprKind as K;
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
