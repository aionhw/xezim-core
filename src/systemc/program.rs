//! The design as the lowering sees it: every class, out-of-class member
//! definition, enum and constant of all translation units, merged by name
//! (a header included by several `.cpp` files defines its classes once).

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};

use super::types::Ty;
use crate::sv_parser::systemc::ScParseResult;
use crate::sv_parser::systemc::ast::*;

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
}

impl<'a> Program<'a> {
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
        p
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

    pub fn class_field_ty(&self, _class: &str, _field: &str) -> Option<Ty> {
        None
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
            scan_stmt(s, out);
        }
    }
}

fn scan_stmt(s: &Stmt, out: &mut BTreeSet<String>) {
    match s {
        Stmt::Block(b) => b.stmts.iter().for_each(|s| scan_stmt(s, out)),
        Stmt::Decl(v) => {
            for d in &v.declarators {
                if let Some(Initializer::Assign(e)) = &d.init {
                    scan_expr(e, out);
                }
                if let Some(Initializer::Paren(a) | Initializer::Brace(a)) = &d.init {
                    a.iter().for_each(|e| scan_expr(e, out));
                }
            }
        }
        Stmt::Expr(e) => scan_expr(e, out),
        Stmt::If {
            init,
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            if let Some(i) = init {
                scan_stmt(i, out);
            }
            if let Condition::Expr(e) = cond.as_ref() {
                scan_expr(e, out);
            }
            scan_stmt(then_branch, out);
            if let Some(e) = else_branch {
                scan_stmt(e, out);
            }
        }
        Stmt::Switch { arms, cond, .. } => {
            if let Condition::Expr(e) = cond.as_ref() {
                scan_expr(e, out);
            }
            for a in arms {
                a.body.iter().for_each(|s| scan_stmt(s, out));
            }
        }
        Stmt::For {
            init,
            cond,
            step,
            body,
            ..
        } => {
            if let Some(i) = init {
                scan_stmt(i, out);
            }
            if let Some(c) = cond
                && let Condition::Expr(e) = c.as_ref()
            {
                scan_expr(e, out);
            }
            if let Some(s) = step {
                scan_expr(s, out);
            }
            scan_stmt(body, out);
        }
        Stmt::RangeFor { range, body, .. } => {
            scan_expr(range, out);
            scan_stmt(body, out);
        }
        Stmt::While { cond, body, .. } => {
            if let Condition::Expr(e) = cond.as_ref() {
                scan_expr(e, out);
            }
            scan_stmt(body, out);
        }
        Stmt::DoWhile { body, cond, .. } => {
            scan_stmt(body, out);
            scan_expr(cond, out);
        }
        Stmt::Return(Some(e), _) => scan_expr(e, out),
        _ => {}
    }
}

fn scan_expr(e: &Expr, out: &mut BTreeSet<String>) {
    use ExprKind as K;
    match &e.kind {
        K::Unary {
            op: UnaryOp::AddrOf,
            operand,
        } => {
            match &operand.kind {
                K::Name(q) if q.segments.len() == 1 => {
                    out.insert(q.last_name().to_string());
                }
                K::Index { base, .. } => {
                    if let Some(q) = base.as_name() {
                        out.insert(q.last_name().to_string());
                    }
                }
                _ => {}
            }
            scan_expr(operand, out);
        }
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
            scan_expr(callee, out);
            args.iter().for_each(|a| scan_expr(a, out));
        }
        K::Binary { lhs, rhs, .. } | K::Assign { lhs, rhs, .. } => {
            scan_expr(lhs, out);
            scan_expr(rhs, out);
        }
        K::Unary { operand, .. } | K::Postfix { operand, .. } => scan_expr(operand, out),
        K::Conditional {
            cond,
            then_expr,
            else_expr,
        } => {
            scan_expr(cond, out);
            scan_expr(then_expr, out);
            scan_expr(else_expr, out);
        }
        K::Index { base, index } => {
            scan_expr(base, out);
            scan_expr(index, out);
        }
        K::Member { base, .. } => scan_expr(base, out),
        K::Cast { expr, .. } | K::Paren(expr) => scan_expr(expr, out),
        _ => {}
    }
}
