//! §6.6.7: "A resolution function shall be automatic (or preserve no state
//! information)". A static resolver preserves no state when every static
//! variable it reads -- its locals and its implicit return variable -- was
//! written earlier in the same call on every path. This is a conservative
//! definite-assignment walk: any construct it does not model counts as a read
//! of every static variable not yet written, so it can reject a stateless
//! function but never accepts one that carries a value between calls.

use super::ElaboratedModule;
use crate::ast::decl::FunctionDeclaration;
use crate::ast::expr::{AssignmentPatternItem, ExprKind, Expression};
use crate::ast::stmt::{ForInit, Statement, StatementKind};
use crate::ast::types::{DataType, Lifetime, StructUnionKind};
use crate::hasher::{HashMap, HashSet};

/// Callee nesting the walk follows before it gives up and rejects.
const MAX_CALL_DEPTH: usize = 8;

/// `Err` describes the first static variable the function (or a static
/// function it calls) reads before writing it in the same call.
pub(super) fn static_carried_variable(
    elab: &ElaboratedModule,
    fd: &FunctionDeclaration,
) -> Result<(), String> {
    let mut visiting = HashSet::default();
    check_function(elab, fd, &mut visiting, 0)
}

fn check_function(
    elab: &ElaboratedModule,
    fd: &FunctionDeclaration,
    visiting: &mut HashSet<String>,
    depth: usize,
) -> Result<(), String> {
    let fname = fd.name.name.name.clone();
    if depth > MAX_CALL_DEPTH {
        return Err(format!("the calls nested below '{fname}'"));
    }
    // A recursive static call re-enters the same storage; the outer check
    // already covers the body.
    if !visiting.insert(fname.clone()) {
        return Ok(());
    }
    let mut decls = vec![(fname.clone(), &fd.return_type)];
    // The implicit return variable (§13.4.1) is static in a static function.
    for s in fd.items.iter() {
        collect_static_decls(s, &mut decls);
    }
    let mut stateful = HashSet::default();
    let mut members = HashMap::default();
    for (name, dt) in decls {
        // A struct variable is written as a whole once each member is.
        if let DataType::Struct(su) = super::resolve_typedef_chain(dt, &elab.typedef_types)
            && su.kind == StructUnionKind::Struct
        {
            let names: Vec<String> = su
                .members
                .iter()
                .flat_map(|m| m.declarators.iter().map(|d| d.name.name.clone()))
                .collect();
            if !names.is_empty() {
                members.insert(name.clone(), names);
            }
        }
        stateful.insert(name);
    }
    let mut walk = Walk {
        elab,
        stateful,
        members,
        carried: None,
        visiting,
        depth,
    };
    let mut set = Some(HashSet::default());
    for s in fd.items.iter() {
        set = walk.stmt(s, set);
    }
    // Falling off the end returns the implicit return variable.
    if let Some(s) = &set
        && !walk.written(&fname, s)
        && walk.carried.is_none()
    {
        walk.carried = Some(fname.clone());
    }
    walk.visiting.remove(&fname);
    match walk.carried {
        None => Ok(()),
        Some(v) if v.contains('\'') => Err(v),
        Some(v) if v == fname => Err(format!("the return variable '{v}' of '{fname}'")),
        Some(v) => Err(format!("'{v}' of '{fname}'")),
    }
}

/// Names declared without `automatic` anywhere in the body. Loop variables
/// declared in a `for` header and `foreach` indices are automatic (§12.7).
fn collect_static_decls<'a>(s: &'a Statement, out: &mut Vec<(String, &'a DataType)>) {
    match &s.kind {
        StatementKind::VarDecl {
            data_type,
            lifetime,
            declarators,
        } if *lifetime != Some(Lifetime::Automatic) => {
            for d in declarators {
                out.push((d.name.name.clone(), data_type));
            }
        }
        StatementKind::If {
            then_stmt,
            else_stmt,
            ..
        } => {
            collect_static_decls(then_stmt, out);
            if let Some(e) = else_stmt {
                collect_static_decls(e, out);
            }
        }
        StatementKind::Case { items, .. } => {
            for it in items {
                collect_static_decls(&it.stmt, out);
            }
        }
        StatementKind::For { body, .. }
        | StatementKind::Foreach { body, .. }
        | StatementKind::While { body, .. }
        | StatementKind::DoWhile { body, .. }
        | StatementKind::Repeat { body, .. }
        | StatementKind::Forever { body } => collect_static_decls(body, out),
        StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
            for s in stmts.iter() {
                collect_static_decls(s, out);
            }
        }
        _ => {}
    }
}

/// `None` is an unreachable point (after `return`, `break` or `continue`),
/// where every variable counts as written. A member written on its own is
/// recorded as `v.m`.
type Written = Option<HashSet<String>>;

struct Walk<'a> {
    elab: &'a ElaboratedModule,
    stateful: HashSet<String>,
    /// Member names of the static struct variables.
    members: HashMap<String, Vec<String>>,
    carried: Option<String>,
    visiting: &'a mut HashSet<String>,
    depth: usize,
}

fn meet(a: Written, b: Written) -> Written {
    match (a, b) {
        (None, x) | (x, None) => x,
        (Some(a), Some(b)) => Some(a.intersection(&b).cloned().collect()),
    }
}

/// `x.m` for a member select of a plain variable, `x` for the variable.
fn member_path(e: &Expression) -> Option<(&str, Option<&str>)> {
    match &e.kind {
        ExprKind::Ident(h) if h.root.is_none() => match h.path.as_slice() {
            [v] if v.selects.is_empty() => Some((v.name.name.as_str(), None)),
            [v, m] if v.selects.is_empty() && m.selects.is_empty() => {
                Some((v.name.name.as_str(), Some(m.name.name.as_str())))
            }
            _ => None,
        },
        ExprKind::MemberAccess { expr, member } => match member_path(expr)? {
            (v, None) => Some((v, Some(member.name.as_str()))),
            _ => None,
        },
        _ => None,
    }
}

impl Walk<'_> {
    fn written(&self, name: &str, set: &HashSet<String>) -> bool {
        set.contains(name)
            || self
                .members
                .get(name)
                .is_some_and(|ms| ms.iter().all(|m| set.contains(&format!("{name}.{m}"))))
    }

    fn note(&mut self, name: &str) {
        if self.carried.is_none() {
            self.carried = Some(name.to_string());
        }
    }

    /// An unmodelled construct: it may read any static variable.
    fn opaque(&mut self, set: &HashSet<String>) {
        if self.carried.is_some() {
            return;
        }
        let mut open: Vec<&String> = self
            .stateful
            .iter()
            .filter(|v| !self.written(v, set))
            .collect();
        open.sort();
        if let Some(v) = open.first() {
            self.carried = Some((*v).clone());
        }
    }

    fn stmt(&mut self, s: &Statement, set: Written) -> Written {
        let mut set = set?;
        match &s.kind {
            StatementKind::Null | StatementKind::Typedef(_) | StatementKind::ParamDecl { .. } => {}
            StatementKind::Expr(e) => self.read(e, &mut set),
            StatementKind::BlockingAssign { lvalue, rvalue } => {
                self.read(rvalue, &mut set);
                self.write(lvalue, &mut set);
            }
            StatementKind::If {
                condition,
                then_stmt,
                else_stmt,
                ..
            } => {
                self.read(condition, &mut set);
                let t = self.stmt(then_stmt, Some(set.clone()));
                let e = match else_stmt {
                    Some(e) => self.stmt(e, Some(set)),
                    None => Some(set),
                };
                return meet(t, e);
            }
            StatementKind::Case { expr, items, .. } => {
                self.read(expr, &mut set);
                // `None` is the identity of `meet`.
                let mut out: Written = None;
                let mut has_default = false;
                for it in items {
                    has_default |= it.is_default;
                    if it.pattern.is_some() {
                        self.opaque(&set);
                    }
                    let mut arm = set.clone();
                    for p in &it.patterns {
                        self.read(p, &mut arm);
                    }
                    out = meet(out, self.stmt(&it.stmt, Some(arm)));
                }
                if !has_default {
                    out = meet(out, Some(set));
                }
                return out;
            }
            StatementKind::For {
                init,
                condition,
                step,
                body,
            } => {
                for i in init {
                    match i {
                        ForInit::VarDecl { init, .. } => self.read(init, &mut set),
                        ForInit::Assign { lvalue, rvalue } => {
                            self.read(rvalue, &mut set);
                            self.write(lvalue, &mut set);
                        }
                    }
                }
                if let Some(c) = condition {
                    self.read(c, &mut set);
                }
                // The body may run zero times, and a later iteration starts
                // with at least what this one had written.
                if let Some(mut after) = self.stmt(body, Some(set.clone())) {
                    for e in step {
                        self.read(e, &mut after);
                    }
                }
            }
            StatementKind::Foreach { array, body, .. } => {
                self.read(array, &mut set);
                self.stmt(body, Some(set.clone()));
            }
            StatementKind::While { condition, body } => {
                self.read(condition, &mut set);
                self.stmt(body, Some(set.clone()));
            }
            StatementKind::DoWhile { body, condition } => {
                if let Some(mut after) = self.stmt(body, Some(set.clone())) {
                    self.read(condition, &mut after);
                }
            }
            StatementKind::Repeat { count, body } => {
                self.read(count, &mut set);
                self.stmt(body, Some(set.clone()));
            }
            StatementKind::SeqBlock { stmts, .. } => {
                let mut cur = Some(set);
                for s in stmts.iter() {
                    cur = self.stmt(s, cur);
                }
                return cur;
            }
            StatementKind::VarDecl {
                lifetime,
                declarators,
                ..
            } => {
                for d in declarators {
                    if let Some(init) = &d.init {
                        self.read(init, &mut set);
                        // A static initializer runs once, before time 0
                        // (§6.21); only an automatic one writes on each call.
                        if *lifetime == Some(Lifetime::Automatic) {
                            set.insert(d.name.name.clone());
                        }
                    }
                }
            }
            StatementKind::Return(e) => {
                match e {
                    Some(e) => self.read(e, &mut set),
                    None => self.opaque(&set),
                }
                return None;
            }
            StatementKind::Break | StatementKind::Continue => return None,
            _ => self.opaque(&set),
        }
        Some(set)
    }

    /// The target of an assignment. Only a whole-variable write counts as
    /// written; a select writes part of it and reads its index expressions.
    fn write(&mut self, lv: &Expression, set: &mut HashSet<String>) {
        if let Some((v, m)) = member_path(lv) {
            set.insert(match m {
                Some(m) => format!("{v}.{m}"),
                None => v.to_string(),
            });
            return;
        }
        match &lv.kind {
            ExprKind::Ident(h) if h.root.is_none() => {
                for seg in &h.path {
                    for sel in &seg.selects {
                        self.read(sel, set);
                    }
                }
                if h.path.len() == 1
                    && h.path[0].selects.is_empty()
                    && let Some(seg) = h.path.first()
                {
                    set.insert(seg.name.name.clone());
                }
            }
            ExprKind::Ident(_) => {}
            ExprKind::Paren(e) => self.write(e, set),
            ExprKind::Concatenation(parts) => {
                for p in parts {
                    self.write(p, set);
                }
            }
            ExprKind::Index { expr, index } => {
                self.read(index, set);
                self.write_part(expr, set);
            }
            ExprKind::RangeSelect {
                expr, left, right, ..
            } => {
                self.read(left, set);
                self.read(right, set);
                self.write_part(expr, set);
            }
            ExprKind::MemberAccess { expr, .. } => self.write_part(expr, set),
            _ => self.opaque(set),
        }
    }

    /// The variable under a select is written only in part: read the select
    /// expressions, but neither read nor write the variable itself.
    fn write_part(&mut self, lv: &Expression, set: &mut HashSet<String>) {
        match &lv.kind {
            ExprKind::Ident(h) => {
                for seg in &h.path {
                    for sel in &seg.selects {
                        self.read(sel, set);
                    }
                }
            }
            ExprKind::Paren(e) | ExprKind::MemberAccess { expr: e, .. } => self.write_part(e, set),
            ExprKind::Index { expr, index } => {
                self.read(index, set);
                self.write_part(expr, set);
            }
            ExprKind::RangeSelect {
                expr, left, right, ..
            } => {
                self.read(left, set);
                self.read(right, set);
                self.write_part(expr, set);
            }
            _ => self.opaque(set),
        }
    }

    fn read_ident(&mut self, name: &str, set: &HashSet<String>) {
        if self.stateful.contains(name) && !self.written(name, set) {
            self.note(name);
        }
    }

    fn read(&mut self, e: &Expression, set: &mut HashSet<String>) {
        if self.carried.is_some() {
            return;
        }
        if let Some((v, Some(m))) = member_path(e) {
            if self.stateful.contains(v) && !set.contains(v) && !set.contains(&format!("{v}.{m}")) {
                self.note(v);
            }
            return;
        }
        match &e.kind {
            ExprKind::Number(_)
            | ExprKind::StringLiteral(_)
            | ExprKind::TypeLiteral(_)
            | ExprKind::Dollar
            | ExprKind::Null
            | ExprKind::Empty => {}
            ExprKind::Ident(h) => {
                if h.root.is_none()
                    && let Some(seg) = h.path.first()
                {
                    let name = seg.name.name.clone();
                    self.read_ident(&name, set);
                }
                for seg in &h.path {
                    for sel in &seg.selects {
                        self.read(sel, set);
                    }
                }
            }
            ExprKind::Unary { operand, .. } => self.read(operand, set),
            ExprKind::Binary { left, right, .. } => {
                self.read(left, set);
                self.read(right, set);
            }
            ExprKind::Conditional {
                condition,
                then_expr,
                else_expr,
            } => {
                self.read(condition, set);
                let mut t = set.clone();
                self.read(then_expr, &mut t);
                let mut f = set.clone();
                self.read(else_expr, &mut f);
            }
            ExprKind::Concatenation(parts) => {
                for p in parts {
                    self.read(p, set);
                }
            }
            ExprKind::Replication { count, exprs } => {
                self.read(count, set);
                for p in exprs {
                    self.read(p, set);
                }
            }
            ExprKind::AssignmentPattern(items) => {
                for it in items {
                    match it {
                        AssignmentPatternItem::Ordered(x)
                        | AssignmentPatternItem::Named(_, x)
                        | AssignmentPatternItem::Typed(_, x)
                        | AssignmentPatternItem::Default(x) => self.read(x, set),
                        AssignmentPatternItem::Keyed(k, x) => {
                            self.read(k, set);
                            self.read(x, set);
                        }
                    }
                }
            }
            ExprKind::TypedPattern { pattern, .. } => self.read(pattern, set),
            ExprKind::SystemCall { args, .. } => {
                for a in args {
                    self.read(a, set);
                }
            }
            ExprKind::NamedArg { expr, .. } => {
                if let Some(x) = expr {
                    self.read(x, set);
                }
            }
            ExprKind::Inside { expr, ranges } => {
                self.read(expr, set);
                for r in ranges {
                    self.read(r, set);
                }
            }
            ExprKind::MemberAccess { expr, .. } => self.read(expr, set),
            ExprKind::Specialization { base, .. } => self.read(base, set),
            ExprKind::Index { expr, index } => {
                self.read(expr, set);
                self.read(index, set);
            }
            ExprKind::RangeSelect {
                expr, left, right, ..
            } => {
                self.read(expr, set);
                self.read(left, set);
                self.read(right, set);
            }
            ExprKind::Range(a, b) => {
                self.read(a, set);
                self.read(b, set);
            }
            ExprKind::Paren(x) => self.read(x, set),
            ExprKind::WithClause { expr, filter } => {
                self.read(expr, set);
                self.read(filter, set);
            }
            ExprKind::StreamOp {
                slice_size, exprs, ..
            } => {
                if let Some(s) = slice_size {
                    self.read(s, set);
                }
                for p in exprs {
                    self.read(p, set);
                }
            }
            ExprKind::Tagged { inner, .. } => {
                if let Some(x) = inner {
                    self.read(x, set);
                }
            }
            ExprKind::AssignExpr { lvalue, rvalue } => {
                self.read(rvalue, set);
                self.write(lvalue, set);
            }
            ExprKind::Call { func, args } => {
                for a in args {
                    self.read(a, set);
                }
                self.call(func, set);
            }
            _ => self.opaque(set),
        }
    }

    /// A call of a user function: a static callee must itself carry nothing.
    fn call(&mut self, func: &Expression, set: &mut HashSet<String>) {
        let ExprKind::Ident(h) = &func.kind else {
            self.read(func, set);
            return;
        };
        if h.root.is_some() || h.path.len() != 1 {
            self.read(func, set);
            return;
        }
        let name = h.path[0].name.name.as_str();
        if self.stateful.contains(name) {
            // The function's own name: a recursive call.
            return;
        }
        let Some(callee) = super::type_props::lookup_resolver(self.elab, name) else {
            return;
        };
        if callee.lifetime == Some(Lifetime::Automatic) {
            return;
        }
        if let Err(v) = check_function(self.elab, callee, self.visiting, self.depth + 1) {
            self.note(&v);
        }
    }
}
