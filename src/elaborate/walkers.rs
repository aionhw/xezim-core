use super::*;

/// Visit every expression reachable from a statement, in evaluation-agnostic
/// order. Statement kinds with no expression payload are skipped.
pub fn for_each_stmt_expr(stmt: &Statement, f: &mut dyn FnMut(&Expression)) {
    use crate::ast::stmt::StatementKind as K;
    match &stmt.kind {
        K::Expr(e) => f(e),
        K::BlockingAssign { lvalue, rvalue } => {
            f(lvalue);
            f(rvalue);
        }
        K::NonblockingAssign {
            lvalue,
            delay,
            rvalue,
        } => {
            f(lvalue);
            if let Some(d) = delay {
                f(d);
            }
            f(rvalue);
        }
        K::If {
            condition,
            then_stmt,
            else_stmt,
            ..
        } => {
            f(condition);
            for_each_stmt_expr(then_stmt, f);
            if let Some(e) = else_stmt {
                for_each_stmt_expr(e, f);
            }
        }
        K::Case { expr, items, .. } => {
            f(expr);
            for it in items {
                for p in &it.patterns {
                    f(p);
                }
                if let Some(g) = &it.guard {
                    f(g);
                }
                for_each_stmt_expr(&it.stmt, f);
            }
        }
        K::For {
            init,
            condition,
            step,
            body,
        } => {
            for i in init {
                match i {
                    crate::ast::stmt::ForInit::VarDecl { init, .. } => f(init),
                    crate::ast::stmt::ForInit::Assign { lvalue, rvalue } => {
                        f(lvalue);
                        f(rvalue);
                    }
                }
            }
            if let Some(c) = condition {
                f(c);
            }
            for st in step {
                f(st);
            }
            for_each_stmt_expr(body, f);
        }
        K::Foreach { array, body, .. } => {
            f(array);
            for_each_stmt_expr(body, f);
        }
        K::ForeachTail { body, .. }
        | K::Forever { body }
        | K::ForeverTail { body }
        | K::RsAction { body } => for_each_stmt_expr(body, f),
        K::While { condition, body } | K::DoWhile { body, condition } => {
            f(condition);
            for_each_stmt_expr(body, f);
        }
        K::Repeat { count, body } => {
            f(count);
            for_each_stmt_expr(body, f);
        }
        K::SeqBlock { stmts, .. } | K::ParBlock { stmts, .. } => {
            for st in stmts {
                for_each_stmt_expr(st, f);
            }
        }
        K::TimingControl { control, stmt } => {
            use crate::ast::stmt::{EventControl, TimingControl};
            match control {
                TimingControl::Delay(e) | TimingControl::Event(EventControl::HierIdentifier(e)) => {
                    f(e)
                }
                TimingControl::Event(EventControl::EventExpr(events)) => {
                    for event in events {
                        f(&event.expr);
                        if let Some(iff) = &event.iff {
                            f(iff);
                        }
                    }
                }
                _ => {}
            }
            for_each_stmt_expr(stmt, f);
        }
        K::Wait { condition, stmt } => {
            f(condition);
            for_each_stmt_expr(stmt, f);
        }
        K::Assertion(a) => {
            f(&a.expr);
            for action in [&a.action, &a.else_action].into_iter().flatten() {
                for_each_stmt_expr(action, f);
            }
        }
        K::ProceduralContinuous(p) => {
            use crate::ast::stmt::ProceduralContinuous as P;
            match p {
                P::Assign { lvalue, rvalue } | P::Force { lvalue, rvalue } => {
                    f(lvalue);
                    f(rvalue);
                }
                P::Deassign(e) | P::Release(e) => f(e),
            }
        }
        K::EventTrigger {
            target: Some(e), ..
        } => f(e),
        K::Coverpoint { expr: e, .. } => f(e),
        K::Cross { items, .. } => {
            for e in items {
                f(e);
            }
        }
        K::WaitOrder { pass, fail, .. } => {
            for action in [pass, fail].into_iter().flatten() {
                for_each_stmt_expr(action, f);
            }
        }
        K::Return(Some(e)) => f(e),
        K::VarDecl { declarators, .. } | K::ParamDecl { declarators, .. } => {
            for d in declarators {
                if let Some(i) = &d.init {
                    f(i);
                }
            }
        }
        K::RandCase { items } => {
            for (w, st) in items {
                f(w);
                for_each_stmt_expr(st, f);
            }
        }
        _ => {}
    }
}

/// Leaf names of every `force` / `release` / procedural `assign` /
/// `deassign` target in the design's procedural code: always, initial and
/// final blocks, module tasks and functions, and class methods. A net that is
/// ever overridden this way must keep storage of its own — the simulator's
/// buffer-collapse pass aliases `assign y = x` onto `x`, and a later
/// `force y = ...` would then reach the shared net. Leaf names (the last path
/// segment) are an over-approximation on purpose: a target spelled without
/// its instance prefix inside a task body must still exclude the prefixed net.
pub fn collect_override_target_leaves(elab: &ElaboratedModule) -> crate::hasher::HashSet<String> {
    collect_write_targets(Some(elab), &mut |_| {}).0
}

/// The two censuses of a single statement, as written (no instance rewrite
/// applied): (override target leaves, procedurally written flat names).
#[allow(clippy::type_complexity)]
pub fn stmt_write_targets(
    stmt: &Statement,
) -> (
    crate::hasher::HashSet<String>,
    crate::hasher::HashSet<String>,
) {
    collect_write_targets(None, &mut |visit| visit(stmt))
}

/// Both write censuses in one walk: (`collect_override_target_leaves`,
/// `collect_procedural_write_names`). `extra` hands further process bodies
/// to the walk (each through the visitor it is given), for always blocks
/// the caller holds outside `elab`.
#[allow(clippy::type_complexity)]
pub fn collect_write_target_sets(
    elab: &ElaboratedModule,
    extra: &mut dyn FnMut(&mut dyn FnMut(&Statement)),
) -> (
    crate::hasher::HashSet<String>,
    crate::hasher::HashSet<String>,
) {
    collect_write_targets(Some(elab), extra)
}

/// Flat names of every variable written by a procedural assignment
/// (blocking, nonblocking, `for` init, assignment expression, `++`/`--`) in
/// the same procedural code. Names inside inlined instance bodies are
/// already instance-prefixed by elaboration, so these are the exact spellings
/// the signal table uses; a task-local spelling without its prefix is not
/// recovered (tasks writing design nets are rare, and the buffer pass only
/// needs this to keep the delta step between a procedurally written variable
/// and a net that copies it).
pub fn collect_procedural_write_names(elab: &ElaboratedModule) -> crate::hasher::HashSet<String> {
    collect_write_targets(Some(elab), &mut |_| {}).1
}

fn collect_write_targets(
    elab: Option<&ElaboratedModule>,
    extra: &mut dyn FnMut(&mut dyn FnMut(&Statement)),
) -> (
    crate::hasher::HashSet<String>,
    crate::hasher::HashSet<String>,
) {
    fn flat(e: &Expression, out: &mut crate::hasher::HashSet<String>) {
        match &e.kind {
            ExprKind::Ident(h) => {
                out.insert(
                    h.path
                        .iter()
                        .map(|s| s.name.name.as_str())
                        .collect::<Vec<_>>()
                        .join("."),
                );
            }
            ExprKind::MemberAccess { expr, member } => {
                let mut base = crate::hasher::HashSet::default();
                flat(expr, &mut base);
                for b in base {
                    out.insert(format!("{}.{}", b, member.name));
                }
            }
            ExprKind::Index { expr, .. } | ExprKind::RangeSelect { expr, .. } => flat(expr, out),
            ExprKind::Concatenation(parts) => {
                for p in parts {
                    flat(p, out);
                }
            }
            _ => {}
        }
    }
    fn leaf(e: &Expression, out: &mut crate::hasher::HashSet<String>) {
        match &e.kind {
            ExprKind::Ident(h) => {
                if let Some(s) = h.path.last() {
                    out.insert(s.name.name.clone());
                }
            }
            ExprKind::MemberAccess { member, .. } => {
                out.insert(member.name.clone());
            }
            ExprKind::Index { expr, .. } | ExprKind::RangeSelect { expr, .. } => leaf(expr, out),
            ExprKind::Concatenation(parts) => {
                for p in parts {
                    leaf(p, out);
                }
            }
            _ => {}
        }
    }
    struct Sets {
        overrides: crate::hasher::HashSet<String>,
        writes: crate::hasher::HashSet<String>,
    }
    fn write_expr(e: &Expression, out: &mut Sets) {
        match &e.kind {
            ExprKind::AssignExpr { lvalue, .. } => flat(lvalue, &mut out.writes),
            ExprKind::Unary { operand, .. } => flat(operand, &mut out.writes),
            _ => {}
        }
    }
    fn walk(stmt: &Statement, out: &mut Sets) {
        use crate::ast::stmt::ProceduralContinuous as PC;
        use crate::ast::stmt::StatementKind as K;
        match &stmt.kind {
            K::ProceduralContinuous(pc) => match pc {
                PC::Assign { lvalue, .. } | PC::Force { lvalue, .. } => {
                    leaf(lvalue, &mut out.overrides)
                }
                PC::Deassign(e) | PC::Release(e) => leaf(e, &mut out.overrides),
            },
            K::BlockingAssign { lvalue, .. } | K::NonblockingAssign { lvalue, .. } => {
                flat(lvalue, &mut out.writes)
            }
            K::Expr(e) => write_expr(e, out),
            K::If {
                then_stmt,
                else_stmt,
                ..
            } => {
                walk(then_stmt, out);
                if let Some(e) = else_stmt {
                    walk(e, out);
                }
            }
            K::Case { items, .. } => {
                for it in items {
                    walk(&it.stmt, out);
                }
            }
            K::For {
                init, step, body, ..
            } => {
                for i in init {
                    if let crate::ast::stmt::ForInit::Assign { lvalue, .. } = i {
                        flat(lvalue, &mut out.writes);
                    }
                }
                for st in step {
                    write_expr(st, out);
                }
                walk(body, out);
            }
            K::Foreach { body, .. }
            | K::ForeachTail { body, .. }
            | K::Forever { body }
            | K::ForeverTail { body }
            | K::RsAction { body }
            | K::While { body, .. }
            | K::DoWhile { body, .. }
            | K::Repeat { body, .. } => walk(body, out),
            K::SeqBlock { stmts, .. } | K::ParBlock { stmts, .. } => {
                for st in stmts {
                    walk(st, out);
                }
            }
            K::TimingControl { stmt, .. } | K::Wait { stmt, .. } => walk(stmt, out),
            K::RandCase { items } => {
                for (_, st) in items {
                    walk(st, out);
                }
            }
            _ => {}
        }
    }
    use crate::ast::decl::ClassMethodKind as CMK;
    let mut out = Sets {
        overrides: crate::hasher::HashSet::default(),
        writes: crate::hasher::HashSet::default(),
    };
    let Some(elab) = elab else {
        extra(&mut |st: &Statement| walk(st, &mut out));
        return (out.overrides, out.writes);
    };
    for b in &elab.always_blocks {
        walk(&b.stmt, &mut out);
    }
    extra(&mut |st: &Statement| walk(st, &mut out));
    for b in elab.initial_blocks.iter().chain(elab.final_blocks.iter()) {
        walk(&b.stmt, &mut out);
    }
    struct RoutineRaw {
        sets: Sets,
        local_decls: Vec<String>,
    }
    let mut routine_memo: HashMap<usize, RoutineRaw> = HashMap::default();
    let mut visit_routine = |items: &crate::ast::shared_vec::SharedVec<Statement>,
                             ports: &[crate::ast::decl::FunctionPort],
                             deferred: Option<&Rc<CallableRewriteCtx>>| {
        let ptr = std::sync::Arc::as_ptr(items.as_arc()) as usize;
        let raw = routine_memo.entry(ptr).or_insert_with(|| {
            let mut sets = Sets {
                overrides: crate::hasher::HashSet::default(),
                writes: crate::hasher::HashSet::default(),
            };
            for s in items.iter() {
                walk(s, &mut sets);
            }
            let local_decls = stmt_list_declared_names(items)
                .into_iter()
                .map(str::to_string)
                .collect();
            RoutineRaw { sets, local_decls }
        });
        let Some(dctx) = deferred else {
            out.overrides.extend(raw.sets.overrides.iter().cloned());
            out.writes.extend(raw.sets.writes.iter().cloned());
            return;
        };
        let is_shadowed = |head: &str| {
            ports.iter().any(|p| p.name.name == head)
                || raw.local_decls.iter().any(|l| l == head)
        };
        for o in &raw.sets.overrides {
            if !is_shadowed(o)
                && let Some(actual) = dctx.ctx.port_map.get(o)
            {
                leaf(actual, &mut out.overrides);
            } else {
                out.overrides.insert(o.clone());
            }
        }
        for w in &raw.sets.writes {
            let head = w.split('.').next().unwrap_or(w);
            if !is_shadowed(head) {
                if dctx.ctx.local_names.contains(head) {
                    out.writes.insert(cat2(&dctx.ctx.prefix, w));
                    continue;
                }
                if let Some(actual) = dctx.ctx.port_map.get(head) {
                    let rest = &w[head.len()..];
                    let mut mapped = crate::hasher::HashSet::default();
                    flat(actual, &mut mapped);
                    for m in mapped {
                        out.writes.insert(format!("{}{}", m, rest));
                    }
                    continue;
                }
                if let Some(iface) = dctx.ctx.interface_map.get(head) {
                    let rest = &w[head.len()..];
                    out.writes.insert(format!("{}{}", iface, rest));
                    continue;
                }
            }
            out.writes.insert(w.clone());
        }
    };
    for (k, t) in &elab.tasks {
        visit_routine(&t.items, &t.ports, elab.deferred_task_bodies.get(k));
    }
    for (k, f) in elab.functions.iter() {
        visit_routine(&f.items, &f.ports, elab.deferred_function_bodies.get(k));
    }
    for c in elab.classes.values() {
        for m in c.methods.values() {
            match &m.kind {
                CMK::Function(f) | CMK::Extern(f) | CMK::PureVirtual(f) => {
                    for s in &f.items {
                        walk(s, &mut out);
                    }
                }
                CMK::Task(t) => {
                    for s in &t.items {
                        walk(s, &mut out);
                    }
                }
            }
        }
    }
    (out.overrides, out.writes)
}

/// Visit every sub-expression (pre-order, `e` included).
pub fn for_each_sub_expr(e: &Expression, f: &mut dyn FnMut(&Expression)) {
    f(e);
    match &e.kind {
        ExprKind::Ident(h) => {
            for segment in &h.path {
                for select in &segment.selects {
                    for_each_sub_expr(select, f);
                }
            }
        }
        ExprKind::Unary { operand, .. } => for_each_sub_expr(operand, f),
        ExprKind::Binary { left, right, .. } => {
            for_each_sub_expr(left, f);
            for_each_sub_expr(right, f);
        }
        ExprKind::Conditional {
            condition,
            then_expr,
            else_expr,
        } => {
            for_each_sub_expr(condition, f);
            for_each_sub_expr(then_expr, f);
            for_each_sub_expr(else_expr, f);
        }
        ExprKind::Concatenation(xs) => {
            for x in xs {
                for_each_sub_expr(x, f);
            }
        }
        ExprKind::StreamOp {
            slice_size, exprs, ..
        } => {
            if let Some(size) = slice_size {
                for_each_sub_expr(size, f);
            }
            for expr in exprs {
                for_each_sub_expr(expr, f);
            }
        }
        ExprKind::Matches { expr, .. } => for_each_sub_expr(expr, f),
        ExprKind::Tagged {
            inner: Some(expr), ..
        } => for_each_sub_expr(expr, f),
        ExprKind::Replication { count, exprs } => {
            for_each_sub_expr(count, f);
            for x in exprs {
                for_each_sub_expr(x, f);
            }
        }
        ExprKind::AssignmentPattern(items) => {
            for it in items {
                if let AssignmentPatternItem::Keyed(key, _) = it {
                    for_each_sub_expr(key, f);
                }
                for_each_sub_expr(it.expr(), f);
            }
        }
        ExprKind::Call { func, args } => {
            for_each_sub_expr(func, f);
            for a in args {
                for_each_sub_expr(a, f);
            }
        }
        ExprKind::SystemCall { args, .. } => {
            for a in args {
                for_each_sub_expr(a, f);
            }
        }
        ExprKind::NamedArg { expr: Some(x), .. } => for_each_sub_expr(x, f),
        ExprKind::Inside { expr, ranges } => {
            for_each_sub_expr(expr, f);
            for r in ranges {
                for_each_sub_expr(r, f);
            }
        }
        ExprKind::MemberAccess { expr, .. }
        | ExprKind::Specialization { base: expr, .. }
        | ExprKind::Paren(expr)
        | ExprKind::ShallowCopy { source: expr }
        | ExprKind::TypedPattern { pattern: expr, .. } => for_each_sub_expr(expr, f),
        ExprKind::Index { expr, index } => {
            for_each_sub_expr(expr, f);
            for_each_sub_expr(index, f);
        }
        ExprKind::RangeSelect {
            expr, left, right, ..
        } => {
            for_each_sub_expr(expr, f);
            for_each_sub_expr(left, f);
            for_each_sub_expr(right, f);
        }
        ExprKind::Range(a, b)
        | ExprKind::AssignExpr {
            lvalue: a,
            rvalue: b,
        } => {
            for_each_sub_expr(a, f);
            for_each_sub_expr(b, f);
        }
        ExprKind::WithClause { expr, filter } => {
            for_each_sub_expr(expr, f);
            for_each_sub_expr(filter, f);
        }
        ExprKind::RandomizeWith { call, .. } => for_each_sub_expr(call, f),
        ExprKind::SvaClocked { events, body } => {
            for event in events {
                for_each_sub_expr(&event.expr, f);
                if let Some(g) = &event.iff {
                    for_each_sub_expr(g, f);
                }
            }
            for_each_sub_expr(body, f);
        }
        _ => {}
    }
}

/// [`for_each_sub_expr`] with mutable access; `f` sees a node before its
/// children, so it may replace the node it is given.
pub fn for_each_sub_expr_mut(e: &mut Expression, f: &mut dyn FnMut(&mut Expression)) {
    f(e);
    match &mut e.kind {
        ExprKind::Unary { operand, .. } => for_each_sub_expr_mut(operand, f),
        ExprKind::Binary { left, right, .. } => {
            for_each_sub_expr_mut(left, f);
            for_each_sub_expr_mut(right, f);
        }
        ExprKind::Conditional {
            condition,
            then_expr,
            else_expr,
        } => {
            for_each_sub_expr_mut(condition, f);
            for_each_sub_expr_mut(then_expr, f);
            for_each_sub_expr_mut(else_expr, f);
        }
        ExprKind::Concatenation(xs) | ExprKind::StreamOp { exprs: xs, .. } => {
            for x in xs {
                for_each_sub_expr_mut(x, f);
            }
        }
        ExprKind::Replication { count, exprs } => {
            for_each_sub_expr_mut(count, f);
            for x in exprs {
                for_each_sub_expr_mut(x, f);
            }
        }
        ExprKind::AssignmentPattern(items) => {
            for it in items {
                match it {
                    AssignmentPatternItem::Ordered(x)
                    | AssignmentPatternItem::Named(_, x)
                    | AssignmentPatternItem::Typed(_, x)
                    | AssignmentPatternItem::Default(x) => for_each_sub_expr_mut(x, f),
                    AssignmentPatternItem::Keyed(k, x) => {
                        for_each_sub_expr_mut(k, f);
                        for_each_sub_expr_mut(x, f);
                    }
                }
            }
        }
        ExprKind::Call { func, args } => {
            for_each_sub_expr_mut(func, f);
            for a in args {
                for_each_sub_expr_mut(a, f);
            }
        }
        ExprKind::SystemCall { args, .. } => {
            for a in args {
                for_each_sub_expr_mut(a, f);
            }
        }
        ExprKind::NamedArg { expr: Some(x), .. } => for_each_sub_expr_mut(x, f),
        ExprKind::Inside { expr, ranges } => {
            for_each_sub_expr_mut(expr, f);
            for r in ranges {
                for_each_sub_expr_mut(r, f);
            }
        }
        ExprKind::MemberAccess { expr, .. }
        | ExprKind::Specialization { base: expr, .. }
        | ExprKind::Paren(expr)
        | ExprKind::ShallowCopy { source: expr }
        | ExprKind::TypedPattern { pattern: expr, .. } => for_each_sub_expr_mut(expr, f),
        ExprKind::Index { expr, index } => {
            for_each_sub_expr_mut(expr, f);
            for_each_sub_expr_mut(index, f);
        }
        ExprKind::RangeSelect {
            expr, left, right, ..
        } => {
            for_each_sub_expr_mut(expr, f);
            for_each_sub_expr_mut(left, f);
            for_each_sub_expr_mut(right, f);
        }
        ExprKind::Range(a, b)
        | ExprKind::AssignExpr {
            lvalue: a,
            rvalue: b,
        } => {
            for_each_sub_expr_mut(a, f);
            for_each_sub_expr_mut(b, f);
        }
        ExprKind::WithClause { expr, filter } => {
            for_each_sub_expr_mut(expr, f);
            for_each_sub_expr_mut(filter, f);
        }
        ExprKind::RandomizeWith { call, .. } => for_each_sub_expr_mut(call, f),
        ExprKind::SvaClocked { events, body } => {
            for event in events {
                for_each_sub_expr_mut(&mut event.expr, f);
                if let Some(g) = &mut event.iff {
                    for_each_sub_expr_mut(g, f);
                }
            }
            for_each_sub_expr_mut(body, f);
        }
        _ => {}
    }
}
