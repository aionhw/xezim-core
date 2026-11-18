//! IEEE 1800-2023 §9.2, §9.3, §12.5, §12.7, §23.6: retain an unchanged
//! root process's storage without skipping scope or reference rewrites.

use super::{
    GEN_RENAME_TLS, MODPORT_SUBST_FLAG, PKG_FLATTEN_ONLY, TYPE_BIND_QUERIES_TLS, TYPE_BIND_TYPES_TLS,
    TYPE_BIND_WIDTHS_TLS,
};
use crate::ast::expr::{ExprKind, Expression};
use crate::ast::stmt::{EventControl, ForInit, Statement, StatementKind, TimingControl};
use crate::ast::Span;

/// Whether the final root rewrite is an identity for this narrow syntax set.
///
/// The caller must have an empty prefix, port map and interface map. This is
/// not an identity test for an instance, a generate rename or a general
/// `rewrite_stmt` invocation. Unknown forms deliberately use the old rewrite.
///
/// On success the caller must use `stmt.clone()`: that shares block storage
/// in ordinary mode, but still visits and resets caches under explicit Fresh or
/// Disabled clone modes. Merely retaining the original would skip that work.
pub(super) fn can_preserve_root_stmt(stmt: &Statement) -> bool {
    // Even a currently empty specialization/rename is an explicit rewrite
    // context. Exclude it rather than infer that its current tables are inert.
    let root_context = GEN_RENAME_TLS.with(|frames| frames.borrow().is_empty())
        && TYPE_BIND_WIDTHS_TLS.with(|bindings| bindings.borrow().is_none())
        && TYPE_BIND_QUERIES_TLS.with(|bindings| bindings.borrow().is_none())
        && TYPE_BIND_TYPES_TLS.with(|bindings| bindings.borrow().is_none())
        && PKG_FLATTEN_ONLY.with(|packages| packages.borrow().is_none())
        // An ordinary index rewrite consumes this transient flag. Starting
        // clear also preserves that state when retaining the expression.
        && MODPORT_SUBST_FLAG.with(|flag| !flag.get());
    root_context && identity_stmt(stmt)
}

/// Report the first failed identity gate, in predicate order, without
/// retaining or printing syntax. The caller uses the same empty root maps
/// as `can_preserve_root_stmt` and calls this only on a rejected body.
pub(super) fn trace_root_rejection(stmt: &Statement) {
    if !crate::oom_trace::enabled() {
        return;
    }
    let rejection = context_rejection(stmt.span)
        .or_else(|| stmt_rejection(stmt))
        .unwrap_or_else(|| rejection("identity.reject.not_reproduced", stmt.span, 0));
    crate::oom_trace::checkpoint(
        rejection.phase,
        &[
            ("root_span_start", stmt.span.start),
            ("root_span_end", stmt.span.end),
            ("span_start", rejection.span.start),
            ("span_end", rejection.span.end),
            ("detail", rejection.detail),
        ],
    );
}

struct RootRejection {
    phase: &'static str,
    span: Span,
    detail: usize,
}

fn rejection(phase: &'static str, span: Span, detail: usize) -> RootRejection {
    RootRejection { phase, span, detail }
}

fn context_rejection(span: Span) -> Option<RootRejection> {
    let frames = GEN_RENAME_TLS.with(|frames| frames.borrow().len());
    if frames != 0 {
        return Some(rejection("identity.reject.context.gen_rename", span, frames));
    }
    if let Some(count) =
        TYPE_BIND_WIDTHS_TLS.with(|bindings| bindings.borrow().as_ref().map(|map| map.len()))
    {
        return Some(rejection("identity.reject.context.type_widths", span, count));
    }
    if let Some(count) =
        TYPE_BIND_QUERIES_TLS.with(|bindings| bindings.borrow().as_ref().map(|map| map.len()))
    {
        return Some(rejection("identity.reject.context.type_queries", span, count));
    }
    if let Some(count) =
        TYPE_BIND_TYPES_TLS.with(|bindings| bindings.borrow().as_ref().map(|map| map.len()))
    {
        return Some(rejection("identity.reject.context.type_bindings", span, count));
    }
    if let Some(count) =
        PKG_FLATTEN_ONLY.with(|packages| packages.borrow().as_ref().map(|set| set.len()))
    {
        return Some(rejection("identity.reject.context.package_flatten", span, count));
    }
    MODPORT_SUBST_FLAG
        .with(|flag| flag.get())
        .then(|| rejection("identity.reject.context.modport_flag", span, 1))
}

fn stmt_rejection(stmt: &Statement) -> Option<RootRejection> {
    match &stmt.kind {
        StatementKind::Null => None,
        StatementKind::BlockingAssign { lvalue, rvalue } => {
            expr_rejection(lvalue).or_else(|| expr_rejection(rvalue))
        }
        StatementKind::NonblockingAssign {
            lvalue,
            delay,
            rvalue,
        } => expr_rejection(lvalue)
            .or_else(|| delay.as_deref().and_then(expr_rejection))
            .or_else(|| expr_rejection(rvalue)),
        StatementKind::Expr(expr) => expr_rejection(expr),
        StatementKind::If {
            condition,
            then_stmt,
            else_stmt,
            ..
        } => expr_rejection(condition)
            .or_else(|| stmt_rejection(then_stmt))
            .or_else(|| else_stmt.as_deref().and_then(stmt_rejection)),
        StatementKind::Case { expr, items, .. } => {
            expr_rejection(expr).or_else(|| {
                items.iter().find_map(|item| {
                    if item.pattern.is_some() {
                        return Some(rejection("identity.reject.case_pattern", item.span, 1));
                    }
                    item.patterns.iter().find_map(expr_rejection)
                        .or_else(|| item.guard.as_deref().and_then(expr_rejection))
                        .or_else(|| stmt_rejection(&item.stmt))
                })
            })
        }
        StatementKind::For {
            init,
            condition,
            step,
            body,
        } => {
            init.iter().enumerate()
                .find_map(|(index, entry)| match entry {
                    ForInit::Assign { lvalue, rvalue } => {
                        expr_rejection(lvalue).or_else(|| expr_rejection(rvalue))
                    }
                    ForInit::VarDecl { name, .. } => {
                        Some(rejection("identity.reject.stmt.for_decl", name.span, index))
                    }
                })
                .or_else(|| condition.as_ref().and_then(expr_rejection))
                .or_else(|| step.iter().find_map(expr_rejection))
                .or_else(|| stmt_rejection(body))
        }
        StatementKind::While { condition, body } => {
            expr_rejection(condition).or_else(|| stmt_rejection(body))
        }
        StatementKind::Repeat { count, body } => {
            expr_rejection(count).or_else(|| stmt_rejection(body))
        }
        StatementKind::Wait { condition, stmt } => {
            expr_rejection(condition).or_else(|| stmt_rejection(stmt))
        }
        StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
            stmts.iter().find_map(stmt_rejection)
        }
        StatementKind::TimingControl { control, stmt } => {
            let rejected = match control {
                TimingControl::Delay(expr) => expr_rejection(expr),
                TimingControl::Event(event) => match event {
                    EventControl::Star | EventControl::ParenStar | EventControl::Identifier(_) => {
                        None
                    }
                    EventControl::HierIdentifier(expr) => expr_rejection(expr),
                    EventControl::EventExpr(events) => events.iter().find_map(|event| {
                        expr_rejection(&event.expr)
                            .or_else(|| event.iff.as_ref().and_then(expr_rejection))
                    }),
                },
            };
            rejected.or_else(|| stmt_rejection(stmt))
        }
        other => {
            let phase = match other {
                StatementKind::ScopePop => "identity.reject.stmt.scope_pop",
                StatementKind::LoopStep => "identity.reject.stmt.loop_step",
                StatementKind::DisableFork => "identity.reject.stmt.disable_fork",
                StatementKind::Foreach { .. } => "identity.reject.stmt.foreach",
                StatementKind::ForeachTail { .. } => "identity.reject.stmt.foreach_tail",
                StatementKind::DoWhile { .. } => "identity.reject.stmt.do_while",
                StatementKind::Forever { .. } => "identity.reject.stmt.forever",
                StatementKind::ForeverTail { .. } => "identity.reject.stmt.forever_tail",
                StatementKind::EventTrigger { .. } => "identity.reject.stmt.event_trigger",
                StatementKind::WaitFork => "identity.reject.stmt.wait_fork",
                StatementKind::Disable(_) => "identity.reject.stmt.disable",
                StatementKind::Return(_) => "identity.reject.stmt.return",
                StatementKind::Break => "identity.reject.stmt.break",
                StatementKind::Continue => "identity.reject.stmt.continue",
                StatementKind::Assertion(_) => "identity.reject.stmt.assertion",
                StatementKind::ProceduralContinuous(_) => {
                    "identity.reject.stmt.procedural_continuous"
                }
                StatementKind::VarDecl { .. } => "identity.reject.stmt.var_decl",
                StatementKind::ParamDecl { .. } => "identity.reject.stmt.param_decl",
                StatementKind::RandCase { .. } => "identity.reject.stmt.randcase",
                StatementKind::Typedef(_) => "identity.reject.stmt.typedef",
                StatementKind::Coverpoint { .. } => "identity.reject.stmt.coverpoint",
                StatementKind::Cross { .. } => "identity.reject.stmt.cross",
                StatementKind::RsAction { .. } => "identity.reject.stmt.rs_action",
                StatementKind::RsReturn => "identity.reject.stmt.rs_return",
                StatementKind::WaitOrder { .. } => "identity.reject.stmt.wait_order",
                _ => "identity.reject.stmt.other",
            };
            Some(rejection(phase, stmt.span, 0))
        }
    }
}

fn expr_rejection(expr: &Expression) -> Option<RootRejection> {
    if let Some(width) = expr.cached_width.get() {
        return Some(rejection(
            "identity.reject.cache.width",
            expr.span,
            width as usize,
        ));
    }
    match &expr.kind {
        ExprKind::Number(_) | ExprKind::StringLiteral(_) => None,
        ExprKind::Ident(name) => {
            let (phase, detail) = if name.root.is_some() {
                ("identity.reject.ident.rooted", name.path.len())
            } else if name.bound.is_upward() {
                ("identity.reject.ident.upward", name.path.len())
            } else if let Some(signal) = name.cached_signal_id.get() {
                ("identity.reject.cache.signal", signal as usize)
            } else if let Some(cached) = name.cached_resolved_name.get() {
                ("identity.reject.cache.name", cached.len())
            } else {
                match name.path.as_slice() {
                    [segment] if !segment.selects.is_empty() => {
                        ("identity.reject.ident.selects", segment.selects.len())
                    }
                    [segment] if segment.name.name.contains(['.', ':', '$']) => {
                        ("identity.reject.ident.qualified", segment.name.name.len())
                    }
                    [_] => return None,
                    _ => ("identity.reject.ident.path", name.path.len()),
                }
            };
            Some(rejection(phase, expr.span, detail))
        }
        ExprKind::Unary { operand, .. } | ExprKind::Paren(operand) => expr_rejection(operand),
        ExprKind::Binary { left, right, .. } | ExprKind::Range(left, right) => {
            expr_rejection(left).or_else(|| expr_rejection(right))
        }
        ExprKind::AssignExpr { lvalue, rvalue } => {
            expr_rejection(lvalue).or_else(|| expr_rejection(rvalue))
        }
        ExprKind::Conditional {
            condition,
            then_expr,
            else_expr,
        } => expr_rejection(condition)
            .or_else(|| expr_rejection(then_expr))
            .or_else(|| expr_rejection(else_expr)),
        ExprKind::Concatenation(parts) => parts.iter().find_map(expr_rejection),
        ExprKind::Replication { count, exprs } => {
            expr_rejection(count).or_else(|| exprs.iter().find_map(expr_rejection))
        }
        ExprKind::Index { expr: base, index } => {
            expr_rejection(base).or_else(|| expr_rejection(index))
        }
        ExprKind::RangeSelect {
            expr: base,
            left,
            right,
            ..
        } => {
            if matches!(base.kind, ExprKind::RangeSelect { .. }) {
                return Some(rejection("identity.reject.nested_range", expr.span, 0));
            }
            expr_rejection(base)
                .or_else(|| expr_rejection(left))
                .or_else(|| expr_rejection(right))
        }
        ExprKind::Call { func, args } => {
            expr_rejection(func).or_else(|| args.iter().find_map(expr_rejection))
        }
        ExprKind::SystemCall { name, args } => {
            if matches!(
                name.as_str(),
                "$bits" | "$left" | "$right" | "$high" | "$low" | "$size" | "$increment"
                    | "$dimensions" | "$unpacked_dimensions"
            ) {
                Some(rejection("identity.reject.type_query", expr.span, args.len()))
            } else {
                args.iter().find_map(expr_rejection)
            }
        }
        other => {
            let phase = match other {
                ExprKind::TypeLiteral(_) => "identity.reject.expr.type_literal",
                ExprKind::AssignmentPattern(_) => "identity.reject.expr.assignment_pattern",
                ExprKind::NamedArg { .. } => "identity.reject.expr.named_arg",
                ExprKind::Inside { .. } => "identity.reject.expr.inside",
                ExprKind::Matches { .. } => "identity.reject.expr.matches",
                ExprKind::MemberAccess { .. } => "identity.reject.expr.member_access",
                ExprKind::Specialization { .. } => "identity.reject.expr.specialization",
                ExprKind::Dollar => "identity.reject.expr.dollar",
                ExprKind::Null => "identity.reject.expr.null",
                ExprKind::This => "identity.reject.expr.this",
                ExprKind::Empty => "identity.reject.expr.empty",
                ExprKind::WithClause { .. } => "identity.reject.expr.with_clause",
                ExprKind::RandomizeWith { .. } => "identity.reject.expr.randomize_with",
                ExprKind::StreamOp { .. } => "identity.reject.expr.stream_op",
                ExprKind::Tagged { .. } => "identity.reject.expr.tagged",
                ExprKind::SvaClocked { .. } => "identity.reject.expr.sva_clocked",
                ExprKind::ShallowCopy { .. } => "identity.reject.expr.shallow_copy",
                ExprKind::TypedPattern { .. } => "identity.reject.expr.typed_pattern",
                _ => "identity.reject.expr.other",
            };
            Some(rejection(phase, expr.span, 0))
        }
    }
}

fn identity_stmt(stmt: &Statement) -> bool {
    match &stmt.kind {
        StatementKind::Null => true,
        StatementKind::BlockingAssign { lvalue, rvalue } => {
            identity_expr(lvalue) && identity_expr(rvalue)
        }
        StatementKind::NonblockingAssign {
            lvalue,
            delay,
            rvalue,
        } => {
            identity_expr(lvalue)
                && delay.as_deref().is_none_or(identity_expr)
                && identity_expr(rvalue)
        }
        StatementKind::Expr(expr) => identity_expr(expr),
        StatementKind::If {
            condition,
            then_stmt,
            else_stmt,
            ..
        } => {
            identity_expr(condition)
                && identity_stmt(then_stmt)
                && else_stmt.as_deref().is_none_or(identity_stmt)
        }
        StatementKind::Case { expr, items, .. } => {
            identity_expr(expr)
                && items.iter().all(|item| {
                    // Pattern bindings introduce names of their own. Keep
                    // them on the complete scope rewrite path.
                    item.pattern.is_none()
                        && item.patterns.iter().all(identity_expr)
                        && item.guard.as_deref().is_none_or(identity_expr)
                        && identity_stmt(&item.stmt)
                })
        }
        StatementKind::For {
            init,
            condition,
            step,
            body,
        } => {
            // Assignment-only headers introduce no loop-local names, so
            // the ordinary shadowing path has no bindings to remove.
            init.iter().all(|entry| match entry {
                ForInit::Assign { lvalue, rvalue } => {
                    identity_expr(lvalue) && identity_expr(rvalue)
                }
                ForInit::VarDecl { .. } => false,
            }) && condition.as_ref().is_none_or(identity_expr)
                && step.iter().all(identity_expr)
                && identity_stmt(body)
        }
        StatementKind::While { condition, body } => identity_expr(condition) && identity_stmt(body),
        StatementKind::Repeat { count, body } => identity_expr(count) && identity_stmt(body),
        StatementKind::Wait { condition, stmt } => identity_expr(condition) && identity_stmt(stmt),
        StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
            // No accepted child introduces a declaration. The scoped list
            // walk therefore has no local-name shadowing to apply (§6.21).
            stmts.iter().all(identity_stmt)
        }
        StatementKind::TimingControl { control, stmt } => {
            let identity_control = match control {
                TimingControl::Delay(expr) => identity_expr(expr),
                TimingControl::Event(event) => identity_event(event),
            };
            identity_control && identity_stmt(stmt)
        }
        // Declarations, binding loops, assertions, event triggers, disables
        // and all other forms keep their existing scope handling.
        _ => false,
    }
}

fn identity_event(event: &EventControl) -> bool {
    match event {
        EventControl::Star | EventControl::ParenStar => true,
        // With empty root maps/prefix this arm copies the identifier and
        // its span unchanged, regardless of the local-name set.
        EventControl::Identifier(_) => true,
        EventControl::HierIdentifier(expr) => identity_expr(expr),
        EventControl::EventExpr(events) => events.iter().all(|event| {
            identity_expr(&event.expr) && event.iff.as_ref().is_none_or(identity_expr)
        }),
    }
}

fn identity_expr(expr: &Expression) -> bool {
    // The ordinary rewrite rebuilds expression-width caches. Retaining an
    // already populated cache could miss an invalidation after inlining,
    // even when its source spelling is unchanged. Disabled caches read as
    // empty and remain disabled through a normal shared clone.
    if expr.cached_width.get().is_some() {
        return false;
    }
    match &expr.kind {
        // Literal memoization is context-free and is copied by the old
        // rewrite too; only contextual caches need the exclusion above.
        ExprKind::Number(_) | ExprKind::StringLiteral(_) => true,
        ExprKind::Ident(name) => {
            // A single unqualified segment cannot take the hierarchical
            // upward-reference path; its bare subroutine path is excluded
            // by `bound`. UPWARD_SCOPES_TLS may therefore stay installed.
            name.root.is_none()
                && !name.bound.is_upward()
                && name.cached_signal_id.get().is_none()
                && name.cached_resolved_name.get().is_none()
                && matches!(name.path.as_slice(), [segment]
                    if segment.selects.is_empty()
                        && !segment.name.name.contains(['.', ':', '$']))
        }
        ExprKind::Unary { operand, .. } | ExprKind::Paren(operand) => identity_expr(operand),
        ExprKind::Binary { left, right, .. } | ExprKind::Range(left, right) => {
            identity_expr(left) && identity_expr(right)
        }
        ExprKind::AssignExpr { lvalue, rvalue } => {
            identity_expr(lvalue) && identity_expr(rvalue)
        }
        ExprKind::Conditional {
            condition,
            then_expr,
            else_expr,
        } => identity_expr(condition) && identity_expr(then_expr) && identity_expr(else_expr),
        ExprKind::Concatenation(parts) => parts.iter().all(identity_expr),
        ExprKind::Replication { count, exprs } => {
            identity_expr(count) && exprs.iter().all(identity_expr)
        }
        ExprKind::Index { expr: base, index } => {
            // Empty root maps cannot select an interface array. Accepted
            // operands cannot substitute a modport expression either, so
            // the normal index arm only reconstructs these operands.
            identity_expr(base) && identity_expr(index)
        }
        ExprKind::RangeSelect {
            expr: base,
            left,
            right,
            ..
        } => {
            // An identical range over another range can collapse. Keep
            // every direct nested range on the complete rewrite path.
            !matches!(base.kind, ExprKind::RangeSelect { .. })
                && identity_expr(base)
                && identity_expr(left)
                && identity_expr(right)
        }
        ExprKind::Call { func, args } => {
            // In particular, a member/scoped/upward callee is excluded by
            // the operand predicate; no call is evaluated by this rewrite.
            identity_expr(func) && args.iter().all(identity_expr)
        }
        ExprKind::SystemCall { name, args } => {
            // These queries can replace a call by a literal in a type
            // binding context. Other system calls only rewrite operands.
            !matches!(
                name.as_str(),
                "$bits"
                    | "$left"
                    | "$right"
                    | "$high"
                    | "$low"
                    | "$size"
                    | "$increment"
                    | "$dimensions"
                    | "$unpacked_dimensions"
            ) && args.iter().all(identity_expr)
        }
        // Member paths can become hierarchical references; type queries
        // and all other unknown forms still take the complete rewrite.
        // Keep every such form on the complete rewrite path for now.
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::binding::Bound;
    use crate::ast::decl::ModuleItem;
    use crate::ast::shared_vec::SharedVec;
    use std::cell::RefCell;
    use std::sync::Arc;
    use std::thread::LocalKey;

    fn initial(body: &str) -> Statement {
        let parsed = crate::parse(&format!(
            "module top; logic a, b, c, clk, enable; initial {body} endmodule"
        ));
        assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
        let crate::ast::Description::Module(module) = &parsed.source.descriptions[0] else {
            panic!("module expected");
        };
        module
            .items
            .iter()
            .find_map(|item| match item {
                ModuleItem::InitialConstruct(initial) => Some(initial.stmt.clone()),
                _ => None,
            })
            .expect("initial expected")
    }

    fn first_lvalue(stmt: &Statement) -> &Expression {
        match &stmt.kind {
            StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
                first_lvalue(&stmts[0])
            }
            StatementKind::BlockingAssign { lvalue, .. } => lvalue,
            _ => panic!("assignment expected"),
        }
    }

    fn block_body(stmt: &Statement) -> &SharedVec<Statement> {
        match &stmt.kind {
            StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => stmts,
            _ => panic!("block expected"),
        }
    }

    fn with_tls_value<T: 'static>(
        key: &'static LocalKey<RefCell<T>>,
        value: T,
        run: impl FnOnce(),
    ) {
        let mut saved = Some(key.with(|cell| cell.replace(value)));
        let _restore = super::super::scopeguard_lite(|| {
            key.with(|cell| *cell.borrow_mut() = saved.take().unwrap());
        });
        run();
    }

    /// §9.3/§9.4: block labels, fork join kinds, edge terms and iff guards
    /// keep their syntax when every operand is a flat root reference.
    #[test]
    fn simple_assignments_blocks_and_event_controls_are_identity_candidates() {
        for source in [
            "begin : boot a = 1; b <= #2 (~a & c); end",
            "begin if (a) begin b = c + 1; end else fork b = 0; c = 1; join end",
            "begin a = a ? {b, c} : {2{b}}; end",
            "begin a = f(b + 1); end",
            "begin a = (b = c); end",
            "begin for (a=0; a<3; a=a+1) begin b[a]=c; end end",
            "begin for (; a;) begin b=c; end end",
            "begin a = b[0]; b[c] = a; end",
            "begin a = b[3:0]; b[c +: 2] = a; b[c -: 2] = a; end",
            "begin case (a) 0: b = c; 1, 2: begin b = 1; end default: b = 0; endcase end",
            "begin case (a) inside [0:3]: b = c; default: b = 0; endcase end",
            "begin while (a) begin b = c; end repeat (2) begin c = b; end end",
            "begin wait (a) begin b = c; end end",
            "begin $display(\"value=%0d\", a); b = $clog2(8); $finish; end",
            "@(posedge clk iff enable) begin a <= b; end",
            "@(posedge clk or negedge enable) begin a <= b; end",
            "@* begin a = b; end",
            "#1 begin a = b; end",
            ";",
        ] {
            assert!(can_preserve_root_stmt(&initial(source)), "{source}");
        }
    }

    /// §23.6/§25.5/§3.12.1: complex references in an operand, a delay or
    /// an event term must still pass through the complete scope rewrite.
    #[test]
    fn nested_reference_conversions_and_unknown_forms_use_the_full_rewrite() {
        for source in [
            "begin a = child.value; end",
            "begin if (a) begin b = child.value; end end",
            "begin a = $unit::b; end",
            "@(posedge child.clk) begin a = b; end",
            "@(posedge clk iff child.enable) begin a = b; end",
            "#(child.delay_value) begin a = b; end",
            "begin a = b[3:0][3:0]; end",
            "begin a = b[child.value]; end",
            "begin a = child.value[0]; end",
            "begin a = b[child.left:0]; end",
            "begin a = int'(b); end",
            "begin $display(child.value); end",
            "begin case (a) 0: b = child.value; endcase end",
            "begin while (child.value) b = c; end",
            "begin wait (child.ready) b = c; end",
            "begin for (int a=0; a<3; a=a+1) b=c; end",
            "begin for (a=child.value; a<3; a=a+1) b=c; end",
            "begin for (a=0; a<3; a=a+1) b=child.value; end",
            "begin repeat (a) b = child.value; end",
            "begin int local_value; a = local_value; end",
            "begin while (a) begin int local_value; b = local_value; end end",
            "begin -> a; end",
        ] {
            assert!(!can_preserve_root_stmt(&initial(source)), "{source}");
        }
    }

    /// §12.7/§23.6: assignment-only loops retain all contextual-cache
    /// checks, including caches on assignment expressions in the step.
    #[test]
    fn assignment_loop_operands_keep_cache_and_rejection_checks() {
        for operand in 0..4 {
            let source = initial("for (a=0; a<3; a=a+1) b=c;");
            assert!(can_preserve_root_stmt(&source));
            let StatementKind::For {
                init,
                condition,
                step,
                ..
            } = &source.kind
            else {
                panic!("for loop expected");
            };
            match operand {
                0 => {
                    let ForInit::Assign { rvalue, .. } = &init[0] else {
                        panic!("assignment initializer expected");
                    };
                    rvalue.cached_width.set(Some(32));
                }
                1 => condition.as_ref().unwrap().cached_width.set(Some(1)),
                2 => step[0].cached_width.set(Some(32)),
                _ => {
                    let ExprKind::AssignExpr { lvalue, .. } = &step[0].kind else {
                        panic!("assignment step expected");
                    };
                    let ExprKind::Ident(name) = &lvalue.kind else {
                        panic!("step target expected");
                    };
                    name.cached_resolved_name.set("old.a".to_string()).unwrap();
                }
            }
            assert!(!can_preserve_root_stmt(&source));
            assert_eq!(
                stmt_rejection(&source).unwrap().phase,
                if operand == 3 {
                    "identity.reject.cache.name"
                } else {
                    "identity.reject.cache.width"
                }
            );
        }
        let source = initial("for (int a=0; a<3; a=a+1) b=c;");
        assert!(!can_preserve_root_stmt(&source));
        assert_eq!(
            stmt_rejection(&source).unwrap().phase,
            "identity.reject.stmt.for_decl"
        );
    }

    /// §11.5.1/§25.5.4: an index retains neither stale contextual state
    /// nor a modport-substitution marker from another rewrite.
    #[test]
    fn select_operands_and_modport_state_require_the_full_rewrite() {
        let source = initial("a = b[0];");
        let StatementKind::BlockingAssign { rvalue, .. } = &source.kind else {
            panic!("assignment expected");
        };
        rvalue.cached_width.set(Some(1));
        assert!(!can_preserve_root_stmt(&source));

        let source = initial("a = b[c];");
        let StatementKind::BlockingAssign { rvalue, .. } = &source.kind else {
            panic!("assignment expected");
        };
        let ExprKind::Index { index, .. } = &rvalue.kind else {
            panic!("index expected");
        };
        index.cached_width.set(Some(32));
        assert!(!can_preserve_root_stmt(&source));

        let source = initial("a = b[0];");
        let StatementKind::BlockingAssign { rvalue, .. } = &source.kind else {
            panic!("assignment expected");
        };
        let ExprKind::Index { expr: base, .. } = &rvalue.kind else {
            panic!("index expected");
        };
        let ExprKind::Ident(name) = &base.kind else {
            panic!("identifier expected");
        };
        name.cached_signal_id.set(Some(7));
        assert!(!can_preserve_root_stmt(&source));

        let source = initial("a = b[3:0];");
        let StatementKind::BlockingAssign { rvalue, .. } = &source.kind else {
            panic!("assignment expected");
        };
        let ExprKind::RangeSelect { right, .. } = &rvalue.kind else {
            panic!("range expected");
        };
        right.cached_width.set(Some(32));
        assert!(!can_preserve_root_stmt(&source));

        let source = initial("a = b[0];");
        let saved = MODPORT_SUBST_FLAG.with(|flag| flag.replace(true));
        let _restore = super::super::scopeguard_lite(|| {
            MODPORT_SUBST_FLAG.with(|flag| flag.set(saved));
        });
        assert!(!can_preserve_root_stmt(&source));
    }

    #[test]
    fn type_queries_and_case_binding_patterns_require_the_full_rewrite() {
        for name in [
            "$bits",
            "$left",
            "$right",
            "$high",
            "$low",
            "$size",
            "$increment",
            "$dimensions",
            "$unpacked_dimensions",
        ] {
            assert!(!can_preserve_root_stmt(&initial(&format!("a = {name}(b);"))));
        }
        let mut source = initial("case (a) 0: b = c; endcase");
        let StatementKind::Case { items, .. } = &mut source.kind else {
            panic!("case expected");
        };
        items[0].pattern = Some(Box::new(crate::ast::stmt::Pattern::Binding(
            crate::ast::Identifier {
                name: "captured".to_string(),
                span: crate::ast::Span::dummy(),
            },
        )));
        assert!(!can_preserve_root_stmt(&source));
    }

    #[test]
    fn case_loop_and_system_call_operand_caches_require_invalidation() {
        let source = initial("case (a) 0: b = c; endcase");
        let StatementKind::Case { items, .. } = &source.kind else {
            panic!("case expected");
        };
        items[0].patterns[0].cached_width.set(Some(32));
        assert!(!can_preserve_root_stmt(&source));

        let source = initial("while (a) b = c;");
        let StatementKind::While { condition, .. } = &source.kind else {
            panic!("while expected");
        };
        condition.cached_width.set(Some(1));
        assert!(!can_preserve_root_stmt(&source));

        let source = initial("wait (a) b = c;");
        let StatementKind::Wait { condition, .. } = &source.kind else {
            panic!("wait expected");
        };
        condition.cached_width.set(Some(1));
        assert!(!can_preserve_root_stmt(&source));

        let source = initial("$display(a);");
        let StatementKind::Expr(expr) = &source.kind else {
            panic!("expression expected");
        };
        let ExprKind::SystemCall { args, .. } = &expr.kind else {
            panic!("system call expected");
        };
        args[0].cached_width.set(Some(1));
        assert!(!can_preserve_root_stmt(&source));
    }

    #[test]
    fn previously_populated_contextual_caches_require_invalidation() {
        let source = initial("begin a = b; end");
        first_lvalue(&source).cached_width.set(Some(1));
        assert!(!can_preserve_root_stmt(&source));

        let source = initial("begin a = b; end");
        let ExprKind::Ident(name) = &first_lvalue(&source).kind else {
            panic!("name expected");
        };
        name.cached_signal_id.set(Some(7));
        assert!(!can_preserve_root_stmt(&source));

        let source = initial("begin a = b; end");
        let ExprKind::Ident(name) = &first_lvalue(&source).kind else {
            panic!("name expected");
        };
        name.cached_resolved_name.set("old.a".into()).unwrap();
        assert!(!can_preserve_root_stmt(&source));
    }

    #[test]
    fn nested_call_and_event_guard_caches_require_invalidation() {
        let source = initial("a = f(b + 1);");
        let StatementKind::BlockingAssign { rvalue, .. } = &source.kind else {
            panic!("assignment expected");
        };
        let ExprKind::Call { args, .. } = &rvalue.kind else {
            panic!("call expected");
        };
        args[0].cached_width.set(Some(8));
        assert!(!can_preserve_root_stmt(&source));

        let source = initial("@(posedge clk iff enable) begin a = b; end");
        let StatementKind::TimingControl {
            control: TimingControl::Event(EventControl::EventExpr(events)),
            ..
        } = &source.kind
        else {
            panic!("event expression expected");
        };
        events[0].iff.as_ref().unwrap().cached_width.set(Some(1));
        assert!(!can_preserve_root_stmt(&source));
    }

    #[test]
    fn upward_binding_is_rejected_even_for_a_flat_identifier() {
        let mut source = initial("a = b;");
        let StatementKind::BlockingAssign { rvalue, .. } = &mut source.kind else {
            panic!("assignment expected");
        };
        let ExprKind::Ident(name) = &mut rvalue.kind else {
            panic!("name expected");
        };
        name.bound = Bound::UPWARD;
        assert!(!can_preserve_root_stmt(&source));
    }

    #[test]
    fn specialization_and_rename_contexts_are_excluded() {
        let source = initial("begin a = b; end");
        assert!(can_preserve_root_stmt(&source));
        with_tls_value(
            &GEN_RENAME_TLS,
            vec![super::super::GenRename::default()],
            || {
                assert!(!can_preserve_root_stmt(&source));
            },
        );
        with_tls_value(&TYPE_BIND_WIDTHS_TLS, Some(Default::default()), || {
            assert!(!can_preserve_root_stmt(&source));
        });
        with_tls_value(&TYPE_BIND_QUERIES_TLS, Some(Default::default()), || {
            assert!(!can_preserve_root_stmt(&source));
        });
        with_tls_value(&TYPE_BIND_TYPES_TLS, Some(Default::default()), || {
            assert!(!can_preserve_root_stmt(&source));
        });
        with_tls_value(&PKG_FLATTEN_ONLY, Some(Default::default()), || {
            assert!(!can_preserve_root_stmt(&source));
        });
        assert!(can_preserve_root_stmt(&source));
    }

    /// §23.6: taking the identity path must not override an explicit request
    /// for private enabled caches or for disabled contextual memoization.
    #[test]
    fn identity_clone_honors_fresh_and_disabled_cache_modes() {
        let source = initial("begin fork begin a = b; end join end");
        let ordinary = source.clone();
        assert!(can_preserve_root_stmt(&source));
        assert!(Arc::ptr_eq(
            block_body(&source).as_arc(),
            block_body(&ordinary).as_arc()
        ));

        let fresh = crate::ast::cache::with_fresh_scope_caches(|| {
            assert!(can_preserve_root_stmt(&source));
            source.clone()
        });
        assert!(!Arc::ptr_eq(
            block_body(&source).as_arc(),
            block_body(&fresh).as_arc()
        ));
        first_lvalue(&fresh).cached_width.set(Some(8));
        assert_eq!(first_lvalue(&fresh).cached_width.get(), Some(8));
        assert_eq!(first_lvalue(&source).cached_width.get(), None);

        let disabled = crate::ast::cache::without_scope_caches(|| {
            assert!(can_preserve_root_stmt(&source));
            source.clone()
        });
        assert!(!Arc::ptr_eq(
            block_body(&source).as_arc(),
            block_body(&disabled).as_arc()
        ));
        first_lvalue(&disabled).cached_width.set(Some(16));
        assert_eq!(first_lvalue(&disabled).cached_width.get(), None);
        let ExprKind::Ident(name) = &first_lvalue(&disabled).kind else {
            panic!("name expected");
        };
        name.cached_signal_id.set(Some(9));
        assert!(name.cached_resolved_name.set("ignored.a".into()).is_err());
        assert_eq!(name.cached_signal_id.get(), None);
        assert_eq!(first_lvalue(&source).cached_width.get(), None);
    }
}
