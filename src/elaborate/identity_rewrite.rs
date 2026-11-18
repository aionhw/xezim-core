//! IEEE 1800-2023 §9.2, §9.3, §23.6: retain an unchanged root process's
//! statement storage without skipping required scope or reference rewrites.

use super::{
    GEN_RENAME_TLS, PKG_FLATTEN_ONLY, TYPE_BIND_QUERIES_TLS, TYPE_BIND_TYPES_TLS,
    TYPE_BIND_WIDTHS_TLS,
};
use crate::ast::expr::{ExprKind, Expression};
use crate::ast::stmt::{EventControl, Statement, StatementKind, TimingControl};

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
        && PKG_FLATTEN_ONLY.with(|packages| packages.borrow().is_none());
    root_context && identity_stmt(stmt)
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
                && delay.as_ref().is_none_or(identity_expr)
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
        // Declarations, loops, assertions, event triggers, disables and all
        // other forms keep their existing rewrite and scope handling.
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
        ExprKind::Conditional {
            condition,
            then_expr,
            else_expr,
        } => identity_expr(condition) && identity_expr(then_expr) && identity_expr(else_expr),
        ExprKind::Concatenation(parts) => parts.iter().all(identity_expr),
        ExprKind::Replication { count, exprs } => {
            identity_expr(count) && exprs.iter().all(identity_expr)
        }
        ExprKind::Call { func, args } => {
            // In particular, a member/scoped/upward callee is excluded by
            // the operand predicate; no call is evaluated by this rewrite.
            identity_expr(func) && args.iter().all(identity_expr)
        }
        // Selects can collapse after rewriting; member paths can become
        // hierarchical references. System calls may fold type queries.
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
            "begin a = b[0]; end",
            "begin a = b[3:0][3:0]; end",
            "begin a = int'(b); end",
            "begin $display(a); end",
            "begin int local_value; a = local_value; end",
            "begin while (a) b = c; end",
            "begin -> a; end",
        ] {
            assert!(!can_preserve_root_stmt(&initial(source)), "{source}");
        }
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
