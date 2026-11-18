//! IEEE 1800-2023 §10.4.2/§16.14.6/§23.6: optional timing storage retains
//! its values, independent rewrites and contextual-cache clone rules.

use xezim_core::ast::cache::{
    LiteralCache, NameCache, SignalCache, with_fresh_scope_caches, without_scope_caches,
};
use xezim_core::ast::expr::{
    BinaryOp, ExprKind, Expression, HierPathSegment, HierarchicalIdentifier, NumberBase,
    NumberLiteral,
};
use xezim_core::ast::stmt::{
    AssertionKind, AssertionStatement, Edge, EventExpr, Statement, StatementKind,
};
use xezim_core::ast::{Identifier, Span};

fn ident(name: &str) -> Expression {
    let span = Span::new(10, 20);
    Expression::new(
        ExprKind::Ident(HierarchicalIdentifier {
            root: None,
            path: vec![HierPathSegment {
                name: Identifier {
                    name: name.into(),
                    span,
                },
                selects: Vec::new(),
            }],
            span,
            cached_signal_id: SignalCache::default(),
            cached_resolved_name: NameCache::default(),
            bound: Default::default(),
        }),
        span,
    )
}

fn integer(value: u64) -> Expression {
    Expression::new(
        ExprKind::Number(NumberLiteral::Integer {
            size: Some(32),
            signed: false,
            base: NumberBase::Decimal,
            value: value.to_string(),
            cached_val: LiteralCache::new(Some((value, 0, 32))),
        }),
        Span::new(21, 23),
    )
}

fn fixture(present: bool) -> Statement {
    let delay = present.then(|| {
        Box::new(Expression::new(
            ExprKind::Binary {
                op: BinaryOp::Add,
                left: Box::new(ident("delay_ticks")),
                right: Box::new(integer(3)),
            },
            Span::new(24, 30),
        ))
    });
    let inferred_clock = present.then(|| {
        Box::new(EventExpr {
            edge: Some(Edge::Posedge),
            expr: ident("clk"),
            iff: Some(Expression::new(
                ExprKind::Binary {
                    op: BinaryOp::Eq,
                    left: Box::new(ident("enable")),
                    right: Box::new(integer(1)),
                },
                Span::new(31, 40),
            )),
            span: Span::new(41, 50),
        })
    });
    Statement::new(
        StatementKind::SeqBlock {
            name: None,
            stmts: vec![
                // Populate the AST field directly: the ordinary parser may
                // encode source-level intra-assignment timing as a marker.
                Statement::new(
                    StatementKind::NonblockingAssign {
                        lvalue: ident("q"),
                        delay,
                        rvalue: integer(17),
                    },
                    Span::new(51, 60),
                ),
                Statement::new(
                    StatementKind::Assertion(AssertionStatement {
                        kind: AssertionKind::Assert,
                        expr: ident("ok"),
                        action: None,
                        else_action: None,
                        is_property: true,
                        is_sequence: false,
                        deferred: None,
                        label: None,
                        procedural: true,
                        inferred_clock,
                        span: Span::new(61, 70),
                    }),
                    Span::new(61, 70),
                ),
            ]
            .into(),
        },
        Span::new(0, 80),
    )
}

fn statements(statement: &Statement) -> &[Statement] {
    let StatementKind::SeqBlock { stmts, .. } = &statement.kind else {
        panic!("sequence expected");
    };
    stmts
}

fn delay(statement: &Statement) -> Option<&Expression> {
    let StatementKind::NonblockingAssign { delay, .. } = &statements(statement)[0].kind else {
        panic!("NBA expected");
    };
    delay.as_deref()
}

fn clock(statement: &Statement) -> Option<&EventExpr> {
    let StatementKind::Assertion(assertion) = &statements(statement)[1].kind else {
        panic!("assertion expected");
    };
    assertion.inferred_clock.as_deref()
}

fn assert_ident(expr: &Expression, expected: &str) {
    let ExprKind::Ident(name) = &expr.kind else {
        panic!("identifier expected");
    };
    assert!(name.root.is_none());
    assert_eq!(name.path.len(), 1);
    assert_eq!(name.path[0].name.name, expected);
    assert!(name.path[0].selects.is_empty());
}

fn literal_cache(expr: &Expression, expected: u64) -> Option<(u64, u64, u32)> {
    let ExprKind::Number(NumberLiteral::Integer {
        size,
        signed,
        base,
        value,
        cached_val,
    }) = &expr.kind
    else {
        panic!("integer expected");
    };
    assert_eq!(*size, Some(32));
    assert!(!*signed);
    assert_eq!(*base, NumberBase::Decimal);
    assert_eq!(value, &expected.to_string());
    cached_val.get()
}

fn assert_payloads(statement: &Statement, present: bool) {
    assert_eq!(statement.span, Span::new(0, 80));
    let StatementKind::NonblockingAssign { lvalue, rvalue, .. } = &statements(statement)[0].kind
    else {
        panic!("NBA expected");
    };
    assert_ident(lvalue, "q");
    let _ = literal_cache(rvalue, 17);
    assert_eq!(delay(statement).is_some(), present);
    if let Some(delay) = delay(statement) {
        let ExprKind::Binary { op, left, right } = &delay.kind else {
            panic!("delay sum expected");
        };
        assert_eq!(*op, BinaryOp::Add);
        assert_ident(left, "delay_ticks");
        let _ = literal_cache(right, 3);
        assert_eq!(delay.span, Span::new(24, 30));
    }
    assert_eq!(clock(statement).is_some(), present);
    if let Some(clock) = clock(statement) {
        assert_eq!(clock.edge, Some(Edge::Posedge));
        assert_eq!(clock.span, Span::new(41, 50));
        assert_ident(&clock.expr, "clk");
        let ExprKind::Binary { op, left, right } = &clock.iff.as_ref().unwrap().kind else {
            panic!("iff comparison expected");
        };
        assert_eq!(*op, BinaryOp::Eq);
        assert_ident(left, "enable");
        let _ = literal_cache(right, 1);
    }
}

fn contextual_operands(statement: &Statement) -> Vec<&Expression> {
    let mut expressions = Vec::new();
    if let Some(delay) = delay(statement) {
        expressions.push(delay);
        let ExprKind::Binary { left, .. } = &delay.kind else {
            panic!("delay sum expected");
        };
        expressions.push(left);
    }
    if let Some(clock) = clock(statement) {
        expressions.push(&clock.expr);
        let iff = clock.iff.as_ref().unwrap();
        expressions.push(iff);
        let ExprKind::Binary { left, .. } = &iff.kind else {
            panic!("iff comparison expected");
        };
        expressions.push(left);
    }
    expressions
}

fn seed_context_caches(statement: &Statement) {
    for expr in contextual_operands(statement) {
        expr.cached_width.set(Some(64));
        if let ExprKind::Ident(name) = &expr.kind {
            name.cached_signal_id.set(Some(77));
            name.cached_resolved_name
                .set("source.binding".into())
                .unwrap();
        }
    }
}

fn assert_empty_context_caches(statement: &Statement) {
    for expr in contextual_operands(statement) {
        assert_eq!(expr.cached_width.get(), None);
        if let ExprKind::Ident(name) = &expr.kind {
            assert_eq!(name.cached_signal_id.get(), None);
            assert!(name.cached_resolved_name.get().is_none());
        }
    }
}

#[test]
fn optional_timing_payloads_round_trip_through_bincode_and_json() {
    for present in [false, true] {
        let original = fixture(present);
        seed_context_caches(&original);
        let bytes = bincode::serde::encode_to_vec(&original, xezim_core::xez_bincode_config())
            .expect("encode timing payloads");
        let (binary, consumed): (Statement, usize) =
            bincode::serde::decode_from_slice(&bytes, xezim_core::xez_bincode_config())
                .expect("decode timing payloads");
        assert_eq!(consumed, bytes.len());
        assert_payloads(&binary, present);
        assert_empty_context_caches(&binary);

        let json = serde_json::to_value(&original).expect("JSON timing payloads");
        let body = &json["kind"]["SeqBlock"]["stmts"];
        assert_eq!(
            body[0]["kind"]["NonblockingAssign"]["delay"].is_object(),
            present
        );
        assert_eq!(
            body[1]["kind"]["Assertion"]["inferred_clock"].is_object(),
            present
        );
        if !present {
            assert!(body[0]["kind"]["NonblockingAssign"]["delay"].is_null());
            assert!(body[1]["kind"]["Assertion"]["inferred_clock"].is_null());
        }
        let restored: Statement = serde_json::from_value(json).expect("restore timing JSON");
        assert_payloads(&restored, present);
        assert_empty_context_caches(&restored);
    }
}

#[test]
fn rewriting_one_copy_keeps_timing_values_and_clock_guards_independent() {
    let original = fixture(true);
    let mut changed = original.clone();
    let StatementKind::SeqBlock { stmts, .. } = &mut changed.kind else {
        panic!("sequence expected");
    };
    let StatementKind::NonblockingAssign { delay: delayed, .. } = &mut stmts[0].kind else {
        panic!("NBA expected");
    };
    **delayed.as_mut().unwrap() = integer(9);
    let StatementKind::Assertion(assertion) = &mut stmts[1].kind else {
        panic!("assertion expected");
    };
    let changed_clock = assertion.inferred_clock.as_deref_mut().unwrap();
    changed_clock.edge = Some(Edge::Negedge);
    changed_clock.expr = ident("other_clock");
    changed_clock.iff = Some(ident("other_enable"));

    assert_payloads(&original, true);
    let _ = literal_cache(delay(&changed).unwrap(), 9);
    let changed_clock = clock(&changed).unwrap();
    assert_eq!(changed_clock.edge, Some(Edge::Negedge));
    assert_ident(&changed_clock.expr, "other_clock");
    assert_ident(changed_clock.iff.as_ref().unwrap(), "other_enable");
}

#[test]
fn fresh_timing_copies_reset_context_caches_and_preserve_literal_values() {
    let original = fixture(true);
    seed_context_caches(&original);
    let private = with_fresh_scope_caches(|| original.clone());
    assert_payloads(&private, true);
    assert_empty_context_caches(&private);
    for expr in contextual_operands(&private) {
        expr.cached_width.set(Some(8));
        assert_eq!(expr.cached_width.get(), Some(8));
        if let ExprKind::Ident(name) = &expr.kind {
            name.cached_signal_id.set(Some(9));
            assert_eq!(name.cached_signal_id.get(), Some(9));
            name.cached_resolved_name
                .set("private.binding".into())
                .unwrap();
        }
    }
    for expr in contextual_operands(&original) {
        assert_eq!(expr.cached_width.get(), Some(64));
        if let ExprKind::Ident(name) = &expr.kind {
            assert_eq!(name.cached_signal_id.get(), Some(77));
            assert_eq!(
                name.cached_resolved_name.get().map(String::as_str),
                Some("source.binding")
            );
        }
    }
    let ExprKind::Binary { right, .. } = &delay(&private).unwrap().kind else {
        panic!("delay sum expected");
    };
    assert_eq!(literal_cache(right, 3), Some((3, 0, 32)));
}

#[test]
fn disabled_timing_copies_cannot_capture_another_scopes_context() {
    let original = fixture(true);
    seed_context_caches(&original);
    let shared = without_scope_caches(|| original.clone());
    assert_payloads(&shared, true);
    assert_empty_context_caches(&shared);
    for expr in contextual_operands(&shared) {
        expr.cached_width.set(Some(8));
        if let ExprKind::Ident(name) = &expr.kind {
            name.cached_signal_id.set(Some(9));
            assert!(
                name.cached_resolved_name
                    .set("ignored.binding".into())
                    .is_err()
            );
        }
    }
    assert_empty_context_caches(&shared);
    for expr in contextual_operands(&original) {
        assert_eq!(expr.cached_width.get(), Some(64));
    }
}
