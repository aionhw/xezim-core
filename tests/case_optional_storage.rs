//! IEEE 1800-2023 §12.6/§23.6: optional case payloads retain their serialized
//! values and independent contextual caches under private clone modes.

use xezim_core::ast::cache::{with_fresh_scope_caches, without_scope_caches};
use xezim_core::ast::decl::ModuleItem;
use xezim_core::ast::expr::{ExprKind, Expression, NumberLiteral};
use xezim_core::ast::stmt::{CaseItem, Pattern, Statement, StatementKind};
use xezim_core::ast::{Description, Span};

fn fixture(present: bool) -> CaseItem {
    let body = if present {
        "case (value) matches 7 &&& (result > 0): result=1; endcase"
    } else {
        "case (value) 7: result=1; endcase"
    };
    let parsed = xezim_core::parse(&format!(
        "module top; int value,result; initial {body} endmodule"
    ));
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
    let Description::Module(module) = parsed.source.descriptions.into_iter().next().unwrap() else {
        panic!("module expected");
    };
    let stmt = module
        .items
        .into_iter()
        .find_map(|item| match item {
            ModuleItem::InitialConstruct(p) => Some(p.stmt),
            _ => None,
        })
        .unwrap();
    let StatementKind::Case { items, .. } = stmt.kind else {
        panic!("case expected");
    };
    items.into_iter().next().unwrap()
}

#[derive(serde::Serialize)]
struct InlineCaseItem {
    patterns: Vec<Expression>,
    is_default: bool,
    stmt: Statement,
    span: Span,
    pattern: Option<Pattern>,
    guard: Option<Expression>,
}

#[test]
fn boxed_case_fields_preserve_json_and_bincode_values() {
    for present in [false, true] {
        let item = fixture(present);
        let inline = InlineCaseItem {
            patterns: item.patterns.clone(),
            is_default: item.is_default,
            stmt: item.stmt.clone(),
            span: item.span,
            pattern: item.pattern.as_deref().cloned(),
            guard: item.guard.as_deref().cloned(),
        };
        let json = serde_json::to_value(&item).unwrap();
        assert_eq!(json, serde_json::to_value(&inline).unwrap());
        let restored: CaseItem = serde_json::from_value(json.clone()).unwrap();
        assert_eq!(serde_json::to_value(restored).unwrap(), json);

        let bytes = bincode::serde::encode_to_vec(&item, bincode::config::standard()).unwrap();
        assert_eq!(
            bytes,
            bincode::serde::encode_to_vec(inline, bincode::config::standard()).unwrap()
        );
        let (restored, used): (CaseItem, usize) =
            bincode::serde::decode_from_slice(&bytes, bincode::config::standard()).unwrap();
        assert_eq!(used, bytes.len());
        assert_eq!(serde_json::to_value(restored).unwrap(), json);
    }
}

fn pattern_expr(item: &CaseItem) -> &Expression {
    let Pattern::Expr(expr) = item.pattern.as_deref().unwrap() else {
        panic!("constant-expression pattern expected");
    };
    expr
}

#[test]
fn boxed_case_clones_preserve_values_and_private_cache_modes() {
    for fresh in [true, false] {
        let source = fixture(true);
        let pattern = pattern_expr(&source);
        pattern.cached_width.set(Some(32));
        source.guard.as_deref().unwrap().cached_width.set(Some(1));
        let ExprKind::Number(NumberLiteral::Integer { cached_val, .. }) = &pattern.kind else {
            panic!("integer expected");
        };
        cached_val.set(Some((7, 0, 32)));
        let mut copy = if fresh {
            with_fresh_scope_caches(|| source.clone())
        } else {
            without_scope_caches(|| source.clone())
        };
        let pattern = pattern_expr(&copy);
        assert_eq!(pattern.cached_width.get(), None);
        assert_eq!(copy.guard.as_deref().unwrap().cached_width.get(), None);
        let ExprKind::Number(NumberLiteral::Integer { cached_val, .. }) = &pattern.kind else {
            panic!("copied integer expected");
        };
        assert_eq!(cached_val.get(), Some((7, 0, 32)));
        pattern.cached_width.set(Some(64));
        copy.guard.as_deref().unwrap().cached_width.set(Some(8));
        assert_eq!(pattern.cached_width.get(), fresh.then_some(64));
        assert_eq!(
            copy.guard.as_deref().unwrap().cached_width.get(),
            fresh.then_some(8)
        );
        assert_eq!(pattern_expr(&source).cached_width.get(), Some(32));
        assert_eq!(source.guard.as_deref().unwrap().cached_width.get(), Some(1));
        **copy.pattern.as_mut().unwrap() = Pattern::Wildcard;
        copy.guard.as_mut().unwrap().span = Span::dummy();
        assert!(matches!(source.pattern.as_deref(), Some(Pattern::Expr(_))));
        assert_ne!(source.guard.as_deref().unwrap().span, Span::dummy());
    }
}
