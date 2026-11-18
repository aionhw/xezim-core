//! IEEE 1800-2023 §12.5/§12.6: ordinary case arms omit pattern payloads;
//! matching arms retain their binding names and optional guards.

use sv_parser::ast::Description;
use sv_parser::ast::decl::ModuleItem;
use sv_parser::ast::expr::{BinaryOp, ExprKind, Expression, NumberLiteral};
use sv_parser::ast::stmt::{CaseItem, Pattern, StatementKind};

fn case_items(body: &str) -> Vec<CaseItem> {
    let parsed = sv_parser::parse(&format!(
        "module top; typedef union tagged {{ void Invalid; int Valid; }} item_t; \
         item_t value; int result; initial {body} endmodule"
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
    items
}

fn unparen(expr: &Expression) -> &Expression {
    match &expr.kind {
        ExprKind::Paren(inner) => unparen(inner),
        _ => expr,
    }
}

#[test]
fn matching_cases_keep_tag_bindings_and_guard_operands() {
    let items = case_items(
        "case (value) matches \
         tagged Valid .n &&& (n > 100): result=n; \
         tagged Valid .n: result=n+1; default: result=0; endcase",
    );
    assert_eq!(items.len(), 3);
    for item in &items[..2] {
        assert!(item.patterns.is_empty());
        let Pattern::Tagged { tag, inner } = item.pattern.as_deref().unwrap() else {
            panic!("tagged pattern expected");
        };
        assert_eq!(tag.name, "Valid");
        let Pattern::Binding(name) = inner.as_deref().unwrap() else {
            panic!("binding expected");
        };
        assert_eq!(name.name, "n");
    }
    let guard = unparen(items[0].guard.as_deref().unwrap());
    let ExprKind::Binary { op, left, right } = &guard.kind else {
        panic!("comparison expected");
    };
    assert_eq!(*op, BinaryOp::Gt);
    let ExprKind::Ident(name) = &left.kind else {
        panic!("guard binding reference expected");
    };
    assert_eq!(name.path[0].name.name, "n");
    let ExprKind::Number(NumberLiteral::Integer { value, .. }) = &right.kind else {
        panic!("guard bound expected");
    };
    assert_eq!(value, "100");
    assert!(items[1].guard.is_none());
    assert!(items[2].is_default);
    assert!(items[2].pattern.is_none());
    assert!(items[2].guard.is_none());
}

#[test]
fn ordinary_case_arms_keep_only_their_value_patterns() {
    let items = case_items("case (result) 0, 1: result=2; default: result=3; endcase");
    assert_eq!(items.len(), 2);
    assert_eq!(items[0].patterns.len(), 2);
    assert!(!items[0].is_default);
    assert!(items[1].is_default);
    for item in items {
        assert!(item.pattern.is_none());
        assert!(item.guard.is_none());
    }
}
