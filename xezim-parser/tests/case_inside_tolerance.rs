//! IEEE 1800-2023 §11.4.13 and §12.5.4: both set membership forms
//! parse the same tolerance bounds. Each bound is a `$__xz_tolerance`
//! call, which evaluation computes from the operand types.

use sv_parser::ast::Description;
use sv_parser::ast::decl::ModuleItem;
use sv_parser::ast::expr::{ExprKind, Expression, NumberLiteral, TOLERANCE_BOUND_FN};
use sv_parser::ast::stmt::{CaseKind, StatementKind};

const SOURCE: &str = r#"
module top;
  int value;
  initial begin
    case (value) inside
      [2+8 +/- (1+1)], [40 +%- 10], [(value inside {[40 +%- 10]}):2]: ;
      default: ;
    endcase
    if (value inside {[2+8 +/- (1+1)], [40 +%- 10]}) value = 1;
  end
endmodule
"#;

const PLAIN_RANGES: &str = r#"
module top;
  int value, c;
  initial
    if (value inside {[1 << 3 : 12], [c == 1 : 8], [c ? 1 : 2 : 8]})
      value = 1;
endmodule
"#;

/// The modes of a tolerance range's two bound calls: 0/1 for `+/-`, 2/3 for
/// `+%-`.
fn bound_ops(range: &Expression) -> (String, String) {
    let ExprKind::Range(lo, hi) = &range.kind else {
        panic!("expected a range");
    };
    let mode = |e: &Expression| match &e.kind {
        ExprKind::SystemCall { name, args } if name == TOLERANCE_BOUND_FN && args.len() == 3 => {
            match &args[2].kind {
                ExprKind::Number(NumberLiteral::Integer { value, .. }) => value.to_string(),
                _ => panic!("expected a literal mode"),
            }
        }
        _ => panic!("expected a tolerance bound"),
    };
    (mode(lo), mode(hi))
}

#[test]
fn tolerance_case_items_share_inside_range_lowering() {
    sv_parser::set_sv2023(true);
    let parsed = sv_parser::parse(SOURCE);
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
    let Description::Module(module) = &parsed.source.descriptions[0] else {
        panic!("expected a module");
    };
    let Some(stmts) = module.items.iter().find_map(|item| match item {
        ModuleItem::InitialConstruct(p) => match &p.stmt.kind {
            StatementKind::SeqBlock { stmts, .. } => Some(stmts),
            _ => None,
        },
        _ => None,
    }) else {
        panic!("expected an initial block");
    };
    let StatementKind::Case {
        kind: CaseKind::CaseInside,
        items,
        ..
    } = &stmts[0].kind
    else {
        panic!("expected a set membership case");
    };
    let StatementKind::If { condition, .. } = &stmts[1].kind else {
        panic!("expected an if statement");
    };
    let ExprKind::Inside { ranges, .. } = &condition.kind else {
        panic!("expected an inside expression");
    };
    let patterns = &items[0].patterns;
    assert_eq!(patterns.len(), 3);
    assert_eq!(ranges.len(), 2);
    assert!(items[1].is_default);
    assert_eq!(bound_ops(&patterns[0]), ("0".into(), "1".into()));
    assert_eq!(bound_ops(&patterns[1]), ("2".into(), "3".into()));
    for (pattern, range) in patterns.iter().zip(ranges) {
        assert_eq!(bound_ops(pattern), bound_ops(range));
    }
    let ExprKind::Range(lo, _) = &patterns[2].kind else {
        panic!("expected a colon range");
    };
    assert!(
        matches!(&lo.kind, ExprKind::Paren(inner) if matches!(inner.kind, ExprKind::Inside { .. }))
    );

    let plain = sv_parser::parse(PLAIN_RANGES);
    assert!(plain.errors.is_empty(), "{:?}", plain.errors);

    // §11.4.13: each tolerance separator is a single token.
    for split in ["+ /-", "+/ -", "+ /* gap */ /-", "+% -"] {
        let source = format!(
            "module top; int value; initial if (value inside {{[10 {split} 2]}}) ; endmodule"
        );
        assert!(!sv_parser::parse(&source).errors.is_empty(), "{split}");
    }

    // This test binary is the sole user of the parser's process-wide mode.
    sv_parser::set_sv2023(false);
    let plain = sv_parser::parse(PLAIN_RANGES);
    assert!(plain.errors.is_empty(), "{:?}", plain.errors);
    assert!(!sv_parser::parse(SOURCE).errors.is_empty());
}
