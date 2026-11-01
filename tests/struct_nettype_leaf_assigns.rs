//! IEEE 1800-2023 §6.6.7 / §7.2: a struct nettype's resolved value is written
//! member by member, each target named by its leaf path (`n.V`), and an
//! identifier driver or alias is read by its leaves too.

const SRC: &str = r#"package ee;
  typedef struct { real V; real I; real R; } ee_t;
  function automatic ee_t res(input ee_t d[]);
    ee_t r;
    r = '{0.0, 0.0, 0.0};
    foreach (d[k]) begin r.V += d[k].V; r.I += d[k].I; r.R += d[k].R; end
    return r;
  endfunction
  nettype ee_t eenet with res;
endpackage
import ee::*;
module src(input real v, output eenet p);
  ee_t t;
  assign t = '{v, 0.0, 1.0};
  assign p = t;
endmodule
module top;
  real v;
  eenet n;
  src u0(.v(v), .p(n));
  src u1(.v(v), .p(n));
endmodule"#;

fn design() -> xezim_core::elaborate::ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[SRC.to_string()],
        Some("top"),
        &[],
        &["ee.sv".to_string()],
        &[],
    )
    .expect("elaborate")
    .1
}

fn has_member_access(e: &xezim_core::ast::expr::Expression) -> bool {
    use xezim_core::ast::expr::{AssignmentPatternItem, ExprKind};
    match &e.kind {
        ExprKind::MemberAccess { expr, .. } => {
            // `res(...).V` is the resolved value's member: legitimate.
            !matches!(expr.kind, ExprKind::Call { .. }) || has_member_access(expr)
        }
        ExprKind::Call { args, .. } => args.iter().any(has_member_access),
        ExprKind::AssignmentPattern(items) => items.iter().any(|it| match it {
            AssignmentPatternItem::Ordered(x) => has_member_access(x),
            _ => false,
        }),
        _ => false,
    }
}

#[test]
fn resolved_members_use_leaf_paths() {
    let model = design();
    let mut leaf_targets = 0;
    for ca in &model.continuous_assigns {
        let xezim_core::ast::expr::ExprKind::Ident(h) = &ca.lhs.kind else {
            assert!(
                !matches!(
                    ca.lhs.kind,
                    xezim_core::ast::expr::ExprKind::MemberAccess { .. }
                ),
                "member-access target: {:?}",
                ca.lhs
            );
            continue;
        };
        let name: Vec<&str> = h.path.iter().map(|s| s.name.name.as_str()).collect();
        if matches!(name.last(), Some(&("V" | "I" | "R"))) {
            leaf_targets += 1;
            assert!(!has_member_access(&ca.rhs), "member access in {:?}", ca.rhs);
        }
    }
    assert!(leaf_targets >= 3, "no leaf-path member assigns");
}
