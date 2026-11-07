//! IEEE 1800-2023 §6.6.7, §7.2, §10.9.2 and §13.4: an unresolved struct
//! driver is lowered like an ordinary struct assignment. A call in one
//! pattern item must survive exactly once, not be copied to every member.

use xezim_core::ast::expr::{ExprKind, Expression};

#[test]
fn pattern_item_call_is_emitted_once() {
    for direction in ["output", "inout"] {
        let src = format!(
            r#"
typedef struct {{ real V; real R; int code; }} e_t;
nettype e_t enet;
module child(input real v, {direction} enet p);
  function automatic real stamp(input real x);
    $display("stamp %f", x);
    return x;
  endfunction
  assign p = '{{code: 7, R: 1.0, V: stamp(v)}};
endmodule
module top;
  real v;
  enet n;
  child u(.v(v), .p(n));
endmodule
"#
        );
        let (_, model) = xezim_core::parse_and_elaborate_multi(
            &[src],
            Some("top"),
            &[],
            &["no_resolver.sv".to_string()],
            &[],
        )
        .expect("elaborate");

        let mut calls = 0;
        for ca in &model.continuous_assigns {
            fn check_rhs(e: &Expression, calls: &mut usize) {
                match &e.kind {
                    ExprKind::Call { .. } => *calls += 1,
                    ExprKind::MemberAccess { expr, .. } => {
                        assert!(
                            !matches!(expr.kind, ExprKind::AssignmentPattern(_)),
                            "member select of a pattern: {e:?}"
                        );
                        check_rhs(expr, calls);
                    }
                    _ => {}
                }
            }
            check_rhs(&ca.rhs, &mut calls);
        }
        assert_eq!(calls, 1, "{direction}: dropped or repeated pattern item");
    }
}
