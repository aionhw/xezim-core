//! §26.3: a package member read by a continuous assignment that writes
//! another scope (a generate block's net, a child's port, a hierarchical
//! target) stays a package reference, while the right-hand side's other
//! names are rooted to the writing scope.

use xezim_core::ast::expr::{ExprKind, Expression};
use xezim_core::elaborate::ElaboratedModule;

fn elab(src: &str) -> ElaboratedModule {
    let (_, mut m) = xezim_core::parse_and_elaborate_multi(
        &[src.to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .expect("elaborate");
    m.materialize_pending();
    m
}

/// `(rooted, dotted name)` of every name an expression reads.
fn names(e: &Expression) -> Vec<(bool, String)> {
    match &e.kind {
        ExprKind::Ident(h) => {
            let path = h
                .path
                .iter()
                .map(|s| s.name.name.as_str())
                .collect::<Vec<_>>()
                .join(".");
            let mut out = vec![(h.root.is_some(), path)];
            for s in &h.path {
                for sel in &s.selects {
                    out.extend(names(sel));
                }
            }
            out
        }
        ExprKind::MemberAccess { expr, member } => match names(expr).as_slice() {
            [(rooted, base)] => vec![(*rooted, format!("{base}.{}", member.name))],
            other => other.to_vec(),
        },
        ExprKind::Index { expr, index } => [names(expr), names(index)].concat(),
        ExprKind::Binary { left, right, .. } => [names(left), names(right)].concat(),
        _ => Vec::new(),
    }
}

fn rhs_names(m: &ElaboratedModule, lhs: &str) -> Vec<(bool, String)> {
    let ca = m
        .continuous_assigns
        .iter()
        .find(|ca| matches!(names(&ca.lhs).as_slice(), [(_, n)] if n == lhs))
        .unwrap_or_else(|| panic!("no continuous assign drives {lhs}"));
    names(&ca.rhs)
}

fn n(rooted: bool, name: &str) -> (bool, String) {
    (rooted, name.to_string())
}

#[test]
fn package_members_stay_unrooted_in_foreign_scope_writes() {
    let m = elab(
        r#"
package p;
  parameter logic [3:0][7:0] C = {8'hA1, 8'hB2, 8'hC3, 8'hD4};
  parameter logic [7:0] V = 8'b1010_0110;
endpackage
module leaf (input logic [7:0] x);
  logic V, y;
  assign y = x[1];
endmodule
module sub;
  logic s;
endmodule
module m;
  logic t;
  for (genvar k = 1; k <= 2; k++) begin : g
    logic [7:0] pc;
    assign pc = p::C[k];
  end
  leaf l (.x(p::C[1] ^ t));
  leaf w (.x(p::V));
  sub s ();
  assign s.s = p::V[1] ^ t;
endmodule
module top;
  logic t;
  m u ();
  sub s ();
  assign s.s = p::V[2] ^ t;
endmodule
"#,
    );
    assert_eq!(rhs_names(&m, "u.g[1].pc"), [n(false, "p.C")]);
    assert_eq!(rhs_names(&m, "u.l.x"), [n(false, "p.C"), n(true, "u.t")]);
    assert_eq!(rhs_names(&m, "u.w.y"), [n(false, "p.V")]);
    assert_eq!(rhs_names(&m, "u.s.s"), [n(false, "p.V"), n(true, "u.t")]);
    assert_eq!(rhs_names(&m, "s.s"), [n(false, "p.V"), n(true, "t")]);
    // `m` imports nothing from `p`: only the qualified names are bound.
    assert!(m.parameters.contains_key("p::C"));
    assert!(!m.parameters.contains_key("C"));
    assert!(!m.parameters.contains_key("V"));
}
