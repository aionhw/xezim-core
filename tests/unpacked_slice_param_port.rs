//! §7.4.6, §23.3.3: an unpacked-array input port connected to a slice of an
//! unpacked array, `.p(arr[0:N-1])`, takes the slice's elements in order:
//! `p[0] = arr[0]`, `p[1] = arr[1]`. Inside an instantiated module the
//! actual's names are prefixed with the instance path before the connection
//! is split, so the bound `N-1` names `w.N`; the module's own parameter map
//! is keyed by the bare name and the bound did not fold. The connection then
//! fell back to indexing the slice expression itself, `arr[0:N-1][t]`, which
//! reads bit `t` of `arr[0]`.

use xezim_core::ast::expr::{ExprKind, Expression, NumberLiteral};

fn elaborate(src: &str) -> xezim_core::ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[src.to_string()],
        Some("t"),
        &[],
        &["t.sv".to_string()],
        &[],
    )
    .expect("elaborate")
    .1
}

fn text(e: &Expression) -> String {
    match &e.kind {
        ExprKind::Ident(h) => h
            .path
            .iter()
            .map(|s| s.name.name.as_str())
            .collect::<Vec<_>>()
            .join("."),
        ExprKind::Index { expr, index } => format!("{}[{}]", text(expr), text(index)),
        ExprKind::RangeSelect {
            expr, left, right, ..
        } => format!("{}[{}:{}]", text(expr), text(left), text(right)),
        ExprKind::Number(NumberLiteral::Integer { value, .. }) => value.clone(),
        ExprKind::Paren(inner) => text(inner),
        _ => "?".to_string(),
    }
}

#[test]
fn parameter_bounded_slice_connects_element_by_element() {
    let m = elaborate(
        r#"
module sink #(parameter N = 2) (input [8:0] p [0:N-1], output [8:0] q);
  assign q = p[0] ^ p[1];
endmodule
module wrap #(parameter N = 2) (input [8:0] d, output [8:0] q);
  wire [8:0] arr [0:3];
  assign arr[0] = d;
  assign arr[1] = d + 9'd1;
  assign arr[2] = 9'd0;
  assign arr[3] = 9'd0;
  sink #(.N(N)) s (.p(arr[0:N-1]), .q(q));
endmodule
module t;
  logic [8:0] d = 9'd39;
  wire [8:0] q;
  wrap #(.N(2)) w (.d(d), .q(q));
endmodule
"#,
    );
    let pairs: Vec<(String, String)> = m
        .continuous_assigns
        .iter()
        .map(|ca| (text(&ca.lhs), text(&ca.rhs)))
        .filter(|(l, _)| l.starts_with("w.s.p["))
        .collect();
    assert!(
        pairs.contains(&("w.s.p[0]".to_string(), "w.arr[0]".to_string()))
            && pairs.contains(&("w.s.p[1]".to_string(), "w.arr[1]".to_string())),
        "each port element takes the matching slice element: {pairs:?}"
    );
}
