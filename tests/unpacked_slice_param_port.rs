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

#[test]
fn indexed_slices_use_the_enclosing_instances_parameter_and_direction() {
    let m = elaborate(
        r#"
module sink(input [7:0] p[0:1], output [7:0] q);
  assign q = p[0] ^ p[1];
endmodule
module wrap #(parameter BASE = 0, W = 2) (output [7:0] a, b);
  wire [7:0] arr[7:0];
  sink up(.p(arr[BASE +: W]), .q(a));
  sink down(.p(arr[BASE -: W]), .q(b));
endmodule
module t;
  parameter BASE = 6;
  wire [7:0] a, b, c, d;
  wrap #(.BASE(2)) lo(.a(a), .b(b));
  wrap #(.BASE(4)) hi(.a(c), .b(d));
endmodule
"#,
    );
    let pairs: Vec<_> = m
        .continuous_assigns
        .iter()
        .map(|ca| (text(&ca.lhs), text(&ca.rhs)))
        .collect();
    for (instance, base) in [("lo", 2), ("hi", 4)] {
        for (sink, indices) in [("up", [base + 1, base]), ("down", [base, base - 1])] {
            for (port, index) in indices.iter().enumerate() {
                let pair = (
                    format!("{instance}.{sink}.p[{port}]"),
                    format!("{instance}.arr[{index}]"),
                );
                assert!(pairs.contains(&pair), "missing {pair:?} in {pairs:?}");
            }
        }
    }
}
