//! §14.3: a clocking skew can be an edge (`clocking_skew ::= edge_identifier
//! [delay_control]`); the edge is kept for the default and per-signal skews.

use xezim_core::{
    ast::{Description, stmt::Edge},
    elaborate::{Definition, elaborate_module},
    hasher::HashMap,
};

#[test]
fn clocking_output_skew_keeps_its_edge() {
    let parsed = xezim_core::parse_str(
        r#"
module top;
  logic clk, a, b, c;
  clocking cb @(posedge clk);
    default output negedge;
    output a;
    output posedge b;
    output #1 c;
  endclocking
endmodule
"#,
    )
    .expect("parse");
    let Description::Module(module) = &parsed.source.descriptions[0] else {
        panic!("module");
    };
    let model =
        elaborate_module(Definition::Module(module), &HashMap::default()).expect("elaborate");
    let cb = &model.clocking_blocks["cb"];
    assert!(matches!(cb.default_output_edge, Some(Edge::Negedge)));
    assert!(cb.default_output_skew.is_none());
    let sig = |n: &str| cb.signals.iter().find(|s| s.name.name == n).expect(n);
    assert!(sig("a").skew_edge.is_none() && sig("a").skew.is_none());
    assert!(matches!(sig("b").skew_edge, Some(Edge::Posedge)));
    assert!(sig("c").skew_edge.is_none() && sig("c").skew.is_some());
}
