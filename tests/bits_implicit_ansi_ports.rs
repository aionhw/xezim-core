//! IEEE 1800-2023 §20.6.2, §23.2.2.3: an untyped ANSI port is one bit wide.

#[test]
fn bits_of_implicit_ansi_ports_sizes_a_child_parameter() {
    let source = r#"
module leaf #(parameter int W = 32) (input [W-1:0] d);
endmodule
module mid(input a, input wire b, input c, input logic [1:0] d);
  leaf #(.W($bits({a, b, c, d}))) u(.d({a, b, c, d}));
  leaf #($bits({a, b, c, d})) ordered(.d({a, b, c, d}));
endmodule
module top;
  mid m(1'b0, 1'b0, 1'b0, 2'b0);
endmodule
"#;
    let (_, module) = xezim_core::parse_and_elaborate_multi(
        &[source.into()],
        Some("top"),
        &[],
        &["t.sv".into()],
        &[],
    )
    .expect("elaborate with the port widths");
    assert_eq!(module.parameters["m.u.W"].to_u64(), Some(5));
    assert_eq!(module.parameters["m.ordered.W"].to_u64(), Some(5));
}
