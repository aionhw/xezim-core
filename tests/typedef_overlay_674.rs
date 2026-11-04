//! IEEE 1800-2023 §6.18 / §23.9: instance-local type widths and snapshot scopes.

#[test]
fn instance_typedef_width_overlays_do_not_escape() {
    let source = r#"
package p; typedef logic [12:0] shared_t; endpackage
module leaf #(parameter int W=4, parameter type T=logic[W-1:0]);
  typedef logic [W-1:0] shared_t;
  localparam int A=$bits(shared_t);
  localparam int B=$bits(logic[W-1:0]);
  localparam int C=$bits(T);
  localparam int D=$bits(p::shared_t);
  typedef logic [B-1:0] dependent_t;
  localparam int E=$bits(dependent_t);
endmodule
module other; import p::*; localparam int A=$bits(shared_t); endmodule
module top;
  leaf #(.W(3)) u0();
  leaf #(.W(7)) u1();
  leaf #(.W(5),.T(logic[8:0])) u2();
  other v();
endmodule
"#;
    for _ in 0..2 {
        let design = xezim_core::parse_and_elaborate_multi(
            &[source.to_string()],
            Some("top"),
            &[],
            &["top.sv".to_string()],
            &[],
        )
        .expect("elaborate")
        .1;
        for (name, width, type_width) in [("u0", 3, 3), ("u1", 7, 7), ("u2", 5, 9)] {
            for field in ["A", "B", "E"] {
                assert_eq!(
                    design.parameters[&format!("{name}.{field}")].to_u64(),
                    Some(width)
                );
            }
            assert_eq!(
                design.parameters[&format!("{name}.C")].to_u64(),
                Some(type_width)
            );
            assert_eq!(design.parameters[&format!("{name}.D")].to_u64(), Some(13));
        }
        assert_eq!(design.parameters["v.A"].to_u64(), Some(13));
    }
}
