//! IEEE 1800-2023 §6.20 / §6.10: a module parameter used as a port actual of
//! an instance inside that module is a constant, so no implicit net is
//! created for it.

const SRC: &str = r#"module leaf(input real a, input int b, output real y); assign y = a + b; endmodule
module mid #(parameter real VREF = 1.25, parameter int N = 3) (output real y, output real z);
  localparam int M = N * 2;
  parameter type T = int;
  leaf u(.a(VREF), .b(N), .y(y));
  leaf v(.a(VREF), .b(M), .y(z));
endmodule
module top;
  real y, z;
  mid m(.y(y), .z(z));
  mid #(.VREF(2.5)) m2(.y(), .z());
endmodule"#;

#[test]
fn parameter_actuals_create_no_nets() {
    let model = xezim_core::parse_and_elaborate_multi(
        &[SRC.to_string()],
        Some("top"),
        &[],
        &["params.sv".to_string()],
        &[],
    )
    .expect("elaborate")
    .1;
    for inst in ["m", "m2"] {
        for p in ["VREF", "N", "M"] {
            let name = format!("{inst}.{p}");
            // The parameter's value is mirrored as a signal either way; the
            // implicit net shows up in the net set.
            assert!(!model.nets.contains(&name), "implicit net {name} created");
        }
    }
}
