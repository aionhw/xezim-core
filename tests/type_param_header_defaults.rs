//! §6.20.3/§20.6.2: a header parameter whose default reads a type parameter
//! of the same header (`parameter int H = $bits(T)`) takes THIS instance's
//! type, default or overridden. It read the previous instance's (0 for the
//! first one). §27.4: a genvar in a type override's dimensions takes the
//! iteration's value. Expected values from the reference simulator.

use xezim_core::value::Value;

const SRC: &str = "\
module leaf #(parameter type T = logic [3:0], parameter int H = $bits(T),
              parameter int H2 = $bits(T) * 2, parameter int H3 = H + 1);
  localparam int B = $bits(T);
endmodule
module dep #(parameter int W = 3, parameter type T = logic [W-1:0], parameter int H = $bits(T),
             parameter type U = T [1:0], parameter int HU = $bits(U));
endmodule
module top;
  typedef logic [6:0] t7;
  leaf u_def ();
  leaf #(.T(logic [9:0])) u_ovr ();
  leaf #(.T(t7)) u_td ();
  leaf #(.T(logic [9:0]), .H(3)) u_h ();
  leaf u_def2 ();
  dep u_d0 ();
  dep #(.W(8)) u_d8 ();
  dep #(.T(byte)) u_db ();
  for (genvar g = 1; g <= 3; g++) begin : gl
    leaf #(.T(logic [g*2-1:0])) u ();
  end
endmodule
";

#[test]
fn header_default_reads_this_instances_type_parameter() {
    let (_, m) = xezim_core::parse_and_elaborate_multi(
        &[SRC.to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .unwrap_or_else(|e| panic!("elaboration failed: {e}"));
    let get = |k: &str| m.parameters.get(k).and_then(Value::to_u64);
    let rows: &[(&str, [u64; 4])] = &[
        ("u_def", [4, 8, 5, 4]),
        ("u_ovr", [10, 20, 11, 10]),
        ("u_td", [7, 14, 8, 7]),
        ("u_h", [3, 20, 4, 10]),
        ("u_def2", [4, 8, 5, 4]),
        ("gl[1].u", [2, 4, 3, 2]),
        ("gl[2].u", [4, 8, 5, 4]),
        ("gl[3].u", [6, 12, 7, 6]),
    ];
    for (inst, want) in rows {
        for (name, w) in ["H", "H2", "H3", "B"].iter().zip(want) {
            assert_eq!(get(&format!("{inst}.{name}")), Some(*w), "{inst}.{name}");
        }
    }
    for (inst, w, h, hu) in [("u_d0", 3, 3, 6), ("u_d8", 8, 8, 16), ("u_db", 3, 8, 16)] {
        assert_eq!(get(&format!("{inst}.W")), Some(w), "{inst}.W");
        assert_eq!(get(&format!("{inst}.H")), Some(h), "{inst}.H");
        assert_eq!(get(&format!("{inst}.HU")), Some(hu), "{inst}.HU");
    }
}
