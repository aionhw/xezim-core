//! §20.7: the array query functions over an instance's type parameter
//! answer from the bound type's declared dimensions, default or overridden:
//! `$left(T)` of `logic [7:2]` is 7, not the width's `[5:0]`. They
//! answered from the width alone, with no dimension. Expected values from
//! the reference simulator.

use xezim_core::value::Value;

const SRC: &str = "\
typedef logic [0:5] asc_t;
typedef logic [3:0][7:0] p2_t;
typedef logic [3:0] ua_t [0:2];
module leaf #(parameter int N = 1, parameter type T = logic [7:2]);
  localparam int L = $left(T), R = $right(T), HI = $high(T), LO = $low(T), SZ = $size(T),
                 INC = $increment(T), DIM = $dimensions(T), UD = $unpacked_dimensions(T),
                 L2 = $left(T, 2);
endmodule
module mid #(parameter type T = logic [6:1]);
  leaf #(.T(T)) u_pass ();
endmodule
module top;
  localparam int N = 12;
  leaf u_def ();
  leaf #(.T(logic [0:5])) u_asc ();
  leaf #(.T(asc_t)) u_td ();
  leaf #(.T(p2_t)) u_p2 ();
  leaf #(.T(ua_t)) u_ua ();
  leaf #(.T(byte)) u_b ();
  leaf #(.N(3), .T(logic [N-1:0])) u_scope ();
  mid m0 ();
  mid #(.T(logic [2:8])) m1 ();
endmodule
";

#[test]
fn array_queries_over_a_type_parameter() {
    let (_, m) = xezim_core::parse_and_elaborate_multi(
        &[SRC.to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .unwrap_or_else(|e| panic!("elaboration failed: {e}"));
    let get = |k: &str| m.parameters.get(k).and_then(Value::to_i64);
    // L R HI LO SZ INC DIM UD
    let rows: &[(&str, [i64; 8])] = &[
        ("u_def", [7, 2, 7, 2, 6, 1, 1, 0]),
        ("u_asc", [0, 5, 5, 0, 6, -1, 1, 0]),
        ("u_td", [0, 5, 5, 0, 6, -1, 1, 0]),
        ("u_p2", [3, 0, 3, 0, 4, 1, 2, 0]),
        ("u_ua", [0, 2, 2, 0, 3, -1, 2, 1]),
        ("u_b", [7, 0, 7, 0, 8, 1, 1, 0]),
        ("u_scope", [11, 0, 11, 0, 12, 1, 1, 0]),
        ("m0.u_pass", [6, 1, 6, 1, 6, 1, 1, 0]),
        ("m1.u_pass", [2, 8, 8, 2, 7, -1, 1, 0]),
    ];
    for (inst, want) in rows {
        let names = ["L", "R", "HI", "LO", "SZ", "INC", "DIM", "UD"];
        for (name, w) in names.iter().zip(want) {
            assert_eq!(get(&format!("{inst}.{name}")), Some(*w), "{inst}.{name}");
        }
    }
    assert_eq!(get("u_p2.L2"), Some(7), "u_p2.L2");
    assert_eq!(get("u_ua.L2"), Some(3), "u_ua.L2");
}
