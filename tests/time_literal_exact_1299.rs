//! §5.8, §3.14.1, §6.12.1 (aionhw/xezim#1299): a time literal is a real value
//! scaled to its scope's time unit and rounded to its precision, each change
//! of unit by an exact power of ten, and a real initializer of an integral
//! variable converts to the nearest integer, a 64-bit one included.

use xezim_core::elaborate::{
    ElaboratedModule, round_time_units, scale_pow10, time_literal_in_units,
};

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

#[test]
fn time_literal_values_are_exact() {
    // 9200 s under 1ns/1fs: 9.2e18 fs, 9.2e12 ns (a division by
    // `10f64.powi(-15)` gave 9199999999999.998).
    assert_eq!(time_literal_in_units(9200.0, -9, -15), 9_200_000_000_000.0);
    assert_eq!(time_literal_in_units(7.0, -9, -15), 7_000_000_000.0);
    assert_eq!(
        time_literal_in_units(9200.0, -12, -15),
        9_200_000_000_000_000.0
    );
    assert_eq!(time_literal_in_units(9200.0, -6, -15), 9_200_000_000.0);
    assert_eq!(time_literal_in_units(1.5, -9, -9), 1_500_000_000.0);
    // Rounded to the precision, ties away from zero, a few ulps of slack.
    assert_eq!(time_literal_in_units(2.5e-12, -12, -12), 3.0);
    assert_eq!(time_literal_in_units(1.4e-12, -12, -12), 1.0);
    assert_eq!(time_literal_in_units(-2.5e-12, -12, -12), -3.0);
    assert_eq!(scale_pow10(9200.0, 15), 9.2e18);
    assert_eq!(scale_pow10(9.2e18, -6), 9.2e12);
    assert_eq!(round_time_units(2.4999999999999996), 3.0);
    assert_eq!(round_time_units(2.4999), 2.0);
    // A count of 2^52 or more is whole already and is left as it is.
    assert_eq!(round_time_units(9.2e15), 9.2e15);
    assert_eq!(round_time_units(9.2e18), 9.2e18);
}

#[test]
fn time_literal_seconds_are_the_nearest_double() {
    let m = elab(
        r#"
`timescale 1ns/1fs
module top;
  realtime r_big = 9200s;
  realtime r_ns = 4294967300ns;
  realtime r_ms = 1500ms;
  initial #9200s;
endmodule
"#,
    );
    assert_eq!(
        m.signals.get("r_big").expect("r_big").value.to_f64(),
        9_200_000_000_000.0
    );
    assert_eq!(
        m.signals.get("r_ns").expect("r_ns").value.to_f64(),
        4_294_967_300.0
    );
    assert_eq!(
        m.signals.get("r_ms").expect("r_ms").value.to_f64(),
        1_500_000_000.0
    );
}

#[test]
fn real_initializers_of_64_bit_variables_convert() {
    let m = elab(
        r#"
`timescale 1ns/1fs
module top;
  time        t_big  = 9200s;
  time        t_ten  = 10ns;
  longint     l_real = 3000000000.0;
  longint     l_neg  = -3000000000.5;
  bit [63:0]  b_real = 5000000000.0;
  logic [47:0] v_real = 1.0e12;
  int         i_real = 3.7;
  real        r_keep = 2.5;
  realtime    rt     = 25ns;
  if (1) begin : g
    time g_time = 9200s;
  end
endmodule
"#,
    );
    let int = |n: &str| {
        let v = &m.signals.get(n).expect(n).value;
        assert!(!v.is_real, "{n} holds a real");
        v.to_u64().expect(n)
    };
    assert_eq!(int("t_big"), 9_200_000_000_000);
    assert_eq!(int("t_ten"), 10);
    assert_eq!(int("l_real"), 3_000_000_000);
    assert_eq!(int("l_neg") as i64, -3_000_000_001);
    assert_eq!(int("b_real"), 5_000_000_000);
    assert_eq!(int("v_real"), 1_000_000_000_000);
    assert_eq!(int("i_real"), 4);
    assert_eq!(int("g.g_time"), 9_200_000_000_000);
    assert!(m.signals.get("r_keep").expect("r_keep").value.is_real);
    assert_eq!(m.signals.get("r_keep").expect("r_keep").value.to_f64(), 2.5);
    assert_eq!(m.signals.get("rt").expect("rt").value.to_f64(), 25.0);
}
