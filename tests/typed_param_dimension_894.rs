//! IEEE 1800-2023 §10.8, §11.6.1: a parameter with a declared type is
//! assigned its initializer, so the operands are evaluated at the declared
//! width wherever the parameter is read — `localparam int A = (8'd128 +
//! 8'd128) >> 8` is 1 in the dimension `logic [A:0]` as it is in its own
//! value (#894). The seed of the top's parameters folded the initializer at
//! the operands' width (0, the 8-bit wrap), and the declarations sized from
//! it kept that width. An untyped parameter keeps the self-determined width.
//! Expected values are the reference simulator's.

use xezim_core::ElaboratedModule;

fn elaborate(source: &str) -> ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[source.to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .unwrap_or_else(|e| panic!("{e}\n{source}"))
    .1
}

fn param(design: &ElaboratedModule, name: &str) -> i64 {
    design
        .parameters
        .get(name)
        .unwrap_or_else(|| panic!("no parameter {name}"))
        .to_i64()
        .unwrap_or_else(|| panic!("{name} is not an integer"))
}

fn width(design: &ElaboratedModule, name: &str) -> u32 {
    design
        .signals
        .get(name)
        .unwrap_or_else(|| panic!("no signal {name}"))
        .width
}

fn bounds(design: &ElaboratedModule, name: &str) -> (i64, i64) {
    let (lo, hi, _) = design
        .arrays
        .get(name)
        .unwrap_or_else(|| panic!("no array {name}"));
    (*lo, *hi)
}

#[test]
fn typed_parameters_size_declarations_at_their_declared_width() {
    let d = elaborate(
        r#"
module child;
  localparam int A = (8'd128 + 8'd128) >> 8;
  logic [A:0] v;
endmodule
module top;
  localparam int A = (8'd128 + 8'd128) >> 8;
  localparam logic [15:0] B = 8'd200 + 8'd100;
  parameter int C = (8'd128 + 8'd128) >> 8;
  localparam A2 = (8'd128 + 8'd128) >> 8;
  logic [A:0] v;
  logic [B:0] vb;
  logic [C:0] vc;
  logic [A2:0] va2;
  logic [A+1:0] rep;
  int ua [B];
  child u();
endmodule
"#,
    );
    assert_eq!(param(&d, "A"), 1);
    assert_eq!(width(&d, "v"), 2);
    assert_eq!(param(&d, "B"), 300);
    assert_eq!(width(&d, "vb"), 301);
    assert_eq!(param(&d, "C"), 1);
    assert_eq!(width(&d, "vc"), 2);
    // Untyped: self-determined, the 8-bit sum wraps to 0.
    assert_eq!(param(&d, "A2"), 0);
    assert_eq!(width(&d, "va2"), 1);
    assert_eq!(width(&d, "rep"), 3);
    assert_eq!(bounds(&d, "ua"), (0, 299));
    assert_eq!(param(&d, "u.A"), 1);
    assert_eq!(width(&d, "u.v"), 2);
}
