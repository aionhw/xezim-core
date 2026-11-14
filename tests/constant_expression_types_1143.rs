//! IEEE 1800-2023: constant-expression values of the typed constant evaluator
//! (aionhw/xezim#1143): integer system-function results are signed
//! (§20.6.2, §20.8.1, §20.9), a condition with a known 1 bit is true
//! (§11.4.11), `inside` is one bit (§11.4.13), a real exponent makes the
//! power real (§11.4.5), an untyped parameter set from a call has the call's
//! type (§6.20.2), a typed two-state parameter holds no x (§6.11.2), and a
//! constant function's `case` compares at the common width (§12.5).

fn elaborate(source: &str) -> xezim_core::ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[source.to_string()],
        Some("t"),
        &[],
        &["t.sv".to_string()],
        &[],
    )
    .expect("elaborate")
    .1
}

#[test]
fn typed_constant_values() {
    let design = elaborate(
        "module t;
          localparam P1 = (~2'sb10) + $clog2(8);
          localparam P2 = 2'b1x ? 3'd7 : 3'd0;
          localparam P3 = 2'bx0 ? 3'd7 : 3'd5;
          localparam N8 = 1 ? (3'sd3 * -3'sd2) : 4'sd0;
          localparam P8 = $countones((N8 < 0) - $isunknown(1'bx));
          localparam C8 = $countbits(8'b1x0z_1100, 'x, 'z);
          localparam P7 = 0 ? (1 inside {1}) : 16'h8000;
          localparam P11 = 1 ? (3'sd3 * 3'sd3 * 3'sd2) : (8'd2 ** 1.0);
          function automatic logic signed [3:0] f12(); return -4'sd7; endfunction
          localparam P12 = f12() ** 2'd3;
          localparam Q12 = {P12, 2'b01};
          localparam bit P4 = 1'bx ? 1 : 0;
          function automatic int f14();
            case (4'sd3 - (1 ? 4'sd5 : 4'd0))
              -2: return 1;
              default: return 2;
            endcase
          endfunction
          localparam P14 = f14();
        endmodule",
    );
    let p = |n: &str| design.parameters[n].clone();
    assert_eq!(p("P1").to_i64(), Some(4));
    assert_eq!(p("P2").to_bin(), "111");
    assert_eq!(p("P3").to_bin(), "1x1");
    assert_eq!(p("P8").to_i64(), Some(0));
    assert_eq!(p("C8").to_i64(), Some(2));
    assert_eq!(p("P7").width, 16);
    assert!(p("P11").is_real);
    assert_eq!(p("P11").to_f64(), 2.0);
    assert_eq!((p("P12").width, p("P12").to_bin()), (4, "1001".to_string()));
    assert_eq!(p("Q12").to_i64(), Some(37));
    assert_eq!(p("P4").to_bin(), "0");
    assert_eq!(p("P14").to_i64(), Some(1));
}

/// §6.12.2: an integral value wider than 64 bits converts to the nearest
/// real, its high bits included.
#[test]
fn wide_value_to_real() {
    let design = elaborate(
        "module t;
          localparam P = 65'shffffffffffffffff - (8'h1 ^ (~4'h7));
          localparam real R = P;
          localparam real N = -70'sd5;
        endmodule",
    );
    assert_eq!(design.parameters["R"].to_f64(), 18446744073709551616.0);
    assert_eq!(design.parameters["N"].to_f64(), -5.0);
}
