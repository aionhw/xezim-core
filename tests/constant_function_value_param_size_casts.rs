//! IEEE 1800-2023 §6.24.1 / §13.4.3: a value parameter used as a
//! casting size is evaluated in the constant function's instance scope.

use xezim_core::hasher::HashMap;

const WIDTHS: &str = r#"module leaf #(parameter int W = 3);
  function automatic int narrow(int unsigned x); return int'(W'(x)); endfunction
  localparam int P = narrow(13);
  logic [P-1:0] sized;
  initial $display("%m W=%0d P=%0d bits=%0d", W, P, $bits(sized));
endmodule
module top #(parameter int W = 6);
  function automatic int root_narrow(int unsigned x); return int'(W'(x)); endfunction
  localparam int P = root_narrow(13);
  leaf c3();
  leaf #(.W(4)) c4();
  initial begin
    $display("top W=%0d P=%0d", W, P);
    #1 $finish;
  end
endmodule"#;
const SCOPES: &str = r#"package widths;
  localparam int PW = 5;
  function automatic int pkg_narrow(int unsigned x); return int'(PW'(x)); endfunction
endpackage
module scoped #(parameter int W = 3);
  localparam int CW = W + 1;
  function automatic int local_narrow(int unsigned x); return int'(CW'(x)); endfunction
  function automatic int nested(int unsigned x); return local_narrow(int'(W'(x))); endfunction
  function automatic int signed_cmp(); return int'(W'(-1) < 0); endfunction
  function automatic int contextual(); return int'(CW'(3'd7 + 3'd6)); endfunction
  function automatic int qualified(int unsigned x); return int'(widths::PW'(x)); endfunction
  localparam int L = local_narrow(31);
  localparam int N = nested(31);
  localparam int S = signed_cmp();
  localparam int C = contextual();
  localparam int K = qualified(63);
  localparam int G = widths::pkg_narrow(63);
  initial $display("%m L=%0d N=%0d S=%0d C=%0d K=%0d G=%0d", L, N, S, C, K, G);
endmodule
module top;
  scoped c3();
  scoped #(.W(4)) c4();
  initial #1 $finish;
endmodule"#;

fn design(src: &str) -> xezim_core::elaborate::ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[src.to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .expect("elaborate")
    .1
}

#[test]
fn value_parameter_casts_fold_before_instance_widths() {
    let model = design(WIDTHS);
    let got: Vec<_> = ["P", "c3.P", "c4.P"]
        .iter()
        .map(|n| model.parameters[*n].to_i64())
        .collect();
    assert_eq!(got, vec![Some(13), Some(5), Some(13)]);
    assert!(
        model.deferred_param_exprs.is_empty(),
        "constant casts must fold at elaboration"
    );
    for (name, width) in [("c3.sized", 5), ("c4.sized", 13)] {
        assert_eq!(model.signals[name].width, width, "{name}");
    }
}

#[test]
fn value_parameter_casts_keep_scope_sign_and_context() {
    let model = design(SCOPES);
    let expected: HashMap<_, _> = [
        ("c3.L", 15),
        ("c3.N", 7),
        ("c3.S", 1),
        ("c3.C", 13),
        ("c3.K", 31),
        ("c3.G", 31),
        ("c4.L", 31),
        ("c4.N", 15),
        ("c4.S", 1),
        ("c4.C", 13),
        ("c4.K", 31),
        ("c4.G", 31),
    ]
    .into_iter()
    .collect();
    for (name, value) in expected {
        assert_eq!(model.parameters[name].to_i64(), Some(value), "{name}");
    }
}
