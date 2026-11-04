//! §6.24.1/§13.4.3: casts inside a constant function evaluate at elaboration.

use xezim_core::{
    ast::Description,
    elaborate::{elaborate_module, Definition},
    hasher::HashMap,
};

#[test]
fn constant_function_casts_fold_with_target_width_and_sign() {
    let parsed = xezim_core::parse_str(
        r#"
module top;
  typedef enum logic [2:0] {N0, N1, N2, N3, N4} dir_e;
  typedef dir_e dir2_t;
  typedef logic [5:0] u6_t;
  function automatic bit has_n(int unsigned r, dir_e d);
    case (d) N0: return r < 2; N1: return r % 2 == 0; default: return 1'b0; endcase
  endfunction
  function automatic int unsigned count_links();
    int unsigned n = 0;
    for (int unsigned r = 0; r < 4; r++) for (int unsigned d = 0; d < 4; d++)
      if (has_n(r, dir_e'(d))) n++;
    return n;
  endfunction
  function automatic int f_int(int unsigned x); return int'(x) + 1; endfunction
  function automatic int f_byte(int x); return byte'(x); endfunction
  function automatic int f_signed(int unsigned x); return (int'(x) < 0) ? 1 : 0; endfunction
  function automatic int f_shortint(int x); return shortint'(x) >>> 4; endfunction
  function automatic int f_size(int x); return 4'(x); endfunction
  function automatic int f_enum(int x); return 32'(dir_e'(x)); endfunction
  function automatic int f_chain(int x); return 32'(dir2_t'(x)); endfunction
  function automatic int f_vec(int x); return u6_t'(x) + 1; endfunction
  localparam int LINKS = count_links();
  localparam int INT_CAST = f_int(4);
  localparam int BYTE_CAST = f_byte(300);
  localparam int SIGNED_CAST = f_signed(32'hffff_ffff);
  localparam int SHORTINT_CAST = f_shortint(32'h0000_8000);
  localparam int SIZE_CAST = f_size(37);
  localparam int ENUM_CAST = f_enum(9);
  localparam int CHAIN_CAST = f_chain(10);
  localparam int VEC_CAST = f_vec(70);
endmodule
"#,
    )
    .expect("parse");
    let Description::Module(module) = &parsed.source.descriptions[0] else {
        panic!("module");
    };
    let model =
        elaborate_module(Definition::Module(module), &HashMap::default()).expect("elaborate");
    let p = |n: &str| model.parameters[n].to_i64();
    assert_eq!(p("LINKS"), Some(4));
    assert_eq!(p("INT_CAST"), Some(5));
    assert_eq!(p("BYTE_CAST"), Some(44));
    assert_eq!(p("SIGNED_CAST"), Some(1));
    assert_eq!(p("SHORTINT_CAST"), Some(-2048));
    assert_eq!(p("SIZE_CAST"), Some(5));
    assert_eq!(p("ENUM_CAST"), Some(1));
    assert_eq!(p("CHAIN_CAST"), Some(2));
    assert_eq!(p("VEC_CAST"), Some(7));
}

#[test]
fn constant_function_casts_to_instance_types() {
    let design = xezim_core::parse_and_elaborate_multi(
        &[r#"
package pk;
  typedef logic [3:0] n_t;
endpackage
typedef logic [7:0] w_t;
module child #(parameter int W = 5, parameter type T = logic [3:0]) ();
  import pk::*;
  typedef logic [W-1:0] w_t;
  typedef w_t v_t;
  function automatic int fw(int x); return w_t'(x); endfunction
  function automatic int fv(int x); return v_t'(x); endfunction
  function automatic int ft(int x); return T'(x); endfunction
  function automatic int fn(int x); return n_t'(x); endfunction
  localparam int CW = fw(37);
  localparam int CV = fv(37);
  localparam int CT = ft(45);
  localparam int CN = fn(37);
endmodule
module top;
  child c5 ();
  child #(.W(6), .T(logic [2:0])) c6 ();
endmodule
"#
        .to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .expect("elaborate")
    .1;
    let get = |k: &str| design.parameters[k].to_i64();
    // The child's own 5-bit `w_t`, not the 8-bit `$unit` one.
    assert_eq!(get("c5.CW"), Some(5));
    assert_eq!(get("c5.CV"), Some(5));
    assert_eq!(get("c5.CT"), Some(13));
    assert_eq!(get("c5.CN"), Some(5));
    assert_eq!(get("c6.CW"), Some(37));
    assert_eq!(get("c6.CT"), Some(5));
}

/// `pkg::opgroup_e'(genvar)` as a constant-function actual. The cast is a
/// named-cast intrinsic; rejecting it left the localparam at 0, so fpnew
/// sized every operation group as 0 operands.
#[test]
fn genvar_enum_cast_argument_folds_per_iteration() {
    let design = xezim_core::parse_and_elaborate_multi(
        &[r#"
package p;
  typedef enum logic [1:0] { ADDMUL, DIVSQRT, NONCOMP, CONV } opgroup_e;
  function automatic int unsigned num_operands(opgroup_e grp);
    case (grp)
      ADDMUL:  return 3;
      DIVSQRT: return 2;
      NONCOMP: return 2;
      CONV:    return 3;
      default: return 0;
    endcase
  endfunction
  localparam int unsigned NUM_OPGROUPS = 4;
endpackage
module top;
  import p::*;
  for (genvar opgrp = 0; opgrp < int'(NUM_OPGROUPS); opgrp++) begin : g
    localparam int unsigned NUM_OPS = p::num_operands(p::opgroup_e'(opgrp));
  end
endmodule
"#
        .to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .expect("elaborate")
    .1;
    let mut found: Vec<(String, Option<i64>)> = design
        .parameters
        .iter()
        .filter(|(k, _)| k.ends_with("NUM_OPS"))
        .map(|(k, v)| (k.clone(), v.to_i64()))
        .collect();
    found.sort();
    let values: Vec<Option<i64>> = found.iter().map(|(_, v)| *v).collect();
    assert_eq!(
        values,
        vec![Some(3), Some(2), Some(2), Some(3)],
        "keys: {found:?}"
    );
}
