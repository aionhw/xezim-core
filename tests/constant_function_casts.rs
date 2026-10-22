//! §6.24.1/§13.4.3: casts inside a constant function evaluate at elaboration.

use xezim_core::{
    ast::Description,
    elaborate::{Definition, elaborate_module},
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
