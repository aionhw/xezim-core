//! §13.4.1: the implicit return variable has its declared type during evaluation.

use xezim_core::{
    ast::Description,
    elaborate::{Definition, elaborate_module},
    hasher::HashMap,
};

#[test]
fn constant_return_assignments_keep_width_and_sign() {
    let parsed = xezim_core::parse_str(
        r#"
module top;
  typedef logic signed [7:0] narrow_t;
  function integer shift_word(input integer arg);
    shift_word=arg;
    shift_word >>>= 3;
  endfunction
  function narrow_t shift_byte(input integer arg);
    shift_byte=arg;
    shift_byte >>>= 3;
  endfunction
  function logic [3:0] truncate_first(input integer arg);
    truncate_first=arg;
    truncate_first >>= 1;
  endfunction
  localparam signed_word=shift_word(-25);
  localparam signed_byte=shift_byte(-25);
  localparam truncated=truncate_first(20);
endmodule
"#,
    )
    .expect("parse");
    let Description::Module(module) = &parsed.source.descriptions[0] else {
        panic!("module");
    };
    let model =
        elaborate_module(Definition::Module(module), &HashMap::default()).expect("elaborate");
    assert_eq!(model.parameters["signed_word"].to_i64(), Some(-4));
    assert_eq!(model.parameters["signed_byte"].to_i64(), Some(-4));
    assert_eq!(model.parameters["truncated"].to_u64(), Some(2));
}
