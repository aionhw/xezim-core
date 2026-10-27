//! §20.6.2/§6.24.1: `$bits` of a cast in a constant expression is the width of the cast's target.

use xezim_core::{
    ast::Description,
    elaborate::{Definition, elaborate_module},
    hasher::HashMap,
};

#[test]
fn bits_of_cast_is_target_width() {
    let parsed = xezim_core::parse_str(
        r#"
module top;
  typedef logic [3:0] q_t;
  typedef enum logic [2:0] {E0, E1} e_t;
  typedef struct packed { logic [2:0] a; logic [1:0] b; } st_t;
  localparam int N = 7;
  localparam int TYPEDEF = $bits(q_t'(45));
  localparam int KEYWORD = $bits(int'(45));
  localparam int SIZE = $bits(5'(45));
  localparam int PARAM_SIZE = $bits(N'(3));
  localparam int ENUM = $bits(e_t'(1));
  localparam int STRUCT = $bits(st_t'(45));
  localparam int BYTE = $bits(byte'(300));
  localparam int SUM = $bits(longint'(1)) + $bits(shortint'(1));
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
    assert_eq!(p("TYPEDEF"), Some(4));
    assert_eq!(p("KEYWORD"), Some(32));
    assert_eq!(p("SIZE"), Some(5));
    assert_eq!(p("PARAM_SIZE"), Some(7));
    assert_eq!(p("ENUM"), Some(3));
    assert_eq!(p("STRUCT"), Some(5));
    assert_eq!(p("BYTE"), Some(8));
    assert_eq!(p("SUM"), Some(80));
}
