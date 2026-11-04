//! §6.24.1: a cast to a typedef in a constant expression takes the
//! typedef's width and signing.

use xezim_core::{
    ast::Description,
    elaborate::{Definition, elaborate_module},
    hasher::HashMap,
};

#[test]
fn typedef_casts_fold_with_typedef_width_and_sign() {
    let parsed = xezim_core::parse_str(
        r#"
module top;
  typedef logic [3:0] q_t;
  typedef q_t q2_t;
  typedef logic signed [3:0] s_t;
  typedef enum logic [1:0] {E0, E1, E2, E3} e_t;
  typedef struct packed { logic [2:0] a; logic [1:0] b; } st_t;
  localparam int N = 3;
  typedef logic [N-1:0] n_t;
  localparam int VEC = q_t'(45);
  localparam int CHAIN = q2_t'(45);
  localparam int SIGNED_VAL = s_t'(12);
  localparam int SIGNED_CMP = s_t'(12) < 0;
  localparam int ENUM_CAST = 32'(e_t'(6));
  localparam int STRUCT_CAST = st_t'(45);
  localparam int PARAM_WIDTH = n_t'(13);
  localparam int NESTED = q_t'(q_t'(45) + 20);
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
    assert_eq!(p("VEC"), Some(13));
    assert_eq!(p("CHAIN"), Some(13));
    assert_eq!(p("SIGNED_VAL"), Some(-4));
    assert_eq!(p("SIGNED_CMP"), Some(1));
    assert_eq!(p("ENUM_CAST"), Some(2));
    assert_eq!(p("STRUCT_CAST"), Some(13));
    assert_eq!(p("PARAM_WIDTH"), Some(5));
    assert_eq!(p("NESTED"), Some(1));
}

/// §6.20.3: a cast to a type parameter of the root module, which is not
/// elaborated as an instance, takes that parameter's type.
#[test]
fn root_type_parameter_cast_folds_with_its_width_and_sign() {
    let parsed = xezim_core::parse_str(
        r#"
module top #(parameter type T = logic [3:0], parameter type S = logic signed [2:0]);
  localparam int H = T'(45);
  localparam int SV = S'(45);
  localparam int SN = S'(45) < 0;
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
    assert_eq!(p("H"), Some(13));
    assert_eq!(p("SV"), Some(-3));
    assert_eq!(p("SN"), Some(1));
}
