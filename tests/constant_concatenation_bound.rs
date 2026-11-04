//! A constant concatenation or replication evaluates in an integer constant
//! context (§11.4.12), such as the `{W{1'b1}}` bound of a covergroup bin
//! range.
use xezim_core::Value;
use xezim_core::ast::Description;
use xezim_core::ast::decl::ParameterKind;
use xezim_core::elaborate::const_eval_i64_with_params;
use xezim_core::hasher::HashMap;

#[test]
fn constant_concatenation_evaluates_as_an_integer() {
    let parsed = xezim_core::parse(
        r#"
module m #(
  parameter int A = {W{1'b1}},
  parameter int B = {2'b10, {2{1'b0}}, H},
  parameter int C = {(W){2'b01}},
  parameter int D = {40{2'b11}},
  parameter int E = {{0{1'b0}}, 2'b11},
  parameter int F = {4'hffff_ffff_ffff_ffff},
  parameter int G = {64'hffff_ffff_ffff_ffff},
  parameter int H = {4'bx},
  parameter int I = {{32'd4294967295{{0{1'b0}}}}, 1'b1}
);
endmodule
"#,
    );
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
    let Description::Module(m) = &parsed.source.descriptions[0] else {
        panic!("expected a module");
    };
    let mut params: HashMap<String, Value> = HashMap::default();
    params.insert("W".to_string(), Value::from_u64(4, 32));
    params.insert("H".to_string(), Value::from_u64(5, 3));
    let values: Vec<Option<i64>> = m
        .params
        .iter()
        .map(|p| match &p.kind {
            ParameterKind::Data { assignments, .. } => {
                const_eval_i64_with_params(assignments[0].init.as_ref().unwrap(), Some(&params))
            }
            _ => panic!("expected a value parameter"),
        })
        .collect();
    // D is 80 bits wide and does not fit; G keeps its 64-bit pattern; H is unknown.
    let (main, new) = values.split_at(4);
    assert_eq!(main, [Some(0xf), Some(0b10_00_101), Some(0b01010101), None]);
    assert_eq!(new, [Some(3), Some(0xf), Some(-1), None, Some(1)]);
}
