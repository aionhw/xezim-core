//! IEEE 1800-2023 §10.9.1, §11.6.1, §6.20.2: a parameter operand of an
//! assignment-pattern key has its declared width and sign (aionhw/xezim#1164).
use xezim_core::ast::{Description, decl::ParameterKind};
use xezim_core::elaborate::const_eval_typed_pattern_index;
use xezim_core::hasher::HashMap;
use xezim_core::value::Value;

fn key(expr: &str) -> xezim_core::ast::expr::Expression {
    let parsed = xezim_core::parse(&format!("module m #(parameter P=({expr})); endmodule"));
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
    let Description::Module(m) = &parsed.source.descriptions[0] else {
        panic!("module")
    };
    let ParameterKind::Data { assignments, .. } = &m.params[0].kind else {
        panic!("parameter")
    };
    assignments[0].init.clone().unwrap()
}

#[test]
fn parameter_leaves_keep_their_type() {
    let mut params: HashMap<String, Value> = HashMap::default();
    params.insert("F".into(), Value::from_u64(15, 4));
    let mut s7 = Value::from_u64(7, 4);
    s7.is_signed = true;
    params.insert("S7".into(), s7);
    params.insert("kp::PF".into(), Value::from_u64(15, 4));
    for (expr, expected) in [
        ("F + 4'd1", Some(0)),
        ("~F", Some(0)),
        ("S7 + 4'sd1", Some(-8)),
        ("kp::PF + 4'd1", Some(0)),
        ("$signed(F) + 0", Some(-1)),
        // An unbound name keeps the caller's fallback.
        ("Q + 1", None),
    ] {
        assert_eq!(
            const_eval_typed_pattern_index(&key(expr), Some(&params), (-16, 16)),
            expected,
            "{expr}"
        );
    }
}
