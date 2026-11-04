//! IEEE 1800-2017 §22.5.1: `M()` supplies an empty actual to a macro
//! with formals, but is a zero-argument invocation when there are no formals.
use sv_parser::preprocessor::Preprocessor;

#[test]
fn empty_actual_is_present_and_substituted() {
    let mut pp = Preprocessor::new();
    let out = pp.preprocess(
        r#"`define IGNORE(prefix) ignored
`define QUOTE(x) `"x`"
`define DEFAULT(x=42) x
`define ZERO() zero
`IGNORE()
`IGNORE(   )
`QUOTE()
`DEFAULT()
`ZERO()
"#,
    );
    assert!(pp.errors().is_empty(), "{:?}", pp.errors());
    assert_eq!(
        out.split_whitespace().collect::<Vec<_>>(),
        ["ignored", "ignored", "\"\"", "42", "zero"]
    );
}

#[test]
fn empty_first_actual_does_not_supply_later_required_actuals() {
    let mut pp = Preprocessor::new();
    pp.preprocess("`define TWO(a,b) a b\n`TWO()\n");
    assert_eq!(pp.errors().len(), 1, "{:?}", pp.errors());
    assert!(pp.errors()[0].contains("missing required argument `b`"));
}

#[test]
fn zero_formal_macro_still_rejects_an_extra_actual() {
    let mut pp = Preprocessor::new();
    pp.preprocess("`define ZERO() zero\n`ZERO(1)\n");
    assert_eq!(pp.errors().len(), 1, "{:?}", pp.errors());
    assert!(pp.errors()[0].contains("1 arguments but only 0 are declared"));
}
