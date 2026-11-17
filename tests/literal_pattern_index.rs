//! IEEE 1800-2023 §5.7.1, §11.8.2, §10.9.1: self-determined literal
//! pattern indices, with the scalar evaluator retained when admission fails.
use xezim_core::ast::{Description, decl::ParameterKind};
use xezim_core::elaborate::{const_eval_i64_with_params, const_eval_pattern_index};

#[test]
fn typed_indices_and_declined_keys() {
    for (expr, expected) in [
        ("2'sb11 & 4", 4),
        ("4'd15 + 4'd1", 0),
        ("~4'd0", 15),
        ("4'sd7 + 4'sd1", -8),
        ("8 / 2'sb11", -8),
        ("4'shf % 3", -1),
        ("64'shffff_ffff_ffff_ffff", -1),
        ("'shffff_ffff", -1),
        ("(2'sb11 + 32'd0) - 4", -1),
    ] {
        let parsed = xezim_core::parse(&format!("module m #(parameter P=({expr})); endmodule"));
        assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
        let Description::Module(m) = &parsed.source.descriptions[0] else {
            panic!("module")
        };
        let ParameterKind::Data { assignments, .. } = &m.params[0].kind else {
            panic!("parameter")
        };
        let e = assignments[0].init.as_ref().unwrap();
        assert_eq!(
            const_eval_pattern_index(e, None, (-16, 16)),
            Some(expected),
            "{expr}"
        );
        // An out-of-range typed result must retain the old index/fallback.
        assert_eq!(
            const_eval_pattern_index(e, None, (100, 101)),
            const_eval_i64_with_params(e, None),
            "{expr}"
        );
    }
}

// §5.7.1: large unsized decimal sizing is outside this pattern-key change.
#[test]
fn large_unsized_decimal_keeps_the_scalar_fallback() {
    let parsed = xezim_core::parse("module m #(parameter P=(2147483648 >>> 31)); endmodule");
    assert!(parsed.errors.is_empty());
    let Description::Module(m) = &parsed.source.descriptions[0] else {
        panic!("module")
    };
    let ParameterKind::Data { assignments, .. } = &m.params[0].kind else {
        panic!("parameter")
    };
    let e = assignments[0].init.as_ref().unwrap();
    assert_eq!(
        xezim_core::elaborate::const_eval_literal_pattern_index(e, (-1, 1)),
        None
    );
    assert_eq!(
        const_eval_pattern_index(e, None, (-1, 1)),
        const_eval_i64_with_params(e, None)
    );
}
