//! IEEE 1800-2023 §5.7.1, §27.4: the elaborator writes a negative value it
//! substitutes (a genvar) or folds as one decimal token such as `-2`. A
//! loaded design re-reads that text, because the literal's cached value is
//! not serialized; it read as x. `Value::from_literal_text` reads it as the
//! two's complement of the magnitude at the literal's width, while
//! `from_str_radix` still leaves a sign to its caller.
use xezim_core::Value;

#[test]
fn negative_decimal_token_reads_as_twos_complement() {
    assert_eq!(
        Value::from_literal_text("-2", 10, 32),
        Value::from_u64(0xffff_fffe, 32)
    );
    assert_eq!(
        Value::from_literal_text("-1", 10, 64),
        Value::from_u64(u64::MAX, 64)
    );
    assert_eq!(
        Value::from_literal_text("-1_000", 10, 16),
        Value::from_u64(0xfc18, 16)
    );
    // A token without a sign reads as before.
    assert_eq!(
        Value::from_literal_text("2", 10, 32),
        Value::from_u64(2, 32)
    );
}

#[test]
fn negative_genvar_literal_survives_without_its_cached_value() {
    use xezim_core::ast::expr::{ExprKind, NumberLiteral};
    let (_, design) = xezim_core::parse_and_elaborate_multi(
        &[r#"
module top;
  int o[-2:1];
  for (genvar k = -2; k <= 1; k++) begin : gk
    assign o[k] = k;
  end
endmodule
"#
        .to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .expect("elaborate");
    let mut seen = 0;
    for ca in &design.continuous_assigns {
        if let ExprKind::Number(NumberLiteral::Integer {
            size,
            value,
            signed,
            ..
        }) = &ca.rhs.kind
            && value.starts_with('-')
        {
            // The text alone, as a loaded design reads it.
            let mut v = Value::from_literal_text(value, 10, size.unwrap_or(32));
            v.is_signed = *signed;
            assert_eq!(v.to_i64(), value.parse::<i64>().ok(), "{value}");
            seen += 1;
        }
    }
    assert!(seen > 0, "{:?}", design.continuous_assigns);
}
