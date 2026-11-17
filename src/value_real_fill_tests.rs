//! IEEE 1800-2023 §5.7.1, §11.8.2: fills have one bit before real conversion.
use super::Value;

#[test]
fn real_equality_uses_self_determined_fills() {
    // §11.4.5 converts the integral operand to real; §6.12.1 maps X/Z to 0.
    for (c, number) in [('0', 0.0), ('1', 1.0), ('x', 0.0), ('z', 0.0)] {
        let fill = Value::fill_of(c);
        for real in [0.0, 1.0, 2.0, u64::MAX as f64] {
            let value = Value::from_f64(real);
            let equal = u64::from(real == number);
            for (a, b) in [(&value, &fill), (&fill, &value)] {
                assert_eq!(a.is_equal(b).to_u64(), Some(equal), "{real} / {c}");
                assert_eq!(a.is_not_equal(b).to_u64(), Some(1 - equal));
            }
        }
    }
}

#[test]
fn real_arithmetic_and_known_relations_use_one_bit_fills() {
    // §11.3.1, §11.4.4, §11.8.2: the real type does not supply a bit width.
    let one = Value::fill_of('1');
    let zero = Value::fill_of('0');
    let two = Value::from_f64(2.0);
    assert_eq!(two.add(&one).to_f64(), 3.0);
    assert_eq!(one.add(&two).to_f64(), 3.0);
    assert_eq!(two.mul(&one).to_f64(), 2.0);
    assert_eq!(one.mul(&two).to_f64(), 2.0);
    assert_eq!(two.sub(&zero).to_f64(), 2.0);
    assert_eq!(two.div(&one).to_f64(), 2.0);
    assert_eq!(one.less_than(&two).to_u64(), Some(1));
    assert_eq!(one.less_equal(&two).to_u64(), Some(1));
    assert_eq!(two.greater_than(&one).to_u64(), Some(1));
    assert_eq!(two.greater_equal(&one).to_u64(), Some(1));
}

#[test]
fn integral_fill_contexts_keep_their_width() {
    // §5.7.1, §11.6: integral contexts still replicate every fill bit.
    for width in [1, 8, 32, 64, 128] {
        for c in ['0', '1', 'x', 'z'] {
            let fill = Value::fill_of(c);
            let expanded = fill.fill_at(width);
            assert_eq!(expanded.case_eq(&fill).to_u64(), Some(1));
            assert_eq!(fill.case_eq(&expanded).to_u64(), Some(1));
            if c == '0' || c == '1' {
                assert_eq!(expanded.is_equal(&fill).to_u64(), Some(1));
                assert_eq!(fill.is_equal(&expanded).to_u64(), Some(1));
                assert_eq!(expanded.less_than(&fill).to_u64(), Some(0));
                assert_eq!(fill.less_equal(&expanded).to_u64(), Some(1));
                assert_eq!(expanded.sub(&fill).to_u64(), Some(0));
            }
        }
    }
}
