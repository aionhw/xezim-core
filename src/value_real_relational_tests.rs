//! IEEE 1800-2023 §11.4.4, §6.12.1: mixed-real relations convert X/Z to zero.
use super::{LogicBit, Value};

#[test]
fn real_relations_convert_unknown_bits_before_comparing() {
    for width in [4, 64, 65, 128, 200] {
        for signed in [false, true] {
            let mut integral = Value::from_u64(9, width);
            integral.set_bit(1, LogicBit::X);
            integral.set_bit(2, LogicBit::Z);
            integral.is_signed = signed;
            // At width 4 the signed value is -7; otherwise it is 9.
            let converted = if signed && width == 4 { -7.0 } else { 9.0 };
            assert_eq!(integral.to_f64(), converted);
            for (real, expected) in [
                (converted - 1.0, [0, 0, 1, 1]),
                (converted, [0, 1, 0, 1]),
                (converted + 1.0, [1, 1, 0, 0]),
            ] {
                let real = Value::from_f64(real);
                let forward = [
                    integral.less_than(&real),
                    integral.less_equal(&real),
                    integral.greater_than(&real),
                    integral.greater_equal(&real),
                ];
                let reverse = [
                    real.greater_than(&integral),
                    real.greater_equal(&integral),
                    real.less_than(&integral),
                    real.less_equal(&integral),
                ];
                for results in [forward, reverse] {
                    for (result, expected) in results.iter().zip(expected) {
                        assert_eq!(result.width, 1);
                        assert_eq!(result.to_u64(), Some(expected));
                        assert!(!result.has_xz());
                    }
                }
            }
            // §11.4.4: without a real operand every relation still yields X.
            let known = Value::from_u64(10, width);
            for (a, b) in [(&integral, &known), (&known, &integral)] {
                for result in [
                    a.less_than(b),
                    a.less_equal(b),
                    a.greater_than(b),
                    a.greater_equal(b),
                ] {
                    assert_eq!(result.get_bit(0), LogicBit::X);
                }
            }
        }
    }
}

#[test]
fn real_relations_keep_fill_normalization() {
    for bit in ['x', 'z', '0'] {
        let fill = Value::fill_of(bit);
        let zero = Value::from_f64(0.0);
        assert_eq!(fill.less_than(&zero).to_u64(), Some(0));
        assert_eq!(fill.less_equal(&zero).to_u64(), Some(1));
        assert_eq!(zero.greater_than(&fill).to_u64(), Some(0));
        assert_eq!(zero.greater_equal(&fill).to_u64(), Some(1));
    }
}
