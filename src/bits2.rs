//! 2-state arbitrary-width logic value (Verilator-style): **no X/Z mask**.
//!
//! This is the compute-core value type for the cycle-based / 2-state simulation
//! path (see xezim-pdes-wt/CYCLE_BASED.md, M1). Unlike the 4-state [`Value`]
//! (which carries an `xz_bits` mask per value), `Bits2` stores only the value
//! bits — `u64` inline for widths ≤ 64, `Vec<u64>` words (LSB word first) for
//! wider — so arithmetic/logic are plain integer ops with no per-bit masking.
//! That is the memory + speed lever vs 4-state. X/Z collapse to 0 on entry
//! (`from_value`), matching Verilator's 2-state semantics.
//!
//! The top (most-significant) word is always kept masked to `width`.

use crate::value::{LogicBit, Value};

#[derive(Debug, Clone, PartialEq, Eq)]
enum B2 {
    Inline(u64),
    Wide(Vec<u64>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Bits2 {
    storage: B2,
    pub width: u32,
}

impl Bits2 {
    #[inline]
    fn nwords_for(width: u32) -> usize {
        (width.max(1) as usize).div_ceil(64)
    }

    /// Mask for the top word given `width` (all-ones when width is a multiple of 64).
    #[inline]
    fn top_mask(width: u32) -> u64 {
        let r = width % 64;
        if r == 0 { u64::MAX } else { (1u64 << r) - 1 }
    }

    #[inline]
    pub fn nwords(&self) -> usize {
        match &self.storage {
            B2::Inline(_) => 1,
            B2::Wide(w) => w.len(),
        }
    }

    /// Word `i` (0 if out of range).
    #[inline]
    pub fn word(&self, i: usize) -> u64 {
        match &self.storage {
            B2::Inline(v) => {
                if i == 0 {
                    *v
                } else {
                    0
                }
            }
            B2::Wide(w) => *w.get(i).unwrap_or(&0),
        }
    }

    /// Build from a word vector, normalizing length + masking the top word.
    fn from_words(mut words: Vec<u64>, width: u32) -> Bits2 {
        let nw = Self::nwords_for(width);
        words.resize(nw, 0);
        if nw > 0 {
            words[nw - 1] &= Self::top_mask(width);
        }
        if width <= 64 {
            Bits2 {
                storage: B2::Inline(words[0] & Self::top_mask(width)),
                width,
            }
        } else {
            Bits2 {
                storage: B2::Wide(words),
                width,
            }
        }
    }

    fn to_words(&self) -> Vec<u64> {
        (0..self.nwords()).map(|i| self.word(i)).collect()
    }

    pub fn zero(width: u32) -> Bits2 {
        Self::from_words(vec![0; Self::nwords_for(width)], width)
    }

    /// Zero-extend / truncate to `w` bits.
    pub fn resize(&self, w: u32) -> Bits2 {
        if self.width == w {
            return self.clone();
        }
        Self::from_words(self.to_words(), w)
    }

    pub fn from_u64(val: u64, width: u32) -> Bits2 {
        Self::from_words(vec![val], width)
    }

    /// Low 64 bits.
    pub fn to_u64(&self) -> u64 {
        self.word(0)
    }

    #[inline]
    pub fn get_bit(&self, i: u32) -> bool {
        if i >= self.width {
            return false;
        }
        (self.word((i / 64) as usize) >> (i % 64)) & 1 == 1
    }

    pub fn set_bit(&mut self, i: u32, b: bool) {
        if i >= self.width {
            return;
        }
        let mut words = self.to_words();
        let w = (i / 64) as usize;
        if b {
            words[w] |= 1u64 << (i % 64);
        } else {
            words[w] &= !(1u64 << (i % 64));
        }
        *self = Self::from_words(words, self.width);
    }

    pub fn is_zero(&self) -> bool {
        (0..self.nwords()).all(|i| self.word(i) == 0)
    }

    // ---- bitwise (operands assumed same width; result is that width) ----
    fn zip_words<F: Fn(u64, u64) -> u64>(&self, o: &Bits2, f: F) -> Bits2 {
        let n = self.nwords().max(o.nwords());
        let words = (0..n).map(|i| f(self.word(i), o.word(i))).collect();
        Self::from_words(words, self.width.max(o.width))
    }
    pub fn and(&self, o: &Bits2) -> Bits2 {
        self.zip_words(o, |a, b| a & b)
    }
    pub fn or(&self, o: &Bits2) -> Bits2 {
        self.zip_words(o, |a, b| a | b)
    }
    pub fn xor(&self, o: &Bits2) -> Bits2 {
        self.zip_words(o, |a, b| a ^ b)
    }
    pub fn not(&self) -> Bits2 {
        let words = (0..self.nwords()).map(|i| !self.word(i)).collect();
        Self::from_words(words, self.width)
    }

    // ---- arithmetic (mod 2^width) ----
    pub fn add(&self, o: &Bits2) -> Bits2 {
        let n = Self::nwords_for(self.width.max(o.width));
        let mut out = vec![0u64; n];
        let mut carry = 0u128;
        for i in 0..n {
            let s = self.word(i) as u128 + o.word(i) as u128 + carry;
            out[i] = s as u64;
            carry = s >> 64;
        }
        Self::from_words(out, self.width.max(o.width))
    }
    /// Two's-complement subtract: a - b = a + ~b + 1 (mod 2^width).
    pub fn sub(&self, o: &Bits2) -> Bits2 {
        self.add(&o.not())
            .add(&Bits2::from_u64(1, self.width.max(o.width)))
    }

    // ---- shifts (logical) ----
    pub fn shl(&self, n: u32) -> Bits2 {
        if n >= self.width {
            return Bits2::zero(self.width);
        }
        let nw = self.nwords();
        let word_sh = (n / 64) as usize;
        let bit_sh = n % 64;
        let mut out = vec![0u64; nw];
        for i in (0..nw).rev() {
            if i < word_sh {
                continue;
            }
            let src = i - word_sh;
            let mut v = self.word(src) << bit_sh;
            if bit_sh != 0 && src >= 1 {
                v |= self.word(src - 1) >> (64 - bit_sh);
            }
            out[i] = v;
        }
        Self::from_words(out, self.width)
    }
    pub fn shr(&self, n: u32) -> Bits2 {
        if n >= self.width {
            return Bits2::zero(self.width);
        }
        let nw = self.nwords();
        let word_sh = (n / 64) as usize;
        let bit_sh = n % 64;
        let mut out = vec![0u64; nw];
        for i in 0..nw {
            let src = i + word_sh;
            if src >= nw {
                break;
            }
            let mut v = self.word(src) >> bit_sh;
            if bit_sh != 0 && src + 1 < nw {
                v |= self.word(src + 1) << (64 - bit_sh);
            }
            out[i] = v;
        }
        Self::from_words(out, self.width)
    }

    // ---- unsigned compare ----
    pub fn ult(&self, o: &Bits2) -> bool {
        let n = self.nwords().max(o.nwords());
        for i in (0..n).rev() {
            let a = self.word(i);
            let b = o.word(i);
            if a != b {
                return a < b;
            }
        }
        false
    }

    /// Part-select `[hi:lo]` (inclusive) → a value of width `hi-lo+1`.
    pub fn slice(&self, hi: u32, lo: u32) -> Bits2 {
        debug_assert!(hi >= lo && hi < self.width);
        let w = hi - lo + 1;
        let shifted = self.shr(lo);
        // re-width (truncate) to w
        Self::from_words(shifted.to_words(), w)
    }

    /// Concatenation `{self, other}` — `self` is the high part.
    pub fn concat(&self, low: &Bits2) -> Bits2 {
        let total = self.width + low.width;
        let hi = {
            // zero-extend self to total, then shift up by low.width
            let ext = Self::from_words(self.to_words(), total);
            ext.shl(low.width)
        };
        let lo = Self::from_words(low.to_words(), total);
        hi.or(&lo)
    }

    /// Numeric (value) equality, zero-extended to the wider operand. Unlike the
    /// derived `==` (which also compares `width`/storage), this matches Verilog
    /// `==` semantics where `8'd5 == 4'd5`.
    pub fn eq_value(&self, o: &Bits2) -> bool {
        let n = self.nwords().max(o.nwords());
        (0..n).all(|i| self.word(i) == o.word(i))
    }

    // ---- multiply (mod 2^width) ----
    /// Schoolbook multiply, result width = max(operand widths), truncated.
    pub fn mul(&self, o: &Bits2) -> Bits2 {
        let width = self.width.max(o.width);
        let n = Self::nwords_for(width);
        let mut out = vec![0u64; n];
        for i in 0..n {
            let ai = self.word(i) as u128;
            if ai == 0 {
                continue;
            }
            let mut carry: u128 = 0;
            for j in 0..(n - i) {
                let idx = i + j;
                let prod = ai * (o.word(j) as u128) + out[idx] as u128 + carry;
                out[idx] = prod as u64;
                carry = prod >> 64;
            }
            // carry past the top word is dropped (mod 2^width).
        }
        Self::from_words(out, width)
    }

    // ---- unsigned divide / remainder (result width = max operand width) ----
    /// Unsigned quotient. Division by zero → 0 (Verilog gives X; 2-state → 0).
    pub fn udiv(&self, o: &Bits2) -> Bits2 {
        self.divmod(o).0
    }
    /// Unsigned remainder. Mod by zero → 0.
    pub fn urem(&self, o: &Bits2) -> Bits2 {
        self.divmod(o).1
    }
    fn divmod(&self, o: &Bits2) -> (Bits2, Bits2) {
        let width = self.width.max(o.width);
        if o.is_zero() {
            return (Bits2::zero(width), Bits2::zero(width));
        }
        if width <= 64 {
            let (a, b) = (self.to_u64(), o.to_u64());
            return (Bits2::from_u64(a / b, width), Bits2::from_u64(a % b, width));
        }
        // Wide: restoring long division MSB→LSB. Partial remainder carries an
        // extra bit (rw) so the left-shift never drops the high bit.
        let rw = width + 1;
        let mut q = Bits2::zero(width);
        let mut r = Bits2::zero(rw);
        let dvsr = o.resize(rw);
        for i in (0..width).rev() {
            r = r.shl(1);
            if self.get_bit(i) {
                r.set_bit(0, true);
            }
            if !r.ult(&dvsr) {
                r = r.sub(&dvsr);
                q.set_bit(i, true);
            }
        }
        (q, r.resize(width))
    }

    // ---- arithmetic shift right (sign-replicating) ----
    /// `>>>` for a value whose MSB (`bit width-1`) is the sign. Logical for a
    /// 0 sign; fills the vacated top `n` bits with 1 for a 1 sign.
    pub fn ashr(&self, n: u32) -> Bits2 {
        if n == 0 || self.width == 0 {
            return self.clone();
        }
        if !self.get_bit(self.width - 1) {
            return self.shr(n);
        }
        let mut r = self.shr(n);
        let fill_from = self.width.saturating_sub(n);
        for i in fill_from..self.width {
            r.set_bit(i, true);
        }
        r
    }

    // ---- 4-state interop ----
    /// Collapse a 4-state [`Value`] to 2-state: known 1 → 1, everything else
    /// (0, X, Z) → 0. This is the cycle-engine entry conversion.
    pub fn from_value(v: &Value) -> Bits2 {
        if v.width <= 64 {
            let (val, xz) = v.raw_bits();
            // known-1 bits are val & !xz; X/Z → 0.
            Self::from_u64(val & !xz, v.width)
        } else {
            let mut b = Bits2::zero(v.width);
            for i in 0..v.width {
                if v.get_bit(i as usize) == LogicBit::One {
                    b.set_bit(i, true);
                }
            }
            b
        }
    }

    /// Lift back to a (fully-known) 4-state [`Value`].
    pub fn to_value(&self) -> Value {
        if self.width <= 64 {
            return Value::from_u64(self.word(0), self.width);
        }
        let mut v = Value::zero(self.width);
        for i in 0..self.width {
            if self.get_bit(i) {
                v.set_bit(i as usize, LogicBit::One);
            }
        }
        v
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn width_mask_and_basic() {
        let a = Bits2::from_u64(0xFF, 4); // masked to 4 bits
        assert_eq!(a.to_u64(), 0xF);
        assert_eq!(a.width, 4);
        assert!(Bits2::zero(8).is_zero());
        assert!(a.get_bit(3));
        assert!(!a.get_bit(4));
    }

    #[test]
    fn logic_ops() {
        let a = Bits2::from_u64(0b1100, 4);
        let b = Bits2::from_u64(0b1010, 4);
        assert_eq!(a.and(&b).to_u64(), 0b1000);
        assert_eq!(a.or(&b).to_u64(), 0b1110);
        assert_eq!(a.xor(&b).to_u64(), 0b0110);
        assert_eq!(a.not().to_u64(), 0b0011); // masked to 4 bits
    }

    #[test]
    fn arithmetic_wraps() {
        let a = Bits2::from_u64(200, 8);
        let b = Bits2::from_u64(100, 8);
        assert_eq!(a.add(&b).to_u64(), (300u64) & 0xFF); // 44
        assert_eq!(b.sub(&a).to_u64(), (100u64.wrapping_sub(200)) & 0xFF); // 156
        let m = Bits2::from_u64(0xFF, 8);
        assert_eq!(m.add(&Bits2::from_u64(1, 8)).to_u64(), 0); // wrap
    }

    #[test]
    fn shifts() {
        let a = Bits2::from_u64(0b0001, 4);
        assert_eq!(a.shl(2).to_u64(), 0b0100);
        assert_eq!(a.shl(4).to_u64(), 0); // out of width
        let b = Bits2::from_u64(0b1000, 4);
        assert_eq!(b.shr(3).to_u64(), 0b0001);
    }

    #[test]
    fn compare() {
        assert!(Bits2::from_u64(5, 8).ult(&Bits2::from_u64(6, 8)));
        assert!(!Bits2::from_u64(6, 8).ult(&Bits2::from_u64(6, 8)));
    }

    #[test]
    fn slice_concat() {
        let a = Bits2::from_u64(0b1011_0010, 8);
        assert_eq!(a.slice(7, 4).to_u64(), 0b1011);
        assert_eq!(a.slice(3, 0).to_u64(), 0b0010);
        let hi = Bits2::from_u64(0xA, 4);
        let lo = Bits2::from_u64(0x5, 4);
        let c = hi.concat(&lo);
        assert_eq!(c.width, 8);
        assert_eq!(c.to_u64(), 0xA5);
    }

    #[test]
    fn wide_values() {
        // 100-bit: set bit 99 and bit 0
        let mut w = Bits2::zero(100);
        w.set_bit(99, true);
        w.set_bit(0, true);
        assert!(w.get_bit(99));
        assert!(w.get_bit(0));
        assert_eq!(w.nwords(), 2);
        // shift bit 0 up to bit 64 (crosses word boundary)
        let s = Bits2::from_u64(1, 100).shl(64);
        assert!(s.get_bit(64));
        assert_eq!(s.word(1), 1);
        // wide add carry across word boundary
        let lo_max = Bits2::from_u64(u64::MAX, 100);
        let one = Bits2::from_u64(1, 100);
        let sum = lo_max.add(&one);
        assert_eq!(sum.word(0), 0);
        assert_eq!(sum.word(1), 1);
        // wide and/not
        assert!(lo_max.and(&one).get_bit(0));
        // wide slice across boundary
        assert_eq!(s.slice(64, 64).to_u64(), 1);
    }

    #[test]
    fn eq_value_cross_width() {
        // 8'd5 == 4'd5 numerically, even though widths differ.
        let a = Bits2::from_u64(5, 8);
        let b = Bits2::from_u64(5, 4);
        assert_ne!(a, b); // derived == includes width
        assert!(a.eq_value(&b)); // numeric == ignores width
        assert!(!Bits2::from_u64(5, 8).eq_value(&Bits2::from_u64(6, 8)));
    }

    #[test]
    fn mul_narrow_and_wide() {
        assert_eq!(
            Bits2::from_u64(12, 8).mul(&Bits2::from_u64(12, 8)).to_u64(),
            144
        );
        assert_eq!(
            Bits2::from_u64(200, 8).mul(&Bits2::from_u64(3, 8)).to_u64(),
            600 & 0xFF
        );
        // wide: (2^64) * 3 = 3<<64 → word1 == 3, word0 == 0 at width 128.
        let big = Bits2::from_u64(1, 128).shl(64); // == 2^64
        let r = big.mul(&Bits2::from_u64(3, 128));
        assert_eq!(r.word(0), 0);
        assert_eq!(r.word(1), 3);
        // wide carry: (2^64-1)*(2^64-1) at width 128.
        let m = Bits2::from_u64(u64::MAX, 128);
        let sq = m.mul(&m); // = 2^128 - 2^65 + 1
        assert_eq!(sq.word(0), 1);
        assert_eq!(sq.word(1), u64::MAX - 1);
    }

    #[test]
    fn ashr_signed() {
        // 8'b1000_0000 >>> 1 = 1100_0000 (sign fill)
        assert_eq!(Bits2::from_u64(0x80, 8).ashr(1).to_u64(), 0xC0);
        // positive: logical
        assert_eq!(Bits2::from_u64(0x40, 8).ashr(1).to_u64(), 0x20);
        // shift past width with sign → all ones
        assert_eq!(Bits2::from_u64(0x80, 8).ashr(9).to_u64(), 0xFF);
        // wide negative: bit 99 set, >>> 4 fills top 4 bits
        let mut w = Bits2::zero(100);
        w.set_bit(99, true);
        let r = w.ashr(4);
        assert!(r.get_bit(99) && r.get_bit(96) && r.get_bit(95));
        assert!(!r.get_bit(94));
    }

    #[test]
    fn div_rem_narrow_and_wide() {
        assert_eq!(
            Bits2::from_u64(100, 16)
                .udiv(&Bits2::from_u64(7, 16))
                .to_u64(),
            14
        );
        assert_eq!(
            Bits2::from_u64(100, 16)
                .urem(&Bits2::from_u64(7, 16))
                .to_u64(),
            2
        );
        assert_eq!(Bits2::from_u64(5, 8).udiv(&Bits2::zero(8)).to_u64(), 0); // /0 -> 0
        // wide: (2^96 + 12345) / 2^32  — quotient 2^64, remainder 12345
        let num = Bits2::from_u64(1, 128)
            .shl(96)
            .add(&Bits2::from_u64(12345, 128));
        let den = Bits2::from_u64(1, 128).shl(32); // 2^32
        let q = num.udiv(&den);
        let r = num.urem(&den);
        assert_eq!(q.word(1), 1); // 2^64
        assert_eq!(q.word(0), 0);
        assert_eq!(r.to_u64(), 12345);
        // q*den + r == num  (round-trip)
        assert!(q.mul(&den).add(&r).eq_value(&num));
    }

    #[test]
    fn wide_mul_add_chain() {
        // accumulate 3 * 7 added across a 128-bit register many times.
        let mut acc = Bits2::zero(128);
        let step = Bits2::from_u64(3, 128).mul(&Bits2::from_u64(7, 128)); // 21
        for _ in 0..1000 {
            acc = acc.add(&step);
        }
        assert_eq!(acc.to_u64(), 21_000);
    }

    #[test]
    fn value_interop() {
        let v = Value::from_u64(0xDEAD, 16);
        let b = Bits2::from_value(&v);
        assert_eq!(b.to_u64(), 0xDEAD);
        assert_eq!(b.to_value().to_u64(), Some(0xDEAD));
        // X collapses to 0
        let x = Value::new(8); // all-X
        assert!(Bits2::from_value(&x).is_zero());
    }
}
