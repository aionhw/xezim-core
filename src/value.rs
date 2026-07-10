//! Value types for SystemVerilog simulation.
//! Supports 4-state logic (0, 1, X, Z) with arbitrary-width bit vectors.
//!
//! Optimized representation: values ≤64 bits use inline u64 storage,
//! avoiding heap allocation entirely. Wider values fall back to Vec<LogicBit>.

use std::fmt;
use serde::{Serialize, Deserialize};

/// A single 4-state logic bit.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum LogicBit {
    Zero,
    One,
    X,
    Z,
}

impl LogicBit {
    pub fn from_char(c: char) -> Self {
        match c {
            '0' => Self::Zero,
            '1' => Self::One,
            'x' | 'X' => Self::X,
            'z' | 'Z' | '?' => Self::Z,
            _ => Self::X,
        }
    }

    pub fn to_bool(self) -> bool {
        matches!(self, Self::One)
    }

    pub fn is_known(self) -> bool {
        matches!(self, Self::Zero | Self::One)
    }
}

impl fmt::Display for LogicBit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Zero => write!(f, "0"),
            Self::One => write!(f, "1"),
            Self::X => write!(f, "x"),
            Self::Z => write!(f, "z"),
        }
    }
}

/// Storage for value bits. Values ≤64 bits use inline u64 pair.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
enum ValueStorage {
    /// Packed: val_bits holds 0/1, xz_bits marks X/Z.
    /// bit i: val=bit i of val_bits, xz=bit i of xz_bits
    /// 0: val=0,xz=0  1: val=1,xz=0  X: val=0,xz=1  Z: val=1,xz=1
    Inline { val_bits: u64, xz_bits: u64 },
    /// Fallback for width > 64.
    Wide(Vec<LogicBit>),
}

/// An arbitrary-width 4-state logic value.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Value {
    storage: ValueStorage,
    pub width: u32,
    pub is_signed: bool,
    /// When true, the inline val_bits hold f64 bits (IEEE 754).
    pub is_real: bool,
}

impl Value {
    /// Bit mask for the valid bits of an inline value.
    #[inline(always)]
    fn mask(width: u32) -> u64 {
        if width >= 64 { u64::MAX } else { (1u64 << width) - 1 }
    }

    /// Hard ceiling on a single Value's bit width (1 Mibit ≈ 128 KiB of `Wide`
    /// storage). No legitimate scalar/packed value is this wide; a larger width
    /// is always an artifact of a parameter underflow — e.g. `[N-1:0]` or a
    /// part-select/`infer_lhs_width` where N resolved to 0, so `N-1` wrapped to
    /// ~u32::MAX. Without this cap such a width allocates multiple GB and OOMs
    /// the run (notably black-parrot config-table extraction the const-evaluator
    /// can't resolve). Matches `elaborate::SANE_MAX_PACKED_WIDTH`.
    pub const MAX_WIDTH: u32 = 1 << 20;

    /// Clamp an absurd (underflowed) width to `MAX_WIDTH`, warning once.
    #[inline]
    fn cap_width(width: u32) -> u32 {
        if width > Self::MAX_WIDTH {
            use std::sync::atomic::{AtomicBool, Ordering};
            static WARNED: AtomicBool = AtomicBool::new(false);
            if !WARNED.swap(true, Ordering::Relaxed) {
                eprintln!("[xezim][warning] value width {} exceeds cap {}; clamping \
                           — likely a parameter underflow (`[N-1:0]` with N=0)",
                    width, Self::MAX_WIDTH);
            }
            Self::MAX_WIDTH
        } else {
            width
        }
    }

    pub fn new(width: u32) -> Self {
        let width = Self::cap_width(width);
        if width <= 64 {
            // All X: xz_bits = all 1s for width bits, val_bits = 0
            Self {
                storage: ValueStorage::Inline { val_bits: 0, xz_bits: Self::mask(width) },
                width,
                is_signed: false, is_real: false,
            }
        } else {
            Self {
                storage: ValueStorage::Wide(vec![LogicBit::X; width as usize]),
                width,
                is_signed: false, is_real: false,
            }
        }
    }

    pub fn zero(width: u32) -> Self {
        let width = Self::cap_width(width);
        if width <= 64 {
            Self { storage: ValueStorage::Inline { val_bits: 0, xz_bits: 0 }, width, is_signed: false, is_real: false }
        } else {
            Self { storage: ValueStorage::Wide(vec![LogicBit::Zero; width as usize]), width, is_signed: false, is_real: false }
        }
    }

    #[inline]
    pub fn from_u64(val: u64, width: u32) -> Self {
        let width = Self::cap_width(width);
        if width <= 64 {
            let mask = Self::mask(width);
            Self { storage: ValueStorage::Inline { val_bits: val & mask, xz_bits: 0 }, width, is_signed: false, is_real: false }
        } else {
            let mut bits = vec![LogicBit::Zero; width as usize];
            for i in 0..64.min(width as usize) {
                if (val >> i) & 1 == 1 { bits[i] = LogicBit::One; }
            }
            Self { storage: ValueStorage::Wide(bits), width, is_signed: false, is_real: false }
        }
    }

    /// Construct a Value from a u128, populating up to 128 bits at the given width.
    /// Bits beyond 128 are zero-filled.
    #[inline]
    pub fn from_u128(val: u128, width: u32) -> Self {
        let width = Self::cap_width(width);
        if width <= 64 {
            let mask = Self::mask(width);
            Self { storage: ValueStorage::Inline { val_bits: (val as u64) & mask, xz_bits: 0 }, width, is_signed: false, is_real: false }
        } else {
            let mut bits = vec![LogicBit::Zero; width as usize];
            let lim = 128.min(width as usize);
            for i in 0..lim {
                if (val >> i) & 1 == 1 { bits[i] = LogicBit::One; }
            }
            Self { storage: ValueStorage::Wide(bits), width, is_signed: false, is_real: false }
        }
    }

    /// Extract value as u128. Returns low 128 bits, treating X/Z as 0.
    #[inline]
    pub fn to_u128(&self) -> u128 {
        match &self.storage {
            ValueStorage::Inline { val_bits, xz_bits } => (*val_bits & !*xz_bits) as u128,
            ValueStorage::Wide(bits) => {
                let mut result: u128 = 0;
                for (i, bit) in bits.iter().enumerate() {
                    if i >= 128 { break; }
                    if *bit == LogicBit::One { result |= 1u128 << i; }
                }
                result
            }
        }
    }

    /// Create a Value from pre-computed inline bits (for cached number literals).
    #[inline]
    pub fn from_inline(val_bits: u64, xz_bits: u64, width: u32) -> Self {
        Self { storage: ValueStorage::Inline { val_bits, xz_bits }, width, is_signed: false, is_real: false }
    }

    /// Create a Value holding an f64 (stored as its IEEE 754 bit pattern in a 64-bit inline).
    pub fn from_f64(f: f64) -> Self {
        Self { storage: ValueStorage::Inline { val_bits: f.to_bits(), xz_bits: 0 }, width: 64, is_signed: false, is_real: true }
    }

    pub fn from_string(s: &str) -> Self {
        let bytes = s.as_bytes();
        let width = (bytes.len() * 8) as u32;
        if width <= 64 {
            let mut val_bits = 0u64;
            for (i, &b) in bytes.iter().rev().enumerate() {
                val_bits |= (b as u64) << (i * 8);
            }
            Self { storage: ValueStorage::Inline { val_bits, xz_bits: 0 }, width, is_signed: false, is_real: false }
        } else {
            let mut bits = Vec::with_capacity(width as usize);
            for &b in bytes.iter().rev() {
                for i in 0..8 {
                    bits.push(if (b >> i) & 1 == 1 { LogicBit::One } else { LogicBit::Zero });
                }
            }
            Self { storage: ValueStorage::Wide(bits), width, is_signed: false, is_real: false }
        }
    }

    /// Extract f64 from a real-typed value.
    pub fn to_f64(&self) -> f64 {
        if self.is_real {
            match &self.storage {
                ValueStorage::Inline { val_bits, .. } => f64::from_bits(*val_bits),
                _ => 0.0,
            }
        } else {
            if self.is_signed {
                self.to_i64().unwrap_or(0) as f64
            } else {
                self.to_u64().unwrap_or(0) as f64
            }
        }
    }

    /// Extract inline bits for caching. Returns None for Wide values.
    #[inline]
    pub fn inline_bits(&self) -> Option<(u64, u64)> {
        match &self.storage {
            ValueStorage::Inline { val_bits, xz_bits } => Some((*val_bits, *xz_bits)),
            _ => None,
        }
    }

    /// Overwrite inline storage in place.
    #[inline]
    pub fn set_inline_bits(&mut self, val_bits: u64, xz_bits: u64) -> bool {
        match &mut self.storage {
            ValueStorage::Inline { val_bits: v, xz_bits: x } => {
                *v = val_bits; *x = xz_bits; true
            }
            _ => false,
        }
    }

    /// Hot-path; called by `check_edge_id` per edge signal per settle
    /// iteration (millions of times on c910-scale runs). Marked
    /// `#[inline(always)]` so the Inline arm collapses to a direct
    /// (u64,u64) load with no enum match in the caller's frame.
    #[inline(always)]
    pub fn raw_bits(&self) -> (u64, u64) {
        match &self.storage {
            ValueStorage::Inline { val_bits, xz_bits } => (*val_bits, *xz_bits),
            ValueStorage::Wide(bits) => {
                let mut v = 0u64;
                let mut x = 0u64;
                for (i, &b) in bits.iter().take(64).enumerate() {
                    match b {
                        LogicBit::One => v |= 1u64 << i,
                        LogicBit::X => x |= 1u64 << i,
                        LogicBit::Z => { v |= 1u64 << i; x |= 1u64 << i; },
                        LogicBit::Zero => {},
                    }
                }
                (v, x)
            }
        }
    }

    /// Access the bits field (compatibility layer for existing code).
    /// Returns a temporary Vec for wide values, or constructs from inline.
    pub fn get_bits(&self) -> BitsRef<'_> {
        BitsRef { value: self }
    }

    #[inline(always)]
    fn inline_vals(&self) -> Option<(u64, u64)> {
        match &self.storage {
            ValueStorage::Inline { val_bits, xz_bits } => Some((*val_bits, *xz_bits)),
            _ => None,
        }
    }

    #[inline(always)]
    pub fn has_xz(&self) -> bool {
        match &self.storage {
            ValueStorage::Inline { xz_bits, .. } => *xz_bits != 0,
            ValueStorage::Wide(bits) => bits.iter().any(|b| matches!(b, LogicBit::X | LogicBit::Z)),
        }
    }

    /// Get bit at position i.
    /// Hot-path; called per gate input from `exec_fused_gate` on
    /// gate-level netlists (>1 billion calls on picorv32 test_synth).
    /// Marked `#[inline(always)]` so the Inline arm collapses to two
    /// shifts and a small match in the caller's frame.
    #[inline(always)]
    pub fn get_bit(&self, i: usize) -> LogicBit {
        if i as u32 >= self.width { return LogicBit::Zero; }
        match &self.storage {
            ValueStorage::Inline { val_bits, xz_bits } => {
                let v = (*val_bits >> i) & 1;
                let x = (*xz_bits >> i) & 1;
                match (v, x) {
                    (0, 0) => LogicBit::Zero,
                    (1, 0) => LogicBit::One,
                    (0, 1) => LogicBit::X,
                    (_, _) => LogicBit::Z,
                }
            }
            ValueStorage::Wide(bits) => bits.get(i).copied().unwrap_or(LogicBit::Zero),
        }
    }

    /// Hot 4-state bit accessor returning compact codes:
    /// 0=0, 1=1, 2=X, 3=Z. This avoids constructing/matching `LogicBit`
    /// in fused gate simulation.
    #[inline(always)]
    pub fn get_bit_code(&self, i: usize) -> u8 {
        if i as u32 >= self.width { return 0; }
        match &self.storage {
            ValueStorage::Inline { val_bits, xz_bits } => {
                (((*xz_bits >> i) & 1) << 1 | ((*val_bits >> i) & 1)) as u8
            }
            ValueStorage::Wide(bits) => match bits.get(i).copied().unwrap_or(LogicBit::Zero) {
                LogicBit::Zero => 0,
                LogicBit::One => 1,
                LogicBit::X => 2,
                LogicBit::Z => 3,
            },
        }
    }

    /// Set one bit from compact 4-state code. Returns true when the bit changed.
    #[inline(always)]
    pub fn set_bit_code(&mut self, i: usize, code: u8) -> bool {
        if i as u32 >= self.width { return false; }
        match &mut self.storage {
            ValueStorage::Inline { val_bits, xz_bits } => {
                let mask = 1u64 << i;
                let cur = (((*xz_bits >> i) & 1) << 1 | ((*val_bits >> i) & 1)) as u8;
                if cur == code { return false; }
                if code & 1 == 0 { *val_bits &= !mask; } else { *val_bits |= mask; }
                if code & 2 == 0 { *xz_bits &= !mask; } else { *xz_bits |= mask; }
                true
            }
            ValueStorage::Wide(bits) => {
                let bit = match code {
                    0 => LogicBit::Zero,
                    1 => LogicBit::One,
                    2 => LogicBit::X,
                    _ => LogicBit::Z,
                };
                if let Some(slot) = bits.get_mut(i) {
                    if *slot == bit { return false; }
                    *slot = bit;
                    true
                } else {
                    false
                }
            }
        }
    }

    /// Set bit at position i. Hot-path mirror of `get_bit`; same
    /// rationale for `#[inline(always)]`.
    #[inline(always)]
    pub fn set_bit(&mut self, i: usize, bit: LogicBit) {
        if i as u32 >= self.width { return; }
        match &mut self.storage {
            ValueStorage::Inline { val_bits, xz_bits } => {
                let mask = 1u64 << i;
                match bit {
                    LogicBit::Zero => { *val_bits &= !mask; *xz_bits &= !mask; }
                    LogicBit::One  => { *val_bits |= mask;  *xz_bits &= !mask; }
                    LogicBit::X    => { *val_bits &= !mask; *xz_bits |= mask; }
                    LogicBit::Z    => { *val_bits |= mask;  *xz_bits |= mask; }
                }
            }
            ValueStorage::Wide(bits) => {
                if let Some(b) = bits.get_mut(i) { *b = bit; }
            }
        }
    }

    /// Convert to `u64`, treating X/Z as 0.
    ///
    /// **Returns the LOW 64 bits for wide values**: any bits at positions
    /// ≥ 64 are silently dropped. The return type is `Option` for symmetry
    /// with potential X/Z failure paths but in practice always returns
    /// `Some(_)` for both inline and wide storage.
    ///
    /// Use this only when the value is known to fit in 64 bits —
    /// typically array indices, bit positions, loop counters, or shift
    /// amounts. For signal values that may exceed 64 bits (Verilog supports
    /// arbitrary widths), prefer `to_u128()`, `get_bits()`, or
    /// Value-aware comparisons.
    #[inline(always)]
    pub fn to_u64(&self) -> Option<u64> {
        match &self.storage {
            ValueStorage::Inline { val_bits, xz_bits } => Some(*val_bits & !*xz_bits),
            ValueStorage::Wide(bits) => {
                let mut result: u64 = 0;
                for (i, bit) in bits.iter().enumerate() {
                    if i >= 64 { break; }
                    if *bit == LogicBit::One { result |= 1u64 << i; }
                }
                Some(result)
            }
        }
    }

    /// Convert to i64 (sign-extended if is_signed).
    pub fn to_i64(&self) -> Option<i64> {
        let raw = self.to_u64()?;
        if self.is_signed && self.width > 0 && self.width < 64 {
            let sign_bit = 1u64 << (self.width - 1);
            if raw & sign_bit != 0 {
                Some((raw | !Self::mask(self.width)) as i64)
            } else {
                Some(raw as i64)
            }
        } else {
            Some(raw as i64)
        }
    }

    /// Resize to target width. If narrowing, truncate. If widening, zero/sign-extend.
    pub fn resize(&self, target: u32) -> Value {
        if target == 0 { return Value::zero(0); }
        if self.is_real {
            if target == 64 { return self.clone(); }
            // convert the real value to an integer (rounding to nearest)
            let f = self.to_f64();
            return Value::from_u64(f.round() as u64, target);
        }
        if target == self.width {
            return self.clone();
        }
        match &self.storage {
            ValueStorage::Inline { val_bits, xz_bits } if target <= 64 => {
                let mask = Self::mask(target);
                if target < self.width {
                    // Truncate
                    Value {
                        storage: ValueStorage::Inline { val_bits: *val_bits & mask, xz_bits: *xz_bits & mask },
                        width: target, is_signed: self.is_signed, is_real: false,
                    }
                } else {
                    // Widen
                    if self.is_signed && self.width > 0 {
                        let sign_bit = if self.width <= 64 { (*xz_bits >> (self.width - 1)) & 1 == 0 && (*val_bits >> (self.width - 1)) & 1 == 1 } else { false };
                        if sign_bit {
                            let ext_mask = mask & !Self::mask(self.width);
                            Value {
                                storage: ValueStorage::Inline { val_bits: *val_bits | ext_mask, xz_bits: *xz_bits },
                                width: target, is_signed: self.is_signed, is_real: false,
                            }
                        } else {
                            Value {
                                storage: ValueStorage::Inline { val_bits: *val_bits, xz_bits: *xz_bits },
                                width: target, is_signed: self.is_signed, is_real: false,
                            }
                        }
                    } else {
                        Value {
                            storage: ValueStorage::Inline { val_bits: *val_bits, xz_bits: *xz_bits },
                            width: target, is_signed: self.is_signed, is_real: false,
                        }
                    }
                }
            }
            _ => {
                // Fall back to bit-by-bit
                let mut result = if self.is_signed {
                    let sign = self.get_bit(self.width.saturating_sub(1) as usize);
                    let fill = if sign == LogicBit::One { LogicBit::One } else { LogicBit::Zero };
                    Value { storage: if target <= 64 {
                        let fill_val = if fill == LogicBit::One { Self::mask(target) } else { 0 };
                        ValueStorage::Inline { val_bits: fill_val, xz_bits: 0 }
                    } else {
                        ValueStorage::Wide(vec![fill; target as usize])
                    }, width: target, is_signed: self.is_signed , is_real: false }
                } else {
                    Value::zero(target)
                };
                result.is_signed = self.is_signed;
                let copy_bits = self.width.min(target) as usize;
                for i in 0..copy_bits {
                    result.set_bit(i, self.get_bit(i));
                }
                result
            }
        }
    }

    // === Arithmetic ===

    pub fn negate(&self) -> Value {
        if self.is_real {
            return Value::from_f64(-self.to_f64());
        }
        if self.has_xz() {
            return Value::new(self.width);
        }
        let w = self.width;
        let v = self.to_u64().unwrap_or(0);
        let mut r = Value::from_u64(v.wrapping_neg(), w);
        r.is_signed = true;
        r
    }

    /// IEEE 1800-2017 §10.7 assignment-padding resize. When widening, if the MSB
    /// of the source is X or Z the extension bits are X or Z respectively;
    /// otherwise behaves like `resize` (zero- or sign-extension). Used when padding
    /// a nonblocking/blocking assignment RHS to the LHS width.
    pub fn resize_for_assign(&self, target: u32) -> Value {
        if target == self.width || self.width == 0 || self.is_real {
            return self.resize(target);
        }
        if target < self.width {
            return self.resize(target);
        }
        let msb = self.get_bit(self.width.saturating_sub(1) as usize);
        if msb != LogicBit::X && msb != LogicBit::Z {
            return self.resize(target);
        }
        // X/Z extend
        match &self.storage {
            ValueStorage::Inline { val_bits, xz_bits } if target <= 64 => {
                let mask = Self::mask(target);
                let ext_mask = mask & !Self::mask(self.width);
                let (new_val, new_xz) = if msb == LogicBit::Z {
                    (*val_bits | ext_mask, *xz_bits | ext_mask)
                } else {
                    (*val_bits, *xz_bits | ext_mask)
                };
                Value {
                    storage: ValueStorage::Inline { val_bits: new_val, xz_bits: new_xz },
                    width: target, is_signed: self.is_signed, is_real: false,
                }
            }
            _ => {
                let mut result = self.resize(target);
                for i in self.width as usize..target as usize {
                    result.set_bit(i, msb);
                }
                result
            }
        }
    }

    #[inline]
    pub fn add(&self, other: &Value) -> Value {
        if self.is_real || other.is_real {
            return Value::from_f64(self.to_f64() + other.to_f64());
        }
        if self.has_xz() || other.has_xz() {
            return Value::new(self.width.max(other.width));
        }
        let w = self.width.max(other.width);
        let result_signed = self.is_signed && other.is_signed;
        let mut v = if w <= 64 {
            let a = self.to_u64().unwrap_or(0);
            let b = other.to_u64().unwrap_or(0);
            Value::from_u64(a.wrapping_add(b), w)
        } else {
            let a = self.to_u128();
            let b = other.to_u128();
            Value::from_u128(a.wrapping_add(b), w)
        };
        v.is_signed = result_signed;
        v
    }

    #[inline]
    pub fn sub(&self, other: &Value) -> Value {
        if self.is_real || other.is_real {
            return Value::from_f64(self.to_f64() - other.to_f64());
        }
        if self.has_xz() || other.has_xz() {
            return Value::new(self.width.max(other.width));
        }
        let w = self.width.max(other.width);
        let result_signed = self.is_signed && other.is_signed;
        let mut v = if w <= 64 {
            let a = self.to_u64().unwrap_or(0);
            let b = other.to_u64().unwrap_or(0);
            Value::from_u64(a.wrapping_sub(b), w)
        } else {
            let a = self.to_u128();
            let b = other.to_u128();
            Value::from_u128(a.wrapping_sub(b), w)
        };
        v.is_signed = result_signed;
        v
    }

    pub fn mul(&self, other: &Value) -> Value {
        if self.is_real || other.is_real {
            return Value::from_f64(self.to_f64() * other.to_f64());
        }
        if self.has_xz() || other.has_xz() { return Value::new(self.width.max(other.width)); }
        let w = self.width.max(other.width);
        let result_signed = self.is_signed && other.is_signed;
        let mut v = if w <= 64 {
            let a = self.to_u64().unwrap_or(0);
            let b = other.to_u64().unwrap_or(0);
            Value::from_u64(a.wrapping_mul(b), w)
        } else {
            let a = self.to_u128();
            let b = other.to_u128();
            Value::from_u128(a.wrapping_mul(b), w)
        };
        v.is_signed = result_signed;
        v
    }

    pub fn div(&self, other: &Value) -> Value {
        if self.is_real || other.is_real {
            return Value::from_f64(self.to_f64() / other.to_f64());
        }
        if self.has_xz() || other.has_xz() { return Value::new(self.width.max(other.width)); }
        let w = self.width.max(other.width);
        if w <= 64 {
            let a = self.to_u64().unwrap_or(0);
            let b = other.to_u64().unwrap_or(0);
            if b == 0 { return Value::new(w); }
            // IEEE 1800 §11.6.1: signed only when BOTH operands are signed;
            // the result then carries that signedness.
            if self.is_signed && other.is_signed {
                let sa = self.to_i64().unwrap_or(0);
                let sb = other.to_i64().unwrap_or(0);
                if sb == 0 { return Value::new(w); }
                let mut r = Value::from_u64(sa.wrapping_div(sb) as u64, w);
                r.is_signed = true;
                r
            } else {
                Value::from_u64(a / b, w)
            }
        } else {
            let a = self.to_u128();
            let b = other.to_u128();
            if b == 0 { return Value::new(w); }
            Value::from_u128(a / b, w)
        }
    }

    pub fn modulo(&self, other: &Value) -> Value {
        if self.is_real || other.is_real {
            return Value::from_f64(self.to_f64() % other.to_f64());
        }
        if self.has_xz() || other.has_xz() { return Value::new(self.width.max(other.width)); }
        let w = self.width.max(other.width);
        if w <= 64 {
            let b = other.to_u64().unwrap_or(0);
            if b == 0 { return Value::new(w); }
            // IEEE 1800 §11.6.1: signed only when BOTH operands are signed.
            if self.is_signed && other.is_signed {
                let sa = self.to_i64().unwrap_or(0);
                let sb = other.to_i64().unwrap_or(0);
                if sb == 0 { return Value::new(w); }
                let mut r = Value::from_u64(sa.wrapping_rem(sb) as u64, w);
                r.is_signed = true;
                r
            } else {
                let a = self.to_u64().unwrap_or(0);
                Value::from_u64(a % b, w)
            }
        } else {
            let a = self.to_u128();
            let b = other.to_u128();
            if b == 0 { return Value::new(w); }
            Value::from_u128(a % b, w)
        }
    }

    pub fn power(&self, other: &Value) -> Value {
        if self.is_real || other.is_real {
            return Value::from_f64(self.to_f64().powf(other.to_f64()));
        }
        if self.has_xz() || other.has_xz() { return Value::new(self.width); }
        let base = self.to_u64().unwrap_or(0);
        let exp = other.to_u64().unwrap_or(0);
        let mut result: u64 = 1;
        for _ in 0..exp.min(64) { result = result.wrapping_mul(base); }
        Value::from_u64(result, self.width)
    }

    // === Bitwise ===

    #[inline]
    pub fn bitwise_and(&self, other: &Value) -> Value {
        let w = self.width.max(other.width);
        match (&self.storage, &other.storage) {
            (ValueStorage::Inline { val_bits: av, xz_bits: ax }, ValueStorage::Inline { val_bits: bv, xz_bits: bx }) => {
                if *ax == 0 && *bx == 0 {
                    // Fast path: no X/Z
                    Value { storage: ValueStorage::Inline { val_bits: av & bv, xz_bits: 0 }, width: w, is_signed: false, is_real: false }
                } else {
                    // X propagation for AND: 0 & X = 0, 1 & X = X
                    let any_xz = ax | bx;
                    let result_val = av & bv & !any_xz;
                    let result_xz = any_xz & !((!av & !ax) | (!bv & !bx)); // known 0 kills X
                    Value { storage: ValueStorage::Inline { val_bits: result_val, xz_bits: result_xz & Self::mask(w) }, width: w, is_signed: false, is_real: false }
                }
            }
            _ => self.bitwise_op_slow(other, |a, b| match (a, b) {
                (LogicBit::Zero, _) | (_, LogicBit::Zero) => LogicBit::Zero,
                (LogicBit::One, LogicBit::One) => LogicBit::One,
                _ => LogicBit::X,
            }),
        }
    }

    #[inline]
    pub fn bitwise_or(&self, other: &Value) -> Value {
        let w = self.width.max(other.width);
        match (&self.storage, &other.storage) {
            (ValueStorage::Inline { val_bits: av, xz_bits: ax }, ValueStorage::Inline { val_bits: bv, xz_bits: bx }) => {
                if *ax == 0 && *bx == 0 {
                    Value { storage: ValueStorage::Inline { val_bits: av | bv, xz_bits: 0 }, width: w, is_signed: false, is_real: false }
                } else {
                    let any_xz = ax | bx;
                    let result_val = (av | bv) & !any_xz;
                    let result_xz = any_xz & !((av & !ax) | (bv & !bx)); // known 1 kills X
                    Value { storage: ValueStorage::Inline { val_bits: result_val | ((av & !ax) | (bv & !bx)), xz_bits: result_xz & Self::mask(w) }, width: w, is_signed: false, is_real: false }
                }
            }
            _ => self.bitwise_op_slow(other, |a, b| match (a, b) {
                (LogicBit::One, _) | (_, LogicBit::One) => LogicBit::One,
                (LogicBit::Zero, LogicBit::Zero) => LogicBit::Zero,
                _ => LogicBit::X,
            }),
        }
    }

    #[inline]
    pub fn bitwise_xor(&self, other: &Value) -> Value {
        let w = self.width.max(other.width);
        match (&self.storage, &other.storage) {
            (ValueStorage::Inline { val_bits: av, xz_bits: ax }, ValueStorage::Inline { val_bits: bv, xz_bits: bx }) => {
                let any_xz = ax | bx;
                let result_val = (av ^ bv) & !any_xz;
                Value { storage: ValueStorage::Inline { val_bits: result_val, xz_bits: any_xz & Self::mask(w) }, width: w, is_signed: false, is_real: false }
            }
            _ => self.bitwise_op_slow(other, |a, b| match (a, b) {
                (LogicBit::Zero, LogicBit::Zero) | (LogicBit::One, LogicBit::One) => LogicBit::Zero,
                (LogicBit::Zero, LogicBit::One) | (LogicBit::One, LogicBit::Zero) => LogicBit::One,
                _ => LogicBit::X,
            }),
        }
    }

    pub fn bitwise_xnor(&self, other: &Value) -> Value {
        let r = self.bitwise_xor(other);
        r.bitwise_not()
    }

    #[inline]
    pub fn bitwise_not(&self) -> Value {
        match &self.storage {
            ValueStorage::Inline { val_bits, xz_bits } => {
                let mask = Self::mask(self.width);
                Value {
                    storage: ValueStorage::Inline { val_bits: (!val_bits & !xz_bits) & mask, xz_bits: *xz_bits },
                    width: self.width, is_signed: self.is_signed, is_real: false,
                }
            }
            ValueStorage::Wide(bits) => {
                let new_bits: Vec<LogicBit> = bits.iter().map(|b| match b {
                    LogicBit::Zero => LogicBit::One,
                    LogicBit::One => LogicBit::Zero,
                    _ => LogicBit::X,
                }).collect();
                Value { storage: ValueStorage::Wide(new_bits), width: self.width, is_signed: self.is_signed , is_real: false }
            }
        }
    }

    fn bitwise_op_slow(&self, other: &Value, op: impl Fn(LogicBit, LogicBit) -> LogicBit) -> Value {
        let w = self.width.max(other.width) as usize;
        let mut result = Value::zero(w as u32);
        for i in 0..w {
            let a = self.get_bit(i);
            let b = other.get_bit(i);
            result.set_bit(i, op(a, b));
        }
        result
    }

    /// Per-bit merge following IEEE 1800 §11.4.11 Table 11-21: a bit is known
    /// only where `self` and `other` agree; every other bit becomes X. Used by
    /// the `?:` operator when the condition is X/Z: both branches are evaluated
    /// and combined bitwise.
    pub fn merge_unknown(&self, other: &Value) -> Value {
        let w = self.width.max(other.width);
        match (&self.storage, &other.storage) {
            (ValueStorage::Inline { val_bits: av, xz_bits: ax },
             ValueStorage::Inline { val_bits: bv, xz_bits: bx }) if w <= 64 => {
                let mask = Self::mask(w);
                let ax = *ax & mask;
                let bx = *bx & mask;
                let av = *av & mask;
                let bv = *bv & mask;
                // Bit is known iff both sides are known and equal.
                let both_known = !ax & !bx & mask;
                let agree = both_known & !(av ^ bv);
                let xz_bits = mask & !agree;
                let val_bits = av & agree;
                Value {
                    storage: ValueStorage::Inline { val_bits, xz_bits },
                    width: w, is_signed: self.is_signed && other.is_signed, is_real: false,
                }
            }
            _ => {
                let mut result = Value::new(w);
                for i in 0..w as usize {
                    let a = if i < self.width as usize { self.get_bit(i) } else { LogicBit::Zero };
                    let b = if i < other.width as usize { other.get_bit(i) } else { LogicBit::Zero };
                    let bit = match (a, b) {
                        (LogicBit::Zero, LogicBit::Zero) => LogicBit::Zero,
                        (LogicBit::One, LogicBit::One) => LogicBit::One,
                        _ => LogicBit::X,
                    };
                    result.set_bit(i, bit);
                }
                result
            }
        }
    }

    // === Shifts ===

    #[inline]
    pub fn shift_left(&self, amount: &Value) -> Value {
        let amt = amount.to_u64().unwrap_or(0) as u32;
        if amount.has_xz() { return Value::new(self.width); }
        match &self.storage {
            ValueStorage::Inline { val_bits, xz_bits } => {
                let mask = Self::mask(self.width);
                if amt >= self.width { return Value::zero(self.width); }
                Value {
                    storage: ValueStorage::Inline {
                        val_bits: (val_bits << amt) & mask,
                        xz_bits: (xz_bits << amt) & mask,
                    },
                    width: self.width, is_signed: self.is_signed, is_real: false,
                }
            }
            _ => {
                let mut result = Value::zero(self.width);
                for i in 0..self.width as usize {
                    let src = (i as u32).checked_sub(amt);
                    if let Some(s) = src {
                        result.set_bit(i, self.get_bit(s as usize));
                    }
                }
                result
            }
        }
    }

    #[inline]
    pub fn shift_right(&self, amount: &Value) -> Value {
        let amt = amount.to_u64().unwrap_or(0) as u32;
        if amount.has_xz() { return Value::new(self.width); }
        match &self.storage {
            ValueStorage::Inline { val_bits, xz_bits } => {
                if amt >= self.width { return Value::zero(self.width); }
                Value {
                    storage: ValueStorage::Inline {
                        val_bits: val_bits >> amt,
                        xz_bits: xz_bits >> amt,
                    },
                    width: self.width, is_signed: self.is_signed, is_real: false,
                }
            }
            _ => {
                let mut result = Value::zero(self.width);
                for i in 0..self.width as usize {
                    let src = i + amt as usize;
                    if src < self.width as usize {
                        result.set_bit(i, self.get_bit(src));
                    }
                }
                result
            }
        }
    }

    pub fn arith_shift_right(&self, amount: &Value) -> Value {
        let amt = amount.to_u64().unwrap_or(0) as u32;
        if amount.has_xz() { return Value::new(self.width); }
        let sign = self.get_bit(self.width.saturating_sub(1) as usize);
        match &self.storage {
            ValueStorage::Inline { val_bits, xz_bits } => {
                if amt >= self.width {
                    return if sign == LogicBit::One {
                        let mask = Self::mask(self.width);
                        Value { storage: ValueStorage::Inline { val_bits: mask, xz_bits: 0 }, width: self.width, is_signed: true , is_real: false }
                    } else { Value::zero(self.width) };
                }
                let shifted_val = val_bits >> amt;
                let shifted_xz = xz_bits >> amt;
                if sign == LogicBit::One && self.width > 0 {
                    let mask = Self::mask(self.width);
                    let ext = mask & !Self::mask(self.width - amt);
                    Value {
                        storage: ValueStorage::Inline { val_bits: shifted_val | ext, xz_bits: shifted_xz },
                        width: self.width, is_signed: true, is_real: false,
                    }
                } else {
                    Value {
                        storage: ValueStorage::Inline { val_bits: shifted_val, xz_bits: shifted_xz },
                        width: self.width, is_signed: self.is_signed, is_real: false,
                    }
                }
            }
            _ => {
                let mut result = Value::zero(self.width);
                for i in 0..self.width as usize {
                    let src = i + amt as usize;
                    let bit = if src < self.width as usize { self.get_bit(src) } else { sign };
                    result.set_bit(i, bit);
                }
                result.is_signed = true;
                result
            }
        }
    }

    // === Comparison ===

    #[inline]
    pub fn is_equal(&self, other: &Value) -> Value {
        if self.is_real || other.is_real {
            return Value::from_u64((self.to_f64() == other.to_f64()) as u64, 1);
        }
        if self.has_xz() || other.has_xz() {
            // IEEE 1800: == returns X only when ambiguous.
            // If any position has both bits known and they differ -> 0.
            let w = self.width.max(other.width) as usize;
            let sign_a = self.is_signed && (self.width as usize) < w;
            let sign_b = other.is_signed && (other.width as usize) < w;
            let top_a = if self.width > 0 { self.get_bit((self.width - 1) as usize) } else { LogicBit::Zero };
            let top_b = if other.width > 0 { other.get_bit((other.width - 1) as usize) } else { LogicBit::Zero };
            for i in 0..w {
                let a = if i < self.width as usize { self.get_bit(i) } else if sign_a { top_a } else { LogicBit::Zero };
                let b = if i < other.width as usize { other.get_bit(i) } else if sign_b { top_b } else { LogicBit::Zero };
                let a_known = matches!(a, LogicBit::Zero | LogicBit::One);
                let b_known = matches!(b, LogicBit::Zero | LogicBit::One);
                if a_known && b_known && a != b {
                    return Value::from_u64(0, 1);
                }
            }
            return Value::new(1);
        }
        // IEEE 1800: if either operand is signed, sign-extend both to max width
        if (self.is_signed || other.is_signed) && self.width != other.width {
            let w = self.width.max(other.width);
            let a = self.resize(w).to_u64().unwrap_or(0);
            let b = other.resize(w).to_u64().unwrap_or(0);
            return Value::from_u64((a == b) as u64, 1);
        }
        let eq = self.to_u64().unwrap_or(0) == other.to_u64().unwrap_or(0);
        Value::from_u64(eq as u64, 1)
    }

    #[inline]
    pub fn is_not_equal(&self, other: &Value) -> Value {
        let eq = self.is_equal(other);
        match eq.get_bit(0) {
            LogicBit::Zero => Value::from_u64(1, 1),
            LogicBit::One => Value::from_u64(0, 1),
            _ => Value::new(1),
        }
    }

    pub fn case_eq(&self, other: &Value) -> Value {
        // === operator: compares including X/Z
        let w = self.width.max(other.width) as usize;
        for i in 0..w {
            if self.get_bit(i) != other.get_bit(i) { return Value::from_u64(0, 1); }
        }
        Value::from_u64(1, 1)
    }

    pub fn case_neq(&self, other: &Value) -> Value {
        let eq = self.case_eq(other);
        if eq.to_u64() == Some(1) { Value::from_u64(0, 1) } else { Value::from_u64(1, 1) }
    }

    /// casez wildcard equality (IEEE 1800 §12.5.1): Z bits (also written
    /// `?` in literals — both lex to LogicBit::Z) on either side are
    /// treated as don't-care positions and always match.
    pub fn casez_eq(&self, other: &Value) -> Value {
        let w = self.width.max(other.width) as usize;
        for i in 0..w {
            let a = self.get_bit(i);
            let b = other.get_bit(i);
            if a == LogicBit::Z || b == LogicBit::Z { continue; }
            if a != b { return Value::from_u64(0, 1); }
        }
        Value::from_u64(1, 1)
    }

    /// casex wildcard equality: X and Z bits on either side are
    /// treated as don't-care.
    pub fn casex_eq(&self, other: &Value) -> Value {
        let w = self.width.max(other.width) as usize;
        for i in 0..w {
            let a = self.get_bit(i);
            let b = other.get_bit(i);
            if matches!(a, LogicBit::X | LogicBit::Z) || matches!(b, LogicBit::X | LogicBit::Z) { continue; }
            if a != b { return Value::from_u64(0, 1); }
        }
        Value::from_u64(1, 1)
    }

    /// SV §11.4.6 wildcard equality (`==?`). X/Z bits in *either*
    /// operand are wildcards (always match) — LRM 1800-2017 explicitly
    /// says "either operand". A hard mismatch on a non-wildcard bit
    /// forces the result to 0; otherwise the result is 1.
    pub fn wildcard_eq(&self, other: &Value) -> Value {
        // SV §11.4.6: only x/z bits in the RIGHT operand (the pattern) are
        // wildcards (don't-cares). An x/z in the LEFT operand at a non-masked
        // position is NOT a wildcard — it makes the result x, unless some
        // other position definitely mismatches (which forces 0).
        let w = self.width.max(other.width) as usize;
        let mut saw_unknown = false;
        for i in 0..w {
            let l = self.get_bit(i);
            let r = other.get_bit(i);
            if matches!(r, LogicBit::X | LogicBit::Z) {
                continue; // wildcard position — excluded from comparison
            }
            if matches!(l, LogicBit::X | LogicBit::Z) {
                saw_unknown = true; // unknown here, but keep scanning for a 0
                continue;
            }
            if l != r {
                return Value::from_u64(0, 1);
            }
        }
        if saw_unknown {
            Value::new(1) // 1-bit x
        } else {
            Value::from_u64(1, 1)
        }
    }

    /// SV §11.4.6 wildcard inequality (`!=?`) — `wildcard_eq` inverted;
    /// X stays X.
    pub fn wildcard_ne(&self, other: &Value) -> Value {
        match self.wildcard_eq(other).get_bit(0) {
            LogicBit::Zero => Value::from_u64(1, 1),
            LogicBit::One => Value::from_u64(0, 1),
            _ => Value::new(1),
        }
    }

    #[inline]
    pub fn less_than(&self, other: &Value) -> Value {
        if self.has_xz() || other.has_xz() { return Value::new(1); }
        if self.is_real || other.is_real {
            return Value::from_u64((self.to_f64() < other.to_f64()) as u64, 1);
        }
        // Per IEEE 1364-2005 §5.5.1 (preserved through SystemVerilog): if
        // EITHER operand is unsigned, the relational comparison is unsigned.
        // Only when BOTH operands are signed do we use signed compare.
        if self.is_signed && other.is_signed {
            let a = self.to_i64().unwrap_or(0);
            let b = other.to_i64().unwrap_or(0);
            Value::from_u64((a < b) as u64, 1)
        } else {
            let a = self.to_u64().unwrap_or(0);
            let b = other.to_u64().unwrap_or(0);
            Value::from_u64((a < b) as u64, 1)
        }
    }

    #[inline]
    pub fn less_equal(&self, other: &Value) -> Value {
        if self.has_xz() || other.has_xz() { return Value::new(1); }
        if self.is_real || other.is_real {
            return Value::from_u64((self.to_f64() <= other.to_f64()) as u64, 1);
        }
        if self.is_signed && other.is_signed {
            Value::from_u64((self.to_i64().unwrap_or(0) <= other.to_i64().unwrap_or(0)) as u64, 1)
        } else {
            Value::from_u64((self.to_u64().unwrap_or(0) <= other.to_u64().unwrap_or(0)) as u64, 1)
        }
    }

    #[inline]
    pub fn greater_than(&self, other: &Value) -> Value { other.less_than(self) }
    #[inline]
    pub fn greater_equal(&self, other: &Value) -> Value { other.less_equal(self) }

    // === Logic ===

    pub fn logic_and(&self, other: &Value) -> Value {
        let a = self.is_nonzero();
        let b = other.is_nonzero();
        match (a, b) {
            (Some(true), Some(true)) => Value::from_u64(1, 1),
            (Some(false), _) | (_, Some(false)) => Value::from_u64(0, 1),
            _ => Value::new(1),
        }
    }

    pub fn logic_or(&self, other: &Value) -> Value {
        let a = self.is_nonzero();
        let b = other.is_nonzero();
        match (a, b) {
            (Some(true), _) | (_, Some(true)) => Value::from_u64(1, 1),
            (Some(false), Some(false)) => Value::from_u64(0, 1),
            _ => Value::new(1),
        }
    }

    pub fn logic_not(&self) -> Value {
        match self.is_nonzero() {
            Some(true) => Value::from_u64(0, 1),
            Some(false) => Value::from_u64(1, 1),
            None => Value::new(1),
        }
    }

    /// Logical implication `->` (IEEE 1800-2017 §11.4.7). `a -> b` is
    /// `!a || b`: definite-false left or definite-true right yields 1;
    /// true-left & false-right yields 0; otherwise X.
    pub fn logic_impl(&self, other: &Value) -> Value {
        match (self.is_nonzero(), other.is_nonzero()) {
            (Some(false), _) | (_, Some(true)) => Value::from_u64(1, 1),
            (Some(true), Some(false)) => Value::from_u64(0, 1),
            _ => Value::new(1),
        }
    }

    /// Logical equivalence `<->` (IEEE 1800-2017 §11.4.7). 1 when both
    /// sides reduce to the same bool, 0 when they disagree, X if either
    /// side is unknown.
    pub fn logic_equiv(&self, other: &Value) -> Value {
        match (self.is_nonzero(), other.is_nonzero()) {
            (Some(x), Some(y)) => Value::from_u64((x == y) as u64, 1),
            _ => Value::new(1),
        }
    }

    /// Returns Some(true) if nonzero, Some(false) if zero, None if contains X/Z.
    pub fn is_nonzero(&self) -> Option<bool> {
        if self.is_real {
            return Some(self.to_f64() != 0.0);
        }
        // Matches iverilog's reduce-to-bool (NetEBLogic, eval_tree.cc):
        // a *definite* 1 anywhere makes the value truthy even if other
        // bits are X/Z. Only return None (unknown) when there are X/Z
        // bits and no definite 1 — i.e. the truth could still go either
        // way. Returning None on *any* X/Z over-propagates X through
        // `&&` / `||` / `!` / `->` / `<->`.
        match &self.storage {
            ValueStorage::Inline { val_bits, xz_bits } => {
                // A bit is a definite 1 where val=1 and xz=0.
                if *val_bits & !*xz_bits != 0 { Some(true) }
                else if *xz_bits != 0 { None }
                else { Some(false) }
            }
            ValueStorage::Wide(bits) => {
                if bits.iter().any(|b| *b == LogicBit::One) { Some(true) }
                else if bits.iter().any(|b| matches!(b, LogicBit::X | LogicBit::Z)) { None }
                else { Some(false) }
            }
        }
    }

    // === Reduction ===

    pub fn reduce_and(&self) -> Value {
        match &self.storage {
            ValueStorage::Inline { val_bits, xz_bits } => {
                let mask = Self::mask(self.width);
                if *xz_bits & mask != 0 { Value::new(1) }
                else { Value::from_u64(if *val_bits & mask == mask { 1 } else { 0 }, 1) }
            }
            ValueStorage::Wide(bits) => {
                if bits.iter().any(|b| !b.is_known()) { Value::new(1) }
                else { Value::from_u64(if bits.iter().all(|b| *b == LogicBit::One) { 1 } else { 0 }, 1) }
            }
        }
    }

    pub fn reduce_or(&self) -> Value {
        match &self.storage {
            ValueStorage::Inline { val_bits, xz_bits } => {
                let mask = Self::mask(self.width);
                if (*val_bits & !xz_bits & mask) != 0 { Value::from_u64(1, 1) }
                else if *xz_bits & mask != 0 { Value::new(1) }
                else { Value::from_u64(0, 1) }
            }
            ValueStorage::Wide(bits) => {
                if bits.iter().any(|b| *b == LogicBit::One) { Value::from_u64(1, 1) }
                else if bits.iter().any(|b| !b.is_known()) { Value::new(1) }
                else { Value::from_u64(0, 1) }
            }
        }
    }

    pub fn reduce_xor(&self) -> Value {
        if self.has_xz() { return Value::new(1); }
        let v = self.to_u64().unwrap_or(0);
        Value::from_u64(v.count_ones() as u64 % 2, 1)
    }

    // === Concatenation ===

    pub fn concat(values: &[Value]) -> Value {
        // values[0] is leftmost (MSB)
        let total_width: u32 = values.iter().map(|v| v.width).sum();
        let mut result = Value::zero(total_width);
        let mut offset = 0u32;
        for val in values.iter().rev() {
            for i in 0..val.width as usize {
                result.set_bit((offset as usize) + i, val.get_bit(i));
            }
            offset += val.width;
        }
        result
    }

    /// Format as hex string.
    pub fn to_hex(&self) -> String {
        if self.width == 0 { return "0".into(); }
        let ndigits = ((self.width + 3) / 4) as usize;
        let mut s = String::with_capacity(ndigits);
        for d in (0..ndigits).rev() {
            let mut digit = 0u8;
            let mut has_x = false;
            for b in 0..4 {
                let bit_idx = d * 4 + b;
                match self.get_bit(bit_idx) {
                    LogicBit::One => digit |= 1 << b,
                    LogicBit::X | LogicBit::Z => has_x = true,
                    _ => {}
                }
            }
            if has_x { s.push('x'); } else { s.push(char::from_digit(digit as u32, 16).unwrap()); }
        }
        s
    }

    /// Format as binary string.
    pub fn to_bin(&self) -> String {
        let mut s = String::with_capacity(self.width as usize);
        for i in (0..self.width as usize).rev() {
            s.push(match self.get_bit(i) {
                LogicBit::Zero => '0',
                LogicBit::One => '1',
                LogicBit::X => 'x',
                LogicBit::Z => 'z',
            });
        }
        if s.is_empty() { s.push('0'); }
        s
    }

    /// Compatibility: access bits as a slice-like interface.
    /// This is for existing code that uses value.bits[i] or value.bits.first().
    pub fn bits_first(&self) -> LogicBit {
        self.get_bit(0)
    }

    /// Extract string content from bit vector.
    pub fn to_string(&self) -> String {
        let mut s = Vec::new();
        let bytes = self.width / 8;
        for b in 0..bytes {
            let mut byte_val = 0u8;
            for bit in 0..8 {
                if self.get_bit((b * 8 + bit) as usize) == LogicBit::One { byte_val |= 1 << bit; }
            }
            if byte_val == 0 { break; }
            s.push(byte_val);
        }
        // SV strings are MSB-first, so byte 0 is the LAST character.
        s.reverse();
        String::from_utf8_lossy(&s).into_owned()
    }
}

/// A reference wrapper for accessing bits, providing compatibility with
/// code that uses `value.bits`.
pub struct BitsRef<'a> {
    value: &'a Value,
}

impl<'a> BitsRef<'a> {
    pub fn first(&self) -> Option<LogicBit> {
        if self.value.width > 0 { Some(self.value.get_bit(0)) } else { None }
    }

    pub fn get(&self, i: usize) -> Option<LogicBit> {
        if (i as u32) < self.value.width { Some(self.value.get_bit(i)) } else { None }
    }

    pub fn len(&self) -> usize {
        self.value.width as usize
    }

    pub fn iter(&self) -> BitsIter<'a> {
        BitsIter { value: self.value, pos: 0 }
    }
}

impl<'a> PartialEq for BitsRef<'a> {
    fn eq(&self, other: &Self) -> bool {
        if self.value.width != other.value.width { return false; }
        for i in 0..self.value.width as usize {
            if self.value.get_bit(i) != other.value.get_bit(i) { return false; }
        }
        true
    }
}

pub struct BitsIter<'a> {
    value: &'a Value,
    pos: usize,
}

impl<'a> Iterator for BitsIter<'a> {
    type Item = LogicBit;
    fn next(&mut self) -> Option<Self::Item> {
        if (self.pos as u32) < self.value.width {
            let bit = self.value.get_bit(self.pos);
            self.pos += 1;
            Some(bit)
        } else {
            None
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}'", self.width)?;
        if self.has_xz() {
            write!(f, "b{}", self.to_bin())
        } else {
            write!(f, "h{}", self.to_hex())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_ops() {
        let a = Value::from_u64(5, 8);
        let b = Value::from_u64(3, 8);
        assert_eq!(a.add(&b).to_u64(), Some(8));
        assert_eq!(a.sub(&b).to_u64(), Some(2));
        assert_eq!(a.bitwise_and(&b).to_u64(), Some(1));
        assert_eq!(a.bitwise_or(&b).to_u64(), Some(7));
    }

    #[test]
    fn test_shifts() {
        let v = Value::from_u64(0x0F, 8);
        assert_eq!(v.shift_left(&Value::from_u64(4, 8)).to_u64(), Some(0xF0));
        assert_eq!(v.shift_right(&Value::from_u64(2, 8)).to_u64(), Some(3));
    }

    #[test]
    fn test_x_propagation() {
        let x = Value::new(8); // all X
        let one = Value::from_u64(1, 8);
        assert!(x.add(&one).has_xz());
        assert!(x.is_equal(&one).has_xz());
    }

    fn bit(b: LogicBit) -> Value {
        let mut v = Value::zero(1);
        v.set_bit(0, b);
        v
    }

    #[test]
    fn test_logic_impl() {
        let z = Value::from_u64(0, 1);
        let o = Value::from_u64(1, 1);
        let x = Value::new(1);
        // truth table
        assert_eq!(z.logic_impl(&z).get_bit(0), LogicBit::One);
        assert_eq!(z.logic_impl(&o).get_bit(0), LogicBit::One);
        assert_eq!(o.logic_impl(&z).get_bit(0), LogicBit::Zero);
        assert_eq!(o.logic_impl(&o).get_bit(0), LogicBit::One);
        // X-propagation: 0 -> x = 1, x -> 1 = 1, 1 -> x = x, x -> 0 = x
        assert_eq!(z.logic_impl(&x).get_bit(0), LogicBit::One);
        assert_eq!(x.logic_impl(&o).get_bit(0), LogicBit::One);
        assert_eq!(o.logic_impl(&x).get_bit(0), LogicBit::X);
        assert_eq!(x.logic_impl(&z).get_bit(0), LogicBit::X);
        assert_eq!(x.logic_impl(&x).get_bit(0), LogicBit::X);
    }

    #[test]
    fn test_logic_equiv() {
        let z = Value::from_u64(0, 1);
        let o = Value::from_u64(1, 1);
        let x = Value::new(1);
        assert_eq!(z.logic_equiv(&z).get_bit(0), LogicBit::One);
        assert_eq!(o.logic_equiv(&o).get_bit(0), LogicBit::One);
        assert_eq!(z.logic_equiv(&o).get_bit(0), LogicBit::Zero);
        assert_eq!(o.logic_equiv(&z).get_bit(0), LogicBit::Zero);
        assert_eq!(x.logic_equiv(&o).get_bit(0), LogicBit::X);
        assert_eq!(z.logic_equiv(&x).get_bit(0), LogicBit::X);
        // non-1-bit reduce-to-bool: 4'b0010 <-> 1 == 1
        assert_eq!(Value::from_u64(2, 4).logic_equiv(&o).get_bit(0), LogicBit::One);
    }

    #[test]
    fn test_wildcard_eq_ne() {
        // 4'b1010 ==? 4'b1010 = 1
        assert_eq!(Value::from_u64(0b1010, 4).wildcard_eq(&Value::from_u64(0b1010, 4)).get_bit(0), LogicBit::One);
        // 4'b1010 ==? 4'b1011 = 0
        assert_eq!(Value::from_u64(0b1010, 4).wildcard_eq(&Value::from_u64(0b1011, 4)).get_bit(0), LogicBit::Zero);
        // 4'b1011 ==? 4'b1x1x  (x in rhs = wildcard) = 1
        let mut rhs = Value::from_u64(0b1010, 4);
        rhs.set_bit(0, LogicBit::X); // ...1x1x
        rhs.set_bit(2, LogicBit::X);
        assert_eq!(Value::from_u64(0b1011, 4).wildcard_eq(&rhs).get_bit(0), LogicBit::One);
        // 4'b0011 ==? 4'b1x1x = 0  (bit3: 0 vs 1, hard mismatch)
        assert_eq!(Value::from_u64(0b0011, 4).wildcard_eq(&rhs).get_bit(0), LogicBit::Zero);
        // x in lhs (rhs binary) => result x
        let mut lhs = Value::from_u64(0b1010, 4);
        lhs.set_bit(2, LogicBit::X);
        assert_eq!(lhs.wildcard_eq(&Value::from_u64(0b1010, 4)).get_bit(0), LogicBit::X);
        // !=? is the inverse; x stays x
        assert_eq!(Value::from_u64(0b1010, 4).wildcard_ne(&Value::from_u64(0b1011, 4)).get_bit(0), LogicBit::One);
        assert_eq!(Value::from_u64(0b1011, 4).wildcard_ne(&rhs).get_bit(0), LogicBit::Zero);
        assert_eq!(lhs.wildcard_ne(&Value::from_u64(0b1010, 4)).get_bit(0), LogicBit::X);
    }

    #[test]
    fn test_is_nonzero_definite_one() {
        // all-X => unknown
        assert_eq!(Value::new(4).is_nonzero(), None);
        // pure zero => false
        assert_eq!(Value::from_u64(0, 4).is_nonzero(), Some(false));
        // pure binary nonzero => true
        assert_eq!(Value::from_u64(2, 4).is_nonzero(), Some(true));
        // a definite 1 with X elsewhere => true (the fix)
        let mut v = Value::new(4); // all X
        v.set_bit(1, LogicBit::One);
        assert_eq!(v.is_nonzero(), Some(true));
        // X bits but no definite 1 => unknown
        let mut v2 = Value::from_u64(0, 4);
        v2.set_bit(0, LogicBit::X);
        assert_eq!(v2.is_nonzero(), None);
        // consequence: `1xxx && 1` is true, not X
        let mut v3 = Value::new(4);
        v3.set_bit(3, LogicBit::One);
        assert_eq!(v3.logic_and(&Value::from_u64(1, 1)).get_bit(0), LogicBit::One);
        // sanity: bit() helper round-trips
        assert_eq!(bit(LogicBit::X).get_bit(0), LogicBit::X);
    }

    #[test]
    fn test_to_dec_string_wide_no_overflow() {
        // Regression: values wider than 128 bits used to overflow the u128
        // accumulator in to_dec_string and panic (UVM prints 4096-bit
        // uvm_bitstream_t fields). Must produce the exact decimal instead.
        assert_eq!(
            Value::ones(128).to_dec_string(),
            "340282366920938463463374607431768211455"
        );
        assert_eq!(
            Value::ones(256).to_dec_string(),
            "115792089237316195423570985008687907853269984665640564039457584007913129639935"
        );
        // Small magnitude carried in a wide storage still prints plainly.
        assert_eq!(Value::from_u64(12345, 200).to_dec_string(), "12345");
        assert_eq!(Value::from_u64(0, 200).to_dec_string(), "0");
        // Signed wide all-ones is -1 (two's complement, no shift overflow).
        let mut neg1 = Value::ones(128);
        neg1.is_signed = true;
        assert_eq!(neg1.to_dec_string(), "-1");
        // Signed wide most-negative: MSB set, rest zero at width 128 => -2^127.
        let mut most_neg = Value::from_u64(0, 128);
        most_neg.set_bit(127, LogicBit::One);
        most_neg.is_signed = true;
        assert_eq!(
            most_neg.to_dec_string(),
            "-170141183460469231731687303715884105728"
        );
    }
}

// Compatibility shims for the simulator
impl Value {
    /// Check if the value represents a nonzero / true condition
    pub fn is_true(&self) -> bool {
        self.is_nonzero().unwrap_or(false)
    }

    /// Check if the value has any unknown (X/Z) bits
    pub fn has_unknown(&self) -> bool {
        match &self.storage {
            ValueStorage::Inline { xz_bits, .. } => *xz_bits != 0,
            ValueStorage::Wide(bits) => bits.iter().any(|b| matches!(b, LogicBit::X | LogicBit::Z)),
        }
    }

    /// Create a value with all bits set to 1
    pub fn ones(width: u32) -> Self {
        let width = Self::cap_width(width);
        if width <= 64 {
            Self::from_u64(Self::mask(width), width)
        } else {
            let bits = vec![LogicBit::One; width as usize];
            Self { storage: ValueStorage::Wide(bits), width, is_signed: false, is_real: false }
        }
    }

    /// Decimal string representation
    pub fn to_dec_string(&self) -> String {
        if self.is_real {
            return format!("{:?}", self.to_f64());
        }
        if self.has_unknown() {
            return "x".to_string();
        }
        if self.width <= 64 {
            if self.is_signed {
                if let Some(v) = self.to_i64() {
                    return format!("{}", v);
                }
            }
            if let Some(v) = self.to_u64() {
                return format!("{}", v);
            }
        }
        // Wide value (> 64 bits): a fixed-width integer accumulator would
        // overflow for anything wider than 128 bits (UVM prints fields such
        // as the 4096-bit `uvm_bitstream_t`), so build the decimal string
        // with a schoolbook base-10 accumulator that handles any width.
        let width = self.width as usize;
        let neg = self.is_signed && self.get_bit(width - 1) == LogicBit::One;

        // Magnitude bits, LSB at index 0. For a negative signed value take
        // the two's-complement (invert + 1) so we print the magnitude.
        let mut mag: Vec<u8> = (0..width)
            .map(|i| (self.get_bit(i) == LogicBit::One) as u8)
            .collect();
        if neg {
            for b in mag.iter_mut() {
                *b ^= 1;
            }
            let mut carry = 1u8;
            for b in mag.iter_mut() {
                let sum = *b + carry;
                *b = sum & 1;
                carry = sum >> 1;
                if carry == 0 {
                    break;
                }
            }
        }

        // Convert magnitude (MSB→LSB) to little-endian decimal digits:
        // digits = digits * 2 + bit, propagating base-10 carries.
        let mut digits: Vec<u8> = vec![0];
        for i in (0..width).rev() {
            let mut carry = mag[i];
            for d in digits.iter_mut() {
                let v = *d * 2 + carry;
                *d = v % 10;
                carry = v / 10;
            }
            while carry > 0 {
                digits.push(carry % 10);
                carry /= 10;
            }
        }

        let mut s = String::with_capacity(digits.len() + neg as usize);
        if neg {
            s.push('-');
        }
        for d in digits.iter().rev() {
            s.push((b'0' + d) as char);
        }
        s
    }

    /// Convert packed bytes to a SystemVerilog-style string.
    /// Interprets the value as big-endian bytes (MSB first) and
    /// trims leading NUL bytes introduced by widening.
    pub fn to_sv_string(&self) -> String {
        let num_bytes = ((self.width + 7) / 8) as usize;
        if num_bytes == 0 {
            return String::new();
        }
        let mut out: Vec<u8> = Vec::new();
        for bi in (0..num_bytes).rev() {
            let mut byte = 0u8;
            for b in 0..8usize {
                let bit_idx = bi * 8 + b;
                if bit_idx >= self.width as usize {
                    break;
                }
                if self.get_bit(bit_idx) == LogicBit::One {
                    byte |= 1u8 << b;
                }
            }
            if byte != 0 {
                out.push(byte);
            }
        }
        String::from_utf8_lossy(&out).to_string()
    }

    /// Hex string representation
    pub fn to_hex_string(&self) -> String {
        self.to_hex()
    }

    /// Binary string representation  
    pub fn to_bin_string(&self) -> String {
        self.to_bin()
    }

    /// Parse from a string with given radix (2, 8, 10, 16)
    pub fn from_str_radix(s: &str, radix: u32, width: u32) -> Self {
        let s = s.trim().replace("_", "");
        if s.contains('x') || s.contains('X') || s.contains('z') || s.contains('Z') || s.contains('?') {
            // XEZIM_X_LITERAL_TO_ZERO=1: coerce X/Z literals in source to 0,
            // matching Verilator's 2-state behavior. Useful for designs that
            // use `{N{1'bx}}` as a "don't care" assertion in case-mux defaults
            // (e.g. XuanTie c910's ct_iu_rbus.v) where the don't-care actually
            // gets sampled and poisons downstream registers in 4-state sims.
            // Cached on first call — env lookup is too slow for the hot path.
            use std::sync::OnceLock;
            static X_TO_ZERO: OnceLock<bool> = OnceLock::new();
            let x_to_zero = *X_TO_ZERO.get_or_init(|| {
                std::env::var("XEZIM_X_LITERAL_TO_ZERO")
                    .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
                    .unwrap_or(false)
            });
            if x_to_zero {
                // Coerce X only (not Z or ?) — Z and ? are kept because:
                //  - ? is the wildcard syntax for casez/casex case labels
                //  - Z is high-impedance, semantically distinct from X
                // Coercing them would break wildcard pattern matching in case
                // statements that use `?` as "don't care" bits.
                let cleaned: String = s.chars()
                    .map(|c| match c { 'x'|'X' => '0', _ => c })
                    .collect();
                if !cleaned.contains('z') && !cleaned.contains('Z') && !cleaned.contains('?') {
                    return Self::from_str_radix(&cleaned, radix, width);
                }
                // Continue with normal parsing — Z/? bits preserved.
            }
            // Parse with unknown bits
            let mut val = Self::zero(width);
            let bits_per_digit = match radix {
                2 => 1, 8 => 3, 16 => 4,
                _ => {
                    // For decimal, can't have x/z
                    return Self::new(width);
                }
            };
            for (i, ch) in s.chars().rev().enumerate() {
                let bit_pos = i * bits_per_digit;
                match ch {
                    'x' | 'X' => {
                        for b in 0..bits_per_digit {
                            if bit_pos + b < width as usize {
                                val.set_bit(bit_pos + b, LogicBit::X);
                            }
                        }
                    }
                    'z' | 'Z' | '?' => {
                        for b in 0..bits_per_digit {
                            if bit_pos + b < width as usize {
                                val.set_bit(bit_pos + b, LogicBit::Z);
                            }
                        }
                    }
                    _ => {
                        if let Some(digit) = ch.to_digit(radix) {
                            for b in 0..bits_per_digit {
                                if bit_pos + b < width as usize {
                                    val.set_bit(bit_pos + b, if (digit >> b) & 1 == 1 { LogicBit::One } else { LogicBit::Zero });
                                }
                            }
                        }
                    }
                }
            }
            // IEEE §5.7.1: If the MSB digit is x, upper bits fill with x.
            // If the MSB digit is z, upper bits fill with z.
            // Otherwise, upper bits fill with 0.
            let specified_bits = s.chars().count() * bits_per_digit;
            if specified_bits < width as usize {
                let msb_char = s.chars().next().unwrap_or('0');
                let fill = match msb_char {
                    'x' | 'X' => LogicBit::X,
                    'z' | 'Z' | '?' => LogicBit::Z,
                    _ => LogicBit::Zero,
                };
                if fill != LogicBit::Zero {
                    for b in specified_bits..width as usize {
                        val.set_bit(b, fill);
                    }
                }
            }
            val
        } else {
            // Pure numeric
            if let Ok(v) = u64::from_str_radix(&s, radix) {
                return Self::from_u64(v, width);
            }
            // Wide value: parse digit-by-digit for radices that are powers of 2.
            let bits_per_digit = match radix { 2 => 1, 8 => 3, 16 => 4, _ => 0 };
            if bits_per_digit == 0 {
                // Decimal wide number not supported here; fall back to zero.
                return Self::zero(width);
            }
            let mut val = Self::zero(width);
            for (i, ch) in s.chars().rev().enumerate() {
                let bit_pos = i * bits_per_digit;
                if let Some(digit) = ch.to_digit(radix) {
                    for b in 0..bits_per_digit {
                        if bit_pos + b < width as usize {
                            val.set_bit(bit_pos + b, if (digit >> b) & 1 == 1 { LogicBit::One } else { LogicBit::Zero });
                        }
                    }
                }
            }
            val
        }
    }

    /// Select a single bit
    pub fn bit_select(&self, index: usize) -> Value {
        let bit = self.get_bit(index);
        let mut v = Value::zero(1);
        v.set_bit(0, bit);
        v
    }

    /// Select a range of bits [left:right]
    #[inline]
    pub fn range_select(&self, left: usize, right: usize) -> Value {
        let width = if left >= right { left - right + 1 } else { right - left + 1 };
        // LRM §11.5.1: out-of-range part-select bits read as X. A runtime index
        // that underflowed (`sig[v-1:0]` with `v` = 0 at time 0 → left ≈ u32::MAX)
        // requests a slice far beyond the source; building it would allocate a
        // multi-GB (cap-clamped) value and stall settling. Return a bounded all-X
        // value instead. Only fires for absurd widths, so in-range selects (which
        // are never wider than MAX_WIDTH) are unaffected.
        if width > Self::MAX_WIDTH as usize {
            return Value::new(width.min((self.width.max(1)) as usize) as u32);
        }
        let lo = left.min(right);
        // Fast path: Inline source whose extraction fits in 64 bits collapses
        // to a single shift+mask per of (val_bits, xz_bits) instead of `width`
        // iterations of get_bit/set_bit. Profile on c906 hello showed this
        // function consuming 53% of CPU due to the per-bit loop.
        if let ValueStorage::Inline { val_bits, xz_bits } = self.storage {
            if width <= 64 {
                let mask = if width == 64 { u64::MAX } else { (1u64 << width) - 1 };
                return Value {
                    storage: ValueStorage::Inline {
                        val_bits: (val_bits >> lo) & mask,
                        xz_bits: (xz_bits >> lo) & mask,
                    },
                    width: width as u32,
                    is_signed: false,
                    is_real: false,
                };
            }
        }
        // Fast path: Wide source whose extraction fits in 64 bits packs into
        // an Inline result via a single per-bit accumulate-into-u64 loop,
        // skipping the per-iteration set_bit dispatch overhead. Profile on
        // c906 hello showed Wide→Inline range_select dominating after the
        // Inline→Inline fast path landed (set_bit fan-out was ~40% of
        // range_select self-time on its own).
        if let ValueStorage::Wide(bits) = &self.storage {
            // Wide → Wide fast path for width > 64: replace the per-bit
            // get_bit/set_bit loop with a single slice copy. The source
            // already stores `Vec<LogicBit>` (1 byte per bit) so the copy
            // is just a memcpy.
            if width > 64 {
                let mut out = vec![LogicBit::Zero; width];
                let len = bits.len();
                if lo < len {
                    let copy_len = (lo + width).min(len) - lo;
                    out[..copy_len].copy_from_slice(&bits[lo..lo + copy_len]);
                }
                return Value {
                    storage: ValueStorage::Wide(out),
                    width: width as u32,
                    is_signed: false,
                    is_real: false,
                };
            }
            if width <= 64 {
                let mut val_bits: u64 = 0;
                let mut xz_bits: u64 = 0;
                let end = lo + width;
                let len = bits.len();
                for i in lo..end.min(len) {
                    let pos = i - lo;
                    let m = 1u64 << pos;
                    match bits[i] {
                        LogicBit::Zero => {}
                        LogicBit::One => { val_bits |= m; }
                        LogicBit::X => { xz_bits |= m; }
                        LogicBit::Z => { val_bits |= m; xz_bits |= m; }
                    }
                }
                return Value {
                    storage: ValueStorage::Inline { val_bits, xz_bits },
                    width: width as u32,
                    is_signed: false,
                    is_real: false,
                };
            }
        }
        let mut result = Value::zero(width as u32);
        for i in 0..width {
            result.set_bit(i, self.get_bit(lo + i));
        }
        result
    }

    /// Placeholder kept for binary compatibility — counters were removed
    /// after they confirmed the fast paths cover 100% of c906 calls.
    pub fn dump_range_select_stats() {}

    /// Not-equal comparison
    pub fn neq(&self, other: &Value) -> Value {
        self.is_not_equal(other)
    }

    /// Less-or-equal comparison
    pub fn leq(&self, other: &Value) -> Value {
        self.less_equal(other)
    }

    /// Greater-or-equal comparison
    pub fn geq(&self, other: &Value) -> Value {
        self.greater_equal(other)
    }
}

impl Value {
    /// Copy the storage from another value (used in NBA apply).
    /// `#[inline(always)]` so the `match` on (self.storage, other.storage)
    /// collapses at the call site (LoadSignal hot path in the bytecode VM)
    /// — copy_from accounted for 16% of c910 hello CPU and showed a cache-
    /// stall pattern at the function-entry signal_table[s] load.
    #[inline(always)]
    pub fn copy_from(&mut self, other: &Value) {
        // Fast path: Inline→Inline is just a word-level overwrite (no alloc).
        // Wide→Wide with the same length reuses `self`'s existing Vec buffer
        // via `extend_from_slice` after `clear()`, avoiding the per-iter
        // allocation that `storage.clone()` would do. Mixed variants fall
        // back to the generic clone.
        //
        // Copies `width`, `is_signed`, and `is_real` as well — this is the
        // drop-in equivalent of `*self = other.clone()` minus the heap
        // allocation for Wide values. Before: callers that wanted full-value
        // replace had to write `*self = other.clone()`; they can now use
        // `copy_from` and get the no-alloc benefit for free.
        match (&mut self.storage, &other.storage) {
            (ValueStorage::Inline { val_bits: sv, xz_bits: sx },
             ValueStorage::Inline { val_bits: ov, xz_bits: ox }) => {
                *sv = *ov; *sx = *ox;
            }
            (ValueStorage::Wide(sv), ValueStorage::Wide(ov)) => {
                sv.clear();
                sv.extend_from_slice(ov);
            }
            _ => {
                self.storage = other.storage.clone();
            }
        }
        self.width = other.width;
        self.is_signed = other.is_signed;
        self.is_real = other.is_real;
    }
}

impl Value {
    /// Instance method concat: self ++ other (self is MSB side)
    pub fn concat_with(&self, other: &Value) -> Value {
        Value::concat(&[self.clone(), other.clone()])
    }
}

impl Value {
    /// Create a value with all bits set to Z
    pub fn all_z(width: u32) -> Self {
        if width <= 64 {
            // For inline: xz_bits = all 1s (marks X/Z), val_bits = all 1s (Z vs X)
            let mask = Self::mask(width);
            Self {
                storage: ValueStorage::Inline { val_bits: mask, xz_bits: mask },
                width,
                is_signed: false, is_real: false,
            }
        } else {
            Self {
                storage: ValueStorage::Wide(vec![LogicBit::Z; width as usize]),
                width,
                is_signed: false, is_real: false,
            }
        }
    }
}
