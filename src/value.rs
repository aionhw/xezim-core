//! Value types for SystemVerilog simulation.
//! Supports 4-state logic (0, 1, X, Z) with arbitrary-width bit vectors.
//!
//! Optimized representation: values ≤64 bits use inline u64 storage,
//! avoiding heap allocation entirely. Wider values (>64 bits) use the packed
//! 2-bit `PackedBits` representation (4 logic bits per byte, ~4× less memory
//! than a `Vec<LogicBit>`), boxed so the storage enum stays 24 bytes.

use serde::{Deserialize, Serialize};
use std::fmt;

use crate::packed_value::PackedBits;

/// A single 4-state logic bit.
///
/// `#[repr(u8)]` pins the discriminants to the 2-bit codes already used by
/// `to_code`/`from_code` (Zero=0, One=1, X=2, Z=3). That makes one `LogicBit`
/// exactly one byte with no padding, which is the code the packed `Wide`
/// storage reads back with `PackedBits` (4 bits per byte).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[repr(u8)]
pub enum LogicBit {
    Zero = 0,
    One = 1,
    X = 2,
    Z = 3,
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

    /// Convert from 2-bit code (for packed storage).
    /// 00 = Zero, 01 = One, 10 = X, 11 = Z
    #[inline]
    pub fn from_code(code: u8) -> Self {
        match code & 0b11 {
            0b00 => Self::Zero,
            0b01 => Self::One,
            0b10 => Self::X,
            _ => Self::Z,  // 0b11
        }
    }

    /// Convert to 2-bit code (for packed storage).
    /// Zero = 00, One = 01, X = 10, Z = 11
    #[inline]
    pub fn to_code(self) -> u8 {
        match self {
            Self::Zero => 0b00,
            Self::One => 0b01,
            Self::X => 0b10,
            Self::Z => 0b11,
        }
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
#[derive(Debug, Clone, Eq, Hash, Serialize, Deserialize)]
enum ValueStorage {
    /// Packed: val_bits holds 0/1, xz_bits marks X/Z.
    /// bit i: val=bit i of val_bits, xz=bit i of xz_bits
    /// 0: val=0,xz=0  1: val=1,xz=0  X: val=0,xz=1  Z: val=1,xz=1
    Inline { val_bits: u64, xz_bits: u64 },
    /// Fallback for width > 64: a boxed, 2-bit-packed array of logic bits.
    /// The serialized wire format stays a `Vec<LogicBit>` (see `wide_serde`)
    /// so on-disk artifacts written by earlier versions remain readable.
    #[serde(with = "wide_serde")]
    Wide(Box<PackedBits>),
}

/// Serialize the boxed packed storage as the historical `Vec<LogicBit>` wire
/// format (Varint bit-count + one `LogicBit` discriminant per bit). This keeps
/// `-o` compile artifacts and design-cache files byte-identical with versions
/// that predate the packed storage, and lets them deserialize into the new
/// representation.
mod wide_serde {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    use super::LogicBit;
    use crate::packed_value::PackedBits;

    // serde `with` passes the field's exact type (`Box<PackedBits>`), so the
    // boxed reference is required by the serde contract.
    #[allow(clippy::borrowed_box)]
    pub fn serialize<S: Serializer>(pb: &Box<PackedBits>, s: S) -> Result<S::Ok, S::Error> {
        pb.iter().collect::<Vec<LogicBit>>().serialize(s)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<Box<PackedBits>, D::Error> {
        let bits = Vec::<LogicBit>::deserialize(d)?;
        Ok(Box::new(PackedBits::from_bits(bits)))
    }
}

impl PartialEq for ValueStorage {
    /// Same result as the previous `#[derive(PartialEq)]` (Inline compares its
    /// two words, Wide compares its bits, mixed variants are never equal).
    /// PackedBits' derived PartialEq compares the packed bytes, which visits
    /// 4× fewer bytes than the old `Vec<LogicBit>` word loop; padding bits in
    /// the top byte are canonicalized to 0 at construction, so byte equality
    /// ⇔ bit equality for every width.
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                ValueStorage::Inline { val_bits: av, xz_bits: ax },
                ValueStorage::Inline { val_bits: bv, xz_bits: bx },
            ) => av == bv && ax == bx,
            (ValueStorage::Wide(a), ValueStorage::Wide(b)) => a == b,
            _ => false,
        }
    }
}

/// An arbitrary-width 4-state logic value.
#[derive(Debug, Clone, Eq, Hash, Serialize, Deserialize)]
pub struct Value {
    storage: ValueStorage,
    pub width: u32,
    pub is_signed: bool,
    /// When true, the inline val_bits hold f64 bits (IEEE 754).
    pub is_real: bool,
    /// §5.7.1 unbased-unsized literal (`'0`/`'1`/`'x`/`'z`): a 1-bit value
    /// that REPLICATES its bit to the width of whatever context consumes it.
    /// Binary ops normalize a fill operand to the other side's width
    /// (`fill_pair`), and `resize`/`resize_for_assign` replicate instead of
    /// zero/sign-extending. Cleared on every resize, so stored signal values
    /// never carry it. Serde default keeps older artifacts readable.
    #[serde(default)]
    pub is_fill: bool,
}

impl PartialEq for Value {
    /// Identical result to the previous `#[derive(PartialEq)]` — `&&` over the
    /// same field comparisons — but the scalar header (`width` and the three
    /// flags) is tested BEFORE the bit storage, so a width/flag mismatch never
    /// walks a `Wide` bit vector. `signal_table[id] != val` change detection in
    /// the VM runs this on every signal write.
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.width == other.width
            && self.is_signed == other.is_signed
            && self.is_real == other.is_real
            && self.is_fill == other.is_fill
            && self.storage == other.storage
    }
}

/// Build Wide storage with every bit set to `bit` (top clamped by width).
fn wide_filled_bits(width: u32, bit: LogicBit) -> ValueStorage {
    ValueStorage::Wide(Box::new(PackedBits::new_fill(width, bit)))
}

impl Value {
    /// §5.7.1 — natural width of an UNSIZED based literal (`'h1234…`).
    ///
    /// An unsized number is at least 32 bits, but its size must never DROP digits
    /// the source actually wrote: `'h123456789ABCDEF0` carries 64 bits of value and
    /// parsing it at a flat 32 silently kept only the low half. Returns
    /// `max(32, bits implied by the digit string)`; the usual context resize then
    /// widens or truncates from there. Small literals are unaffected (their natural
    /// width is under 32), so this only ever widens a constant that would have lost
    /// data.
    pub fn unsized_literal_width(value: &str, radix: u32) -> u32 {
        let digits = value.chars().filter(|c| *c != '_').count() as u32;
        let natural = match radix {
            2 => digits,
            8 => digits.saturating_mul(3),
            16 => digits.saturating_mul(4),
            // Decimal: use the magnitude when it fits, else a safe upper bound
            // (log2(10) < 3.33, so 4 bits per digit never under-counts).
            _ => {
                let cleaned: String = value.chars().filter(|c| *c != '_').collect();
                match cleaned.parse::<u128>() {
                    Ok(v) => (128 - v.leading_zeros()).max(1),
                    Err(_) => digits.saturating_mul(4),
                }
            }
        };
        natural.max(32)
    }

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
    ///
    /// The warning machinery (atomic + `eprintln!`) lives in an out-of-line
    /// `#[cold]` helper: `cap_width` is on the constructor path of every
    /// `Value::new`/`zero`/`from_u64`, all of which are inlined across the
    /// crate boundary into the VM loop, and the formatting code inlined there
    /// otherwise bloats those call sites for a branch that never fires.
    #[inline(always)]
    fn cap_width(width: u32) -> u32 {
        if width > Self::MAX_WIDTH {
            Self::cap_width_cold(width)
        } else {
            width
        }
    }

    #[cold]
    #[inline(never)]
    fn cap_width_cold(width: u32) -> u32 {
        use std::sync::atomic::{AtomicBool, Ordering};
        static WARNED: AtomicBool = AtomicBool::new(false);
        if !WARNED.swap(true, Ordering::Relaxed) {
            eprintln!("[xezim][warning] value width {} exceeds cap {}; clamping \
                       — likely a parameter underflow (`[N-1:0]` with N=0)",
                width, Self::MAX_WIDTH);
        }
        Self::MAX_WIDTH
    }

    /// §5.7.1: an unbased-unsized literal — 1-bit, replicating into any
    /// consuming context (see `is_fill`).
    pub fn fill_of(c: char) -> Self {
        let mut v = match c {
            '0' => Value::zero(1),
            '1' => Value::from_u64(1, 1),
            'z' | 'Z' => Value::all_z(1),
            _ => Value::new(1), // x
        };
        v.is_fill = true;
        v
    }

    /// Replicate this fill value's bit to `width` (flag cleared).
    #[cold]
    #[inline(never)]
    fn fill_at(&self, width: u32) -> Value {
        let width = Self::cap_width(width.max(1));
        let bit = self.get_bit(0);
        if width <= 64 {
            let m = Self::mask(width);
            let (v, x) = match bit {
                LogicBit::Zero => (0, 0),
                LogicBit::One => (m, 0),
                LogicBit::X => (0, m),
                LogicBit::Z => (m, m),
            };
            Value { storage: ValueStorage::Inline { val_bits: v, xz_bits: x }, width, is_signed: false, is_real: false, is_fill: false }
        } else {
            Value { storage: wide_filled_bits(width, bit), width, is_signed: false, is_real: false, is_fill: false }
        }
    }

    /// Normalize a binary op's operands when either is a §5.7.1 fill value:
    /// the fill side widens (by bit replication) to the other side's width.
    /// Returns None on the hot path (no fill involved).
    ///
    /// Every binary operator starts with this, so the hot path must be nothing
    /// but two flag loads and a branch. The widening itself (two `Value`
    /// clones plus `fill_at`) is out of line and `#[cold]` so it does not get
    /// inlined into `add`/`bitwise_and`/`is_equal`/… and push them past the
    /// cross-crate inlining threshold.
    #[inline(always)]
    fn fill_pair(&self, other: &Value) -> Option<(Value, Value)> {
        if self.is_fill || other.is_fill {
            Some(self.fill_pair_cold(other))
        } else {
            None
        }
    }

    #[cold]
    #[inline(never)]
    fn fill_pair_cold(&self, other: &Value) -> (Value, Value) {
        let w = self.width.max(other.width).max(1);
        let a = if self.is_fill { self.fill_at(w) } else { self.clone() };
        let b = if other.is_fill { other.fill_at(w) } else { other.clone() };
        (a, b)
    }

    /// `#[inline]`: `xezim` builds with `lto = false`, so an unannotated
    /// `pub fn` in this crate is a real cross-crate call. `Value::new(1)` (a
    /// 1-bit X) is the X-propagation result of nearly every operator, so it
    /// must collapse to two immediate stores at the call site.
    #[inline]
    pub fn new(width: u32) -> Self {
        let width = Self::cap_width(width);
        if width <= 64 {
            // All X: xz_bits = all 1s for width bits, val_bits = 0
            Self {
                storage: ValueStorage::Inline { val_bits: 0, xz_bits: Self::mask(width) },
                width,
                is_signed: false, is_real: false, is_fill: false,
            }
        } else {
            Self {
                storage: ValueStorage::Wide(Box::new(PackedBits::new_x(width))),
                width,
                is_signed: false, is_real: false, is_fill: false,
            }
        }
    }

    #[inline]
    pub fn zero(width: u32) -> Self {
        let width = Self::cap_width(width);
        if width <= 64 {
            Self { storage: ValueStorage::Inline { val_bits: 0, xz_bits: 0 }, width, is_signed: false, is_real: false, is_fill: false }
        } else {
            Self { storage: ValueStorage::Wide(Box::new(PackedBits::new_zero(width))), width, is_signed: false, is_real: false, is_fill: false }
        }
    }

    #[inline]
    pub fn from_u64(val: u64, width: u32) -> Self {
        let width = Self::cap_width(width);
        if width <= 64 {
            let mask = Self::mask(width);
            Self { storage: ValueStorage::Inline { val_bits: val & mask, xz_bits: 0 }, width, is_signed: false, is_real: false, is_fill: false }
        } else {
            let mut pb = PackedBits::new_zero(width);
            for i in 0..64.min(width as usize) {
                if (val >> i) & 1 == 1 { pb.set(i, LogicBit::One); }
            }
            Self { storage: ValueStorage::Wide(Box::new(pb)), width, is_signed: false, is_real: false, is_fill: false }
        }
    }

    /// Construct a Value from a u128, populating up to 128 bits at the given width.
    /// Bits beyond 128 are zero-filled.
    #[inline]
    pub fn from_u128(val: u128, width: u32) -> Self {
        let width = Self::cap_width(width);
        if width <= 64 {
            let mask = Self::mask(width);
            Self { storage: ValueStorage::Inline { val_bits: (val as u64) & mask, xz_bits: 0 }, width, is_signed: false, is_real: false, is_fill: false }
        } else {
            let mut pb = PackedBits::new_zero(width);
            let lim = 128.min(width as usize);
            for i in 0..lim {
                if (val >> i) & 1 == 1 { pb.set(i, LogicBit::One); }
            }
            Self { storage: ValueStorage::Wide(Box::new(pb)), width, is_signed: false, is_real: false, is_fill: false }
        }
    }

    /// Extract value as u128. Returns low 128 bits, treating X/Z as 0.
    #[inline]
    pub fn to_u128(&self) -> u128 {
        match &self.storage {
            ValueStorage::Inline { val_bits, xz_bits } => (*val_bits & !*xz_bits) as u128,
            ValueStorage::Wide(bits) => {
                let mut result: u128 = 0;
                for i in 0..128.min(bits.len() as usize) {
                    if bits.get(i) == LogicBit::One { result |= 1u128 << i; }
                }
                result
            }
        }
    }

    /// Create a Value from pre-computed inline bits (for cached number literals).
    #[inline]
    pub fn from_inline(val_bits: u64, xz_bits: u64, width: u32) -> Self {
        Self { storage: ValueStorage::Inline { val_bits, xz_bits }, width, is_signed: false, is_real: false, is_fill: false }
    }

    /// Create a Value holding an f64 (stored as its IEEE 754 bit pattern in a 64-bit inline).
    pub fn from_f64(f: f64) -> Self {
        Self { storage: ValueStorage::Inline { val_bits: f.to_bits(), xz_bits: 0 }, width: 64, is_signed: false, is_real: true, is_fill: false }
    }

    pub fn from_string(s: &str) -> Self {
        // A SystemVerilog string is a BYTE string. ASCII maps 1:1; any char
        // above 0x7F is taken as its Latin-1 byte (one byte per char, the
        // inverse of `to_sv_string`) so raw-byte content — §21.2.1.4
        // unformatted `%u`/`%z` dumps — round-trips instead of expanding
        // into multi-byte UTF-8.
        let latin1: Vec<u8>;
        let bytes: &[u8] = if s.is_ascii() {
            s.as_bytes()
        } else {
            latin1 = s.chars().map(|c| (c as u32) as u8).collect();
            &latin1
        };
        let width = (bytes.len() * 8) as u32;
        if width <= 64 {
            let mut val_bits = 0u64;
            for (i, &b) in bytes.iter().rev().enumerate() {
                val_bits |= (b as u64) << (i * 8);
            }
            Self { storage: ValueStorage::Inline { val_bits, xz_bits: 0 }, width, is_signed: false, is_real: false, is_fill: false }
        } else {
            let bits = bytes.iter().rev().flat_map(|&b| (0..8).map(move |i| {
                if (b >> i) & 1 == 1 { LogicBit::One } else { LogicBit::Zero }
            }));
            Self { storage: ValueStorage::Wide(Box::new(PackedBits::from_bits(bits))), width, is_signed: false, is_real: false, is_fill: false }
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
            ValueStorage::Wide(bits) => bits.raw_bits_low64(),
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
            ValueStorage::Wide(bits) => bits.has_xz(),
        }
    }

    /// §6.11.1 / §10.7: coerce to a 2-state value by mapping every X and Z
    /// bit to 0. A 2-state object (`bit`/`byte`/`int`/…) can never hold X or Z,
    /// so an implicit conversion of a 4-state RHS drops the unknowns before the
    /// bits land in the destination. Known bits are preserved; the result is
    /// fully defined (xz cleared).
    #[inline]
    pub fn to_two_state(&self) -> Value {
        if self.is_real || !self.has_xz() {
            return self.clone();
        }
        match &self.storage {
            ValueStorage::Inline { val_bits, xz_bits } => Value {
                storage: ValueStorage::Inline {
                    val_bits: *val_bits & !*xz_bits,
                    xz_bits: 0,
                },
                width: self.width,
                is_signed: self.is_signed,
                is_real: false, is_fill: false,
            },
            ValueStorage::Wide(_bits) => {
                let mut out = self.clone();
                if let ValueStorage::Wide(ob) = &mut out.storage {
                    ob.transform(|b| if matches!(b, LogicBit::X | LogicBit::Z) { LogicBit::Zero } else { b });
                }
                out
            }
        }
    }

    /// Get bit at position i.
    /// Hot-path; called per gate input from `exec_fused_gate` on
    /// gate-level netlists (>1 billion calls on picorv32 test_synth).
    /// Marked `#[inline(always)]` so the Inline arm collapses to two
    /// shifts and a small match in the caller's frame.
    #[inline(always)]
    pub fn get_bit(&self, i: usize) -> LogicBit {
        // Compare in `usize`: `i as u32` TRUNCATES, so a 64-bit index whose low
        // 32 bits happen to be small (what a negative part-select base becomes
        // after wrapping — `w[-4 +: 8]`) slipped past the range guard and
        // panicked on the shift below. Widening `self.width` instead of
        // narrowing `i` costs nothing on this hot path.
        if i >= self.width as usize {
            // §5.7.1: a fill value replicates its bit into any wider context.
            if self.is_fill {
                return self.get_bit(0);
            }
            return LogicBit::Zero;
        }
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
            ValueStorage::Wide(bits) => bits.get(i),
        }
    }

    /// Hot 4-state bit accessor returning compact codes:
    /// 0=0, 1=1, 2=X, 3=Z. This avoids constructing/matching `LogicBit`
    /// in fused gate simulation.
    #[inline(always)]
    pub fn get_bit_code(&self, i: usize) -> u8 {
        if i >= self.width as usize {
            if self.is_fill {
                return self.get_bit_code(0);
            }
            return 0;
        }
        match &self.storage {
            ValueStorage::Inline { val_bits, xz_bits } => {
                (((*xz_bits >> i) & 1) << 1 | ((*val_bits >> i) & 1)) as u8
            }
            ValueStorage::Wide(bits) => match bits.get(i) {
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
        if i >= self.width as usize { return false; }
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
                if i >= bits.len() as usize {
                    return false;
                }
                if bits.get(i) == bit {
                    return false;
                }
                bits.set(i, bit);
                true
            }
        }
    }

    /// Set bit at position i. Hot-path mirror of `get_bit`; same
    /// rationale for `#[inline(always)]`.
    #[inline(always)]
    pub fn set_bit(&mut self, i: usize, bit: LogicBit) {
        if i >= self.width as usize { return; }
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
                if i < bits.len() as usize {
                    bits.set(i, bit);
                }
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
                let (v, x) = bits.raw_bits_low64();
                Some(v & !x)
            }
        }
    }

    /// Convert to i64 (sign-extended if is_signed).
    #[inline]
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
    ///
    /// Split into an `#[inline]` head and an out-of-line tail. The head covers
    /// everything an inline (≤64-bit) value can hit — the same-width no-op and
    /// the truncate/extend mask — as straight-line register work with no heap
    /// traffic; `Wide` storage, reals, fills and `target == 0` go to
    /// `resize_slow`, whose body is unchanged. Previously the whole function
    /// (including the `Vec`-building generic arm) was one unannotated
    /// `pub fn`, i.e. a cross-crate call for every resize.
    #[inline]
    pub fn resize(&self, target: u32) -> Value {
        if !self.is_fill && !self.is_real && target != 0 {
            if target == self.width {
                return self.clone();
            }
            if let ValueStorage::Inline { val_bits, xz_bits } = self.storage {
                if target <= 64 {
                    let mask = Self::mask(target);
                    if target < self.width {
                        // Truncate
                        return Value {
                            storage: ValueStorage::Inline {
                                val_bits: val_bits & mask,
                                xz_bits: xz_bits & mask,
                            },
                            width: target, is_signed: self.is_signed, is_real: false, is_fill: false,
                        };
                    }
                    // Widen: sign-extend only for a signed source whose MSB is
                    // a KNOWN 1 (an X/Z MSB does not replicate here — that is
                    // `resize_for_assign`'s job).
                    let mut v = val_bits;
                    if self.is_signed
                        && self.width > 0
                        && self.width <= 64
                        && (xz_bits >> (self.width - 1)) & 1 == 0
                        && (val_bits >> (self.width - 1)) & 1 == 1
                    {
                        v |= mask & !Self::mask(self.width);
                    }
                    return Value {
                        storage: ValueStorage::Inline { val_bits: v, xz_bits },
                        width: target, is_signed: self.is_signed, is_real: false, is_fill: false,
                    };
                }
            }
        }
        self.resize_slow(target)
    }

    #[inline(never)]
    fn resize_slow(&self, target: u32) -> Value {
        if self.is_fill {
            // §5.7.1: an unbased-unsized literal replicates into the target.
            return self.fill_at(target);
        }
        if target == 0 { return Value::zero(0); }
        if self.is_real {
            if target == 64 { return self.clone(); }
            // convert the real value to an integer (rounding to nearest,
            // ties away from zero). Cast via i64 so a negative real keeps its
            // two's-complement low bits — a direct `as u64` saturates any
            // negative value to 0 (§10.7 real→integral, e.g. -7.0 -> 4'd9).
            let f = self.to_f64();
            if !f.is_finite() {
                return Value::zero(target);
            }
            return Value::from_u64(f.round() as i64 as u64, target);
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
                        width: target, is_signed: self.is_signed, is_real: false, is_fill: false,
                    }
                } else {
                    // Widen
                    if self.is_signed && self.width > 0 {
                        let sign_bit = if self.width <= 64 { (*xz_bits >> (self.width - 1)) & 1 == 0 && (*val_bits >> (self.width - 1)) & 1 == 1 } else { false };
                        if sign_bit {
                            let ext_mask = mask & !Self::mask(self.width);
                            Value {
                                storage: ValueStorage::Inline { val_bits: *val_bits | ext_mask, xz_bits: *xz_bits },
                                width: target, is_signed: self.is_signed, is_real: false, is_fill: false,
                            }
                        } else {
                            Value {
                                storage: ValueStorage::Inline { val_bits: *val_bits, xz_bits: *xz_bits },
                                width: target, is_signed: self.is_signed, is_real: false, is_fill: false,
                            }
                        }
                    } else {
                        Value {
                            storage: ValueStorage::Inline { val_bits: *val_bits, xz_bits: *xz_bits },
                            width: target, is_signed: self.is_signed, is_real: false, is_fill: false,
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
                        ValueStorage::Wide(Box::new(PackedBits::new_fill(target, fill)))
                    }, width: target, is_signed: self.is_signed , is_real: false, is_fill: false }
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

    #[inline]
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
    #[inline]
    pub fn resize_for_assign(&self, target: u32) -> Value {
        if self.is_fill {
            // §5.7.1: an unbased-unsized literal replicates into the target.
            return self.fill_at(target);
        }
        if target == self.width || self.width == 0 || self.is_real {
            return self.resize(target);
        }
        if target < self.width {
            return self.resize(target);
        }
        let msb = self.get_bit(self.width.saturating_sub(1) as usize);
        // §10.7: the RHS is padded to the LHS width using its OWN signedness.
        // Only a signed source replicates its MSB — and when that MSB is X or Z
        // the extension bits take X/Z. An unsigned source always zero-extends,
        // even when its MSB (or any lower bit) is X/Z.
        if !self.is_signed || (msb != LogicBit::X && msb != LogicBit::Z) {
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
                    width: target, is_signed: self.is_signed, is_real: false, is_fill: false,
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
    /// IEEE 1800-2017 §11.8.2 step 2: in a SIGNED expression every operand is
    /// converted to the expression's width by **sign** extension before the
    /// operation. `to_u64` zero-extends, which turns a narrow signed `-3` into
    /// 253 — so an 8-bit `parameter signed [7:0]` met a 32-bit literal as a
    /// positive number and `SP * 2` evaluated to 506 instead of -6 (likewise
    /// `SP - 1` → 252, `SP + 1` → 254). `div`/`mod` already sign-extended via
    /// `to_i64`, which is why only `+`/`-`/`*` were wrong.
    ///
    /// Equal-width operands are untouched: two's-complement add/sub/mul are
    /// sign-agnostic at a fixed width, so this changes only the mixed-width
    /// signed case.
    #[inline]
    fn operand_bits_u64(&self, signed_expr: bool, w: u32) -> u64 {
        if signed_expr && self.width < w && self.width < 64 {
            self.to_i64().unwrap_or(0) as u64
        } else {
            self.to_u64().unwrap_or(0)
        }
    }

    #[inline]
    fn operand_bits_u128(&self, signed_expr: bool, w: u32) -> u128 {
        if signed_expr && self.width < w && self.width < 64 {
            self.to_i64().unwrap_or(0) as i128 as u128
        } else {
            self.to_u128()
        }
    }

    /// `#[inline]` (like `sub`, which already had it): with `lto = false` the
    /// unannotated version was a cross-crate call whose whole ≤64-bit body is
    /// ~10 instructions of register arithmetic once inlined.
    #[inline]
    pub fn add(&self, other: &Value) -> Value {
        if let Some((a, b)) = self.fill_pair(other) {
            return a.add(&b);
        }
        if self.is_real || other.is_real {
            return Value::from_f64(self.to_f64() + other.to_f64());
        }
        if self.has_xz() || other.has_xz() {
            return Value::new(self.width.max(other.width));
        }
        let w = self.width.max(other.width);
        let result_signed = self.is_signed && other.is_signed;
        let mut v = if w <= 64 {
            let a = self.operand_bits_u64(result_signed, w);
            let b = other.operand_bits_u64(result_signed, w);
            Value::from_u64(a.wrapping_add(b), w)
        } else {
            let a = self.operand_bits_u128(result_signed, w);
            let b = other.operand_bits_u128(result_signed, w);
            Value::from_u128(a.wrapping_add(b), w)
        };
        v.is_signed = result_signed;
        v
    }

    #[inline]
    pub fn sub(&self, other: &Value) -> Value {
        if let Some((a, b)) = self.fill_pair(other) {
            return a.sub(&b);
        }
        if self.is_real || other.is_real {
            return Value::from_f64(self.to_f64() - other.to_f64());
        }
        if self.has_xz() || other.has_xz() {
            return Value::new(self.width.max(other.width));
        }
        let w = self.width.max(other.width);
        let result_signed = self.is_signed && other.is_signed;
        let mut v = if w <= 64 {
            let a = self.operand_bits_u64(result_signed, w);
            let b = other.operand_bits_u64(result_signed, w);
            Value::from_u64(a.wrapping_sub(b), w)
        } else {
            let a = self.operand_bits_u128(result_signed, w);
            let b = other.operand_bits_u128(result_signed, w);
            Value::from_u128(a.wrapping_sub(b), w)
        };
        v.is_signed = result_signed;
        v
    }

    #[inline]
    pub fn mul(&self, other: &Value) -> Value {
        if let Some((a, b)) = self.fill_pair(other) {
            return a.mul(&b);
        }
        if self.is_real || other.is_real {
            return Value::from_f64(self.to_f64() * other.to_f64());
        }
        if self.has_xz() || other.has_xz() { return Value::new(self.width.max(other.width)); }
        let w = self.width.max(other.width);
        let result_signed = self.is_signed && other.is_signed;
        let mut v = if w <= 64 {
            let a = self.operand_bits_u64(result_signed, w);
            let b = other.operand_bits_u64(result_signed, w);
            Value::from_u64(a.wrapping_mul(b), w)
        } else {
            let a = self.operand_bits_u128(result_signed, w);
            let b = other.operand_bits_u128(result_signed, w);
            Value::from_u128(a.wrapping_mul(b), w)
        };
        v.is_signed = result_signed;
        v
    }

    pub fn div(&self, other: &Value) -> Value {
        if let Some((a, b)) = self.fill_pair(other) {
            return a.div(&b);
        }
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
            // §11.6.1: signed only when BOTH operands are signed — the WIDE
            // path ignored signedness entirely, so a 128-bit `-5 / 3` divided
            // the raw two's-complement pattern and returned a huge positive
            // number.
            if self.is_signed && other.is_signed {
                let sa = Self::i128_at_width(a, self.width);
                let sb = Self::i128_at_width(b, other.width);
                if sb == 0 { return Value::new(w); }
                let q = sa.wrapping_div(sb);
                let mut r = Value::from_u128(q as u128, w);
                r.is_signed = true;
                return r;
            }
            Value::from_u128(a / b, w)
        }
    }

    /// Sign-extend a `width`-bit pattern to i128 (width capped at 128).
    #[inline]
    fn i128_at_width(raw: u128, width: u32) -> i128 {
        if width == 0 || width >= 128 {
            return raw as i128;
        }
        let sign = 1u128 << (width - 1);
        if raw & sign != 0 {
            (raw | (!0u128 << width)) as i128
        } else {
            raw as i128
        }
    }

    pub fn modulo(&self, other: &Value) -> Value {
        if let Some((a, b)) = self.fill_pair(other) {
            return a.modulo(&b);
        }
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
            // §11.6.1: signed remainder in the wide path too (sign follows
            // the FIRST operand, as in the 64-bit arm).
            if self.is_signed && other.is_signed {
                let sa = Self::i128_at_width(a, self.width);
                let sb = Self::i128_at_width(b, other.width);
                if sb == 0 { return Value::new(w); }
                let q = sa.wrapping_rem(sb);
                let mut r = Value::from_u128(q as u128, w);
                r.is_signed = true;
                return r;
            }
            Value::from_u128(a % b, w)
        }
    }

    pub fn power(&self, other: &Value) -> Value {
        if self.is_real || other.is_real {
            return Value::from_f64(self.to_f64().powf(other.to_f64()));
        }
        if self.has_xz() || other.has_xz() { return Value::new(self.width); }
        // §11.8.1: the result of `**` is signed iff BOTH operands are signed.
        // (Without this the two's-complement bits are right but the result reads
        // as unsigned — `(-2)**3` prints 4294967288 instead of -8.)
        let result_signed = self.is_signed && other.is_signed;
        // §11.4.3: a negative integer exponent yields 0 for |base|>1, and 1 or
        // -1 for base == 1 / -1 — not a huge unsigned loop count. Detect it via
        // the signed operand rather than the wrapped u64.
        let neg_exp = other.is_signed && other.to_i64().unwrap_or(0) < 0;
        let result: u64 = if neg_exp {
            match self.to_i64().unwrap_or(0) {
                1 => 1,
                // base -1: 1 for even exp, all-ones (-1 in the result width) for odd
                -1 => if other.to_i64().unwrap_or(0) % 2 == 0 { 1 } else { u64::MAX },
                _ => 0,
            }
        } else {
            // Accumulate in u128 so a WIDE result survives — `2**100` on a
            // 128-bit operand computed in u64 wrapped to 0. The iteration cap
            // grows with the width (an even base saturates to 0 well before
            // it; an odd base cycles, and real designs don't raise to
            // astronomic exponents).
            let base = self.to_u128();
            let exp = other.to_u64().unwrap_or(0);
            let mut r: u128 = 1;
            for _ in 0..exp.min(4096) {
                r = r.wrapping_mul(base);
                if r == 0 {
                    break;
                }
            }
            let mut v = Value::from_u128(r, self.width);
            v.is_signed = result_signed;
            return v;
        };
        let mut v = Value::from_u64(result, self.width);
        v.is_signed = result_signed;
        v
    }

    // === Bitwise ===

    #[inline]
    pub fn bitwise_and(&self, other: &Value) -> Value {
        if let Some((a, b)) = self.fill_pair(other) {
            return a.bitwise_and(&b);
        }
        let w = self.width.max(other.width);
        match (&self.storage, &other.storage) {
            (ValueStorage::Inline { val_bits: av, xz_bits: ax }, ValueStorage::Inline { val_bits: bv, xz_bits: bx }) => {
                if *ax == 0 && *bx == 0 {
                    // Fast path: no X/Z
                    Value { storage: ValueStorage::Inline { val_bits: av & bv, xz_bits: 0 }, width: w, is_signed: false, is_real: false, is_fill: false }
                } else {
                    // X propagation for AND: 0 & X = 0, 1 & X = X
                    let any_xz = ax | bx;
                    let result_val = av & bv & !any_xz;
                    let result_xz = any_xz & !((!av & !ax) | (!bv & !bx)); // known 0 kills X
                    Value { storage: ValueStorage::Inline { val_bits: result_val, xz_bits: result_xz & Self::mask(w) }, width: w, is_signed: false, is_real: false, is_fill: false }
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
        if let Some((a, b)) = self.fill_pair(other) {
            return a.bitwise_or(&b);
        }
        let w = self.width.max(other.width);
        match (&self.storage, &other.storage) {
            (ValueStorage::Inline { val_bits: av, xz_bits: ax }, ValueStorage::Inline { val_bits: bv, xz_bits: bx }) => {
                if *ax == 0 && *bx == 0 {
                    Value { storage: ValueStorage::Inline { val_bits: av | bv, xz_bits: 0 }, width: w, is_signed: false, is_real: false, is_fill: false }
                } else {
                    let any_xz = ax | bx;
                    let result_val = (av | bv) & !any_xz;
                    let result_xz = any_xz & !((av & !ax) | (bv & !bx)); // known 1 kills X
                    Value { storage: ValueStorage::Inline { val_bits: result_val | ((av & !ax) | (bv & !bx)), xz_bits: result_xz & Self::mask(w) }, width: w, is_signed: false, is_real: false, is_fill: false }
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
        if let Some((a, b)) = self.fill_pair(other) {
            return a.bitwise_xor(&b);
        }
        let w = self.width.max(other.width);
        match (&self.storage, &other.storage) {
            (ValueStorage::Inline { val_bits: av, xz_bits: ax }, ValueStorage::Inline { val_bits: bv, xz_bits: bx }) => {
                let any_xz = ax | bx;
                let result_val = (av ^ bv) & !any_xz;
                Value { storage: ValueStorage::Inline { val_bits: result_val, xz_bits: any_xz & Self::mask(w) }, width: w, is_signed: false, is_real: false, is_fill: false }
            }
            _ => self.bitwise_op_slow(other, |a, b| match (a, b) {
                (LogicBit::Zero, LogicBit::Zero) | (LogicBit::One, LogicBit::One) => LogicBit::Zero,
                (LogicBit::Zero, LogicBit::One) | (LogicBit::One, LogicBit::Zero) => LogicBit::One,
                _ => LogicBit::X,
            }),
        }
    }

    #[inline]
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
                    width: self.width, is_signed: self.is_signed, is_real: false, is_fill: false,
                }
            }
            ValueStorage::Wide(bits) => {
                let mut nb = bits.clone();
                nb.transform(|b| match b {
                    LogicBit::Zero => LogicBit::One,
                    LogicBit::One => LogicBit::Zero,
                    _ => LogicBit::X,
                });
                Value {
                    storage: ValueStorage::Wide(nb),
                    width: self.width,
                    is_signed: self.is_signed,
                    is_real: false,
                    is_fill: false,
                }
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
    #[inline]
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
                    width: w, is_signed: self.is_signed && other.is_signed, is_real: false, is_fill: false,
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
                    width: self.width, is_signed: self.is_signed, is_real: false, is_fill: false,
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
                    width: self.width, is_signed: self.is_signed, is_real: false, is_fill: false,
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

    /// IEEE 1800-2017 §11.4.10: `>>>` fills with the sign bit ONLY when the left
    /// operand is signed. On an unsigned operand it is a plain logical shift —
    /// filling with the MSB there silently corrupts the high bits.
    #[inline]
    pub fn arith_shift_right(&self, amount: &Value) -> Value {
        if !self.is_signed {
            return self.shift_right(amount);
        }
        let amt = amount.to_u64().unwrap_or(0) as u32;
        if amount.has_xz() { return Value::new(self.width); }
        let sign = self.get_bit(self.width.saturating_sub(1) as usize);
        match &self.storage {
            ValueStorage::Inline { val_bits, xz_bits } => {
                if amt >= self.width {
                    return if sign == LogicBit::One {
                        let mask = Self::mask(self.width);
                        Value { storage: ValueStorage::Inline { val_bits: mask, xz_bits: 0 }, width: self.width, is_signed: true , is_real: false, is_fill: false }
                    } else { Value::zero(self.width) };
                }
                let shifted_val = val_bits >> amt;
                let shifted_xz = xz_bits >> amt;
                if sign == LogicBit::One && self.width > 0 {
                    let mask = Self::mask(self.width);
                    let ext = mask & !Self::mask(self.width - amt);
                    Value {
                        storage: ValueStorage::Inline { val_bits: shifted_val | ext, xz_bits: shifted_xz },
                        width: self.width, is_signed: true, is_real: false, is_fill: false,
                    }
                } else {
                    Value {
                        storage: ValueStorage::Inline { val_bits: shifted_val, xz_bits: shifted_xz },
                        width: self.width, is_signed: self.is_signed, is_real: false, is_fill: false,
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
        if let Some((a, b)) = self.fill_pair(other) {
            return a.is_equal(&b);
        }
        if self.is_real || other.is_real {
            return Value::from_u64((self.to_f64() == other.to_f64()) as u64, 1);
        }
        if self.has_xz() || other.has_xz() {
            // IEEE 1800: == returns X only when ambiguous.
            // If any position has both bits known and they differ -> 0.
            let w = self.width.max(other.width) as usize;
            // Two zero-width values (e.g. empty strings) are always equal
            // regardless of internal X/Z bits in the storage.  Class-property
            // string fields may have spurious X bits after allocation even
            // when logically empty (width 0).
            if w == 0 {
                return Value::from_u64(1, 1);
            }
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

    #[inline(always)]
    pub fn case_eq(&self, other: &Value) -> Value {
        // Nearly every dynamic case comparison in RTL is an inline value.
        // Compare its packed 4-state encoding a word at a time instead of
        // dispatching get_bit() for every bit. Preserve the LRM's signed
        // extension rule, including replication of an X/Z sign bit.
        if !self.is_fill && !other.is_fill {
            if let (Some((mut av, mut ax)), Some((mut bv, mut bx))) =
                (self.inline_bits(), other.inline_bits())
            {
                let w = self.width.max(other.width);
                let mask = Self::mask(w);
                if self.is_signed && other.is_signed {
                    if self.width > 0 && self.width < w {
                        let ext = mask & !Self::mask(self.width);
                        let sign = 1u64 << (self.width - 1);
                        if av & sign != 0 {
                            av |= ext;
                        }
                        if ax & sign != 0 {
                            ax |= ext;
                        }
                    }
                    if other.width > 0 && other.width < w {
                        let ext = mask & !Self::mask(other.width);
                        let sign = 1u64 << (other.width - 1);
                        if bv & sign != 0 {
                            bv |= ext;
                        }
                        if bx & sign != 0 {
                            bx |= ext;
                        }
                    }
                }
                let equal = (av & mask) == (bv & mask) && (ax & mask) == (bx & mask);
                return Value::from_u64(equal as u64, 1);
            }
        }
        self.case_eq_slow(other)
    }

    #[cold]
    #[inline(never)]
    fn case_eq_slow(&self, other: &Value) -> Value {
        if let Some((a, b)) = self.fill_pair(other) {
            return a.case_eq(&b);
        }
        // === operator: compares including X/Z. §11.4.5/§11.6.1: operands of
        // unequal size are extended to the common width; the comparison is
        // signed (MSB-replicated, including an X/Z MSB) only when BOTH operands
        // are signed, otherwise zero-extended. Without this a 64-bit signed
        // value compared to a 32-bit signed `-16` mismatched in the top 32 bits.
        let w = self.width.max(other.width) as usize;
        let both_signed = self.is_signed && other.is_signed;
        let sign_a = both_signed && (self.width as usize) < w;
        let sign_b = both_signed && (other.width as usize) < w;
        let top_a = if self.width > 0 { self.get_bit((self.width - 1) as usize) } else { LogicBit::Zero };
        let top_b = if other.width > 0 { other.get_bit((other.width - 1) as usize) } else { LogicBit::Zero };
        for i in 0..w {
            let a = if i < self.width as usize { self.get_bit(i) } else if sign_a { top_a } else { LogicBit::Zero };
            let b = if i < other.width as usize { other.get_bit(i) } else if sign_b { top_b } else { LogicBit::Zero };
            if a != b { return Value::from_u64(0, 1); }
        }
        Value::from_u64(1, 1)
    }

    #[inline]
    pub fn case_neq(&self, other: &Value) -> Value {
        let eq = self.case_eq(other);
        if eq.to_u64() == Some(1) { Value::from_u64(0, 1) } else { Value::from_u64(1, 1) }
    }

    /// casez wildcard equality (IEEE 1800 §12.5.1): Z bits (also written
    /// `?` in literals — both lex to LogicBit::Z) on either side are
    /// treated as don't-care positions and always match.
    pub fn casez_eq(&self, other: &Value) -> Value {
        if let Some((a, b)) = self.fill_pair(other) {
            return a.casez_eq(&b);
        }
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
        if let Some((a, b)) = self.fill_pair(other) {
            return a.casex_eq(&b);
        }
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
        if let Some((a, b)) = self.fill_pair(other) {
            return a.less_than(&b);
        }
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
        if let Some((a, b)) = self.fill_pair(other) {
            return a.less_equal(&b);
        }
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

    /// `#[inline]` on the logic operators and on `is_nonzero`: with
    /// `lto = false` a `logic_and` in the VM was three cross-crate calls
    /// (`logic_and` + two `is_nonzero`) for what is, on inline storage,
    /// four ALU ops per operand.
    #[inline]
    pub fn logic_and(&self, other: &Value) -> Value {
        let a = self.is_nonzero();
        let b = other.is_nonzero();
        match (a, b) {
            (Some(true), Some(true)) => Value::from_u64(1, 1),
            (Some(false), _) | (_, Some(false)) => Value::from_u64(0, 1),
            _ => Value::new(1),
        }
    }

    #[inline]
    pub fn logic_or(&self, other: &Value) -> Value {
        let a = self.is_nonzero();
        let b = other.is_nonzero();
        match (a, b) {
            (Some(true), _) | (_, Some(true)) => Value::from_u64(1, 1),
            (Some(false), Some(false)) => Value::from_u64(0, 1),
            _ => Value::new(1),
        }
    }

    #[inline]
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
    #[inline]
    pub fn is_nonzero(&self) -> Option<bool> {
        if self.is_real {
            return Some(self.to_f64() != 0.0);
        }
        // Matches a reference simulator's reduce-to-bool (NetEBLogic, eval_tree.cc):
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
                if bits.iter().any(|b| b == LogicBit::One) { Some(true) }
                else if bits.has_xz() { None }
                else { Some(false) }
            }
        }
    }

    // === Reduction ===

    #[inline]
    pub fn reduce_and(&self) -> Value {
        // §11.4.8 (Table 11-13): a known 0 bit forces the result to 0 even in
        // the presence of X/Z. Only when NO bit is 0 does an X/Z make the
        // result X; all-ones gives 1. (Previously an X/Z short-circuited to X
        // before the 0-check, so `&4'b1x0z` wrongly gave x instead of 0.)
        match &self.storage {
            ValueStorage::Inline { val_bits, xz_bits } => {
                let mask = Self::mask(self.width);
                // A bit is a known 0 when both its value and xz bits are clear.
                if (!*val_bits & !*xz_bits & mask) != 0 { Value::from_u64(0, 1) }
                else if *xz_bits & mask != 0 { Value::new(1) }
                else { Value::from_u64(1, 1) }
            }
            ValueStorage::Wide(bits) => {
                if bits.iter().any(|b| b == LogicBit::Zero) { Value::from_u64(0, 1) }
                else if bits.iter().any(|b| !b.is_known()) { Value::new(1) }
                else { Value::from_u64(1, 1) }
            }
        }
    }

    #[inline]
    pub fn reduce_or(&self) -> Value {
        match &self.storage {
            ValueStorage::Inline { val_bits, xz_bits } => {
                let mask = Self::mask(self.width);
                if (*val_bits & !xz_bits & mask) != 0 { Value::from_u64(1, 1) }
                else if *xz_bits & mask != 0 { Value::new(1) }
                else { Value::from_u64(0, 1) }
            }
            ValueStorage::Wide(bits) => {
                if bits.iter().any(|b| b == LogicBit::One) { Value::from_u64(1, 1) }
                else if bits.iter().any(|b| !b.is_known()) { Value::new(1) }
                else { Value::from_u64(0, 1) }
            }
        }
    }

    #[inline]
    pub fn reduce_xor(&self) -> Value {
        if self.has_xz() { return Value::new(1); }
        let v = self.to_u64().unwrap_or(0);
        Value::from_u64(v.count_ones() as u64 % 2, 1)
    }

    // === Concatenation ===

    /// `#[inline]`: `concat_refs` is generic (so it is codegen'd in the calling
    /// crate) but this wrapper was not, which made every `Value::concat(&parts)`
    /// in the VM a cross-crate call into `xezim-core` that then called the
    /// monomorphised `concat_refs` again.
    #[inline]
    pub fn concat(values: &[Value]) -> Value {
        Self::concat_refs(values.iter())
    }

    /// Concatenate borrowed values without forcing callers to clone them into
    /// a temporary slice. `values[0]` is the leftmost (MSB) operand.
    pub fn concat_refs<'a, I>(values: I) -> Value
    where
        I: DoubleEndedIterator<Item = &'a Value> + Clone,
    {
        let total_width: u32 = values.clone().map(|v| v.width).sum();
        if total_width <= 64 {
            let mut out_v = 0u64;
            let mut out_x = 0u64;
            let mut offset = 0u32;
            for val in values.rev() {
                if val.width == 0 {
                    continue;
                }
                let (v, x) = val.raw_bits();
                let mask = Self::mask(val.width);
                out_v |= (v & mask) << offset;
                out_x |= (x & mask) << offset;
                offset += val.width;
            }
            return Value {
                storage: ValueStorage::Inline {
                    val_bits: out_v,
                    xz_bits: out_x,
                },
                width: total_width,
                is_signed: false,
                is_real: false, is_fill: false,
            };
        }

        // Wide result. Build the packed bit vector ONCE by appending each
        // operand's bits LSB-first, instead of allocating a zero-filled
        // `Value::zero(total_width)` and then driving `set_bit` (bounds check +
        // storage `match` + read-modify-write) for every one of
        // `total_width` bits. An inline operand is unpacked straight from its
        // two words.
        //
        // `Value::zero` capped its width at `MAX_WIDTH` and silently dropped
        // the `set_bit`s past the cap, so `capped` reproduces that exactly.
        let capped = Self::cap_width(total_width);
        let capped_len = capped as usize;
        let mut pb = PackedBits::new();
        for val in values.rev() {
            let room = capped_len - pb.len() as usize;
            if room == 0 {
                break;
            }
            let take = (val.width as usize).min(room);
            match &val.storage {
                ValueStorage::Wide(bits) => {
                    let n = take.min(bits.len() as usize);
                    for i in 0..n {
                        pb.push(bits.get(i));
                    }
                    // A short `Wide` buffer reads as 0 past its end, matching
                    // `get_bit`'s `unwrap_or(LogicBit::Zero)`.
                    for _ in n..take {
                        pb.push(LogicBit::Zero);
                    }
                }
                ValueStorage::Inline { val_bits, xz_bits } => {
                    for i in 0..take {
                        pb.push(if i < 64 {
                            LogicBit::from_code(
                                ((((*xz_bits >> i) & 1) << 1) | ((*val_bits >> i) & 1)) as u8,
                            )
                        } else {
                            // Inline storage declared wider than 64 bits: keep
                            // the pre-existing `get_bit` behaviour verbatim.
                            val.get_bit(i)
                        });
                    }
                }
            }
        }
        while pb.len() < capped {
            pb.push(LogicBit::Zero);
        }
        Value {
            storage: ValueStorage::Wide(Box::new(pb)),
            width: capped,
            is_signed: false,
            is_real: false, is_fill: false,
        }
    }

    /// Format as hex string.
    pub fn to_hex(&self) -> String {
        if self.width == 0 { return "0".into(); }
        let ndigits = self.width.div_ceil(4) as usize;
        let mut s = String::with_capacity(ndigits);
        for d in (0..ndigits).rev() {
            // §21.2.1.2 unknown casing, per hex digit (matches reference/commercial
            // tools): a nibble that is entirely x prints `x`, entirely z prints
            // `z`, and one that MIXES unknown bits with known bits (or x with z)
            // prints uppercase `X` (any x) or `Z` (some z, no x). Only a fully
            // known nibble is a hex digit. The old code collapsed every unknown
            // nibble to lowercase `x`, losing z and mis-casing partials.
            let mut digit = 0u8;
            let (mut n_x, mut n_z, mut n_bits) = (0u32, 0u32, 0u32);
            for b in 0..4 {
                let bit_idx = d * 4 + b;
                if bit_idx >= self.width as usize {
                    continue;
                }
                n_bits += 1;
                match self.get_bit(bit_idx) {
                    LogicBit::One => digit |= 1 << b,
                    LogicBit::X => n_x += 1,
                    LogicBit::Z => n_z += 1,
                    _ => {}
                }
            }
            let ch = if n_x == 0 && n_z == 0 {
                char::from_digit(digit as u32, 16).unwrap()
            } else if n_x == n_bits {
                'x'
            } else if n_z == n_bits {
                'z'
            } else if n_x > 0 {
                'X'
            } else {
                'Z'
            };
            s.push(ch);
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
    fn concat_refs_preserves_order_and_unknown_bits() {
        let a = Value::from_str_radix("10xz", 2, 4);
        let b = Value::from_str_radix("0110", 2, 4);
        let parts = [&a, &b];
        let result = Value::concat_refs(parts.into_iter());
        assert_eq!(result.width, 8);
        assert_eq!(result.to_bin(), "10xz0110");

        let wide_a = Value::from_str_radix(&"1".repeat(65), 2, 65);
        let wide_b = Value::from_u64(2, 2);
        let wide_parts = [&wide_a, &wide_b];
        let wide_result = Value::concat_refs(wide_parts.into_iter());
        assert_eq!(wide_result.width, 67);
        assert_eq!(wide_result.get_bit(0), LogicBit::Zero);
        assert_eq!(wide_result.get_bit(1), LogicBit::One);
        assert!((2..67).all(|bit| wide_result.get_bit(bit) == LogicBit::One));
    }

    #[test]
    fn test_shifts() {
        let v = Value::from_u64(0x0F, 8);
        assert_eq!(v.shift_left(&Value::from_u64(4, 8)).to_u64(), Some(0xF0));
        assert_eq!(v.shift_right(&Value::from_u64(2, 8)).to_u64(), Some(3));
    }

    /// Build the `code`-th 4-state pattern of `width` bits (2 bits per
    /// position: 0=0, 1=1, 2=x, 3=z) for exhaustive differential testing.
    fn four_state(mut code: usize, width: u32, signed: bool) -> Value {
        let mut v = Value::zero(width);
        v.is_signed = signed;
        for i in 0..width as usize {
            v.set_bit(i, LogicBit::from_code((code & 3) as u8));
            code >>= 2;
        }
        v
    }

    // `range_select`/`bit_select` grew shift+mask fast paths for inline
    // storage. `range_select_signed` is the untouched per-bit reference for
    // exactly the same §11.5.1 rule (source bits outside `0..width` read x),
    // so the two must agree bit-for-bit on every 4-state input — in range,
    // partially overhanging, and entirely out of range.
    #[test]
    fn range_and_bit_select_match_per_bit_reference() {
        for width in 1u32..=5 {
            for code in 0..(1usize << (2 * width)) {
                for signed in [false, true] {
                    let v = four_state(code, width, signed);
                    for left in 0..9usize {
                        for right in 0..9usize {
                            let got = v.range_select(left, right);
                            let want = v.range_select_signed(
                                left.max(right) as i64,
                                left.min(right) as i64,
                            );
                            assert_eq!(
                                got, want,
                                "range_select({left},{right}) on {v} (signed={signed})"
                            );
                        }
                    }
                    for i in 0..9usize {
                        let got = v.bit_select(i);
                        let want = if i < width as usize {
                            let mut b = Value::zero(1);
                            b.set_bit(0, v.get_bit(i));
                            b
                        } else {
                            Value::new(1)
                        };
                        assert_eq!(got, want, "bit_select({i}) on {v}");
                    }
                }
            }
        }
    }

    // `resize` grew an inline fast path. Reference: copy the low bits, pad
    // with the sign bit only when the source is signed AND its MSB is a known
    // 1 (an x/z MSB pads with 0 — `resize_for_assign` is what replicates it).
    #[test]
    fn resize_matches_per_bit_reference() {
        for width in 1u32..=4 {
            for code in 0..(1usize << (2 * width)) {
                for signed in [false, true] {
                    let v = four_state(code, width, signed);
                    for target in 1u32..=7 {
                        let got = v.resize(target);
                        let mut want = Value::zero(target);
                        want.is_signed = signed;
                        let msb = v.get_bit((width - 1) as usize);
                        let pad = if signed && msb == LogicBit::One {
                            LogicBit::One
                        } else {
                            LogicBit::Zero
                        };
                        for i in 0..target as usize {
                            want.set_bit(
                                i,
                                if i < width as usize { v.get_bit(i) } else { pad },
                            );
                        }
                        assert_eq!(got, want, "resize({target}) on {v} (signed={signed})");
                    }
                }
            }
        }
    }

    // `concat_refs`' >64-bit arm now appends into one pre-sized `Vec` instead
    // of driving `set_bit` over a zero-filled value. `values[0]` is the MSB
    // operand, so the result reads back as the operands' bits concatenated.
    #[test]
    fn wide_concat_matches_per_bit_reference() {
        let a = Value::from_str_radix(&"10xz".repeat(10), 2, 40); // inline, 40 bits
        let b = Value::from_str_radix(&"1x0z".repeat(18), 2, 72); // wide, 72 bits
        let c = four_state(0b11_10_01_00, 4, false);
        let parts = [a.clone(), b.clone(), c.clone()];
        let got = Value::concat(&parts);
        assert_eq!(got.width, 40 + 72 + 4);
        // Expected bit i, LSB-first: c, then b, then a.
        for i in 0..4usize {
            assert_eq!(got.get_bit(i), c.get_bit(i), "c bit {i}");
        }
        for i in 0..72usize {
            assert_eq!(got.get_bit(4 + i), b.get_bit(i), "b bit {i}");
        }
        for i in 0..40usize {
            assert_eq!(got.get_bit(76 + i), a.get_bit(i), "a bit {i}");
        }
        // A zero-width operand contributes nothing.
        let with_empty = Value::concat(&[a.clone(), Value::zero(0), b.clone(), c.clone()]);
        assert_eq!(with_empty, got);
    }

    // `Wide` equality is now compared a machine word at a time; it must still
    // detect a difference at ANY bit position, including the unaligned tail.
    #[test]
    fn wide_equality_detects_every_bit_position() {
        for width in [65u32, 70, 96, 128, 129, 200] {
            let base = Value::from_str_radix(&"1x0z".repeat(64), 2, width);
            assert_eq!(base, base.clone());
            for i in 0..width as usize {
                let mut other = base.clone();
                let flipped = match base.get_bit(i) {
                    LogicBit::Zero => LogicBit::One,
                    LogicBit::One => LogicBit::X,
                    LogicBit::X => LogicBit::Z,
                    LogicBit::Z => LogicBit::Zero,
                };
                other.set_bit(i, flipped);
                assert_ne!(base, other, "width {width}, bit {i}");
            }
            // Differing width or flags is a mismatch even with equal bits.
            let mut signed = base.clone();
            signed.is_signed = true;
            assert_ne!(base, signed);
            assert_ne!(base, base.resize(width + 8));
        }
    }

    // `copy_from`'s Wide→Wide arm takes a `copy_from_slice` shortcut when the
    // lengths already match; it must still handle a width change.
    #[test]
    fn copy_from_wide_handles_same_and_different_widths() {
        let src = Value::from_str_radix(&"1x0z".repeat(32), 2, 128);
        let mut dst = Value::zero(128);
        dst.copy_from(&src);
        assert_eq!(dst, src);
        let narrower = Value::from_str_radix(&"z1x0".repeat(20), 2, 80);
        dst.copy_from(&narrower);
        assert_eq!(dst, narrower);
        let wider = Value::ones(300);
        dst.copy_from(&wider);
        assert_eq!(dst, wider);
    }

    // Packed wide storage must keep the historical on-wire representation
    // (`u8` variant tag, then a Varint bit count, then one `LogicBit`
    // discriminant per bit). `-o` compile artifacts and design-cache files
    // written before packed storage rely on that byte layout.
    #[test]
    fn wide_serde_keeps_legacy_vec_wire_format() {
        use bincode::Options;
        let opts = crate::xez_bincode_options();
        let mut val = Value::zero(120);
        val.set_bit(0, LogicBit::One);
        val.set_bit(5, LogicBit::X);
        val.set_bit(119, LogicBit::Z);
        assert!(matches!(&val.storage, ValueStorage::Wide(_)));

        let bytes = opts.serialize(&val).unwrap();
        // Value = storage, then width (Varint), then three bools. Storage:
        // tag byte 1 (Wide), Varint count 120, then 120 LogicBit codes.
        assert_eq!(bytes[0], 1, "Wide variant tag");
        assert_eq!(bytes[1], 120, "Varint bit count (single byte < 128)");
        for i in 0..120usize {
            let want = match i {
                0 => 1,
                5 => 2,
                119 => 3,
                _ => 0,
            };
            assert_eq!(bytes[2 + i], want, "bit {} LogicBit code", i);
        }
    }

    // A wide value must survive a bincode round trip (artifacts + design cache).
    #[test]
    fn wide_serde_round_trip_preserves_bits() {
        use bincode::Options;
        let opts = crate::xez_bincode_options();
        let val = Value::from_str_radix(&"10xz".repeat(40), 2, 160);
        let bytes = opts.serialize(&val).unwrap();
        let back: Value = opts.deserialize(&bytes).unwrap();
        assert_eq!(back, val);
        assert_eq!(back.width, 160);
        for i in 0..160 {
            assert_eq!(back.get_bit(i), val.get_bit(i), "bit {}", i);
        }
    }

    // Exercise every rewritten Wide arm against a known 160-bit pattern, so a
    // packing bug cannot hide behind another packed path.
    #[test]
    fn wide_ops_are_bit_accurate() {
        let a = Value::from_str_radix(&"f0".repeat(20), 16, 160); // 0xF0F0…F0
        let b = Value::from_str_radix(&"0f".repeat(20), 16, 160); // 0x0F0F…0F
        assert_eq!(a.bitwise_and(&b), Value::zero(160));
        assert_eq!(a.bitwise_or(&b), Value::ones(160));
        assert_eq!(a.bitwise_xor(&b), Value::ones(160));
        assert_eq!(a.bitwise_not(), b);
        assert_eq!(b.bitwise_not(), a);

        // Reductions (Table 11-13 / 11-14 semantics).
        assert_eq!(a.reduce_and().to_u64(), Some(0), "0xF0… has zero nibbles");
        assert_eq!(b.reduce_or().to_u64(), Some(1), "0x0F… has one nibbles");
        assert_eq!(Value::ones(160).reduce_and().to_u64(), Some(1));
        assert_eq!(Value::zero(160).reduce_or().to_u64(), Some(0));

        // Part-select: Wide→Inline and Wide→Wide.
        assert_eq!(a.range_select(7, 0).to_u64(), Some(0xF0));
        assert_eq!(a.range_select(159, 152).to_u64(), Some(0xF0));
        assert_eq!(a.range_select(95, 64).to_u64(), Some(0xF0F0F0F0));
        assert_eq!(
            a.range_select(127, 64),
            Value::from_u64(0xF0F0F0F0F0F0F0F0, 64)
        );
        assert_eq!(a.range_select(159, 0), a);

        // Resize keeps the low bits; wide→inline at exactly 64.
        assert_eq!(a.resize(96).width, 96);
        assert_eq!(a.resize(96), a.range_select(95, 0));
        assert_eq!(a.resize(64), a.range_select(63, 0));

        // 2-state coercion drops X/Z, preserving known nibbles.
        let x = Value::from_str_radix(&"x".repeat(40), 16, 160);
        assert_eq!(x.to_two_state(), Value::zero(160));
        let mix = Value::from_str_radix(&"f0xz".repeat(10), 16, 160);
        let ts = mix.to_two_state();
        assert!(!ts.has_xz());
        assert_eq!(ts.range_select(15, 12).to_u64(), Some(0xF));
        assert_eq!(ts.range_select(11, 8).to_u64(), Some(0x0));
    }

    // Padding bits above `width` in the last packed byte (widths not a
    // multiple of 4, e.g. 66 bits → 17 bytes with 2 padding slots) must never
    // leak X/Z into has_xz/==/Hash. `new_fill` canonicalizes them to Zero.
    #[test]
    fn wide_padding_bits_are_canonical_zero() {
        let mut v = Value::new(66); // all-X, width not a multiple of 4
        for i in 0..66 {
            v.set_bit(i, LogicBit::Zero);
        }
        assert!(!v.has_xz(), "all-zero 66-bit value must have no X/Z");

        // Deserialize re-packs via `push` (padding left zero); it must equal
        // the canonical construction and round-trip unchanged.
        use bincode::Options;
        let opts = crate::xez_bincode_options();
        let back: Value = opts.deserialize(&opts.serialize(&v).unwrap()).unwrap();
        assert_eq!(back, v);

        // All-X 66-bit: has_xz true, and equality with itself is unaffected.
        let x = Value::new(66);
        assert!(x.has_xz());
        assert_eq!(x, x);
        // Clearing every live bit leaves padding zero too.
        let mut y = Value::new(66);
        for i in 0..66 {
            y.set_bit(i, LogicBit::Zero);
        }
        assert!(!y.has_xz());
    }

    // IEEE 1800-2017 §5.7.1: a single-`x` decimal literal is all-X and a
    // single-`z`/`?` decimal literal is all-Z (previously mis-rendered as
    // all-X). Higher radices are unaffected.
    #[test]
    fn test_decimal_single_x_z_render() {
        let dx = Value::from_str_radix("x", 10, 8);
        assert_eq!(dx.to_bin(), "xxxxxxxx", "8'dx must be all-X");
        for i in 0..8 { assert_eq!(dx.get_bit(i), LogicBit::X); }

        let dz = Value::from_str_radix("z", 10, 8);
        assert_eq!(dz.to_bin(), "zzzzzzzz", "8'dz must be all-Z, not all-X");
        for i in 0..8 { assert_eq!(dz.get_bit(i), LogicBit::Z); }

        let dq = Value::from_str_radix("?", 10, 8);
        for i in 0..8 { assert_eq!(dq.get_bit(i), LogicBit::Z, "8'd? is all-Z"); }

        // Sanity: hex x/z paths unchanged.
        assert_eq!(Value::from_str_radix("xx", 16, 8).to_bin(), "xxxxxxxx");
        assert_eq!(Value::from_str_radix("zz", 16, 8).to_bin(), "zzzzzzzz");
    }

    // §21.2.1.2 unknown-value casing for `%h` and `%d` (matches a reference simulator): an
    // all-x group prints lowercase `x`, all-z prints `z`, and a group MIXING
    // unknown with known bits (or x with z) prints uppercase `X`/`Z`. The old
    // code collapsed every unknown to lowercase `x`, losing z entirely.
    #[test]
    fn test_hex_dec_unknown_casing() {
        let h = |b: &str| Value::from_str_radix(b, 2, 8).to_hex();
        assert_eq!(h("1010xx01"), "aX", "partial-x nibble is uppercase X");
        assert_eq!(h("1010zz01"), "aZ", "partial-z nibble is uppercase Z");
        assert_eq!(h("xxxxxxxx"), "xx", "all-x nibble is lowercase x");
        assert_eq!(h("zzzzzzzz"), "zz", "all-z nibble is lowercase z (not x)");
        assert_eq!(h("1010xz01"), "aX", "x+z in one nibble favours X");
        assert_eq!(h("10101010"), "aa", "fully known nibble is a hex digit");

        let d = |b: &str| Value::from_str_radix(b, 2, 8).to_dec_string();
        assert_eq!(d("1010xx01"), "X", "partially-unknown %d is uppercase X");
        assert_eq!(d("xxxxxxxx"), "x", "all-x %d is lowercase x");
        assert_eq!(d("zzzzzzzz"), "z", "all-z %d is lowercase z (not x)");
    }

    #[test]
    fn test_x_propagation() {
        let x = Value::new(8); // all X
        let one = Value::from_u64(1, 8);
        assert!(x.add(&one).has_xz());
        assert!(x.is_equal(&one).has_xz());
    }

    #[test]
    fn case_eq_inline_preserves_four_state_extension() {
        let mut signed_x = Value::from_str_radix("x001", 2, 4);
        signed_x.is_signed = true;
        let mut extended_x = Value::from_str_radix("xxxxx001", 2, 8);
        extended_x.is_signed = true;
        assert!(signed_x.case_eq(&extended_x).is_true());

        let mut signed_z = Value::from_str_radix("z001", 2, 4);
        signed_z.is_signed = true;
        let mut extended_z = Value::from_str_radix("zzzzz001", 2, 8);
        extended_z.is_signed = true;
        assert!(signed_z.case_eq(&extended_z).is_true());

        let unsigned_x = Value::from_str_radix("x001", 2, 4);
        assert!(!unsigned_x.case_eq(&extended_x).is_true());
        assert!(Value::fill_of('z').case_eq(&Value::all_z(8)).is_true());
    }

    #[test]
    fn case_eq_inline_matches_bitwise_reference() {
        fn four_state_value(mut code: usize, width: u32, signed: bool) -> Value {
            let mut value = Value::zero(width);
            value.is_signed = signed;
            for bit_idx in 0..width as usize {
                let bit = match code & 3 {
                    0 => LogicBit::Zero,
                    1 => LogicBit::One,
                    2 => LogicBit::X,
                    _ => LogicBit::Z,
                };
                value.set_bit(bit_idx, bit);
                code >>= 2;
            }
            value
        }

        for left_width in 1..=4 {
            for right_width in 1..=4 {
                for left_signed in [false, true] {
                    for right_signed in [false, true] {
                        let left_count = 1usize << (2 * left_width);
                        let right_count = 1usize << (2 * right_width);
                        for left_code in 0..left_count {
                            let left =
                                four_state_value(left_code, left_width, left_signed);
                            for right_code in 0..right_count {
                                let right =
                                    four_state_value(right_code, right_width, right_signed);
                                assert_eq!(
                                    left.case_eq(&right).to_u64(),
                                    left.case_eq_slow(&right).to_u64()
                                );
                            }
                        }
                    }
                }
            }
        }
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
    #[inline]
    pub fn is_true(&self) -> bool {
        self.is_nonzero().unwrap_or(false)
    }

    /// Check if the value has any unknown (X/Z) bits
    #[inline]
    pub fn has_unknown(&self) -> bool {
        match &self.storage {
            ValueStorage::Inline { xz_bits, .. } => *xz_bits != 0,
            ValueStorage::Wide(bits) => bits.has_xz(),
        }
    }

    /// Create a value with all bits set to 1
    #[inline]
    pub fn ones(width: u32) -> Self {
        let width = Self::cap_width(width);
        if width <= 64 {
            Self::from_u64(Self::mask(width), width)
        } else {
            Self { storage: ValueStorage::Wide(Box::new(PackedBits::new_fill(width, LogicBit::One))), width, is_signed: false, is_real: false, is_fill: false }
        }
    }

    /// Decimal string representation
    pub fn to_dec_string(&self) -> String {
        if self.is_real {
            return format!("{:?}", self.to_f64());
        }
        if self.has_unknown() {
            // §21.2.1.2 unknown casing for `%d`: a value that is entirely x
            // prints `x`, entirely z prints `z`, and one that mixes unknown with
            // known bits (or x with z) prints uppercase `X`/`Z`. The old code
            // always returned lowercase `x`, losing z and mis-casing partials.
            let (mut n_x, mut n_z) = (0u32, 0u32);
            for i in 0..self.width as usize {
                match self.get_bit(i) {
                    LogicBit::X => n_x += 1,
                    LogicBit::Z => n_z += 1,
                    _ => {}
                }
            }
            let w = self.width;
            let ch = if n_x == w {
                'x'
            } else if n_z == w {
                'z'
            } else if n_x > 0 {
                'X'
            } else {
                'Z'
            };
            return ch.to_string();
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

    /// The value's bytes as string content, big-endian (MSB first), with the
    /// LEADING NUL bytes introduced by widening trimmed. Zero bytes at or
    /// below the first nonzero byte are kept: they are genuine content —
    /// §21.2.1.4 unformatted `%u`/`%z` dumps end in alignment NULs that
    /// `len()`/`getc()` must observe.
    pub fn sv_string_bytes(&self) -> Vec<u8> {
        let num_bytes = self.width.div_ceil(8) as usize;
        let mut out: Vec<u8> = Vec::new();
        let mut started = false;
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
                started = true;
            }
            if started {
                out.push(byte);
            }
        }
        out
    }

    /// Convert packed bytes to a SystemVerilog-style string. Each byte maps
    /// to one char (Latin-1, the inverse of `from_string`), so raw bytes
    /// above 0x7F survive a round-trip instead of becoming U+FFFD.
    pub fn to_sv_string(&self) -> String {
        self.sv_string_bytes().into_iter().map(|b| b as char).collect()
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
                    // IEEE 1800-2017 §5.7.1: a decimal literal's value may be a
                    // SINGLE `x` or a SINGLE `z`/`?` (underscores already
                    // stripped) standing for a whole all-unknown/all-hi-Z value —
                    // never multiple such digits, never mixed with numeric
                    // digits, never a mix of x and z. The parser rejects those
                    // malformed forms (see validate_number_literal); here we only
                    // render the two legal single-digit cases. A lone `z`/`?`
                    // fills all bits with Z (previously mis-rendered as all-X).
                    if s.len() == 1 {
                        match s.as_bytes()[0] {
                            b'x' | b'X' => return Self::new(width),
                            b'z' | b'Z' | b'?' => {
                                let mut v = Self::zero(width);
                                for b in 0..width as usize { v.set_bit(b, LogicBit::Z); }
                                return v;
                            }
                            _ => {}
                        }
                    }
                    // Malformed decimal (multi/mixed x/z): the parser should have
                    // already reported this. Fall back to all-X defensively.
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
    ///
    /// Hot path (inline source, index inside the vector) is a shift and two
    /// masks that build the 1-bit result directly. The old body always went
    /// `Value::zero(1)` + `set_bit(0, …)`, i.e. a construct-then-read-modify-
    /// write through a `match` on the storage enum, and was an out-of-line
    /// cross-crate call on top (no `#[inline]`, `lto = false`).
    #[inline]
    pub fn bit_select(&self, index: usize) -> Value {
        if let ValueStorage::Inline { val_bits, xz_bits } = self.storage {
            // `index < 64` keeps the shifts in range for the (rare) inline
            // value whose declared width exceeds 64.
            if index < self.width as usize && index < 64 {
                return Value {
                    storage: ValueStorage::Inline {
                        val_bits: (val_bits >> index) & 1,
                        xz_bits: (xz_bits >> index) & 1,
                    },
                    width: 1, is_signed: false, is_real: false, is_fill: false,
                };
            }
        }
        self.bit_select_slow(index)
    }

    #[inline(never)]
    fn bit_select_slow(&self, index: usize) -> Value {
        // §11.5.1: a bit-select address outside the vector bounds reads as x
        // (for a 4-state type). A fill value replicates instead (§5.7.1).
        if (index as u32) >= self.width && !self.is_fill {
            return Value::new(1);
        }
        let bit = self.get_bit(index);
        let mut v = Value::zero(1);
        v.set_bit(0, bit);
        v
    }

    /// Select a range of bits [left:right] (§11.5.1). Source indices outside
    /// the vector bounds read as x; a fill value (§5.7.1) replicates instead.
    ///
    /// The overwhelmingly common shape — an inline (≤64-bit) source, both
    /// bounds inside the vector — is handled here as a single shift+mask pair
    /// and nothing else. It used to reach the same arithmetic only after
    /// `range_select_zext` had re-derived the width, re-checked `MAX_WIDTH`,
    /// re-matched the storage enum and returned a `Value` that this function
    /// then re-inspected for overhang; the combined body was large enough that
    /// LLVM emitted it out of line despite the `#[inline]`.
    #[inline]
    pub fn range_select(&self, left: usize, right: usize) -> Value {
        if let ValueStorage::Inline { val_bits, xz_bits } = self.storage {
            if !self.is_fill {
                let (lo, hi) = if left >= right { (right, left) } else { (left, right) };
                // `hi < self.width` implies the whole select is in range, so
                // §11.5.1's x-on-overrun rule cannot fire; `hi < 64` keeps the
                // shift in range and bounds `width` at 64 (no overflow in
                // `hi - lo + 1`).
                if hi < 64 && hi < self.width as usize {
                    let width = hi - lo + 1;
                    let mask = if width == 64 { u64::MAX } else { (1u64 << width) - 1 };
                    return Value {
                        storage: ValueStorage::Inline {
                            val_bits: (val_bits >> lo) & mask,
                            xz_bits: (xz_bits >> lo) & mask,
                        },
                        width: width as u32,
                        is_signed: false,
                        is_real: false, is_fill: false,
                    };
                }
            }
        }
        self.range_select_slow(left, right)
    }

    #[inline(never)]
    fn range_select_slow(&self, left: usize, right: usize) -> Value {
        let result = self.range_select_zext(left, right);
        if self.is_fill {
            return result;
        }
        let lo = left.min(right);
        let w = self.width as usize;
        let width = result.width as usize;
        if lo >= w {
            // The entire select is beyond the vector — all bits read x.
            return Value::new(width as u32);
        }
        if lo + width <= w {
            // Fully in range — the fast paths already produced the value.
            return result;
        }
        // Partial overhang: the low bits are real, the high bits read x.
        let mut result = result;
        for i in 0..width {
            if lo + i >= w {
                result.set_bit(i, LogicBit::X);
            }
        }
        result
    }

    /// §11.5.1 part-select with SIGNED source bounds — used for `[l -: w]`
    /// when `l < w-1`, where the low index falls below 0. `hi >= lo`; every
    /// output bit whose source index is <0 or >=width reads x. `is_fill`
    /// values replicate their bit 0 into any position instead.
    pub fn range_select_signed(&self, hi: i64, lo: i64) -> Value {
        let width = (hi - lo + 1).max(0);
        if width == 0 {
            return Value::zero(0);
        }
        let width = width as usize;
        let mut result = Value::new(width as u32); // starts all-x
        let w = self.width as i64;
        for j in 0..width {
            let src = lo + j as i64;
            if self.is_fill {
                result.set_bit(j, self.get_bit(0));
            } else if src >= 0 && src < w {
                result.set_bit(j, self.get_bit(src as usize));
            }
            // otherwise leave x
        }
        result
    }

    /// Zero-extending range select (internal). Bits beyond the source width
    /// come back as 0; `range_select` overlays the §11.5.1 x-on-overrun rule.
    #[inline]
    fn range_select_zext(&self, left: usize, right: usize) -> Value {
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
            // Inline storage is a u64, so only `lo < 64` is shift-safe. An
            // out-of-range part-select (`lo >= 64`, which since Inline ⇒
            // width <= 64 means every requested bit is beyond the value) must
            // not enter the fast path — `val_bits >> lo` would overflow.
            // Fall through to the generic get_bit loop, which returns Zero
            // for bits beyond `self.width` (LRM §11.5.1 out-of-range reads).
            if width <= 64 && lo < 64 {
                let mask = if width == 64 { u64::MAX } else { (1u64 << width) - 1 };
                return Value {
                    storage: ValueStorage::Inline {
                        val_bits: (val_bits >> lo) & mask,
                        xz_bits: (xz_bits >> lo) & mask,
                    },
                    width: width as u32,
                    is_signed: false,
                    is_real: false, is_fill: false,
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
            // Wide → Wide: copy the selected bits into a fresh packed value.
            // (The packed 2-bit encoding no longer gives a byte-aligned memcpy
            // for arbitrary `lo`; the per-bit copy below is correct and still
            // O(width). A packed-shift fast path can follow if profiling ever
            // shows this hot for wide signals.)
            if width > 64 {
                let mut out = PackedBits::new_zero(width as u32);
                let len = bits.len() as usize;
                let copy_len = width.min(len.saturating_sub(lo));
                for i in 0..copy_len {
                    out.set(i, bits.get(lo + i));
                }
                return Value {
                    storage: ValueStorage::Wide(Box::new(out)),
                    width: width as u32,
                    is_signed: false,
                    is_real: false, is_fill: false,
                };
            }
            if width <= 64 {
                let mut val_bits: u64 = 0;
                let mut xz_bits: u64 = 0;
                let end = lo + width;
                let len = bits.len() as usize;
                for i in lo..end.min(len) {
                    let pos = i - lo;
                    let m = 1u64 << pos;
                    match bits.get(i) {
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
                    is_real: false, is_fill: false,
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
    #[inline]
    pub fn neq(&self, other: &Value) -> Value {
        self.is_not_equal(other)
    }

    /// Less-or-equal comparison
    #[inline]
    pub fn leq(&self, other: &Value) -> Value {
        self.less_equal(other)
    }

    /// Greater-or-equal comparison
    #[inline]
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
        // Wide→Wide with the same width memcpys the packed bytes into the
        // existing boxed slice, avoiding the per-iter allocation that
        // `storage.clone()` would do. Mixed variants fall back to the generic
        // clone.
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
                // Equal widths (the norm — a signal keeps its width) copy
                // straight over the existing packed bytes: one memcpy, no
                // length store, no capacity check, no realloc. Only a genuine
                // width change reallocates the boxed storage.
                if sv.len() == ov.len() {
                    sv.data_mut().copy_from_slice(ov.data());
                } else {
                    *sv = Box::new(PackedBits::from_data(ov.data().to_vec(), ov.len()));
                }
            }
            _ => {
                self.storage = other.storage.clone();
            }
        }
        self.width = other.width;
        self.is_signed = other.is_signed;
        self.is_real = other.is_real;
        self.is_fill = other.is_fill;
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
    #[inline]
    pub fn all_z(width: u32) -> Self {
        if width <= 64 {
            // For inline: xz_bits = all 1s (marks X/Z), val_bits = all 1s (Z vs X)
            let mask = Self::mask(width);
            Self {
                storage: ValueStorage::Inline { val_bits: mask, xz_bits: mask },
                width,
                is_signed: false, is_real: false, is_fill: false,
            }
        } else {
            Self {
                storage: ValueStorage::Wide(Box::new(PackedBits::new_fill(width, LogicBit::Z))),
                width,
                is_signed: false, is_real: false, is_fill: false,
            }
        }
    }
}

