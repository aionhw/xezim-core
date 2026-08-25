//! Value types for SystemVerilog simulation.
//! Supports 4-state logic (0, 1, X, Z) with arbitrary-width bit vectors.
//!
//! Optimized representation: values ≤64 bits use inline u64 storage,
//! avoiding heap allocation entirely. Wider values fall back to Vec<LogicBit>.

use std::fmt;
use serde::{Serialize, Deserialize};

/// A single 4-state logic bit.
///
/// `#[repr(u8)]` pins the discriminants to the 2-bit codes already used by
/// `to_code`/`from_code` (Zero=0, One=1, X=2, Z=3). That makes one `LogicBit`
/// exactly one byte with no padding, which `wide_bits_eq` relies on to compare
/// `Wide` storage a machine word at a time instead of a byte at a time.
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
    /// Fallback for width > 64: two-plane word storage (see `WidePlanes`).
    Wide(Box<WidePlanes>),
}

/// Two-plane word storage for widths > 64: bit `i` of the value lives in
/// `val[i/64]` bit `i%64`, its x/z flag in `xz` at the same position — the
/// SAME (v, xz) encoding the `Inline` variant uses, extended to N words.
///
/// Replaces `Vec<LogicBit>` (ONE BYTE per bit): heap footprint drops ~4x
/// (c906 holds X/Z in 95% of its 35 M signals, most of them wide during the
/// init storm), `clone` becomes two word memcpys instead of a byte-vector
/// copy, and bitwise/compare ops can run word-parallel instead of per-bit.
/// Per-bit access stays available through `get`/`set`, so every method that
/// walks bits via `Value::get_bit` keeps working unchanged.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct WidePlanes {
    pub val: Vec<u64>,
    pub xz: Vec<u64>,
    /// Number of live bits (the owning `Value.width` mirrors this; kept here
    /// so plane code never reaches back into the `Value`).
    pub nbits: u32,
}

impl WidePlanes {
    #[inline]
    pub fn nwords(nbits: u32) -> usize {
        (nbits.max(1) as usize).div_ceil(64)
    }
    pub fn zeroed(nbits: u32) -> Self {
        let n = Self::nwords(nbits);
        Self { val: vec![0; n], xz: vec![0; n], nbits }
    }
    /// All bits set to `bit`.
    pub fn filled(nbits: u32, bit: LogicBit) -> Self {
        let n = Self::nwords(nbits);
        let (v, x) = match bit {
            LogicBit::Zero => (0u64, 0u64),
            LogicBit::One => (u64::MAX, 0),
            LogicBit::X => (0, u64::MAX),
            LogicBit::Z => (u64::MAX, u64::MAX),
        };
        let mut p = Self { val: vec![v; n], xz: vec![x; n], nbits };
        p.mask_top();
        p
    }
    /// Clear any bits at or above `nbits` in the top word.
    #[inline]
    pub fn mask_top(&mut self) {
        let r = (self.nbits % 64) as u64;
        if r != 0 {
            let m = (1u64 << r) - 1;
            if let Some(w) = self.val.last_mut() {
                *w &= m;
            }
            if let Some(w) = self.xz.last_mut() {
                *w &= m;
            }
        }
    }
    /// From value words (2-state), LSB word first.
    pub fn from_val_words(words: &[u64], nbits: u32) -> Self {
        let n = Self::nwords(nbits);
        let mut val = vec![0u64; n];
        for (i, w) in words.iter().take(n).enumerate() {
            val[i] = *w;
        }
        let mut p = Self { val, xz: vec![0; n], nbits };
        p.mask_top();
        p
    }
    pub fn from_bits(bits: &[LogicBit]) -> Self {
        let mut p = Self::zeroed(bits.len() as u32);
        for (i, b) in bits.iter().enumerate() {
            p.set(i, *b);
        }
        p
    }
    #[inline]
    pub fn get(&self, i: usize) -> LogicBit {
        if i >= self.nbits as usize {
            return LogicBit::Zero;
        }
        let (w, b) = (i / 64, i % 64);
        let v = (self.val[w] >> b) & 1;
        let x = (self.xz[w] >> b) & 1;
        match (v, x) {
            (0, 0) => LogicBit::Zero,
            (1, 0) => LogicBit::One,
            (0, 1) => LogicBit::X,
            _ => LogicBit::Z,
        }
    }
    #[inline]
    pub fn set(&mut self, i: usize, bit: LogicBit) {
        if i >= self.nbits as usize {
            return;
        }
        let (w, b) = (i / 64, i % 64);
        let (v, x) = match bit {
            LogicBit::Zero => (0u64, 0u64),
            LogicBit::One => (1, 0),
            LogicBit::X => (0, 1),
            LogicBit::Z => (1, 1),
        };
        self.val[w] = (self.val[w] & !(1 << b)) | (v << b);
        self.xz[w] = (self.xz[w] & !(1 << b)) | (x << b);
    }
    #[inline]
    pub fn len(&self) -> usize {
        self.nbits as usize
    }
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.nbits == 0
    }
    #[inline]
    pub fn any_xz(&self) -> bool {
        self.xz.iter().any(|&w| w != 0)
    }
    /// Splice `n` (≤64) bits of (v, x) planes in at bit position `pos`.
    #[inline]
    pub fn splice64(&mut self, pos: usize, v: u64, x: u64, n: usize) {
        if n == 0 || pos >= self.nbits as usize {
            return;
        }
        let n = n.min(64).min(self.nbits as usize - pos);
        let mask = if n >= 64 { u64::MAX } else { (1u64 << n) - 1 };
        let (v, x) = (v & mask, x & mask);
        let (wi, off) = (pos / 64, pos % 64);
        self.val[wi] = (self.val[wi] & !(mask << off)) | (v << off);
        self.xz[wi] = (self.xz[wi] & !(mask << off)) | (x << off);
        if off + n > 64 {
            let hi_n = off + n - 64;
            let hi_mask = (1u64 << hi_n) - 1;
            self.val[wi + 1] = (self.val[wi + 1] & !hi_mask) | (v >> (64 - off));
            self.xz[wi + 1] = (self.xz[wi + 1] & !hi_mask) | (x >> (64 - off));
        }
    }
    /// Extract up to 64 bits of both planes starting at `pos`.
    #[inline]
    pub fn extract64(&self, pos: usize, n: usize) -> (u64, u64) {
        let n = n.min(64);
        let mask = if n >= 64 { u64::MAX } else { (1u64 << n) - 1 };
        let (wi, off) = (pos / 64, pos % 64);
        let take = |plane: &[u64]| -> u64 {
            let lo = plane.get(wi).copied().unwrap_or(0) >> off;
            let hi = if off > 0 {
                plane.get(wi + 1).copied().unwrap_or(0) << (64 - off)
            } else {
                0
            };
            (lo | hi) & mask
        };
        (take(&self.val), take(&self.xz))
    }

    /// Iterate the live bits, LSB first.
    pub fn iter_bits(&self) -> impl Iterator<Item = LogicBit> + '_ {
        (0..self.nbits as usize).map(move |i| self.get(i))
    }
    /// Vec-compat alias for `iter_bits` (pre-planes code iterated the
    /// `Vec<LogicBit>` directly).
    pub fn iter(&self) -> impl Iterator<Item = LogicBit> + '_ {
        self.iter_bits()
    }
    pub fn contains(&self, b: &LogicBit) -> bool {
        self.iter_bits().any(|x| x == *b)
    }
    /// Vec-compat: `bits.get(i).copied()` shape.
    pub fn get_opt(&self, i: usize) -> Option<LogicBit> {
        if i < self.nbits as usize { Some(self.get(i)) } else { None }
    }
    pub fn to_bit_vec(&self) -> Vec<LogicBit> {
        self.iter_bits().collect()
    }
}

/// Bit-vector equality for `Wide` storage, a machine word at a time.
///
/// `LogicBit` is not one of the primitive types std marks `BytewiseEq`, so the
/// derived `Vec<LogicBit> == Vec<LogicBit>` lowers to `iter().zip().all()` —
/// one byte compared per loop iteration, which is what showed up as the
/// dominant cost of `signal_table[id] != val` change detection on wide buses.
/// Because `LogicBit` is `#[repr(u8)]` (one byte, no padding, no provenance,
/// and `==` is exactly byte equality) the two vectors can be compared as raw
/// bytes, 8 at a time.
#[inline]
fn wide_bits_eq(a: &[LogicBit], b: &[LogicBit]) -> bool {
    const _: () = assert!(std::mem::size_of::<LogicBit>() == 1);
    let n = a.len();
    if n != b.len() {
        return false;
    }
    let pa = a.as_ptr().cast::<u8>();
    let pb = b.as_ptr().cast::<u8>();
    // SAFETY: `pa`/`pb` are the starts of two live byte ranges of `n` bytes
    // each (LogicBit is one byte, so len == byte length). Every read below is
    // an unaligned read fully inside `0..n` of its own range.
    unsafe {
        let mut i = 0usize;
        while i + 8 <= n {
            if pa.add(i).cast::<u64>().read_unaligned() != pb.add(i).cast::<u64>().read_unaligned()
            {
                return false;
            }
            i += 8;
        }
        if i < n {
            if n >= 8 {
                // Overlapping tail word — cheaper than a byte loop.
                if pa.add(n - 8).cast::<u64>().read_unaligned()
                    != pb.add(n - 8).cast::<u64>().read_unaligned()
                {
                    return false;
                }
            } else {
                while i < n {
                    if *pa.add(i) != *pb.add(i) {
                        return false;
                    }
                    i += 1;
                }
            }
        }
    }
    true
}

/// Mask selecting bit 0 of every byte of a `u64`.
const LSB_OF_EACH_BYTE: u64 = 0x0101_0101_0101_0101;

/// Scatter the 8 bits of `b` into the low bit of 8 consecutive bytes
/// (little-endian: bit `i` of `b` lands in bit 0 of byte `i`).
///
/// Used to unpack the packed `Inline` 4-state encoding into the one-byte-per-bit
/// `Wide` representation eight bits at a time. `x * 0x0101…` broadcasts the byte
/// to all eight lanes, the `& 0x8040…0201` keeps only bit `i` in lane `i`, and
/// the `+ 0x7f7f…` / `>> 7` pair normalises "lane is nonzero" to 1 without any
/// inter-lane carry (the largest lane value is `0x80 + 0x7f = 0xff`).
#[inline(always)]
fn scatter_bits_to_bytes(b: u8) -> u64 {
    let lanes = (b as u64).wrapping_mul(LSB_OF_EACH_BYTE) & 0x8040_2010_0804_0201;
    (lanes.wrapping_add(0x7f7f_7f7f_7f7f_7f7f) >> 7) & LSB_OF_EACH_BYTE
}

/// Inverse of `scatter_bits_to_bytes`: gather bit 0 of each of 8 bytes into one
/// byte (byte `i` -> bit `i`).
///
/// The multiplier `0x0102040810204080` is `Σ_{j<8} 2^(56-7j)`, which moves lane
/// `i`'s bit from position `8i` to position `56+i`. No two (lane,
/// multiplier-term) products share an exponent — `8i - 7j = 8i' - 7j'` forces
/// `i-i' = 7k` and `j-j' = 8k`, impossible for distinct indices in `0..8` — so
/// the product is a sum of distinct powers of two and carries cannot corrupt
/// the result. (Note the low byte is `0x80`, not the `0x81` of the superficially
/// similar bit-reversal constant: a `2^0` term would fold lane 7 back onto
/// bit 0.)
#[inline(always)]
fn gather_byte_lsbs(lanes: u64) -> u8 {
    ((lanes & LSB_OF_EACH_BYTE).wrapping_mul(0x0102_0408_1020_4080) >> 56) as u8
}

#[inline(never)]
fn storage_eq_slow(a: &ValueStorage, b: &ValueStorage) -> bool {
    match (a, b) {
        (ValueStorage::Wide(a), ValueStorage::Wide(b)) => a == b,
        _ => false,
    }
}

impl PartialEq for ValueStorage {
    /// Same result as the previous `#[derive(PartialEq)]` (Inline compares its
    /// two words, Wide compares its bits, mixed variants are never equal); only
    /// the Wide arm is faster (see `wide_bits_eq`).
    ///
    /// The two-word arm is the one `signal_table[id] != val` runs on every
    /// signal write, so it stays in the caller; the `Wide` word-at-a-time
    /// comparison is an out-of-line tail rather than a loop LLVM has to price
    /// into every inlining decision about `Value::eq`.
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        if let (
            ValueStorage::Inline { val_bits: av, xz_bits: ax },
            ValueStorage::Inline { val_bits: bv, xz_bits: bx },
        ) = (self, other)
        {
            return av == bv && ax == bx;
        }
        storage_eq_slow(self, other)
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
    ValueStorage::Wide(Box::new(WidePlanes::filled(width, bit)))
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
        // ONE byte pass where `chars().filter(..).count()` decoded UTF-8. A
        // UTF-8 continuation byte (`0b10xxxxxx`) is never the start of a
        // character and `_` is ASCII, so counting non-continuation bytes that
        // are not `_` is exactly the original character count — for non-ASCII
        // input too. This runs once per number literal.
        let digits = value
            .as_bytes()
            .iter()
            .filter(|&&b| b & 0xC0 != 0x80 && b != b'_')
            .count() as u32;
        let natural = match radix {
            2 => digits,
            8 => digits.saturating_mul(3),
            16 => digits.saturating_mul(4),
            // Decimal: use the magnitude when it fits, else a safe upper bound
            // (log2(10) < 3.33, so 4 bits per digit never under-counts).
            _ => {
                // `parse` the borrowed string directly when there is no `_` to
                // strip, which is the overwhelmingly common case; only a
                // separator-bearing literal still pays for a scratch `String`.
                let parsed = if value.len() == digits as usize {
                    value.parse::<u128>()
                } else {
                    let cleaned: String = value.chars().filter(|c| *c != '_').collect();
                    cleaned.parse::<u128>()
                };
                match parsed {
                    Ok(v) => (128 - v.leading_zeros()).max(1),
                    Err(_) => digits.saturating_mul(4),
                }
            }
        };
        natural.max(32)
    }

    /// §5.7.1 — an UNSIZED based literal whose digits are uniformly x (or
    /// uniformly z/?) extends with that digit "to the size of the expression",
    /// exactly like an unbased-unsized fill: `u64 = 'bx` must be 64 x bits,
    /// not 32 x bits zero-extended. Returns the fill char when the digit
    /// string qualifies, so the literal evaluators can mark the (32-bit)
    /// value `is_fill`. A MIXED leading-x/z literal (`'bx1`) stays a plain
    /// 32-bit value — extension past 32 bits is not attempted for it.
    pub fn unsized_xz_fill_char(value: &str) -> Option<char> {
        let mut fill: Option<char> = None;
        for c in value.chars() {
            let f = match c {
                '_' => continue,
                'x' | 'X' => 'x',
                'z' | 'Z' | '?' => 'z',
                _ => return None,
            };
            match fill {
                None => fill = Some(f),
                Some(prev) if prev != f => return None,
                _ => {}
            }
        }
        fill
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
                storage: ValueStorage::Wide(Box::new(WidePlanes::filled(width, LogicBit::X))),
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
            Self { storage: ValueStorage::Wide(Box::new(WidePlanes::filled(width, LogicBit::Zero))), width, is_signed: false, is_real: false, is_fill: false }
        }
    }

    #[inline]
    pub fn from_u64(val: u64, width: u32) -> Self {
        let width = Self::cap_width(width);
        if width <= 64 {
            let mask = Self::mask(width);
            Self { storage: ValueStorage::Inline { val_bits: val & mask, xz_bits: 0 }, width, is_signed: false, is_real: false, is_fill: false }
        } else {
            let mut bits = vec![LogicBit::Zero; width as usize];
            for i in 0..64.min(width as usize) {
                if (val >> i) & 1 == 1 { bits[i] = LogicBit::One; }
            }
            Self { storage: ValueStorage::Wide(Box::new(WidePlanes::from_bits(&bits))), width, is_signed: false, is_real: false, is_fill: false }
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
            let mut bits = vec![LogicBit::Zero; width as usize];
            let lim = 128.min(width as usize);
            for i in 0..lim {
                if (val >> i) & 1 == 1 { bits[i] = LogicBit::One; }
            }
            Self { storage: ValueStorage::Wide(Box::new(WidePlanes::from_bits(&bits))), width, is_signed: false, is_real: false, is_fill: false }
        }
    }

    /// Extract value as u128. Returns low 128 bits, treating X/Z as 0.
    #[inline]
    pub fn to_u128(&self) -> u128 {
        match &self.storage {
            ValueStorage::Inline { val_bits, xz_bits } => (*val_bits & !*xz_bits) as u128,
            ValueStorage::Wide(bits) => {
                let w0 = bits.val.first().copied().unwrap_or(0)
                    & !bits.xz.first().copied().unwrap_or(0);
                let w1 = bits.val.get(1).copied().unwrap_or(0)
                    & !bits.xz.get(1).copied().unwrap_or(0);
                (w0 as u128) | ((w1 as u128) << 64)
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
            let mut bits = Vec::with_capacity(width as usize);
            for &b in bytes.iter().rev() {
                for i in 0..8 {
                    bits.push(if (b >> i) & 1 == 1 { LogicBit::One } else { LogicBit::Zero });
                }
            }
            Self { storage: ValueStorage::Wide(Box::new(WidePlanes::from_bits(&bits))), width, is_signed: false, is_real: false, is_fill: false }
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
    /// Both planes when storage is `Inline`, else None — the cheap
    /// discriminant check fast paths need without exposing the storage enum.
    #[inline]
    pub fn inline_planes(&self) -> Option<(u64, u64)> {
        match &self.storage {
            ValueStorage::Inline { val_bits, xz_bits } => Some((*val_bits, *xz_bits)),
            ValueStorage::Wide(_) => None,
        }
    }

    /// Overwrite both planes in place. Caller guarantees the storage is
    /// already `Inline` and the bits are masked to `self.width`.
    #[inline]
    pub fn set_inline_planes(&mut self, v: u64, x: u64) {
        self.storage = ValueStorage::Inline { val_bits: v, xz_bits: x };
    }

    pub fn raw_bits(&self) -> (u64, u64) {
        match &self.storage {
            ValueStorage::Inline { val_bits, xz_bits } => (*val_bits, *xz_bits),
            ValueStorage::Wide(bits) => (
                bits.val.first().copied().unwrap_or(0),
                bits.xz.first().copied().unwrap_or(0),
            ),
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
    /// (value, xz) bits of the ≤64-bit slice `[lo +: w]`, SWAR-chunked over
    /// the repr(u8) Wide layout (val bit = code bit0, xz bit = code bit1).
    /// Out-of-range positions read 0/0 — callers bound `lo..lo+w` themselves
    /// or treat the zeros as their existing get_bit loop did.
    pub fn slice_bits_swar(&self, lo: usize, w: usize) -> (u64, u64) {
        let w = w.min(64);
        match &self.storage {
            ValueStorage::Inline { val_bits, xz_bits } => {
                let mask = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
                ((val_bits >> lo) & mask, (xz_bits >> lo) & mask)
            }
            ValueStorage::Wide(bits) => {
                // Plane extraction: at most two word reads per plane.
                let nb = bits.nbits as usize;
                if lo >= nb {
                    return (0, 0);
                }
                let w = w.min(nb - lo);
                let mask = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
                let (wi, off) = (lo / 64, lo % 64);
                let take = |plane: &[u64]| -> u64 {
                    let lo64 = plane.get(wi).copied().unwrap_or(0) >> off;
                    let hi64 = if off > 0 {
                        plane.get(wi + 1).copied().unwrap_or(0) << (64 - off)
                    } else {
                        0
                    };
                    (lo64 | hi64) & mask
                };
                (take(&bits.val), take(&bits.xz))
            }
        }
    }

    /// Two-state word extraction for widths ≤ 128 (P5 wide islands):
    /// fills `v` with the value bits and returns true iff the value is
    /// X/Z-free (and representable: not fill, not real). The word layout is
    /// little-endian: v[0] = bits 63..0, v[1] = bits 127..64.
    pub fn words128_if_clean(&self, v: &mut [u64; 2]) -> bool {
        if self.is_fill || self.is_real || self.width > 128 {
            return false;
        }
        match &self.storage {
            ValueStorage::Inline { val_bits, xz_bits } => {
                if *xz_bits != 0 {
                    return false;
                }
                v[0] = *val_bits;
                v[1] = 0;
                true
            }
            ValueStorage::Wide(bits) => {
                // Planes: clean test is a word scan, extraction two copies.
                if bits.any_xz() {
                    return false;
                }
                v[0] = bits.val.first().copied().unwrap_or(0);
                v[1] = bits.val.get(1).copied().unwrap_or(0);
                true
            }
        }
    }

    /// Two-state word writeback for widths ≤ 128 (P5 wide islands): sets the
    /// value to exactly `v` (X/Z cleared) at the CURRENT width, preserving
    /// the storage kind. Returns true when the stored value CHANGED. Bits of
    /// `v` above the width must already be masked by the caller.
    pub fn set_words128(&mut self, v: [u64; 2]) -> bool {
        match &mut self.storage {
            ValueStorage::Inline { val_bits, xz_bits } => {
                let changed = *val_bits != v[0] || *xz_bits != 0;
                *val_bits = v[0];
                *xz_bits = 0;
                changed
            }
            ValueStorage::Wide(bits) => {
                // Planes: masked word compare-and-store, X/Z cleared.
                let nb = bits.nbits;
                let n = WidePlanes::nwords(nb).min(2);
                let mut want = [0u64; 2];
                want[0] = v[0];
                if n > 1 {
                    want[1] = v[1];
                }
                let r = (nb % 64) as u64;
                if r != 0 && WidePlanes::nwords(nb) <= 2 {
                    want[n - 1] &= (1u64 << r) - 1;
                }
                let mut changed = false;
                for wi in 0..n {
                    if bits.val[wi] != want[wi] {
                        bits.val[wi] = want[wi];
                        changed = true;
                    }
                    if bits.xz[wi] != 0 {
                        bits.xz[wi] = 0;
                        changed = true;
                    }
                }
                changed
            }
        }
    }

    /// Construct a two-state value of `width` (65..=128 uses Wide storage)
    /// from little-endian words. Bits above `width` must be pre-masked.
    pub fn from_words128(v: [u64; 2], width: u32) -> Value {
        if width <= 64 {
            return Value::from_u64(v[0], width);
        }
        let mut bits = vec![LogicBit::Zero; width as usize];
        for (i, b) in bits.iter_mut().enumerate() {
            if (v[i >> 6] >> (i & 63)) & 1 != 0 {
                *b = LogicBit::One;
            }
        }
        Value {
            storage: ValueStorage::Wide(Box::new(WidePlanes::from_bits(&bits))),
            width,
            is_signed: false,
            is_real: false,
            is_fill: false,
        }
    }

    pub fn has_xz(&self) -> bool {
        match &self.storage {
            ValueStorage::Inline { xz_bits, .. } => *xz_bits != 0,
            ValueStorage::Wide(bits) => bits.iter().any(|b| matches!(b, LogicBit::X | LogicBit::Z)),
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
                    // X/Z -> 0: clear the value bit wherever xz is set.
                    for wi in 0..ob.val.len() {
                        ob.val[wi] &= !ob.xz[wi];
                        ob.xz[wi] = 0;
                    }
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
            // `LogicBit` is `#[repr(u8)]` with exactly these discriminants, so
            // the four-way match this used to run IS the identity cast (and
            // `LogicBit::Zero as u8 == 0` covers the out-of-range default).
            ValueStorage::Wide(bits) => bits.get(i) as u8,
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
                if i < bits.nbits as usize {
                    if bits.get(i) == bit { return false; }
                    bits.set(i, bit);
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
                bits.set(i, bit);
            }
        }
    }

    /// Copy a contiguous bit slice into this value and report whether any bit
    /// changed. Bounds are clipped to both values. Wide-to-wide transfers use
    /// slice operations instead of dispatching once per bit.
    pub fn copy_bits_from(
        &mut self,
        dst_start: usize,
        source: &Value,
        src_start: usize,
        count: usize,
    ) -> bool {
        let count = count
            .min((self.width as usize).saturating_sub(dst_start))
            .min((source.width as usize).saturating_sub(src_start));
        if count == 0 {
            return false;
        }
        match (&mut self.storage, &source.storage) {
            (
                ValueStorage::Inline {
                    val_bits: dst_v,
                    xz_bits: dst_x,
                },
                ValueStorage::Inline {
                    val_bits: src_v,
                    xz_bits: src_x,
                },
            ) => {
                let low_mask = if count >= 64 {
                    u64::MAX
                } else {
                    (1u64 << count) - 1
                };
                let mask = low_mask << dst_start;
                let next_v = (*dst_v & !mask) | (((*src_v >> src_start) & low_mask) << dst_start);
                let next_x = (*dst_x & !mask) | (((*src_x >> src_start) & low_mask) << dst_start);
                let changed = next_v != *dst_v || next_x != *dst_x;
                *dst_v = next_v;
                *dst_x = next_x;
                changed
            }
            (ValueStorage::Wide(dst), ValueStorage::Wide(src)) => {
                let mut changed = false;
                for off in 0..count {
                    let b = src.get(src_start + off);
                    if dst.get(dst_start + off) != b {
                        dst.set(dst_start + off, b);
                        changed = true;
                    }
                }
                changed
            }
            _ => {
                let mut changed = false;
                for offset in 0..count {
                    changed |= self.set_bit_code(
                        dst_start + offset,
                        source.get_bit_code(src_start + offset),
                    );
                }
                changed
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
                let result = bits.val.first().copied().unwrap_or(0)
                    & !bits.xz.first().copied().unwrap_or(0);
                Some(result)
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
    ///
    /// The head no longer carries the `target == self.width` early-out: for
    /// `Inline` storage the widen arm below already reproduces `self.clone()`
    /// exactly when `target == self.width` (the sign-extension mask
    /// `mask(target) & !mask(self.width)` is empty, so both words pass through
    /// and every header field is copied), and for `Wide` storage the clone
    /// belongs in the out-of-line tail rather than in a head that every VM
    /// `Resize` wants inlined. Dropping it takes the `Vec`-clone code — the
    /// only bulky thing left in the head — out of the inlining cost estimate,
    /// which is what kept LLVM emitting a real cross-crate call here.
    #[inline]
    pub fn resize(&self, target: u32) -> Value {
        if !self.is_fill && !self.is_real && target != 0 {
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
                        wide_filled_bits(target, fill)
                    }, width: target, is_signed: self.is_signed , is_real: false, is_fill: false }
                } else {
                    Value::zero(target)
                };
                result.is_signed = self.is_signed;
                let copy_bits = self.width.min(target) as usize;
                // `set_bit` ignores any index past `result.width` (which the
                // unsigned branch's `Value::zero` may have capped below
                // `target`), so clamping the copy to the destination buffer is
                // the same work with the per-bit dispatch removed.
                // Per-bit copy: `set_bit`/`get_bit` are word-indexed plane
                // ops now, so the former byte-layout block copies no longer
                // apply. This is the SLOW path; the plane-native fast paths
                // above handle the common widths.
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
    /// a nonblocking/blocking assignment RHS to the LHS width. Only a SIGNED
    /// source replicates its MSB; an unsigned source always zero-extends, even
    /// when its MSB (or any lower bit) is X/Z.
    ///
    /// Every case that is a plain `resize` — which is all of them but a signed
    /// widening off an X/Z MSB — is decided here in flag tests and one
    /// `get_bit`, so `resize`'s inline arm lands directly in the caller instead
    /// of behind two calls. The `||` chain short-circuits before the `get_bit`
    /// whenever `self.width == 0`, so the `width - 1` cannot underflow.
    #[inline]
    pub fn resize_for_assign(&self, target: u32) -> Value {
        if !self.is_fill
            && (!self.is_signed
                || target <= self.width
                || self.width == 0
                || self.is_real
                || {
                    let msb = self.get_bit(self.width as usize - 1);
                    msb != LogicBit::X && msb != LogicBit::Z
                })
        {
            return self.resize(target);
        }
        self.resize_for_assign_slow(target)
    }

    #[cold]
    #[inline(never)]
    fn resize_for_assign_slow(&self, target: u32) -> Value {
        if self.is_fill {
            // §5.7.1: an unbased-unsized literal replicates into the target.
            return self.fill_at(target);
        }
        let msb = self.get_bit(self.width.saturating_sub(1) as usize);
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
        if !self.is_fill && !other.is_fill {
            if let (ValueStorage::Inline { val_bits: av, xz_bits: ax },
                    ValueStorage::Inline { val_bits: bv, xz_bits: bx })
                = (&self.storage, &other.storage)
            {
                let w = self.width.max(other.width);
                if *ax == 0 && *bx == 0 {
                    // Fast path: no X/Z
                    return Value { storage: ValueStorage::Inline { val_bits: av & bv, xz_bits: 0 }, width: w, is_signed: false, is_real: false, is_fill: false };
                }
                // X propagation for AND: 0 & X = 0, 1 & X = X
                let any_xz = ax | bx;
                let result_val = av & bv & !any_xz;
                let result_xz = any_xz & !((!av & !ax) | (!bv & !bx)); // known 0 kills X
                return Value { storage: ValueStorage::Inline { val_bits: result_val, xz_bits: result_xz & Self::mask(w) }, width: w, is_signed: false, is_real: false, is_fill: false };
            }
        }
        self.bitwise_and_slow(other)
    }

    /// `Wide` operand or a §5.7.1 fill — same two steps `bitwise_and` used to
    /// run inline. Out of line so the monomorphised `bitwise_op_slow` closure
    /// and the `fill_pair` widening stop counting against the inlining budget
    /// of the two-word arm above, which is the one the VM executes.
    #[cold]
    #[inline(never)]
    fn bitwise_and_slow(&self, other: &Value) -> Value {
        if let Some((a, b)) = self.fill_pair(other) {
            return a.bitwise_and(&b);
        }
        let op_bit = |a: LogicBit, b: LogicBit| match (a, b) {
            (LogicBit::Zero, _) | (_, LogicBit::Zero) => LogicBit::Zero,
            (LogicBit::One, LogicBit::One) => LogicBit::One,
            _ => LogicBit::X,
        };
        if let Some((a, b, w)) = self.wide_bitwise_pair(other) {
            // A KNOWN 0 on either side forces 0; two known 1s give 1; anything
            // else is x. "known 0" is `!val & !xz`, "known 1" is `val & !xz`.
            let bits = Self::wide_bitwise_lanes(a, b, w, |av, ax, bv, bx| {
                let zero_out = ((!av & !ax) | (!bv & !bx));
                let one_out = av & !ax & bv & !bx;
                (one_out, !zero_out & !one_out)
            }, op_bit);
            return Self::wide_bitwise_value(bits, w);
        }
        self.bitwise_op_slow(other, op_bit)
    }

    #[inline]
    pub fn bitwise_or(&self, other: &Value) -> Value {
        if !self.is_fill && !other.is_fill {
            if let (ValueStorage::Inline { val_bits: av, xz_bits: ax },
                    ValueStorage::Inline { val_bits: bv, xz_bits: bx })
                = (&self.storage, &other.storage)
            {
                let w = self.width.max(other.width);
                if *ax == 0 && *bx == 0 {
                    return Value { storage: ValueStorage::Inline { val_bits: av | bv, xz_bits: 0 }, width: w, is_signed: false, is_real: false, is_fill: false };
                }
                let any_xz = ax | bx;
                let result_val = (av | bv) & !any_xz;
                let result_xz = any_xz & !((av & !ax) | (bv & !bx)); // known 1 kills X
                return Value { storage: ValueStorage::Inline { val_bits: result_val | ((av & !ax) | (bv & !bx)), xz_bits: result_xz & Self::mask(w) }, width: w, is_signed: false, is_real: false, is_fill: false };
            }
        }
        self.bitwise_or_slow(other)
    }

    /// See `bitwise_and_slow`.
    #[cold]
    #[inline(never)]
    fn bitwise_or_slow(&self, other: &Value) -> Value {
        if let Some((a, b)) = self.fill_pair(other) {
            return a.bitwise_or(&b);
        }
        let op_bit = |a: LogicBit, b: LogicBit| match (a, b) {
            (LogicBit::One, _) | (_, LogicBit::One) => LogicBit::One,
            (LogicBit::Zero, LogicBit::Zero) => LogicBit::Zero,
            _ => LogicBit::X,
        };
        if let Some((a, b, w)) = self.wide_bitwise_pair(other) {
            // A KNOWN 1 on either side forces 1; two known 0s give 0; anything
            // else is x.
            let bits = Self::wide_bitwise_lanes(a, b, w, |av, ax, bv, bx| {
                let one_out = ((av & !ax) | (bv & !bx));
                let zero_out = !av & !ax & !bv & !bx;
                (one_out, !one_out & !zero_out)
            }, op_bit);
            return Self::wide_bitwise_value(bits, w);
        }
        self.bitwise_op_slow(other, op_bit)
    }

    #[inline]
    pub fn bitwise_xor(&self, other: &Value) -> Value {
        if !self.is_fill && !other.is_fill {
            if let (ValueStorage::Inline { val_bits: av, xz_bits: ax },
                    ValueStorage::Inline { val_bits: bv, xz_bits: bx })
                = (&self.storage, &other.storage)
            {
                let w = self.width.max(other.width);
                let any_xz = ax | bx;
                let result_val = (av ^ bv) & !any_xz;
                return Value { storage: ValueStorage::Inline { val_bits: result_val, xz_bits: any_xz & Self::mask(w) }, width: w, is_signed: false, is_real: false, is_fill: false };
            }
        }
        self.bitwise_xor_slow(other)
    }

    /// See `bitwise_and_slow`.
    #[cold]
    #[inline(never)]
    fn bitwise_xor_slow(&self, other: &Value) -> Value {
        if let Some((a, b)) = self.fill_pair(other) {
            return a.bitwise_xor(&b);
        }
        let op_bit = |a: LogicBit, b: LogicBit| match (a, b) {
            (LogicBit::Zero, LogicBit::Zero) | (LogicBit::One, LogicBit::One) => LogicBit::Zero,
            (LogicBit::Zero, LogicBit::One) | (LogicBit::One, LogicBit::Zero) => LogicBit::One,
            _ => LogicBit::X,
        };
        if let Some((a, b, w)) = self.wide_bitwise_pair(other) {
            // Known on BOTH sides gives their xor; any unknown gives x.
            let bits = Self::wide_bitwise_lanes(a, b, w, |av, ax, bv, bx| {
                let unknown = (ax | bx);
                ((av ^ bv) & !unknown, unknown)
            }, op_bit);
            return Self::wide_bitwise_value(bits, w);
        }
        self.bitwise_op_slow(other, op_bit)
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
                let new_bits: Vec<LogicBit> = bits.iter().map(|b| match b {
                    LogicBit::Zero => LogicBit::One,
                    LogicBit::One => LogicBit::Zero,
                    _ => LogicBit::X,
                }).collect();
                Value { storage: ValueStorage::Wide(Box::new(WidePlanes::from_bits(&new_bits))), width: self.width, is_signed: self.is_signed , is_real: false, is_fill: false }
            }
        }
    }

    /// `Some(width)` when both operands are `Wide` buffers of the SAME declared
    /// width, with at least that many bytes of storage, and a width the
    /// `MAX_WIDTH` clamp cannot touch. That is exactly the shape for which the
    /// byte-parallel bitwise path reproduces the `get_bit`/`set_bit` loop
    /// verbatim: no index reads Zero past a short operand, neither operand is
    /// narrower than the result, and `Value::zero(w)` would not have clamped.
    #[inline]
    fn wide_bitwise_pair<'v>(&'v self, other: &'v Value)
        -> Option<(&'v WidePlanes, &'v WidePlanes, usize)>
    {
        if self.width != other.width || self.width <= 64 || self.width > Self::MAX_WIDTH {
            return None;
        }
        let w = self.width as usize;
        match (&self.storage, &other.storage) {
            (ValueStorage::Wide(a), ValueStorage::Wide(b)) if a.len() >= w && b.len() >= w => {
                Some((a, b, w))
            }
            _ => None,
        }
    }

    /// Evaluate a 4-state bitwise operator over two `Wide` operands a WORD
    /// at a time.
    ///
    /// Two-plane storage makes this the trivial form: `op_lanes` is the
    /// operator's truth table as bit-parallel lane algebra over (val, xz)
    /// planes, and a plane word carries 64 payload bits — so this processes
    /// 64 bits per iteration where the byte-coded layout managed 8, with no
    /// unsafe. The `_op_bit` scalar form is retained in the signature so the
    /// call sites read unchanged; the top word is masked after the loop.
    #[inline(always)]
    fn wide_bitwise_lanes(
        a: &WidePlanes,
        b: &WidePlanes,
        w: usize,
        op_lanes: impl Fn(u64, u64, u64, u64) -> (u64, u64),
        _op_bit: impl Fn(LogicBit, LogicBit) -> LogicBit,
    ) -> WidePlanes {
        let mut out = WidePlanes::zeroed(w as u32);
        let n = out.val.len();
        for i in 0..n {
            let (rv, rx) = op_lanes(
                a.val.get(i).copied().unwrap_or(0),
                a.xz.get(i).copied().unwrap_or(0),
                b.val.get(i).copied().unwrap_or(0),
                b.xz.get(i).copied().unwrap_or(0),
            );
            out.val[i] = rv;
            out.xz[i] = rx;
        }
        out.mask_top();
        out
    }

    #[inline(always)]
    fn wide_bitwise_value(bits: WidePlanes, w: usize) -> Value {
        Value {
            storage: ValueStorage::Wide(Box::new(bits)),
            width: w as u32,
            is_signed: false,
            is_real: false,
            is_fill: false,
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
    #[inline]
    pub fn casez_eq(&self, other: &Value) -> Value {
        // `wildcard_mask` = Z on either side: Z is the only code with both the
        // value and the xz bit set. See `case_wildcard_operands`.
        if let Some((av, ax, bv, bx, m)) = self.case_wildcard_operands(other) {
            let wild = (av & ax) | (bv & bx);
            return Self::case_wildcard_result(av, ax, bv, bx, wild, m);
        }
        self.casez_eq_slow(other)
    }

    #[cold]
    #[inline(never)]
    fn casez_eq_slow(&self, other: &Value) -> Value {
        if let Some((a, b)) = self.fill_pair(other) {
            return a.casez_eq(&b);
        }
        let w = self.width.max(other.width) as usize;
        let both_signed = self.is_signed && other.is_signed;
        let sign_a = both_signed && (self.width as usize) < w;
        let sign_b = both_signed && (other.width as usize) < w;
        let top_a = if self.width > 0 { self.get_bit((self.width - 1) as usize) } else { LogicBit::Zero };
        let top_b = if other.width > 0 { other.get_bit((other.width - 1) as usize) } else { LogicBit::Zero };
        for i in 0..w {
            let a = if i < self.width as usize { self.get_bit(i) } else if sign_a { top_a } else { LogicBit::Zero };
            let b = if i < other.width as usize { other.get_bit(i) } else if sign_b { top_b } else { LogicBit::Zero };
            if a == LogicBit::Z || b == LogicBit::Z { continue; }
            if a != b { return Value::from_u64(0, 1); }
        }
        Value::from_u64(1, 1)
    }

    /// casex wildcard equality: X and Z bits on either side are
    /// treated as don't-care.
    #[inline]
    pub fn casex_eq(&self, other: &Value) -> Value {
        // `wildcard_mask` = X or Z on either side, i.e. simply "the xz bit is
        // set" — X and Z are exactly the two codes with `xz = 1`.
        if let Some((av, ax, bv, bx, m)) = self.case_wildcard_operands(other) {
            let wild = ax | bx;
            return Self::case_wildcard_result(av, ax, bv, bx, wild, m);
        }
        self.casex_eq_slow(other)
    }

    #[cold]
    #[inline(never)]
    fn casex_eq_slow(&self, other: &Value) -> Value {
        if let Some((a, b)) = self.fill_pair(other) {
            return a.casex_eq(&b);
        }
        let w = self.width.max(other.width) as usize;
        let both_signed = self.is_signed && other.is_signed;
        let sign_a = both_signed && (self.width as usize) < w;
        let sign_b = both_signed && (other.width as usize) < w;
        let top_a = if self.width > 0 { self.get_bit((self.width - 1) as usize) } else { LogicBit::Zero };
        let top_b = if other.width > 0 { other.get_bit((other.width - 1) as usize) } else { LogicBit::Zero };
        for i in 0..w {
            let a = if i < self.width as usize { self.get_bit(i) } else if sign_a { top_a } else { LogicBit::Zero };
            let b = if i < other.width as usize { other.get_bit(i) } else if sign_b { top_b } else { LogicBit::Zero };
            if matches!(a, LogicBit::X | LogicBit::Z) || matches!(b, LogicBit::X | LogicBit::Z) { continue; }
            if a != b { return Value::from_u64(0, 1); }
        }
        Value::from_u64(1, 1)
    }

    /// Shared entry test for the `casez`/`casex` bit-algebra fast paths.
    ///
    /// Returns `(a_val, a_xz, b_val, b_xz, compare_mask)` when BOTH operands
    /// are ordinary inline (≤64-bit) values, which is what every dynamic
    /// `casez`/`casex` arm in RTL actually is. Each operand's words are masked
    /// to its OWN width first, reproducing `get_bit`'s "reads Zero past
    /// `width`" rule (neither wildcard comparison sign-extends — the per-bit
    /// loops call `get_bit` for the full `max(width)` range regardless of
    /// signedness). `compare_mask` covers `max(width)` bits.
    #[inline(always)]
    fn case_wildcard_operands(&self, other: &Value) -> Option<(u64, u64, u64, u64, u64)> {
        if self.is_fill || other.is_fill || self.width > 64 || other.width > 64 {
            return None;
        }
        let (av, ax) = self.inline_bits()?;
        let (bv, bx) = other.inline_bits()?;
        let am = Self::mask(self.width);
        let bm = Self::mask(other.width);
        let (mut av, mut ax) = (av & am, ax & am);
        let (mut bv, mut bx) = (bv & bm, bx & bm);
        let w = self.width.max(other.width);
        let m = Self::mask(w);
        // §11.6.1 as applied by §12.5: operands of unequal width extend to
        // the common width, sign-replicated only when BOTH are signed. The
        // sign bit is replicated in both planes, so an X/Z sign bit extends
        // as X/Z — for casez that turns a Z sign bit into wildcard fill,
        // exactly what the per-bit reference loop produces.
        if self.is_signed && other.is_signed {
            if self.width > 0 && self.width < w {
                let ext = m & !am;
                let sign = 1u64 << (self.width - 1);
                if av & sign != 0 {
                    av |= ext;
                }
                if ax & sign != 0 {
                    ax |= ext;
                }
            }
            if other.width > 0 && other.width < w {
                let ext = m & !bm;
                let sign = 1u64 << (other.width - 1);
                if bv & sign != 0 {
                    bv |= ext;
                }
                if bx & sign != 0 {
                    bx |= ext;
                }
            }
        }
        Some((av, ax, bv, bx, m))
    }

    /// The per-bit loops keep a position when it is a wildcard on either side
    /// and otherwise demand an exact 4-state match, i.e. the result is 1 iff no
    /// non-wildcard position differs in EITHER of the two encoding planes.
    #[inline(always)]
    fn case_wildcard_result(av: u64, ax: u64, bv: u64, bx: u64, wild: u64, mask: u64) -> Value {
        let differs = ((av ^ bv) | (ax ^ bx)) & !wild & mask;
        Value::from_u64((differs == 0) as u64, 1)
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
        // §11.4.6 extends operands like the equality operators: sign-replicate
        // only when BOTH are signed (an X/Z sign bit replicates as itself).
        let both_signed = self.is_signed && other.is_signed;
        let sign_l = both_signed && (self.width as usize) < w;
        let sign_r = both_signed && (other.width as usize) < w;
        let top_l = if self.width > 0 { self.get_bit((self.width - 1) as usize) } else { LogicBit::Zero };
        let top_r = if other.width > 0 { other.get_bit((other.width - 1) as usize) } else { LogicBit::Zero };
        let mut saw_unknown = false;
        for i in 0..w {
            let l = if i < self.width as usize { self.get_bit(i) } else if sign_l { top_l } else { LogicBit::Zero };
            let r = if i < other.width as usize { other.get_bit(i) } else if sign_r { top_r } else { LogicBit::Zero };
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
                if bits.contains(&LogicBit::One) { Some(true) }
                else if bits.iter().any(|b| matches!(b, LogicBit::X | LogicBit::Z)) { None }
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
                if bits.contains(&LogicBit::Zero) { Value::from_u64(0, 1) }
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
                if bits.contains(&LogicBit::One) { Value::from_u64(1, 1) }
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

        // Wide result: build the two word planes directly. The former
        // byte-buffer construction (one byte per bit + raw-pointer stores)
        // served the byte-coded layout and is obsolete with planes; this is
        // one `splice64` per ≤64-bit run of each operand, no unsafe.
        let total = total_width as usize;
        let capped = Self::cap_width(total_width) as usize;
        let mut out = WidePlanes::zeroed(capped as u32);
        let clamped = capped != total;
        let mut len = 0usize;
        for val in values.rev() {
            let mut take = val.width as usize;
            if clamped {
                let room = capped - len;
                if room == 0 {
                    break;
                }
                if take > room {
                    take = room;
                }
            }
            match &val.storage {
                ValueStorage::Inline { val_bits, xz_bits } => {
                    out.splice64(len, *val_bits, *xz_bits, take.min(64));
                    // An Inline storage declared wider than 64 keeps the
                    // pre-existing get_bit behaviour (reads Zero) — the
                    // zeroed planes already hold that.
                }
                ValueStorage::Wide(bits) => {
                    let mut j = 0usize;
                    while j < take {
                        let n = (take - j).min(64);
                        let (v, x) = bits.extract64(j, n);
                        out.splice64(len + j, v, x, n);
                        j += n;
                    }
                }
            }
            len += take;
        }
        Value {
            storage: ValueStorage::Wide(Box::new(out)),
            width: capped as u32,
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
    fn contiguous_bit_copy_reports_changes() {
        let source = Value::from_u64(0b1010, 4);
        let mut target = Value::from_u64(0xffff, 16);
        assert!(target.copy_bits_from(5, &source, 0, 4));
        assert_eq!(target.to_u64(), Some(0xff5f));
        assert!(!target.copy_bits_from(5, &source, 0, 4));

        let mut wide_source = Value::zero(128);
        wide_source.set_bit(0, LogicBit::One);
        wide_source.set_bit(1, LogicBit::X);
        wide_source.set_bit(2, LogicBit::Z);
        wide_source.set_bit(127, LogicBit::One);
        let mut wide_target = Value::zero(256);
        assert!(wide_target.copy_bits_from(32, &wide_source, 0, 128));
        for offset in 0..128 {
            assert_eq!(wide_target.get_bit(32 + offset), wide_source.get_bit(offset));
        }
        assert_eq!(wide_target.get_bit(31), LogicBit::Zero);
        assert_eq!(wide_target.get_bit(160), LogicBit::Zero);
        assert!(!wide_target.copy_bits_from(32, &wide_source, 0, 128));
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

    /// Deterministic 4-state pattern generator for widths that are too large to
    /// enumerate exhaustively. `seed` selects the pattern.
    fn patterned(width: u32, seed: u64, signed: bool) -> Value {
        let mut v = Value::zero(width);
        v.is_signed = signed;
        let mut s = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(1);
        for i in 0..width as usize {
            s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            v.set_bit(i, LogicBit::from_code(((s >> 33) & 3) as u8));
        }
        v
    }

    /// The bit-per-byte scatter/gather helpers must be exact inverses over all
    /// 256 byte patterns — `concat_refs`, `resize` and `range_select` all encode
    /// their 4-state planes through them.
    #[test]
    fn scatter_gather_round_trip() {
        for b in 0u16..=255 {
            let b = b as u8;
            let lanes = scatter_bits_to_bytes(b);
            for i in 0..8 {
                assert_eq!(
                    (lanes >> (8 * i)) & 0xff,
                    ((b >> i) & 1) as u64,
                    "scatter byte {i} of {b:#04x}"
                );
            }
            assert_eq!(gather_byte_lsbs(lanes), b, "round trip {b:#04x}");
            // A payload in the other bit lanes must not leak into the gather.
            assert_eq!(gather_byte_lsbs(lanes | 0xfefe_fefe_fefe_fefe), b);
        }
    }

    /// Per-bit reference for the `casez`/`casex` wildcard comparisons,
    /// transcribed from the `get_bit` loops the bit-algebra fast paths replaced.
    /// Neither comparison sign-extends: positions past an operand's width read
    /// Zero regardless of signedness.
    fn case_wildcard_reference(a: &Value, b: &Value, casex: bool) -> Value {
        let w = a.width.max(b.width) as usize;
        // §11.4.6 via §11.8.2: with BOTH operands signed, the narrower one
        // sign-extends to the comparison width (its top bit repeats, X/Z
        // included); any unsigned operand makes the context unsigned and
        // everything zero-extends. Mirrors `casez_eq_slow`, which was
        // verified against a reference simulator.
        let both_signed = a.is_signed && b.is_signed;
        let ext = |v: &Value| -> LogicBit {
            if both_signed && (v.width as usize) < w && v.width > 0 {
                v.get_bit((v.width - 1) as usize)
            } else {
                LogicBit::Zero
            }
        };
        let (ext_a, ext_b) = (ext(a), ext(b));
        for i in 0..w {
            let x = if i < a.width as usize { a.get_bit(i) } else { ext_a };
            let y = if i < b.width as usize { b.get_bit(i) } else { ext_b };
            let wild = if casex {
                matches!(x, LogicBit::X | LogicBit::Z) || matches!(y, LogicBit::X | LogicBit::Z)
            } else {
                x == LogicBit::Z || y == LogicBit::Z
            };
            if wild {
                continue;
            }
            if x != y {
                return Value::from_u64(0, 1);
            }
        }
        Value::from_u64(1, 1)
    }

    // `casez_eq`/`casex_eq` grew a whole-word bit-algebra fast path for two
    // inline operands. Exhaustive over every 4-state pattern of widths 1..=4 on
    // both sides, in all four signedness combinations, plus the mixed-width
    // cases that exercise the "reads Zero past `width`" masking.
    #[test]
    fn casez_casex_match_per_bit_reference() {
        for wa in 1u32..=4 {
            for wb in 1u32..=4 {
                for ca in 0..(1usize << (2 * wa)) {
                    for cb in 0..(1usize << (2 * wb)) {
                        for sa in [false, true] {
                            for sb in [false, true] {
                                let a = four_state(ca, wa, sa);
                                let b = four_state(cb, wb, sb);
                                assert_eq!(
                                    a.casez_eq(&b),
                                    case_wildcard_reference(&a, &b, false),
                                    "casez {a} ({wa},{sa}) vs {b} ({wb},{sb})"
                                );
                                assert_eq!(
                                    a.casex_eq(&b),
                                    case_wildcard_reference(&a, &b, true),
                                    "casex {a} ({wa},{sa}) vs {b} ({wb},{sb})"
                                );
                            }
                        }
                    }
                }
            }
        }
        // Wide (>64-bit) operands still take the per-bit path, and a §5.7.1
        // fill operand still replicates before comparing.
        for w in [65u32, 96, 100] {
            for seed in 0..8u64 {
                let a = patterned(w, seed, false);
                let b = patterned(w, seed ^ 1, true);
                assert_eq!(a.casez_eq(&b), case_wildcard_reference(&a, &b, false));
                assert_eq!(a.casex_eq(&b), case_wildcard_reference(&a, &b, true));
                assert_eq!(a.casez_eq(&a), Value::from_u64(1, 1));
            }
        }
        for c in ['0', '1', 'x', 'z'] {
            let f = Value::fill_of(c);
            for code in 0..(1usize << 6) {
                let v = four_state(code, 3, false);
                let widened = f.resize(3);
                assert_eq!(f.casez_eq(&v), widened.casez_eq(&v), "fill '{c}' casez vs {v}");
                assert_eq!(f.casex_eq(&v), widened.casex_eq(&v), "fill '{c}' casex vs {v}");
            }
        }
    }

    /// Per-bit reference for `concat_refs`: append each operand's `get_bit`s
    /// LSB-first, right-most operand first, stopping at `MAX_WIDTH`.
    fn concat_reference(parts: &[Value]) -> Value {
        let total: u32 = parts.iter().map(|v| v.width).sum();
        let capped = total.min(Value::MAX_WIDTH);
        let mut out = Value::zero(capped);
        let mut off = 0usize;
        for v in parts.iter().rev() {
            for i in 0..v.width as usize {
                if off >= capped as usize {
                    break;
                }
                out.set_bit(off, v.get_bit(i));
                off += 1;
            }
        }
        out
    }

    // `concat_refs`' >64-bit arm unpacks inline operands eight bits per store
    // and memcpy's wide ones. Differential against the per-bit reference over
    // operand shapes that straddle every boundary the byte-parallel code has:
    // widths that are and are not multiples of 8, operands that are inline
    // (≤64) and wide (>64), and totals just above 64.
    #[test]
    fn wide_concat_byte_parallel_matches_reference() {
        let shapes: &[&[u32]] = &[
            &[65],
            &[64, 1],
            &[1, 64],
            &[33, 32],
            &[7, 58],
            &[3, 5, 7, 11, 13, 17, 19],
            &[72, 8],
            &[8, 72],
            &[100, 100],
            &[64, 64, 64],
            &[1; 70],
            &[0, 65, 0, 3],
            &[65, 0],
            &[130, 2, 9],
        ];
        for shape in shapes {
            for seed in 0..4u64 {
                let parts: Vec<Value> = shape
                    .iter()
                    .enumerate()
                    .map(|(i, &w)| patterned(w, seed * 31 + i as u64, i % 2 == 0))
                    .collect();
                let got = Value::concat(&parts);
                let want = concat_reference(&parts);
                assert_eq!(got.width, want.width, "width for {shape:?} seed {seed}");
                for i in 0..want.width as usize {
                    assert_eq!(
                        got.get_bit(i),
                        want.get_bit(i),
                        "bit {i} of concat {shape:?} seed {seed}"
                    );
                }
                assert_eq!(got, want, "concat {shape:?} seed {seed}");
            }
        }
    }

    // `range_select`'s Wide→Inline gather now re-packs eight source bytes per
    // multiply. It must agree with the per-bit reference for every offset and
    // every result width up to 64, including the unaligned head and tail and
    // selects that run off the end of the source.
    #[test]
    fn wide_range_select_gather_matches_reference() {
        for src_w in [65u32, 71, 128, 130] {
            for seed in 0..3u64 {
                let v = patterned(src_w, seed, seed % 2 == 0);
                for lo in 0..(src_w as usize + 4) {
                    for w in [1usize, 2, 7, 8, 9, 15, 16, 31, 63, 64] {
                        let got = v.range_select(lo + w - 1, lo);
                        let want = v.range_select_signed((lo + w - 1) as i64, lo as i64);
                        assert_eq!(
                            got, want,
                            "range_select({}, {lo}) on width {src_w} seed {seed}",
                            lo + w - 1
                        );
                    }
                }
            }
        }
    }

    // `resize_slow`'s generic arm builds its destination with a slice copy
    // (Wide→Wide) or the byte-parallel unpack (Inline→Wide) instead of driving
    // `set_bit` per bit. Same reference as `resize_matches_per_bit_reference`,
    // over widths that force the Wide paths.
    #[test]
    fn wide_resize_matches_per_bit_reference() {
        for width in [1u32, 7, 8, 33, 63, 64, 65, 70, 96, 129] {
            for seed in 0..3u64 {
                for signed in [false, true] {
                    let v = patterned(width, seed, signed);
                    for target in [1u32, 3, 8, 31, 63, 64, 65, 66, 71, 96, 128, 200] {
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
                        assert_eq!(
                            got, want,
                            "resize({target}) on width {width} seed {seed} signed {signed}"
                        );
                    }
                }
            }
        }
    }

    // `bitwise_and`/`or`/`xor` and `resize_for_assign` were split into an
    // inline two-word head and a `#[cold]` tail. Differential against the
    // per-bit truth tables / §10.7 padding rule they encode, exhaustively over
    // every 4-state pattern of widths 1..=3 on both sides and both
    // signednesses, plus §5.7.1 fill operands and `Wide` storage (which take
    // the tail).
    #[test]
    fn split_bitwise_and_assign_resize_match_reference() {
        let and = |a: LogicBit, b: LogicBit| match (a, b) {
            (LogicBit::Zero, _) | (_, LogicBit::Zero) => LogicBit::Zero,
            (LogicBit::One, LogicBit::One) => LogicBit::One,
            _ => LogicBit::X,
        };
        let or = |a: LogicBit, b: LogicBit| match (a, b) {
            (LogicBit::One, _) | (_, LogicBit::One) => LogicBit::One,
            (LogicBit::Zero, LogicBit::Zero) => LogicBit::Zero,
            _ => LogicBit::X,
        };
        let xor = |a: LogicBit, b: LogicBit| match (a, b) {
            (LogicBit::Zero, LogicBit::Zero) | (LogicBit::One, LogicBit::One) => LogicBit::Zero,
            (LogicBit::Zero, LogicBit::One) | (LogicBit::One, LogicBit::Zero) => LogicBit::One,
            _ => LogicBit::X,
        };
        // The per-bit reference the `Wide`/mixed arm still runs.
        let per_bit = |a: &Value, b: &Value, op: &dyn Fn(LogicBit, LogicBit) -> LogicBit| {
            let w = a.width.max(b.width) as usize;
            let mut r = Value::zero(w as u32);
            for i in 0..w {
                r.set_bit(i, op(a.get_bit(i), b.get_bit(i)));
            }
            r
        };
        for wa in 1u32..=3 {
            for wb in 1u32..=3 {
                for ca in 0..(1usize << (2 * wa)) {
                    for cb in 0..(1usize << (2 * wb)) {
                        for sa in [false, true] {
                            for sb in [false, true] {
                                let a = four_state(ca, wa, sa);
                                let b = four_state(cb, wb, sb);
                                for (got, want, nm) in [
                                    (a.bitwise_and(&b), per_bit(&a, &b, &and), "and"),
                                    (a.bitwise_or(&b), per_bit(&a, &b, &or), "or"),
                                    (a.bitwise_xor(&b), per_bit(&a, &b, &xor), "xor"),
                                ] {
                                    assert_eq!(
                                        got.width, want.width,
                                        "{nm} width {a} vs {b}"
                                    );
                                    for i in 0..want.width as usize {
                                        assert_eq!(
                                            got.get_bit(i),
                                            want.get_bit(i),
                                            "{nm} bit {i}: {a} vs {b}"
                                        );
                                    }
                                }
                                // §10.7 assignment padding: only a signed source
                                // with an x/z MSB extends with x/z.
                                for target in 1u32..=8 {
                                    let got = a.resize_for_assign(target);
                                    let msb = a.get_bit((wa - 1) as usize);
                                    let want = if target > wa
                                        && sa
                                        && (msb == LogicBit::X || msb == LogicBit::Z)
                                    {
                                        let mut r = a.resize(target);
                                        for i in wa as usize..target as usize {
                                            r.set_bit(i, msb);
                                        }
                                        r
                                    } else {
                                        a.resize(target)
                                    };
                                    assert_eq!(
                                        got, want,
                                        "resize_for_assign({target}) on {a} signed={sa}"
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
        // Fill operands and Wide storage take the `#[cold]` tails.
        for c in ['0', '1', 'x', 'z'] {
            let f = Value::fill_of(c);
            let v = four_state(0b11_10_01_00, 4, false);
            let w = f.resize(4);
            assert_eq!(f.bitwise_and(&v), w.bitwise_and(&v), "fill '{c}' and");
            assert_eq!(f.bitwise_or(&v), w.bitwise_or(&v), "fill '{c}' or");
            assert_eq!(f.bitwise_xor(&v), w.bitwise_xor(&v), "fill '{c}' xor");
            assert_eq!(f.resize_for_assign(5), f.resize(5), "fill '{c}' rfa");
        }
        // The byte-parallel `Wide` arm handles eight bits per word with a
        // per-bit tail, and only engages for two equal-width `Wide` buffers —
        // so cover widths that are and are not multiples of 8, and the mixed
        // shapes (unequal widths, Wide-vs-inline) that must still fall back.
        for &wa in &[65u32, 66, 71, 72, 96, 100, 128, 129] {
            for seed in 0..3u64 {
                for &wb in &[wa, wa + 1, 64, 8] {
                    let a = patterned(wa, seed, seed % 2 == 0);
                    let b = patterned(wb, seed + 7, wb % 2 == 0);
                    assert_eq!(a.bitwise_and(&b), per_bit(&a, &b, &and), "and {wa}x{wb}");
                    assert_eq!(a.bitwise_or(&b), per_bit(&a, &b, &or), "or {wa}x{wb}");
                    assert_eq!(a.bitwise_xor(&b), per_bit(&a, &b, &xor), "xor {wa}x{wb}");
                    assert_eq!(b.bitwise_and(&a), per_bit(&b, &a, &and), "and {wb}x{wa}");
                    assert_eq!(b.bitwise_or(&a), per_bit(&b, &a, &or), "or {wb}x{wa}");
                    assert_eq!(b.bitwise_xor(&a), per_bit(&b, &a, &xor), "xor {wb}x{wa}");
                }
            }
        }
        for seed in 0..4u64 {
            let a = patterned(96, seed, seed % 2 == 0);
            let b = patterned(96, seed + 7, false);
            // `ValueStorage::eq`'s Wide comparison moved to a `#[cold]` tail.
            let bits_equal = a.width == b.width
                && (0..a.width as usize).all(|i| a.get_bit(i) == b.get_bit(i));
            assert_eq!(a == b, bits_equal && a.is_signed == b.is_signed);
            assert!(a == a.clone());
            assert!(a != a.resize(97));
        }
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
            ValueStorage::Wide(bits) => bits.iter().any(|b| matches!(b, LogicBit::X | LogicBit::Z)),
        }
    }

    /// Create a value with all bits set to 1
    #[inline]
    pub fn ones(width: u32) -> Self {
        let width = Self::cap_width(width);
        if width <= 64 {
            Self::from_u64(Self::mask(width), width)
        } else {
            let bits = vec![LogicBit::One; width as usize];
            Self { storage: ValueStorage::Wide(Box::new(WidePlanes::from_bits(&bits))), width, is_signed: false, is_real: false, is_fill: false }
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
        match &self.storage {
            ValueStorage::Inline { val_bits, xz_bits } => {
                // `index < 64` keeps the shifts in range for the (rare) inline
                // value whose declared width exceeds 64.
                if index < self.width as usize && index < 64 {
                    return Value {
                        storage: ValueStorage::Inline {
                            val_bits: (*val_bits >> index) & 1,
                            xz_bits: (*xz_bits >> index) & 1,
                        },
                        width: 1, is_signed: false, is_real: false, is_fill: false,
                    };
                }
            }
            // `Wide` storage is one byte per bit and `LogicBit`'s discriminant
            // IS the `(xz << 1) | val` code, so an in-range select is a byte
            // load and two masks — the same result `bit_select_slow` produced,
            // without the out-of-line call. `index < self.width` rules out
            // §11.5.1's x-on-overrun, and a short buffer still falls through.
            ValueStorage::Wide(bits) => {
                if index < self.width as usize {
                    {
                        let code = bits.get(index) as u64;
                        return Value {
                            storage: ValueStorage::Inline {
                                val_bits: code & 1,
                                xz_bits: (code >> 1) & 1,
                            },
                            width: 1, is_signed: false, is_real: false, is_fill: false,
                        };
                    }
                }
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
        // Same result as `Value::zero(1)` + `set_bit(0, get_bit(index))` —
        // `get_bit_code`'s code is exactly (xz << 1) | val, which is how
        // `set_bit` lays a `LogicBit` into the two inline words — but built in
        // one step instead of a constructor plus a read-modify-write.
        let code = self.get_bit_code(index) as u64;
        Value {
            storage: ValueStorage::Inline { val_bits: code & 1, xz_bits: (code >> 1) & 1 },
            width: 1, is_signed: false, is_real: false, is_fill: false,
        }
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
            // Wide → Wide fast path for width > 64: replace the per-bit
            // get_bit/set_bit loop with a single slice copy. The source
            // already stores `Vec<LogicBit>` (1 byte per bit) so the copy
            // is just a memcpy.
            if width > 64 {
                // Plane shift-copy: each destination word gathers from the
                // (at most two) source words it straddles; out-of-range
                // source words read 0, matching get_bit's Zero.
                let mut out = WidePlanes::zeroed(width as u32);
                let (wi0, off) = (lo / 64, lo % 64);
                let n = out.val.len();
                for wi in 0..n {
                    let take = |plane: &[u64]| -> u64 {
                        let lo64 = plane.get(wi0 + wi).copied().unwrap_or(0) >> off;
                        let hi64 = if off > 0 {
                            plane.get(wi0 + wi + 1).copied().unwrap_or(0) << (64 - off)
                        } else {
                            0
                        };
                        lo64 | hi64
                    };
                    out.val[wi] = take(&bits.val);
                    out.xz[wi] = take(&bits.xz);
                }
                out.mask_top();
                return Value {
                    storage: ValueStorage::Wide(Box::new(out)),
                    width: width as u32,
                    is_signed: false,
                    is_real: false, is_fill: false,
                };
            }
            if width <= 64 {
                // Plane extraction, same shape as slice_bits_swar.
                let mask = if width >= 64 { u64::MAX } else { (1u64 << width) - 1 };
                let (wi, off) = (lo / 64, lo % 64);
                let take = |plane: &[u64]| -> u64 {
                    let lo64 = plane.get(wi).copied().unwrap_or(0) >> off;
                    let hi64 = if off > 0 {
                        plane.get(wi + 1).copied().unwrap_or(0) << (64 - off)
                    } else {
                        0
                    };
                    (lo64 | hi64) & mask
                };
                let val_bits = take(&bits.val);
                let xz_bits = take(&bits.xz);
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
                // Equal lengths (the norm — a signal keeps its width) copy
                // straight over the existing buffer: one memcpy, no length
                // store, no capacity check, and no `RawVec::grow` call kept
                // alive on the path. Only a genuine width change needs the
                // clear + reserve + extend dance.
                if sv.nbits == ov.nbits {
                    sv.val.copy_from_slice(&ov.val);
                    sv.xz.copy_from_slice(&ov.xz);
                } else {
                    **sv = (**ov).clone();
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
    /// Create a value with all bits set to X (§6.6.4: a never-driven `trireg`
    /// reads x, unlike other nets' z).
    #[inline]
    pub fn all_x(width: u32) -> Self {
        if width <= 64 {
            // Inline encoding: xz_bits marks X/Z, val_bits picks Z (1) vs X (0).
            Self {
                storage: ValueStorage::Inline { val_bits: 0, xz_bits: Self::mask(width) },
                width,
                is_signed: false, is_real: false, is_fill: false,
            }
        } else {
            Self {
                storage: ValueStorage::Wide(Box::new(WidePlanes::filled(width, LogicBit::X))),
                width,
                is_signed: false, is_real: false, is_fill: false,
            }
        }
    }

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
                storage: ValueStorage::Wide(Box::new(WidePlanes::filled(width, LogicBit::Z))),
                width,
                is_signed: false, is_real: false, is_fill: false,
            }
        }
    }
}

#[cfg(test)]
mod wide_probe_tests {
    use super::*;

    #[test]
    fn from_bits_roundtrip() {
        let mut bits = vec![LogicBit::Zero; 96];
        bits[0] = LogicBit::One;
        bits[2] = LogicBit::One;
        bits[95] = LogicBit::One;
        let p = WidePlanes::from_bits(&bits);
        assert_eq!(p.get(0), LogicBit::One);
        assert_eq!(p.get(1), LogicBit::Zero);
        assert_eq!(p.get(2), LogicBit::One);
        assert_eq!(p.get(95), LogicBit::One);
        assert_eq!(p.val[0], 0b101);
        assert_eq!(p.val[1], 1u64 << 31);
    }

    #[test]
    fn concat_wide_probe() {
        let hn = Value::from_u64(0b101, 3);
        let z = Value::zero(93);
        let c = Value::concat(&[z, hn]);
        assert_eq!(c.width, 96);
        assert_eq!(c.get_bit(0), LogicBit::One, "bit0");
        assert_eq!(c.get_bit(1), LogicBit::Zero, "bit1");
        assert_eq!(c.get_bit(2), LogicBit::One, "bit2");
        assert_eq!(c.to_u128() & 0x7, 0b101);
    }
}
