//! Packed value storage for wide signals (>64 bits).
//!
//! This module provides a memory-efficient representation for wide 4-state
//! logic values. Instead of using 1 byte per bit (Vec<LogicBit>), it packs
//! 4 bits per byte using 2 bits per bit:
//!
//! - 00 = Zero
//! - 01 = One  
//! - 10 = X
//! - 11 = Z
//!
//! This provides a **4× memory reduction** compared to `Vec<LogicBit>` for
//! wide signals, with only slight overhead for bit access.
//!
//! # Usage
//!
//! This module is intended to eventually replace `ValueStorage::Wide` in the
//! `Value` type. For now, it's a separate implementation that can be tested
//! and benchmarked independently.

use serde::{Serialize, Deserialize};
use crate::value::LogicBit;

/// Packed storage for wide 4-state logic values.
///
/// Each byte stores 4 bits using 2 bits per bit:
/// ```text
/// Byte:  b7 b6 b5 b4  b3 b2 b1 b0
/// Bits:  bit3       bit2       bit1       bit0
///        [1:0]     [3:2]     [5:4]     [7:6]
/// ```
///
/// Encoding:
/// - 0b00 = Zero
/// - 0b01 = One
/// - 0b10 = X
/// - 0b11 = Z
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct PackedBits {
    /// Packed bits: 4 bits per byte (2 bits per logic bit)
    data: Vec<u8>,
    /// Number of actual bits stored (may be less than data.len() * 4)
    len: u32,
}

impl PackedBits {
    /// Create a new empty PackedBits.
    pub fn new() -> Self {
        Self { data: Vec::new(), len: 0 }
    }

    /// Create PackedBits with given width, all bits initialized to X.
    pub fn new_x(width: u32) -> Self {
        Self::new_fill(width, LogicBit::X)
    }

    /// Create PackedBits with given width, all bits initialized to Zero.
    pub fn new_zero(width: u32) -> Self {
        let num_bytes = Self::bytes_needed(width);
        Self {
            data: vec![0x00; num_bytes],
            len: width,
        }
    }

    /// Create PackedBits with given width, all bits initialized to specified value.
    ///
    /// The unused slots above `width` in the last byte (the padding bits) are
    /// masked back to Zero. This keeps the invariant that `has_xz`, `==` and
    /// `Hash` only observe the `width` live bits — without it, an all-X
    /// `new_x(66)` would read X in the two padding slots of the 17th byte and
    /// `has_xz()` would report true, and two values with identical live bits
    /// but different construction histories could compare unequal.
    pub fn new_fill(width: u32, bit: LogicBit) -> Self {
        let code = bit.to_code();
        let fill_byte = code * 0x55;  // Replicate 2-bit code across byte
        let num_bytes = Self::bytes_needed(width);
        let mut data = vec![fill_byte; num_bytes];
        let pad = width % 4;
        if pad != 0 {
            data[num_bytes - 1] &= (1u8 << (pad * 2)) - 1;
        }
        Self { data, len: width }
    }

    /// Calculate number of bytes needed to store `num_bits` bits.
    #[inline]
    fn bytes_needed(num_bits: u32) -> usize {
        ((num_bits as usize + 3) / 4).max(1)
    }

    /// Get the number of bits stored.
    #[inline]
    pub fn len(&self) -> u32 {
        self.len
    }

    /// Check if empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Get bit at position i.
    /// Returns LogicBit::Zero if i >= len.
    #[inline]
    pub fn get(&self, i: usize) -> LogicBit {
        if i >= self.len as usize {
            return LogicBit::Zero;
        }
        let byte_idx = i / 4;
        let shift = (i % 4) * 2;
        let code = (self.data[byte_idx] >> shift) & 0b11;
        LogicBit::from_code(code)
    }

    /// Set bit at position i.
    /// Returns true if the bit changed.
    #[inline]
    pub fn set(&mut self, i: usize, bit: LogicBit) -> bool {
        if i >= self.len as usize {
            return false;
        }
        let byte_idx = i / 4;
        let shift = (i % 4) * 2;
        let code = bit.to_code();
        let mask = 0b11 << shift;
        let old = self.data[byte_idx];
        let new = (old & !mask) | ((code as u8) << shift);
        if old == new {
            return false;
        }
        self.data[byte_idx] = new;
        true
    }

    /// Check if any bit is X or Z.
    #[inline]
    pub fn has_xz(&self) -> bool {
        // Check if any byte has bits 2-3 or 6-7 set (X or Z codes)
        for &byte in &self.data {
            // Mask out the high bit of each 2-bit code (bit 1 of each pair)
            // For X (10): high bit is 1, low bit is 0
            // For Z (11): high bit is 1, low bit is 1
            // So we check if any high bit is set (X or Z)
            if (byte & 0b10101010) != 0 {
                return true;
            }
        }
        false
    }

    /// Extract the low 64 bits as (val_bits, xz_bits).
    /// Used for compatibility with inline storage operations.
    #[inline]
    pub fn raw_bits_low64(&self) -> (u64, u64) {
        let mut val_bits = 0u64;
        let mut xz_bits = 0u64;
        let num_bits = (64).min(self.len as usize);
        for i in 0..num_bits {
            match self.get(i) {
                LogicBit::Zero => {},
                LogicBit::One => val_bits |= 1u64 << i,
                LogicBit::X => xz_bits |= 1u64 << i,
                LogicBit::Z => { val_bits |= 1u64 << i; xz_bits |= 1u64 << i; },
            }
        }
        (val_bits, xz_bits)
    }

    /// Iterate over bits.
    pub fn iter(&self) -> PackedBitsIter<'_> {
        PackedBitsIter {
            data: &self.data,
            len: self.len as usize,
            index: 0,
        }
    }

    /// Get the underlying data for serialization.
    pub fn data(&self) -> &[u8] {
        &self.data
    }

    /// Memory size in bytes.
    pub fn memory_size(&self) -> usize {
        self.data.capacity()
    }

    /// Build from raw packed bytes and an explicit bit length (deserialization
    /// / slice-copy fast path). The caller guarantees `data` holds
    /// `Self::bytes_needed(len)` bytes.
    pub fn from_data(data: Vec<u8>, len: u32) -> Self {
        Self { data, len }
    }

    /// Build by appending bits in LSB-first order.
    pub fn from_bits(bits: impl IntoIterator<Item = LogicBit>) -> Self {
        let mut pb = PackedBits::new();
        for b in bits {
            pb.push(b);
        }
        pb
    }

    /// Append a single bit, growing the backing byte as needed.
    pub fn push(&mut self, bit: LogicBit) {
        if self.len % 4 == 0 {
            self.data.push(0);
        }
        let byte_idx = self.data.len() - 1;
        let shift = (self.len % 4) * 2;
        self.data[byte_idx] |= bit.to_code() << shift;
        self.len += 1;
    }

    /// A new packed value of `new_len` bits: the overlap with `self` is copied
    /// and any remaining bits are filled with `fill` (§10.7 resize semantics).
    pub fn resized(&self, new_len: u32, fill: LogicBit) -> Self {
        let mut out = PackedBits::new_fill(new_len, fill);
        let copy = new_len.min(self.len);
        for i in 0..copy as usize {
            out.set(i, self.get(i));
        }
        out
    }

    /// Map every bit through `f` in place (2-state coercion, bitwise NOT, …).
    pub fn transform(&mut self, mut f: impl FnMut(LogicBit) -> LogicBit) {
        for i in 0..self.len as usize {
            self.set(i, f(self.get(i)));
        }
    }

    /// Mutable access to the packed bytes (length-preserving writes).
    pub fn data_mut(&mut self) -> &mut [u8] {
        &mut self.data
    }
}

impl Default for PackedBits {
    fn default() -> Self {
        Self::new()
    }
}

/// Iterator over packed bits.
pub struct PackedBitsIter<'a> {
    data: &'a [u8],
    len: usize,
    index: usize,
}

impl<'a> Iterator for PackedBitsIter<'a> {
    type Item = LogicBit;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.len {
            return None;
        }
        let byte_idx = self.index / 4;
        let shift = (self.index % 4) * 2;
        let code = (self.data[byte_idx] >> shift) & 0b11;
        self.index += 1;
        Some(LogicBit::from_code(code))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.len - self.index;
        (remaining, Some(remaining))
    }
}

impl ExactSizeIterator for PackedBitsIter<'_> {}

/// Benchmark comparison between Vec<LogicBit> and PackedBits.
#[cfg(test)]
mod benchmarks {
    use super::*;
    use std::time::Instant;

    fn create_wide_value(width: usize) -> Vec<LogicBit> {
        (0..width)
            .map(|i| {
                match i % 4 {
                    0 => LogicBit::Zero,
                    1 => LogicBit::One,
                    2 => LogicBit::X,
                    _ => LogicBit::Z,
                }
            })
            .collect()
    }

    fn create_packed_value(width: usize) -> PackedBits {
        let mut pb = PackedBits::new_x(width as u32);
        for i in 0..width {
            let bit = match i % 4 {
                0 => LogicBit::Zero,
                1 => LogicBit::One,
                2 => LogicBit::X,
                _ => LogicBit::Z,
            };
            pb.set(i, bit);
        }
        pb
    }

    #[test]
    fn test_packed_vs_wide_memory() {
        let width = 10000;  // 10K bits
        
        let wide = create_wide_value(width);
        let packed = create_packed_value(width);
        
        // Vec<LogicBit> uses 1 byte per bit (enum with repr u8)
        let wide_size = wide.capacity() * std::mem::size_of::<LogicBit>();
        // PackedBits uses ~1 byte per 4 bits (2 bits per bit encoding)
        let packed_size = packed.memory_size();
        
        println!("Width: {} bits", width);
        println!("Vec<LogicBit> size: {} bytes ({:.2} KB)", wide_size, wide_size as f64 / 1024.0);
        println!("PackedBits size: {} bytes ({:.2} KB)", packed_size, packed_size as f64 / 1024.0);
        println!("Reduction: {:.1}x", wide_size as f64 / packed_size as f64);
        
        // Should be ~4x reduction (1 byte/bit -> 0.25 bytes/bit)
        assert!(wide_size > packed_size * 3);  // At least 3x reduction
    }

    #[test]
    fn test_packed_access() {
        let width = 1000;
        let packed = create_packed_value(width);
        
        // Test all access patterns
        for i in 0..width {
            let bit = packed.get(i);
            let expected = match i % 4 {
                0 => LogicBit::Zero,
                1 => LogicBit::One,
                2 => LogicBit::X,
                _ => LogicBit::Z,
            };
            assert_eq!(bit, expected);
        }
    }

    #[test]
    fn test_packed_has_xz() {
        use crate::value::LogicBit;
        let mut pb = PackedBits::new_zero(100);
        assert!(!pb.has_xz());
        
        pb.set(10, LogicBit::X);
        assert!(pb.has_xz());
        
        pb.set(10, LogicBit::Zero);
        assert!(!pb.has_xz());
        
        pb.set(20, LogicBit::Z);
        assert!(pb.has_xz());
    }
}
