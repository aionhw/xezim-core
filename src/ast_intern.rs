//! Exact sharing of immutable syntax within one elaboration pass (#721).
//!
//! Hashes only select candidates. Equality compares the complete serialized
//! syntax, including spans, so collisions cannot alias different programs.
//! Derived evaluator caches are serde-skipped and are not syntax identity.

use crate::hasher::{DeterministicState, HashMap};
use serde::Serialize;
use std::hash::{BuildHasher, Hasher};
use std::io::{self, Write};

pub(crate) struct AstInterner<T> {
    buckets: HashMap<(u64, u64), Vec<T>>,
}

impl<T> Default for AstInterner<T> {
    fn default() -> Self {
        Self {
            buckets: HashMap::default(),
        }
    }
}

struct HashWriter<H> {
    hash: H,
    bytes: u64,
}

impl<H: Hasher> Write for HashWriter<H> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        self.hash.write(bytes);
        self.bytes += bytes.len() as u64;
        Ok(bytes.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

struct CompareWriter<'a> {
    expected: &'a [u8],
    position: usize,
    equal: bool,
}

impl Write for CompareWriter<'_> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        let end = self.position.saturating_add(bytes.len());
        self.equal &= self.expected.get(self.position..end) == Some(bytes);
        self.position = end;
        Ok(bytes.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

impl<T: Serialize + Clone> AstInterner<T> {
    pub(crate) fn intern(&mut self, value: T) -> T {
        let mut writer = HashWriter {
            hash: DeterministicState::default().build_hasher(),
            bytes: 0,
        };
        if bincode::serde::encode_into_std_write(&value, &mut writer, crate::xez_bincode_config())
            .is_err()
        {
            return value;
        }
        self.intern_bucket(value, (writer.hash.finish(), writer.bytes))
    }

    fn intern_bucket(&mut self, value: T, key: (u64, u64)) -> T {
        let bucket = self.buckets.entry(key).or_default();
        if !bucket.is_empty() {
            // Only a hash match needs this temporary buffer. No serialized
            // payload is retained in the interner, and existing candidates
            // stream into a comparator rather than allocating a second copy.
            let Ok(bytes) = bincode::serde::encode_to_vec(&value, crate::xez_bincode_config())
            else {
                return value;
            };
            for candidate in bucket.iter() {
                let mut compare = CompareWriter {
                    expected: &bytes,
                    position: 0,
                    equal: true,
                };
                if bincode::serde::encode_into_std_write(
                    candidate,
                    &mut compare,
                    crate::xez_bincode_config(),
                )
                .is_ok()
                    && compare.equal
                    && compare.position == bytes.len()
                {
                    return candidate.clone();
                }
            }
        }
        bucket.push(value.clone());
        value
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::rc::Rc;

    /// §9.2: sharing syntax must never change the process it represents,
    /// even when different bodies collide in the hash lookup.
    #[test]
    fn collisions_compare_complete_syntax() {
        let mut pool = AstInterner::default();
        let first = pool.intern_bucket(Rc::new("x".to_string()), (0, 2));
        let different = pool.intern_bucket(Rc::new("y".to_string()), (0, 2));
        let same = pool.intern_bucket(Rc::new("x".to_string()), (0, 2));
        assert!(!Rc::ptr_eq(&first, &different));
        assert!(Rc::ptr_eq(&first, &same));
        assert_eq!(different.as_str(), "y");
    }
}
