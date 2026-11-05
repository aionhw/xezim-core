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
        // Encode incoming syntax once (§9.2, §13.3/§13.4). The temporary
        // buffer also supplies exact comparison on a hit; only canonical AST
        // handles are retained, so the index never holds serialized copies.
        let Ok(bytes) = bincode::serde::encode_to_vec(&value, crate::xez_bincode_config()) else {
            return value;
        };
        let mut hash = DeterministicState::default().build_hasher();
        hash.write(&bytes);
        let key = (hash.finish(), bytes.len() as u64);
        self.intern_encoded(value, &bytes, key)
    }

    fn intern_encoded(&mut self, value: T, bytes: &[u8], key: (u64, u64)) -> T {
        let bucket = self.buckets.entry(key).or_default();
        if !bucket.is_empty() {
            for candidate in bucket.iter() {
                let mut compare = CompareWriter {
                    expected: bytes,
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

    #[cfg(test)]
    fn intern_bucket(&mut self, value: T, key: (u64, u64)) -> T {
        let bytes = bincode::serde::encode_to_vec(&value, crate::xez_bincode_config()).unwrap();
        self.intern_encoded(value, &bytes, key)
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

    /// Incoming syntax must be encoded once even when an equal body exists.
    #[test]
    fn cache_hit_encodes_incoming_body_once() {
        use std::cell::Cell;
        #[derive(Clone)]
        struct Counted(Rc<String>, Rc<Cell<usize>>);
        impl Serialize for Counted {
            fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
                self.1.set(self.1.get() + 1);
                self.0.serialize(s)
            }
        }
        let mut pool = AstInterner::default();
        let first_count = Rc::new(Cell::new(0));
        let first = pool.intern(Counted(Rc::new("body".into()), first_count.clone()));
        assert_eq!(first_count.get(), 1);
        let next_count = Rc::new(Cell::new(0));
        let hit = pool.intern(Counted(Rc::new("body".into()), next_count.clone()));
        assert_eq!(next_count.get(), 1);
        assert!(Rc::ptr_eq(&first.0, &hit.0));
        assert_eq!(first_count.get(), 2, "canonical body is compared exactly");
    }
}
