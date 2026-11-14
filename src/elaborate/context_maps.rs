//! Share immutable instance type contexts without depending on map order.

use crate::hasher::{DeterministicState, HashMap};
use serde::{Serialize, Serializer, ser::SerializeMap};
use std::hash::{BuildHasher, Hasher};
use std::rc::{Rc, Weak};

pub(super) struct MapInterner<V> {
    maps: HashMap<(u64, usize), Weak<HashMap<String, V>>>,
}

impl<V> Default for MapInterner<V> {
    fn default() -> Self {
        Self {
            maps: HashMap::default(),
        }
    }
}

impl<V: Serialize> MapInterner<V> {
    pub(super) fn intern(&mut self, map: HashMap<String, V>) -> Rc<HashMap<String, V>> {
        let value = Rc::new(map);
        let Ok(bytes) =
            bincode::serde::encode_to_vec(&OrderedMap(&value), crate::xez_bincode_config())
        else {
            return value;
        };
        let mut hash = DeterministicState::default().build_hasher();
        hash.write(&bytes);
        self.intern_encoded(value, &bytes, (hash.finish(), bytes.len()))
    }

    fn intern_encoded(
        &mut self,
        value: Rc<HashMap<String, V>>,
        bytes: &[u8],
        key: (u64, usize),
    ) -> Rc<HashMap<String, V>> {
        if let Some(candidate) = self.maps.get(&key).and_then(Weak::upgrade) {
            if bincode::serde::encode_to_vec(&OrderedMap(&candidate), crate::xez_bincode_config())
                .is_ok_and(|encoded| encoded.as_slice() == bytes)
            {
                return candidate;
            }
        }
        // An eager program body or an instance without deferred bodies may
        // discard its context immediately. The index must not retain it.
        // A hash collision only replaces this reuse candidate; full bytes
        // above decide equality, so distinct contexts can never alias.
        self.maps.insert(key, Rc::downgrade(&value));
        value
    }

    #[cfg(test)]
    pub(super) fn intern_bucket(
        &mut self,
        map: HashMap<String, V>,
        key: (u64, usize),
    ) -> Rc<HashMap<String, V>> {
        let value = Rc::new(map);
        let bytes = bincode::serde::encode_to_vec(&OrderedMap(&value), crate::xez_bincode_config())
            .unwrap();
        self.intern_encoded(value, &bytes, key)
    }
}

struct OrderedMap<'a, V>(&'a HashMap<String, V>);

impl<V: Serialize> Serialize for OrderedMap<'_, V> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        // §6.20.3: a type context's identity includes every binding. The
        // exact interner compares complete syntax, including source spans;
        // sort only the map entries so insertion order cannot prevent reuse.
        let mut entries: Vec<_> = self.0.iter().collect();
        entries.sort_unstable_by(|a, b| a.0.cmp(b.0));
        let mut map = serializer.serialize_map(Some(entries.len()))?;
        for (name, value) in entries {
            map.serialize_entry(name, value)?;
        }
        map.end()
    }
}
