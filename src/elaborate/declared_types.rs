use super::{DataType, HashMap};
use std::collections::BTreeSet;
use std::ops::{Bound, Deref, DerefMut};
use std::sync::OnceLock;

/// Declared types keep their map representation in compiled artifacts.
/// Struct-local scope switches also need the keys beneath one dotted prefix.
#[derive(Debug, Default, serde::Serialize, serde::Deserialize)]
#[serde(transparent)]
pub struct DeclaredTypes {
    map: HashMap<String, DataType>,
    #[serde(skip)]
    dotted: OnceLock<BTreeSet<String>>,
}

impl DeclaredTypes {
    pub fn with_prefix<'a>(
        &'a self,
        prefix: &'a str,
    ) -> impl Iterator<Item = (&'a String, &'a DataType)> {
        assert!(prefix.contains('.'));
        let keys = self.dotted.get_or_init(|| {
            self.map
                .keys()
                .filter(|key| key.contains('.'))
                .cloned()
                .collect()
        });
        keys.range::<str, _>((Bound::Included(prefix), Bound::Unbounded))
            .take_while(move |key| key.starts_with(prefix))
            .map(|key| (key, &self.map[key]))
    }

    pub fn insert(&mut self, key: String, value: DataType) -> Option<DataType> {
        if let Some(keys) = self.dotted.get_mut()
            && key.contains('.')
            && !self.map.contains_key(&key)
        {
            keys.insert(key.clone());
        }
        self.map.insert(key, value)
    }

    pub fn remove(&mut self, key: &str) -> Option<DataType> {
        if key.contains('.')
            && let Some(keys) = self.dotted.get_mut()
        {
            keys.remove(key);
        }
        self.map.remove(key)
    }

    pub fn get_mut(&mut self, key: &str) -> Option<&mut DataType> {
        self.map.get_mut(key)
    }
}

impl Deref for DeclaredTypes {
    type Target = HashMap<String, DataType>;

    fn deref(&self) -> &Self::Target {
        &self.map
    }
}

impl DerefMut for DeclaredTypes {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // Bulk edits and callers taking the raw map can change keys arbitrarily.
        self.dotted.take();
        &mut self.map
    }
}

impl<'a> IntoIterator for &'a DeclaredTypes {
    type Item = (&'a String, &'a DataType);
    type IntoIter = std::collections::hash_map::Iter<'a, String, DataType>;

    fn into_iter(self) -> Self::IntoIter {
        self.map.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn member_lookup_tracks_key_changes_and_loads_plain_maps() {
        let ty = DataType::Void(crate::ast::Span::new(0, 0));
        let mut original = HashMap::default();
        for key in ["s", "s.a", "s.a.b", "ss.a"] {
            original.insert(key.to_string(), ty.clone());
        }
        let cfg = bincode::config::standard();
        let bytes = bincode::serde::encode_to_vec(&original, cfg).unwrap();
        let (mut types, _): (DeclaredTypes, _) =
            bincode::serde::decode_from_slice(&bytes, cfg).unwrap();
        let members = |types: &DeclaredTypes| {
            types
                .with_prefix("s.")
                .map(|(k, _)| k.clone())
                .collect::<Vec<_>>()
        };
        assert_eq!(members(&types), ["s.a", "s.a.b"]);
        types.remove("s.a");
        types.insert("s.c".into(), ty.clone());
        assert_eq!(members(&types), ["s.a.b", "s.c"]);
        // Bulk mutable access may replace keys without changing the map length.
        let raw: &mut HashMap<_, _> = &mut types;
        raw.remove("s.a.b");
        raw.insert("s.d".into(), ty);
        assert_eq!(members(&types), ["s.c", "s.d"]);
        assert_eq!(
            bincode::serde::encode_to_vec(&types, cfg).unwrap(),
            bincode::serde::encode_to_vec(&types.map, cfg).unwrap()
        );
    }
}
