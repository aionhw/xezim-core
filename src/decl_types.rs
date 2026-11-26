//! Declared types of signals and value parameters (IEEE 1800-2023 §6.8,
//! §6.20.2), one shared copy per declaration (aionhw/xezim#721).
//!
//! Every signal records the data type it was declared with. The instances of
//! a definition declare the same types, and so do the declarators of one
//! declaration; holding a private copy of the type tree in each signal's
//! entry made it the largest per-signal cost of a design. A [`DeclTypeMap`]
//! holds each type behind an `Rc`, and a [`DeclTypeInterner`] hands the
//! signals of one declaration the same one. A [`ParamDeclTypeMap`] does the
//! same for the explicitly typed value parameters.
//!
//! A shared type is immutable. Its contextual evaluator caches (widths,
//! resolved names) are disabled, so reading it for one instance never leaves
//! a result behind for another; what a name in a dimension resolves to stays
//! a property of the signal the type is read for.

use crate::ast::types::DataType;
use crate::hasher::{DeterministicState, HashMap};
use crate::shared_names::{self, SharedName, SharedNameMap};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeSet, hash_map};
use std::hash::{BuildHasher, Hasher};
use std::ops::Bound;
use std::rc::Rc;
use std::sync::OnceLock;

/// Signal name to declared type, with the borrowed `String`-key API of the
/// map it replaces. Serde keeps the plain map representation: a shared type
/// is written once per entry and read back as an entry of its own.
///
/// `dotted` orders the keys that hold a `.`, built on the first
/// [`DeclTypeMap::with_prefix`] and kept current by `insert` and `remove`,
/// so the members beneath one name are read without visiting every signal.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(transparent)]
pub struct DeclTypeMap {
    map: HashMap<String, Rc<DataType>>,
    #[serde(skip)]
    dotted: OnceLock<BTreeSet<String>>,
}

impl DeclTypeMap {
    pub fn len(&self) -> usize {
        self.map.len()
    }
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
    pub fn get(&self, name: &str) -> Option<&DataType> {
        self.map.get(name).map(|ty| &**ty)
    }
    /// The entry itself, for a caller that records the same type again.
    pub fn get_shared(&self, name: &str) -> Option<&Rc<DataType>> {
        self.map.get(name)
    }
    pub fn get_key_value(&self, name: &str) -> Option<(&String, &Rc<DataType>)> {
        self.map.get_key_value(name)
    }
    pub fn contains_key(&self, name: &str) -> bool {
        self.map.contains_key(name)
    }
    /// The entries whose key starts with `prefix` (a name and its `.`), in
    /// key order.
    pub fn with_prefix<'a>(
        &'a self,
        prefix: &'a str,
    ) -> impl Iterator<Item = (&'a String, &'a Rc<DataType>)> {
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
            .filter_map(|key| self.map.get_key_value(key.as_str()))
    }
    /// The type of `name`, for changing it. A type other signals hold too is
    /// copied first: they keep the one they had.
    pub fn get_mut(&mut self, name: &str) -> Option<&mut DataType> {
        self.map.get_mut(name).map(Rc::make_mut)
    }
    /// Record `ty` for `name` alone. Returns the type `name` had.
    pub fn insert(&mut self, name: String, ty: DataType) -> Option<Rc<DataType>> {
        self.insert_shared(name, Rc::new(ty))
    }
    /// Record a type that other signals hold too.
    pub fn insert_shared(&mut self, name: String, ty: Rc<DataType>) -> Option<Rc<DataType>> {
        if let Some(keys) = self.dotted.get_mut()
            && name.contains('.')
            && !self.map.contains_key(&name)
        {
            keys.insert(name.clone());
        }
        self.map.insert(name, ty)
    }
    pub fn remove(&mut self, name: &str) -> Option<Rc<DataType>> {
        if name.contains('.')
            && let Some(keys) = self.dotted.get_mut()
        {
            keys.remove(name);
        }
        self.map.remove(name)
    }
    /// The entry of `name`, to give it a type when it has none.
    pub fn entry(&mut self, name: String) -> Entry<'_> {
        self.dotted.take();
        Entry(self.map.entry(name))
    }
    pub fn retain(&mut self, mut keep: impl FnMut(&String, &DataType) -> bool) {
        self.dotted.take();
        self.map.retain(|name, ty| keep(name, ty));
    }
    /// The entries themselves, for code that moves them between tables.
    pub fn as_map(&self) -> &HashMap<String, Rc<DataType>> {
        &self.map
    }
    pub fn as_map_mut(&mut self) -> &mut HashMap<String, Rc<DataType>> {
        // The caller may change any key.
        self.dotted.take();
        &mut self.map
    }
    pub fn iter(&self) -> Iter<'_> {
        Iter(self.map.iter())
    }
    pub fn keys(&self) -> hash_map::Keys<'_, String, Rc<DataType>> {
        self.map.keys()
    }
    pub fn values(&self) -> impl Iterator<Item = &DataType> {
        self.map.values().map(|ty| &**ty)
    }
}

impl std::ops::Index<&str> for DeclTypeMap {
    type Output = DataType;
    fn index(&self, name: &str) -> &DataType {
        &self.map[name]
    }
}

pub struct Entry<'a>(hash_map::Entry<'a, String, Rc<DataType>>);

impl Entry<'_> {
    pub fn or_insert_with(self, make: impl FnOnce() -> DataType) {
        self.0.or_insert_with(|| Rc::new(make()));
    }
    pub fn or_insert(self, ty: DataType) {
        self.0.or_insert_with(|| Rc::new(ty));
    }
}

pub struct Iter<'a>(hash_map::Iter<'a, String, Rc<DataType>>);

impl<'a> Iterator for Iter<'a> {
    type Item = (&'a String, &'a DataType);
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(name, ty)| (name, &**ty))
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<'a> IntoIterator for &'a DeclTypeMap {
    type Item = (&'a String, &'a DataType);
    type IntoIter = Iter<'a>;
    fn into_iter(self) -> Iter<'a> {
        self.iter()
    }
}

/// Value parameter name to declared type (§6.20.2), keyed as the parameter
/// table is. Serde keeps the plain map representation, as [`DeclTypeMap`]
/// does.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(transparent)]
pub struct ParamDeclTypeMap(SharedNameMap<Rc<DataType>>);

impl ParamDeclTypeMap {
    pub fn len(&self) -> usize {
        self.0.len()
    }
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    pub fn get(&self, name: &str) -> Option<&DataType> {
        self.0.get(name).map(|ty| &**ty)
    }
    /// The entry itself, which the parameters of one declaration share.
    pub fn get_shared(&self, name: &str) -> Option<&Rc<DataType>> {
        self.0.get(name)
    }
    pub fn contains_key(&self, name: &str) -> bool {
        self.0.contains_key(name)
    }
    /// The key of `name`, which the tables keyed by it share.
    pub fn shared_key(&self, name: &str) -> Option<&SharedName> {
        self.0.shared_key(name)
    }
    /// Record a type that other parameters may hold too. Returns the type
    /// `name` had.
    pub fn insert_shared<K: Into<SharedName>>(
        &mut self,
        name: K,
        ty: Rc<DataType>,
    ) -> Option<Rc<DataType>> {
        self.0.insert(name, ty)
    }
    pub fn keys(&self) -> shared_names::Keys<'_, Rc<DataType>> {
        self.0.keys()
    }
    pub fn iter(&self) -> impl Iterator<Item = (&String, &DataType)> + Clone {
        self.0.iter().map(|(name, ty)| (name, &**ty))
    }
}

impl<'a> IntoIterator for &'a ParamDeclTypeMap {
    type Item = (&'a String, &'a DataType);
    type IntoIter = ParamIter<'a>;
    fn into_iter(self) -> ParamIter<'a> {
        ParamIter(self.0.iter())
    }
}

pub struct ParamIter<'a>(shared_names::Iter<'a, Rc<DataType>>);

impl<'a> Iterator for ParamIter<'a> {
    type Item = (&'a String, &'a DataType);
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(name, ty)| (name, &**ty))
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

/// One shared copy of each declared type of each definition, for the length
/// of an inlining pass.
///
/// The hash only selects candidates. Equality is the definition's name and
/// the complete serialized syntax, spans included, kept beside each shared
/// type so a lookup encodes the incoming type once: the fields serde skips
/// are the evaluator caches, disabled in a shared copy, and the lexical
/// bindings (§23.9), which one definition assigns the same way to the same
/// source text.
#[derive(Default)]
pub(crate) struct DeclTypeInterner {
    types: HashMap<(u64, usize), Vec<(Box<str>, Box<[u8]>, Rc<DataType>)>>,
    encoded: Vec<u8>,
    #[cfg(test)]
    pub(crate) copies: usize,
}

impl DeclTypeInterner {
    /// The shared copy of `ty` as definition `owner` declares it.
    pub(crate) fn intern(&mut self, ty: &DataType, owner: &str) -> Rc<DataType> {
        self.encoded.clear();
        if bincode::serde::encode_into_std_write(ty, &mut self.encoded, crate::xez_bincode_config())
            .is_err()
        {
            return Self::shared_copy(ty);
        }
        let mut hash = DeterministicState::default().build_hasher();
        hash.write(owner.as_bytes());
        hash.write_u8(0xff);
        hash.write(&self.encoded);
        let bucket = self
            .types
            .entry((hash.finish(), self.encoded.len()))
            .or_default();
        for (candidate_owner, candidate_syntax, candidate) in bucket.iter() {
            if **candidate_owner == *owner && **candidate_syntax == *self.encoded {
                return Rc::clone(candidate);
            }
        }
        let shared = Self::shared_copy(ty);
        #[cfg(test)]
        {
            self.copies += 1;
        }
        bucket.push((
            owner.into(),
            self.encoded.as_slice().into(),
            Rc::clone(&shared),
        ));
        shared
    }

    /// A copy no evaluation can leave a scope-dependent result in.
    fn shared_copy(ty: &DataType) -> Rc<DataType> {
        Rc::new(crate::ast::cache::without_scope_caches(|| ty.clone()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Span;
    use crate::ast::expr::{ExprKind, Expression, NumberBase, NumberLiteral};
    use crate::ast::types::{IntegerVectorType, PackedDimension};

    fn number(text: &str, at: usize) -> Expression {
        Expression::new(
            ExprKind::Number(NumberLiteral::Integer {
                size: None,
                signed: true,
                base: NumberBase::Decimal,
                value: text.to_string(),
                cached_val: Default::default(),
            }),
            Span::new(at, at + text.len()),
        )
    }

    fn vector(msb: &str, at: usize) -> DataType {
        DataType::IntegerVector {
            kind: IntegerVectorType::Logic,
            signing: None,
            dimensions: vec![PackedDimension::Range {
                left: Box::new(number(msb, at + 7)),
                right: Box::new(number("0", at + 10)),
                span: Span::new(at + 6, at + 12),
            }],
            span: Span::new(at, at + 12),
        }
    }

    /// §6.8: the signals of one declaration hold one type; a different
    /// range, source position or definition is a different type.
    #[test]
    fn equal_declarations_of_one_definition_share_a_type() {
        let mut pool = DeclTypeInterner::default();
        let first = pool.intern(&vector("7", 40), "leaf");
        let again = pool.intern(&vector("7", 40), "leaf");
        assert!(Rc::ptr_eq(&first, &again));
        assert_eq!(pool.copies, 1);
        for (other, owner) in [
            (vector("15", 40), "leaf"),
            (vector("7", 80), "leaf"),
            (vector("7", 40), "other_leaf"),
        ] {
            let distinct = pool.intern(&other, owner);
            assert!(!Rc::ptr_eq(&first, &distinct));
        }
        assert_eq!(pool.copies, 4);
    }

    /// A shared type keeps no evaluation result: a width cached while it is
    /// read for one instance must not answer for another.
    #[test]
    fn shared_types_keep_no_scope_dependent_cache() {
        let mut pool = DeclTypeInterner::default();
        let source = vector("7", 40);
        let shared = pool.intern(&source, "leaf");
        let DataType::IntegerVector { dimensions, .. } = &*shared else {
            panic!("vector expected");
        };
        let PackedDimension::Range { left, .. } = &dimensions[0] else {
            panic!("range expected");
        };
        left.cached_width.set(Some(32));
        assert_eq!(left.cached_width.get(), None);
        // The declaration it was copied from keeps working caches.
        let DataType::IntegerVector { dimensions, .. } = &source else {
            panic!("vector expected");
        };
        let PackedDimension::Range { left, .. } = &dimensions[0] else {
            panic!("range expected");
        };
        left.cached_width.set(Some(32));
        assert_eq!(left.cached_width.get(), Some(32));
    }

    /// The map answers with the type, whether an entry is shared or not, and
    /// serializes as the plain map it replaces.
    #[test]
    fn map_reads_and_serializes_like_a_plain_map() {
        let mut pool = DeclTypeInterner::default();
        let shared = pool.intern(&vector("7", 40), "leaf");
        let mut map = DeclTypeMap::default();
        assert!(
            map.insert_shared("u1.d".to_string(), Rc::clone(&shared))
                .is_none()
        );
        assert!(
            map.insert_shared("u2.d".to_string(), Rc::clone(&shared))
                .is_none()
        );
        assert!(map.insert("top.q".to_string(), vector("3", 90)).is_none());
        assert!(std::ptr::eq(
            map.get("u1.d").unwrap(),
            map.get("u2.d").unwrap()
        ));
        assert!(Rc::ptr_eq(map.get_shared("u1.d").unwrap(), &shared));
        assert_eq!(map.len(), 3);

        // The same inserts into the plain map it replaces write the same bytes.
        let mut plain: HashMap<String, DataType> = HashMap::default();
        plain.insert("u1.d".to_string(), vector("7", 40));
        plain.insert("u2.d".to_string(), vector("7", 40));
        plain.insert("top.q".to_string(), vector("3", 90));
        let config = crate::xez_bincode_config();
        let bytes = bincode::serde::encode_to_vec(&map, config).unwrap();
        assert_eq!(
            bytes,
            bincode::serde::encode_to_vec(&plain, config).unwrap()
        );
        let (loaded, _): (DeclTypeMap, usize) =
            bincode::serde::decode_from_slice(&bytes, config).unwrap();
        assert_eq!(loaded.len(), 3);
        assert_eq!(
            bincode::serde::encode_to_vec(&loaded, config).unwrap(),
            bytes
        );
        assert!(!std::ptr::eq(
            loaded.get("u1.d").unwrap(),
            loaded.get("u2.d").unwrap()
        ));

        assert!(map.remove("u2.d").is_some());
        assert!(map.remove("u2.d").is_none());
        assert!(map.contains_key("u1.d") && !map.contains_key("u2.d"));
    }

    /// Changing one signal's type leaves the signals it was shared with
    /// alone (copy on write).
    #[test]
    fn changing_a_shared_entry_copies_it_first() {
        let mut pool = DeclTypeInterner::default();
        let shared = pool.intern(&vector("7", 40), "leaf");
        let mut map = DeclTypeMap::default();
        map.insert_shared("u1.d".to_string(), Rc::clone(&shared));
        map.insert_shared("u2.d".to_string(), Rc::clone(&shared));
        *map.get_mut("u1.d").unwrap() = vector("3", 90);
        let msb = |ty: &DataType| {
            let DataType::IntegerVector { dimensions, .. } = ty else {
                panic!("vector expected");
            };
            let PackedDimension::Range { left, .. } = &dimensions[0] else {
                panic!("range expected");
            };
            match &left.kind {
                ExprKind::Number(NumberLiteral::Integer { value, .. }) => value.clone(),
                other => panic!("literal expected, got {other:?}"),
            }
        };
        assert_eq!(msb(map.get("u1.d").unwrap()), "3");
        assert_eq!(msb(map.get("u2.d").unwrap()), "7");
        assert!(Rc::ptr_eq(map.get_shared("u2.d").unwrap(), &shared));
        assert_eq!(msb(&shared), "7");
        map.retain(|name, _| name != "u2.d");
        assert_eq!(map.len(), 1);
    }

    /// §7.2: the members beneath one name are read in key order, follow
    /// later inserts, removals and bulk edits, and the map keeps its plain
    /// serialized form.
    #[test]
    fn member_lookup_tracks_key_changes_and_loads_plain_maps() {
        let ty = vector("7", 40);
        let mut original: HashMap<String, DataType> = HashMap::default();
        for key in ["s", "s.a", "s.a.b", "ss.a"] {
            original.insert(key.to_string(), ty.clone());
        }
        let cfg = bincode::config::standard();
        let bytes = bincode::serde::encode_to_vec(&original, cfg).unwrap();
        let (mut types, _): (DeclTypeMap, _) =
            bincode::serde::decode_from_slice(&bytes, cfg).unwrap();
        let members = |types: &DeclTypeMap| {
            types
                .with_prefix("s.")
                .map(|(k, _)| k.clone())
                .collect::<Vec<_>>()
        };
        assert_eq!(members(&types), ["s.a", "s.a.b"]);
        types.remove("s.a");
        types.insert("s.c".into(), ty.clone());
        assert_eq!(members(&types), ["s.a.b", "s.c"]);
        // Bulk mutable access may replace keys without changing the length.
        let raw = types.as_map_mut();
        raw.remove("s.a.b");
        raw.insert("s.d".into(), Rc::new(ty.clone()));
        assert_eq!(members(&types), ["s.c", "s.d"]);
        types.entry("s.e".into()).or_insert(ty.clone());
        types.retain(|name, _| name != "s.c");
        assert_eq!(members(&types), ["s.d", "s.e"]);
        assert_eq!(types.clone().with_prefix("ss.").count(), 1);
        assert_eq!(
            bincode::serde::encode_to_vec(&types, cfg).unwrap(),
            bincode::serde::encode_to_vec(types.as_map(), cfg).unwrap()
        );
    }
}
