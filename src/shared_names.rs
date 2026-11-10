//! Shared immutable hierarchical names. The weak registry owns no name text
//! and is scoped to elaboration or artifact loading; live designs continue to
//! own their names after the registry and its allocation are released.

use crate::hasher::{DeterministicState, HashMap};
use serde::{Deserialize, Deserializer, Serialize};
use std::{
    borrow::{Borrow, Cow},
    cell::RefCell,
    collections::hash_map,
    hash::{BuildHasher, Hash, Hasher},
    ops::{Deref, Index},
    sync::{Arc, Weak},
};

/// The usual hash has one weak pointer inline in its table entry. Only
/// genuine hash collisions allocate a candidate vector; neither table owns
/// name text. Equality always checks the complete string, regardless of hash.
#[derive(Default)]
struct NameRegistry {
    primary: HashMap<u64, Weak<String>>,
    collisions: HashMap<u64, Vec<Weak<String>>>,
}

impl NameRegistry {
    fn intern(&mut self, hash: u64, value: Cow<'_, str>) -> Arc<String> {
        match self.primary.entry(hash) {
            hash_map::Entry::Vacant(entry) => {
                let name = Arc::new(value.into_owned());
                entry.insert(Arc::downgrade(&name));
                name
            }
            hash_map::Entry::Occupied(mut entry) => {
                let primary = entry.get().upgrade();
                if primary
                    .as_ref()
                    .is_some_and(|name| name.as_str() == value.as_ref())
                {
                    return primary.expect("matched live name");
                }
                if let Some(bucket) = self.collisions.get_mut(&hash) {
                    let mut existing = None;
                    bucket.retain(|weak| {
                        if let Some(name) = weak.upgrade() {
                            if name.as_str() == value.as_ref() {
                                existing = Some(name);
                            }
                            true
                        } else {
                            false
                        }
                    });
                    if let Some(name) = existing {
                        return name;
                    }
                    if bucket.is_empty() {
                        self.collisions.remove(&hash);
                    }
                }
                // Borrowed inputs allocate only after every candidate misses.
                let name = Arc::new(value.into_owned());
                let weak = Arc::downgrade(&name);
                if primary.is_none() {
                    entry.insert(weak);
                } else {
                    self.collisions.entry(hash).or_default().push(weak);
                }
                name
            }
        }
    }

    #[cfg(test)]
    fn capacity(&self) -> usize {
        self.primary.capacity() + self.collisions.capacity()
    }

    #[cfg(test)]
    fn is_empty(&self) -> bool {
        self.primary.is_empty() && self.collisions.is_empty()
    }
}

thread_local! {
    static NAMES: RefCell<NameRegistry> = RefCell::new(NameRegistry::default());
    static SCOPE_DEPTH: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

pub(crate) fn reset_registry() {
    NAMES.with(|names| *names.borrow_mut() = NameRegistry::default());
}

pub(crate) struct RegistryScope;

impl Drop for RegistryScope {
    fn drop(&mut self) {
        SCOPE_DEPTH.with(|depth| {
            let remaining = depth.get() - 1;
            depth.set(remaining);
            if remaining == 0 {
                reset_registry();
            }
        });
    }
}

/// Start a temporary index, freeing it on success, early error, or panic.
/// Nested operations reuse the outer index and leave its lifetime unchanged.
pub(crate) fn registry_scope() -> RegistryScope {
    SCOPE_DEPTH.with(|depth| {
        if depth.get() == 0 {
            reset_registry();
        }
        depth.set(depth.get() + 1);
    });
    RegistryScope
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize)]
#[serde(transparent)]
pub struct SharedName(Arc<String>);

impl SharedName {
    pub fn ptr_eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl SharedName {
    fn intern(value: Cow<'_, str>) -> Self {
        // Runtime initialization and independent API users can create names
        // after elaboration returns. Do not accumulate a thread-lifetime weak
        // index for those unscoped operations.
        if SCOPE_DEPTH.with(|depth| depth.get() == 0) {
            return Self(Arc::new(value.into_owned()));
        }
        let mut hasher = DeterministicState::default().build_hasher();
        value.as_ref().hash(&mut hasher);
        let hash = hasher.finish();
        NAMES.with(|names| Self(names.borrow_mut().intern(hash, value)))
    }
}

impl From<String> for SharedName {
    fn from(value: String) -> Self {
        Self::intern(Cow::Owned(value))
    }
}
impl From<&str> for SharedName {
    fn from(value: &str) -> Self {
        Self::intern(Cow::Borrowed(value))
    }
}
impl From<&String> for SharedName {
    fn from(value: &String) -> Self {
        Self::from(value.as_str())
    }
}
impl From<SharedName> for String {
    fn from(value: SharedName) -> Self {
        Arc::try_unwrap(value.0).unwrap_or_else(|v| (*v).clone())
    }
}
impl Default for SharedName {
    fn default() -> Self {
        String::new().into()
    }
}
impl Deref for SharedName {
    type Target = String;
    fn deref(&self) -> &String {
        &self.0
    }
}
impl Borrow<str> for SharedName {
    fn borrow(&self) -> &str {
        self.0.as_str()
    }
}
impl Borrow<String> for SharedName {
    fn borrow(&self) -> &String {
        &self.0
    }
}
impl AsRef<str> for SharedName {
    fn as_ref(&self) -> &str {
        self.0.as_str()
    }
}
impl std::fmt::Display for SharedName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}
impl PartialEq<String> for SharedName {
    fn eq(&self, rhs: &String) -> bool {
        **self == *rhs
    }
}
impl PartialEq<str> for SharedName {
    fn eq(&self, rhs: &str) -> bool {
        self.as_str() == rhs
    }
}
impl PartialEq<&str> for SharedName {
    fn eq(&self, rhs: &&str) -> bool {
        self.as_str() == *rhs
    }
}
impl<'de> Deserialize<'de> for SharedName {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        String::deserialize(d).map(Self::from)
    }
}

/// Deterministic map with shared keys and the existing borrowed String-key API.
/// Serde retains the ordinary map representation (no wrapper tag or field).
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(transparent)]
pub struct SharedNameMap<V>(HashMap<SharedName, V>);

impl<V> Default for SharedNameMap<V> {
    fn default() -> Self {
        Self(HashMap::default())
    }
}
impl<V> SharedNameMap<V> {
    pub fn len(&self) -> usize {
        self.0.len()
    }
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    pub fn capacity(&self) -> usize {
        self.0.capacity()
    }
    pub fn clear(&mut self) {
        self.0.clear();
    }
    pub fn reserve(&mut self, additional: usize) {
        self.0.reserve(additional);
    }
    pub fn shrink_to_fit(&mut self) {
        self.0.shrink_to_fit();
    }
    pub fn get<Q: ?Sized + Hash + Eq>(&self, key: &Q) -> Option<&V>
    where
        SharedName: Borrow<Q>,
    {
        self.0.get(key)
    }
    pub fn get_mut<Q: ?Sized + Hash + Eq>(&mut self, key: &Q) -> Option<&mut V>
    where
        SharedName: Borrow<Q>,
    {
        self.0.get_mut(key)
    }
    pub fn contains_key<Q: ?Sized + Hash + Eq>(&self, key: &Q) -> bool
    where
        SharedName: Borrow<Q>,
    {
        self.0.contains_key(key)
    }
    pub fn remove<Q: ?Sized + Hash + Eq>(&mut self, key: &Q) -> Option<V>
    where
        SharedName: Borrow<Q>,
    {
        self.0.remove(key)
    }
    pub fn insert<K: Into<SharedName>>(&mut self, key: K, value: V) -> Option<V> {
        self.0.insert(key.into(), value)
    }
    pub fn entry<K: Into<SharedName>>(&mut self, key: K) -> hash_map::Entry<'_, SharedName, V> {
        self.0.entry(key.into())
    }
    pub fn retain(&mut self, mut predicate: impl FnMut(&String, &mut V) -> bool) {
        self.0.retain(|key, value| predicate(key, value));
    }
    pub fn values(&self) -> hash_map::Values<'_, SharedName, V> {
        self.0.values()
    }
    pub fn values_mut(&mut self) -> hash_map::ValuesMut<'_, SharedName, V> {
        self.0.values_mut()
    }
    pub fn iter(&self) -> Iter<'_, V> {
        Iter(self.0.iter())
    }
    pub fn iter_mut(&mut self) -> IterMut<'_, V> {
        IterMut(self.0.iter_mut())
    }
    pub fn keys(&self) -> Keys<'_, V> {
        Keys(self.0.keys())
    }
    pub fn shared_key<Q: ?Sized + Hash + Eq>(&self, key: &Q) -> Option<&SharedName>
    where
        SharedName: Borrow<Q>,
    {
        self.0.get_key_value(key).map(|(k, _)| k)
    }
}
impl<Q: ?Sized + Hash + Eq, V> Index<&Q> for SharedNameMap<V>
where
    SharedName: Borrow<Q>,
{
    type Output = V;
    fn index(&self, key: &Q) -> &V {
        &self.0[key]
    }
}
impl<K: Into<SharedName>, V> Extend<(K, V)> for SharedNameMap<V> {
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        self.0.extend(iter.into_iter().map(|(k, v)| (k.into(), v)));
    }
}
impl<K: Into<SharedName>, V> FromIterator<(K, V)> for SharedNameMap<V> {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let mut map = Self::default();
        map.extend(iter);
        map
    }
}
impl<V> From<HashMap<String, V>> for SharedNameMap<V> {
    fn from(map: HashMap<String, V>) -> Self {
        map.into_iter().collect()
    }
}

pub struct Iter<'a, V>(hash_map::Iter<'a, SharedName, V>);
impl<'a, V> Iterator for Iter<'a, V> {
    type Item = (&'a String, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(k, v)| (&**k, v))
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}
impl<V> ExactSizeIterator for Iter<'_, V> {}
impl<V> Clone for Iter<'_, V> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}
pub struct IterMut<'a, V>(hash_map::IterMut<'a, SharedName, V>);
impl<'a, V> Iterator for IterMut<'a, V> {
    type Item = (&'a String, &'a mut V);
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(k, v)| (&**k, v))
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}
impl<V> ExactSizeIterator for IterMut<'_, V> {}
pub struct Keys<'a, V>(hash_map::Keys<'a, SharedName, V>);
impl<'a, V> Iterator for Keys<'a, V> {
    type Item = &'a String;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|k| &**k)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}
impl<V> ExactSizeIterator for Keys<'_, V> {}
impl<V> Clone for Keys<'_, V> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}
pub struct IntoIter<V>(hash_map::IntoIter<SharedName, V>);
impl<V> Iterator for IntoIter<V> {
    type Item = (String, V);
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(k, v)| (k.into(), v))
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}
impl<V> ExactSizeIterator for IntoIter<V> {}
impl<'a, V> IntoIterator for &'a SharedNameMap<V> {
    type Item = (&'a String, &'a V);
    type IntoIter = Iter<'a, V>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
impl<'a, V> IntoIterator for &'a mut SharedNameMap<V> {
    type Item = (&'a String, &'a mut V);
    type IntoIter = IterMut<'a, V>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}
impl<V> IntoIterator for SharedNameMap<V> {
    type Item = (String, V);
    type IntoIter = IntoIter<V>;
    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self.0.into_iter())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unique_names_use_inline_weak_entries_without_collision_vectors() {
        let _scope = registry_scope();
        let names: Vec<_> = (0..256)
            .map(|i| SharedName::from(format!("top.deep.leaf.PARAM_{i}")))
            .collect();
        for name in &names {
            assert!(name.ptr_eq(&SharedName::from(name.as_str())));
            assert!(name.ptr_eq(&SharedName::from(&**name)));
        }
        NAMES.with(|registry| {
            let registry = registry.borrow();
            assert_eq!(registry.primary.len(), 256);
            assert_eq!(registry.collisions.capacity(), 0);
            assert!(
                registry
                    .primary
                    .values()
                    .all(|name| name.strong_count() == 1)
            );
        });
    }

    #[test]
    fn colliding_names_keep_distinct_storage_and_reuse_dead_primary_slots() {
        let mut registry = NameRegistry::default();
        let first = registry.intern(7, Cow::Borrowed("top.a.P"));
        let second = registry.intern(7, Cow::Borrowed("top.b.P"));
        assert!(!Arc::ptr_eq(&first, &second));
        assert!(Arc::ptr_eq(
            &first,
            &registry.intern(7, Cow::Borrowed("top.a.P"))
        ));
        assert!(Arc::ptr_eq(
            &second,
            &registry.intern(7, Cow::Owned("top.b.P".into()))
        ));
        assert_eq!(registry.collisions[&7].len(), 1);
        let weak_first = Arc::downgrade(&first);
        drop(first);
        assert!(weak_first.upgrade().is_none());
        let third = registry.intern(7, Cow::Borrowed("top.c.P"));
        assert!(Arc::ptr_eq(
            &third,
            &registry.primary[&7].upgrade().unwrap()
        ));
        assert!(Arc::ptr_eq(
            &second,
            &registry.intern(7, Cow::Borrowed("top.b.P"))
        ));
        drop(second);
        let fourth = registry.intern(7, Cow::Borrowed("top.d.P"));
        assert_eq!(
            registry.collisions[&7].len(),
            1,
            "dead collision is discarded"
        );
        assert_eq!(third.as_str(), "top.c.P");
        assert_eq!(fourth.as_str(), "top.d.P");
        let weak_third = Arc::downgrade(&third);
        let weak_fourth = Arc::downgrade(&fourth);
        drop(third);
        drop(fourth);
        assert!(weak_third.upgrade().is_none());
        assert!(weak_fourth.upgrade().is_none());
    }
    #[test]
    fn registry_allocation_is_released_on_success_and_early_error() {
        let name = {
            let _scope = registry_scope();
            let name = SharedName::from("root.leaf.P");
            NAMES.with(|names| assert!(!names.borrow().is_empty()));
            name
        };
        NAMES.with(|names| assert_eq!(names.borrow().capacity(), 0));
        assert_eq!(name, "root.leaf.P");
        let fail = || -> Result<(), ()> {
            let _scope = registry_scope();
            let _name = SharedName::from("root.leaf.ERROR");
            Err(())?;
            Ok(())
        };
        assert!(fail().is_err());
        NAMES.with(|names| assert_eq!(names.borrow().capacity(), 0));
    }
    #[test]
    fn names_share_across_maps_without_registry_ownership() {
        let _scope = registry_scope();
        let name = SharedName::from("root.deep.leaf.PARAM");
        let mut signals = SharedNameMap::default();
        let mut types = SharedNameMap::default();
        signals.insert(name.to_string(), name.clone());
        types.insert(name.to_string(), 32);
        assert!(name.ptr_eq(signals.shared_key(name.as_str()).unwrap()));
        assert!(name.ptr_eq(types.shared_key(name.as_str()).unwrap()));
        reset_registry();
        assert_eq!(signals["root.deep.leaf.PARAM"], name);
        assert_eq!(types["root.deep.leaf.PARAM"], 32);
        let weak = Arc::downgrade(&name.0);
        drop(signals);
        drop(types);
        drop(name);
        assert!(weak.upgrade().is_none());
    }
    #[test]
    fn ordinary_map_wire_representation_and_name_sharing_round_trip() {
        let _scope = registry_scope();
        let mut map = SharedNameMap::default();
        map.insert("top.leaf.P", SharedName::from("top.leaf.P"));
        let bytes = bincode::serde::encode_to_vec(&map, bincode::config::standard()).unwrap();
        let (ordinary, _): (HashMap<String, String>, usize) =
            bincode::serde::decode_from_slice(&bytes, bincode::config::standard()).unwrap();
        assert_eq!(ordinary["top.leaf.P"], "top.leaf.P");
        let (decoded, _): (SharedNameMap<SharedName>, usize) =
            bincode::serde::decode_from_slice(&bytes, bincode::config::standard()).unwrap();
        assert!(
            decoded
                .shared_key("top.leaf.P")
                .unwrap()
                .ptr_eq(&decoded["top.leaf.P"])
        );
    }

    #[test]
    fn nested_scopes_preserve_the_outer_index() {
        let outer = registry_scope();
        let name = SharedName::from("top.P");
        {
            let _inner = registry_scope();
            assert!(name.ptr_eq(&SharedName::from("top.P")));
        }
        assert!(name.ptr_eq(&SharedName::from("top.P")));
        drop(outer);
        NAMES.with(|names| assert_eq!(names.borrow().capacity(), 0));
        assert_eq!(name, "top.P");
    }

    #[test]
    fn unscoped_runtime_inserts_do_not_accumulate_a_registry() {
        reset_registry();
        let mut signals = SharedNameMap::default();
        for i in 0..256 {
            let name = format!("runtime.synthetic_{i}");
            signals.insert(name.clone(), SharedName::from(name));
        }
        assert_eq!(signals.len(), 256);
        NAMES.with(|names| assert_eq!(names.borrow().capacity(), 0));
        drop(signals);
        NAMES.with(|names| assert_eq!(names.borrow().capacity(), 0));
    }
}
