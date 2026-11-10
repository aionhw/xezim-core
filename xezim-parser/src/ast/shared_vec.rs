//! Copy-on-write storage for immutable subroutine bodies (§13.3, §13.4).
//!
//! A declaration's signature belongs to its scope, while clones may share
//! its unchanged body. Rewriters obtain exclusive storage before mutation.

use std::ops::{Deref, DerefMut};
use std::sync::Arc;

#[derive(Debug)]
pub struct SharedVec<T>(Arc<Vec<T>>);

impl<T> Clone for SharedVec<T> {
    fn clone(&self) -> Self {
        Self(Arc::clone(&self.0))
    }
}

impl<T> Default for SharedVec<T> {
    fn default() -> Self {
        Self(Arc::new(Vec::new()))
    }
}

impl<T> From<Vec<T>> for SharedVec<T> {
    fn from(value: Vec<T>) -> Self {
        Self(Arc::new(value))
    }
}

impl<T> From<Arc<Vec<T>>> for SharedVec<T> {
    fn from(value: Arc<Vec<T>>) -> Self {
        Self(value)
    }
}

impl<T> SharedVec<T> {
    pub fn as_arc(&self) -> &Arc<Vec<T>> {
        &self.0
    }

    pub fn into_arc(self) -> Arc<Vec<T>> {
        self.0
    }
}

impl<T: Clone> SharedVec<T> {
    pub fn into_vec(self) -> Vec<T> {
        Arc::try_unwrap(self.0).unwrap_or_else(|shared| (*shared).clone())
    }
}

impl<T> Deref for SharedVec<T> {
    type Target = Vec<T>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: Clone> DerefMut for SharedVec<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        Arc::make_mut(&mut self.0)
    }
}

impl<T> FromIterator<T> for SharedVec<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Vec::from_iter(iter).into()
    }
}

impl<'a, T> IntoIterator for &'a SharedVec<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T: Clone> IntoIterator for &'a mut SharedVec<T> {
    type Item = &'a mut T;
    type IntoIter = std::slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<T: Clone> IntoIterator for SharedVec<T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.into_vec().into_iter()
    }
}

#[cfg(feature = "serde")]
impl<T: serde::Serialize> serde::Serialize for SharedVec<T> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        (**self).serialize(serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de, T: serde::Deserialize<'de>> serde::Deserialize<'de> for SharedVec<T> {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        // A restored declaration can be shared immediately by elaboration or
        // runtime clones; contextual memoization must not bind it to one scope.
        super::cache::without_scope_caches(|| Vec::deserialize(deserializer).map(Into::into))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// §13.3/§13.4: rewriting one scope must not change a sibling's body.
    #[test]
    fn cloned_body_shares_until_rewritten() {
        let original: SharedVec<_> = vec![1, 2, 3].into();
        let mut sibling = original.clone();
        assert!(Arc::ptr_eq(original.as_arc(), sibling.as_arc()));
        sibling[1] = 7;
        assert_eq!(&**original, &[1, 2, 3]);
        assert_eq!(&**sibling, &[1, 7, 3]);
        assert!(!Arc::ptr_eq(original.as_arc(), sibling.as_arc()));
    }

    #[cfg(feature = "json-cli")]
    #[test]
    fn serialized_body_remains_a_sequence() {
        let original: SharedVec<_> = vec![1, 2, 3].into();
        assert_eq!(serde_json::to_string(&original).unwrap(), "[1,2,3]");
        let restored: SharedVec<i32> = serde_json::from_str("[1,2,3]").unwrap();
        assert_eq!(&**restored, &[1, 2, 3]);
    }
}
