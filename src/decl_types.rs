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
    map: SharedNameMap<Rc<DataType>>,
    #[serde(skip)]
    dotted: OnceLock<BTreeSet<SharedName>>,
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
                .shared_keys()
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
        let key: SharedName = name.into();
        if let Some(keys) = self.dotted.get_mut()
            && key.contains('.')
            && !self.map.contains_key(key.as_str())
        {
            keys.insert(key.clone());
        }
        self.map.insert(key, ty)
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
    pub fn as_map(&self) -> &SharedNameMap<Rc<DataType>> {
        &self.map
    }
    pub fn as_map_mut(&mut self) -> &mut SharedNameMap<Rc<DataType>> {
        // The caller may change any key.
        self.dotted.take();
        &mut self.map
    }
    pub fn iter(&self) -> Iter<'_> {
        Iter(self.map.iter())
    }
    pub fn keys(&self) -> shared_names::Keys<'_, Rc<DataType>> {
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

pub struct Entry<'a>(hash_map::Entry<'a, SharedName, Rc<DataType>>);

impl Entry<'_> {
    pub fn or_insert_with(self, make: impl FnOnce() -> DataType) {
        self.0.or_insert_with(|| Rc::new(make()));
    }
    pub fn or_insert(self, ty: DataType) {
        self.0.or_insert_with(|| Rc::new(ty));
    }
    pub fn or_insert_shared(self, ty: &Rc<DataType>) {
        self.0.or_insert_with(|| Rc::clone(ty));
    }
}

pub struct Iter<'a>(shared_names::Iter<'a, Rc<DataType>>);

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
    fast_types: HashMap<u64, Vec<(Box<str>, FastTyOwned, Rc<DataType>)>>,
    types: HashMap<(u64, usize), Vec<(Box<str>, Box<[u8]>, Rc<DataType>)>>,
    encoded: Vec<u8>,
    #[cfg(test)]
    pub(crate) copies: usize,
}

#[derive(Clone, PartialEq, Eq)]
enum FastRange<'a> {
    None,
    Unsized(crate::ast::Span),
    ConstInt {
        dim_span: crate::ast::Span,
        l_span: crate::ast::Span,
        l_size: Option<u32>,
        l_signed: bool,
        l_base: u8,
        l_val: &'a str,
        r_span: crate::ast::Span,
        r_size: Option<u32>,
        r_signed: bool,
        r_base: u8,
        r_val: &'a str,
    },
}

enum FastRangeOwned {
    None,
    Unsized(crate::ast::Span),
    ConstInt {
        dim_span: crate::ast::Span,
        l_span: crate::ast::Span,
        l_size: Option<u32>,
        l_signed: bool,
        l_base: u8,
        l_val: Box<str>,
        r_span: crate::ast::Span,
        r_size: Option<u32>,
        r_signed: bool,
        r_base: u8,
        r_val: Box<str>,
    },
}

impl FastRange<'_> {
    fn hash_into<H: std::hash::Hasher>(&self, h: &mut H) {
        use std::hash::Hash;
        match *self {
            Self::None => 0u8.hash(h),
            Self::Unsized(s) => {
                1u8.hash(h);
                s.start.hash(h);
                s.end.hash(h);
            }
            Self::ConstInt {
                dim_span,
                l_span,
                l_size,
                l_signed,
                l_base,
                l_val,
                r_span,
                r_size,
                r_signed,
                r_base,
                r_val,
            } => {
                2u8.hash(h);
                (dim_span.start, dim_span.end).hash(h);
                (l_span.start, l_span.end, l_size, l_signed, l_base, l_val).hash(h);
                (r_span.start, r_span.end, r_size, r_signed, r_base, r_val).hash(h);
            }
        }
    }

    fn to_owned(&self) -> FastRangeOwned {
        match *self {
            Self::None => FastRangeOwned::None,
            Self::Unsized(s) => FastRangeOwned::Unsized(s),
            Self::ConstInt {
                dim_span,
                l_span,
                l_size,
                l_signed,
                l_base,
                l_val,
                r_span,
                r_size,
                r_signed,
                r_base,
                r_val,
            } => FastRangeOwned::ConstInt {
                dim_span,
                l_span,
                l_size,
                l_signed,
                l_base,
                l_val: l_val.into(),
                r_span,
                r_size,
                r_signed,
                r_base,
                r_val: r_val.into(),
            },
        }
    }
}

impl FastRangeOwned {
    fn as_ref(&self) -> FastRange<'_> {
        match self {
            Self::None => FastRange::None,
            Self::Unsized(s) => FastRange::Unsized(*s),
            Self::ConstInt {
                dim_span,
                l_span,
                l_size,
                l_signed,
                l_base,
                l_val,
                r_span,
                r_size,
                r_signed,
                r_base,
                r_val,
            } => FastRange::ConstInt {
                dim_span: *dim_span,
                l_span: *l_span,
                l_size: *l_size,
                l_signed: *l_signed,
                l_base: *l_base,
                l_val,
                r_span: *r_span,
                r_size: *r_size,
                r_signed: *r_signed,
                r_base: *r_base,
                r_val,
            },
        }
    }
}

#[derive(PartialEq, Eq)]
enum FastTy<'a> {
    IntVec {
        kind: u8,
        signing: Option<u8>,
        range: FastRange<'a>,
        span: crate::ast::Span,
    },
    IntAtom {
        kind: u8,
        signing: Option<u8>,
        span: crate::ast::Span,
    },
    Real {
        kind: u8,
        span: crate::ast::Span,
    },
    Simple {
        kind: u8,
        span: crate::ast::Span,
    },
    Void(crate::ast::Span),
    Implicit {
        signing: Option<u8>,
        range: FastRange<'a>,
        span: crate::ast::Span,
    },
    TypeRef {
        scope: Option<(&'a str, crate::ast::Span)>,
        ident: (&'a str, crate::ast::Span),
        tn_span: crate::ast::Span,
        span: crate::ast::Span,
    },
}

enum FastTyOwned {
    IntVec {
        kind: u8,
        signing: Option<u8>,
        range: FastRangeOwned,
        span: crate::ast::Span,
    },
    IntAtom {
        kind: u8,
        signing: Option<u8>,
        span: crate::ast::Span,
    },
    Real {
        kind: u8,
        span: crate::ast::Span,
    },
    Simple {
        kind: u8,
        span: crate::ast::Span,
    },
    Void(crate::ast::Span),
    Implicit {
        signing: Option<u8>,
        range: FastRangeOwned,
        span: crate::ast::Span,
    },
    TypeRef {
        scope: Option<(Box<str>, crate::ast::Span)>,
        ident: (Box<str>, crate::ast::Span),
        tn_span: crate::ast::Span,
        span: crate::ast::Span,
    },
}

impl<'a> FastTy<'a> {
    fn from_data_type(ty: &'a DataType) -> Option<Self> {
        use crate::ast::expr::{ExprKind, NumberBase, NumberLiteral};
        use crate::ast::types::{
            IntegerAtomType, IntegerVectorType, PackedDimension, RealType, SimpleType, Signing,
        };
        let enc_signing = |s: Option<Signing>| {
            s.map(|x| match x {
                Signing::Signed => 0,
                Signing::Unsigned => 1,
            })
        };
        let enc_base = |b: NumberBase| match b {
            NumberBase::Decimal => 0,
            NumberBase::Binary => 1,
            NumberBase::Octal => 2,
            NumberBase::Hex => 3,
        };
        let enc_dims = |dims: &'a [PackedDimension]| -> Option<FastRange<'a>> {
            match dims {
                [] => Some(FastRange::None),
                [PackedDimension::Unsized(s)] => Some(FastRange::Unsized(*s)),
                [PackedDimension::Range { left, right, span }] => match (&left.kind, &right.kind) {
                    (
                        ExprKind::Number(NumberLiteral::Integer {
                            size: l_size,
                            signed: l_signed,
                            base: l_base,
                            value: l_val,
                            ..
                        }),
                        ExprKind::Number(NumberLiteral::Integer {
                            size: r_size,
                            signed: r_signed,
                            base: r_base,
                            value: r_val,
                            ..
                        }),
                    ) => Some(FastRange::ConstInt {
                        dim_span: *span,
                        l_span: left.span,
                        l_size: *l_size,
                        l_signed: *l_signed,
                        l_base: enc_base(*l_base),
                        l_val: l_val.as_str(),
                        r_span: right.span,
                        r_size: *r_size,
                        r_signed: *r_signed,
                        r_base: enc_base(*r_base),
                        r_val: r_val.as_str(),
                    }),
                    _ => None,
                },
                _ => None,
            }
        };
        Some(match ty {
            DataType::IntegerVector {
                kind,
                signing,
                dimensions,
                span,
            } => Self::IntVec {
                kind: match kind {
                    IntegerVectorType::Bit => 0,
                    IntegerVectorType::Logic => 1,
                    IntegerVectorType::Reg => 2,
                },
                signing: enc_signing(*signing),
                range: enc_dims(dimensions)?,
                span: *span,
            },
            DataType::IntegerAtom {
                kind,
                signing,
                span,
            } => Self::IntAtom {
                kind: match kind {
                    IntegerAtomType::Byte => 0,
                    IntegerAtomType::ShortInt => 1,
                    IntegerAtomType::Int => 2,
                    IntegerAtomType::LongInt => 3,
                    IntegerAtomType::Integer => 4,
                    IntegerAtomType::Time => 5,
                },
                signing: enc_signing(*signing),
                span: *span,
            },
            DataType::Real { kind, span } => Self::Real {
                kind: match kind {
                    RealType::Real => 0,
                    RealType::ShortReal => 1,
                    RealType::RealTime => 2,
                },
                span: *span,
            },
            DataType::Simple { kind, span } => Self::Simple {
                kind: match kind {
                    SimpleType::String => 0,
                    SimpleType::Chandle => 1,
                    SimpleType::Event => 2,
                },
                span: *span,
            },
            DataType::Void(span) => Self::Void(*span),
            DataType::Implicit {
                signing,
                dimensions,
                span,
            } => Self::Implicit {
                signing: enc_signing(*signing),
                range: enc_dims(dimensions)?,
                span: *span,
            },
            DataType::TypeReference {
                name,
                dimensions,
                type_args,
                span,
            } if dimensions.is_empty()
                && type_args.is_empty()
                && name.scopes.len() <= 1
                && name.scopes.iter().all(|s| s.type_args.is_empty()) =>
            {
                Self::TypeRef {
                    scope: name
                        .scopes
                        .first()
                        .map(|s| (s.name.name.as_str(), s.name.span)),
                    ident: (name.name.name.as_str(), name.name.span),
                    tn_span: name.span,
                    span: *span,
                }
            }
            _ => return None,
        })
    }

    fn hash_with_owner<H: std::hash::Hasher>(&self, owner: &str, h: &mut H) {
        use std::hash::Hash;
        owner.hash(h);
        match self {
            Self::IntVec {
                kind,
                signing,
                range,
                span,
            } => {
                0u8.hash(h);
                (*kind, *signing, span.start, span.end).hash(h);
                range.hash_into(h);
            }
            Self::IntAtom {
                kind,
                signing,
                span,
            } => {
                1u8.hash(h);
                (*kind, *signing, span.start, span.end).hash(h);
            }
            Self::Real { kind, span } => {
                2u8.hash(h);
                (*kind, span.start, span.end).hash(h);
            }
            Self::Simple { kind, span } => {
                3u8.hash(h);
                (*kind, span.start, span.end).hash(h);
            }
            Self::Void(span) => {
                4u8.hash(h);
                (span.start, span.end).hash(h);
            }
            Self::Implicit {
                signing,
                range,
                span,
            } => {
                5u8.hash(h);
                (*signing, span.start, span.end).hash(h);
                range.hash_into(h);
            }
            Self::TypeRef {
                scope,
                ident,
                tn_span,
                span,
            } => {
                6u8.hash(h);
                scope.map(|(n, s)| (n, s.start, s.end)).hash(h);
                (ident.0, ident.1.start, ident.1.end).hash(h);
                (tn_span.start, tn_span.end, span.start, span.end).hash(h);
            }
        }
    }

    fn to_owned(&self) -> FastTyOwned {
        match *self {
            Self::IntVec {
                kind,
                signing,
                ref range,
                span,
            } => FastTyOwned::IntVec {
                kind,
                signing,
                range: range.to_owned(),
                span,
            },
            Self::IntAtom {
                kind,
                signing,
                span,
            } => FastTyOwned::IntAtom {
                kind,
                signing,
                span,
            },
            Self::Real { kind, span } => FastTyOwned::Real { kind, span },
            Self::Simple { kind, span } => FastTyOwned::Simple { kind, span },
            Self::Void(span) => FastTyOwned::Void(span),
            Self::Implicit {
                signing,
                ref range,
                span,
            } => FastTyOwned::Implicit {
                signing,
                range: range.to_owned(),
                span,
            },
            Self::TypeRef {
                scope,
                ident,
                tn_span,
                span,
            } => FastTyOwned::TypeRef {
                scope: scope.map(|(n, s)| (n.into(), s)),
                ident: (ident.0.into(), ident.1),
                tn_span,
                span,
            },
        }
    }
}

impl FastTyOwned {
    fn as_ref(&self) -> FastTy<'_> {
        match self {
            Self::IntVec {
                kind,
                signing,
                range,
                span,
            } => FastTy::IntVec {
                kind: *kind,
                signing: *signing,
                range: range.as_ref(),
                span: *span,
            },
            Self::IntAtom {
                kind,
                signing,
                span,
            } => FastTy::IntAtom {
                kind: *kind,
                signing: *signing,
                span: *span,
            },
            Self::Real { kind, span } => FastTy::Real {
                kind: *kind,
                span: *span,
            },
            Self::Simple { kind, span } => FastTy::Simple {
                kind: *kind,
                span: *span,
            },
            Self::Void(span) => FastTy::Void(*span),
            Self::Implicit {
                signing,
                range,
                span,
            } => FastTy::Implicit {
                signing: *signing,
                range: range.as_ref(),
                span: *span,
            },
            Self::TypeRef {
                scope,
                ident,
                tn_span,
                span,
            } => FastTy::TypeRef {
                scope: scope.as_ref().map(|(n, s)| (&**n, *s)),
                ident: (&*ident.0, ident.1),
                tn_span: *tn_span,
                span: *span,
            },
        }
    }
}

impl DeclTypeInterner {
    /// The shared copy of `ty` as definition `owner` declares it.
    pub(crate) fn intern(&mut self, ty: &DataType, owner: &str) -> Rc<DataType> {
        if let Some(fast) = FastTy::from_data_type(ty) {
            let mut hash = DeterministicState::default().build_hasher();
            fast.hash_with_owner(owner, &mut hash);
            let bucket = self.fast_types.entry(hash.finish()).or_default();
            for (candidate_owner, candidate_ty, candidate) in bucket.iter() {
                if &**candidate_owner == owner && candidate_ty.as_ref() == fast {
                    return Rc::clone(candidate);
                }
            }
            let shared = Self::shared_copy(ty);
            #[cfg(test)]
            {
                self.copies += 1;
            }
            bucket.push((owner.into(), fast.to_owned(), Rc::clone(&shared)));
            return shared;
        }
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

thread_local! {
    static TOP_DECL_TYPES: std::cell::RefCell<Option<DeclTypeInterner>> =
        const { std::cell::RefCell::new(None) };
}

pub(crate) struct TopDeclTypesScope {
    prev: Option<DeclTypeInterner>,
}

impl Drop for TopDeclTypesScope {
    fn drop(&mut self) {
        TOP_DECL_TYPES.with(|slot| *slot.borrow_mut() = self.prev.take());
    }
}

/// Start a scoped type interner for root-module and generate-block
/// declarations so repeated `wire [7:0]` / `logic [7:0]` declarations share
/// one `Rc<DataType>` instead of cloning the type tree per signal (#721).
pub(crate) fn top_decl_types_scope() -> TopDeclTypesScope {
    let prev = TOP_DECL_TYPES.with(|slot| slot.borrow_mut().replace(DeclTypeInterner::default()));
    TopDeclTypesScope { prev }
}

/// Strip source spans from simple leaf/vector types before interning into
/// `var_decl_types`, which never reports source locations (those live in
/// `decl_sites`). Collapses thousands of identical `wire [7:0]` lines into one
/// shared `Rc<DataType>`.
fn canonicalize_simple_decl_type(ty: &DataType) -> Option<DataType> {
    use crate::ast::{
        Span,
        expr::{ExprKind, Expression, NumberLiteral},
        types::PackedDimension,
    };
    fn canon_const_expr(e: &Expression) -> Option<Expression> {
        match &e.kind {
            ExprKind::Number(NumberLiteral::Integer {
                size,
                signed,
                base,
                value,
                cached_val,
            }) => Some(Expression::new(
                ExprKind::Number(NumberLiteral::Integer {
                    size: *size,
                    signed: *signed,
                    base: *base,
                    value: value.clone(),
                    cached_val: cached_val.clone(),
                }),
                Span::dummy(),
            )),
            _ => None,
        }
    }
    fn canon_dims(dims: &[PackedDimension]) -> Option<Vec<PackedDimension>> {
        let mut out = Vec::with_capacity(dims.len());
        for d in dims {
            match d {
                PackedDimension::Range { left, right, .. } => out.push(PackedDimension::Range {
                    left: Box::new(canon_const_expr(left)?),
                    right: Box::new(canon_const_expr(right)?),
                    span: Span::dummy(),
                }),
                PackedDimension::Unsized(_) => out.push(PackedDimension::Unsized(Span::dummy())),
            }
        }
        Some(out)
    }
    match ty {
        DataType::IntegerVector {
            kind,
            signing,
            dimensions,
            ..
        } => Some(DataType::IntegerVector {
            kind: *kind,
            signing: *signing,
            dimensions: canon_dims(dimensions)?,
            span: Span::dummy(),
        }),
        DataType::Implicit {
            signing,
            dimensions,
            ..
        } => Some(DataType::Implicit {
            signing: *signing,
            dimensions: canon_dims(dimensions)?,
            span: Span::dummy(),
        }),
        DataType::IntegerAtom { kind, signing, .. } => Some(DataType::IntegerAtom {
            kind: *kind,
            signing: *signing,
            span: Span::dummy(),
        }),
        DataType::Real { kind, .. } => Some(DataType::Real {
            kind: *kind,
            span: Span::dummy(),
        }),
        _ => None,
    }
}

/// Return a shared `Rc<DataType>` for a top-level or generate-block
/// declaration, interning across the active `top_decl_types_scope` when present.
pub(crate) fn intern_top_decl_type(ty: &DataType) -> Rc<DataType> {
    TOP_DECL_TYPES.with(|slot| {
        let mut slot = slot.borrow_mut();
        if let Some(pool) = slot.as_mut() {
            if let Some(canon) = canonicalize_simple_decl_type(ty) {
                pool.intern(&canon, "")
            } else {
                pool.intern(ty, "")
            }
        } else {
            Rc::new(ty.clone())
        }
    })
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
            Span::from_usize(at, at + text.len()),
        )
    }

    fn vector(msb: &str, at: usize) -> DataType {
        DataType::IntegerVector {
            kind: IntegerVectorType::Logic,
            signing: None,
            dimensions: vec![PackedDimension::Range {
                left: Box::new(number(msb, at + 7)),
                right: Box::new(number("0", at + 10)),
                span: Span::from_usize(at + 6, at + 12),
            }],
            span: Span::from_usize(at, at + 12),
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
        raw.insert("s.d", Rc::new(ty.clone()));
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

    #[test]
    fn fast_intern_covers_common_shapes_and_preserves_spans_and_owner() {
        use crate::ast::Identifier;
        use crate::ast::types::{
            IntegerAtomType, RealType, SimpleType, Signing, TypeName, TypeScope,
        };

        let sp = |a: u32, b: u32| Span::new(a, b);
        let mut pool = DeclTypeInterner::default();

        let int_ty = DataType::IntegerAtom {
            kind: IntegerAtomType::Int,
            signing: Some(Signing::Signed),
            span: sp(10, 13),
        };
        let r1 = pool.intern(&int_ty, "m1");
        let r2 = pool.intern(&int_ty, "m1");
        assert!(Rc::ptr_eq(&r1, &r2));
        let r3 = pool.intern(&int_ty, "m2");
        assert!(!Rc::ptr_eq(&r1, &r3));
        assert_eq!(pool.copies, 2);

        let samples = vec![
            DataType::Real {
                kind: RealType::Real,
                span: sp(20, 24),
            },
            DataType::Simple {
                kind: SimpleType::String,
                span: sp(30, 36),
            },
            DataType::Void(sp(40, 44)),
            DataType::IntegerVector {
                kind: IntegerVectorType::Bit,
                signing: None,
                dimensions: vec![],
                span: sp(50, 53),
            },
            DataType::IntegerVector {
                kind: IntegerVectorType::Reg,
                signing: Some(Signing::Unsigned),
                dimensions: vec![PackedDimension::Unsized(sp(60, 62))],
                span: sp(55, 62),
            },
            DataType::Implicit {
                signing: Some(Signing::Signed),
                dimensions: vec![PackedDimension::Range {
                    left: Box::new(number("31", 70)),
                    right: Box::new(number("0", 73)),
                    span: sp(69, 74),
                }],
                span: sp(65, 74),
            },
            DataType::TypeReference {
                name: Box::new(TypeName {
                    scopes: vec![],
                    name: Identifier {
                        name: "word_t".to_string(),
                        span: sp(80, 86),
                    },
                    span: sp(80, 86),
                    bound: Default::default(),
                }),
                dimensions: vec![],
                type_args: vec![],
                span: sp(80, 86),
            },
            DataType::TypeReference {
                name: Box::new(TypeName {
                    scopes: vec![TypeScope {
                        name: Identifier {
                            name: "pkg".to_string(),
                            span: sp(90, 93),
                        },
                        type_args: vec![],
                    }],
                    name: Identifier {
                        name: "word_t".to_string(),
                        span: sp(95, 101),
                    },
                    span: sp(90, 101),
                    bound: Default::default(),
                }),
                dimensions: vec![],
                type_args: vec![],
                span: sp(90, 101),
            },
        ];

        for ty in &samples {
            let a = pool.intern(ty, "leaf");
            let b = pool.intern(ty, "leaf");
            assert!(Rc::ptr_eq(&a, &b));
        }
        assert_eq!(pool.copies, 2 + samples.len());
        // Fast types live in `fast_types`, without populating `bincode` `types`.
        assert!(pool.types.is_empty());

        // Different span or literal on TypeReference must produce a distinct copy.
        let shifted_tref = DataType::TypeReference {
            name: Box::new(TypeName {
                scopes: vec![],
                name: Identifier {
                    name: "word_t".to_string(),
                    span: sp(200, 206),
                },
                span: sp(200, 206),
                bound: Default::default(),
            }),
            dimensions: vec![],
            type_args: vec![],
            span: sp(200, 206),
        };
        let t_orig = pool.intern(&samples[6], "leaf");
        let t_shift = pool.intern(&shifted_tref, "leaf");
        assert!(!Rc::ptr_eq(&t_orig, &t_shift));
    }
}
