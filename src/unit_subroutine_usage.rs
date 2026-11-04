//! IEEE 1800-2023 §3.12.1: retain a compilation-unit subroutine only where used.
//!
//! This conservative scan visits every serialized AST value, including type
//! dimensions, defaults and rarely used declaration kinds. A matching string
//! literal can retain an extra body; missing an AST field must never drop one.
//! No AST is cloned and no serialized buffer is built.

use crate::hasher::{HashMap, HashSet};
use serde::{Serialize, ser};

type Error = serde::de::value::Error;

pub(crate) struct Usage {
    names: HashSet<String>,
    deps: HashMap<String, HashSet<String>>,
}

impl Usage {
    pub(crate) fn new(
        functions: &[crate::ast::decl::FunctionDeclaration],
        tasks: &[crate::ast::decl::TaskDeclaration],
    ) -> Self {
        let names = functions
            .iter()
            .filter(|f| !f.name.has_scope())
            .map(|f| f.name.name.name.clone())
            .chain(
                tasks
                    .iter()
                    .filter(|t| !t.name.has_scope())
                    .map(|t| t.name.name.name.clone()),
            )
            .collect();
        let mut usage = Self {
            names,
            deps: HashMap::default(),
        };
        for f in functions.iter().filter(|f| !f.name.has_scope()) {
            let refs = usage.references(f);
            usage
                .deps
                .entry(f.name.name.name.clone())
                .or_default()
                .extend(refs);
        }
        for t in tasks.iter().filter(|t| !t.name.has_scope()) {
            let refs = usage.references(t);
            usage
                .deps
                .entry(t.name.name.name.clone())
                .or_default()
                .extend(refs);
        }
        usage
    }

    pub(crate) fn references<T: Serialize + ?Sized>(&self, value: &T) -> HashSet<String> {
        let mut found = HashSet::default();
        if self.names.is_empty() {
            return found;
        }
        let mut scan = Scan {
            names: &self.names,
            found: &mut found,
        };
        // AST Serialize implementations are derived and infallible. If a new
        // custom implementation declines traversal, preserve every candidate.
        if value.serialize(&mut scan).is_err() {
            return self.names.clone();
        }
        found
    }

    pub(crate) fn close(&self, mut found: HashSet<String>) -> HashSet<String> {
        let mut pending: Vec<_> = found.iter().cloned().collect();
        while let Some(name) = pending.pop() {
            if let Some(deps) = self.deps.get(&name) {
                for dep in deps {
                    if found.insert(dep.clone()) {
                        pending.push(dep.clone());
                    }
                }
            }
        }
        found
    }
}

struct Scan<'a> {
    names: &'a HashSet<String>,
    found: &'a mut HashSet<String>,
}

macro_rules! scalar {
    ($($method:ident($ty:ty)),* $(,)?) => {$(
        fn $method(self, _: $ty) -> Result<(), Error> { Ok(()) }
    )*};
}

impl<'a, 'b> ser::Serializer for &'a mut Scan<'b> {
    type Ok = ();
    type Error = Error;
    type SerializeSeq = Self;
    type SerializeTuple = Self;
    type SerializeTupleStruct = Self;
    type SerializeTupleVariant = Self;
    type SerializeMap = Self;
    type SerializeStruct = Self;
    type SerializeStructVariant = Self;

    scalar! { serialize_bool(bool), serialize_i8(i8), serialize_i16(i16), serialize_i32(i32),
    serialize_i64(i64), serialize_i128(i128), serialize_u8(u8), serialize_u16(u16),
    serialize_u32(u32), serialize_u64(u64), serialize_u128(u128), serialize_f32(f32),
    serialize_f64(f64), serialize_char(char) }
    fn serialize_str(self, v: &str) -> Result<(), Error> {
        if let Some(name) = self.names.get(v) {
            self.found.insert(name.clone());
        }
        Ok(())
    }
    fn serialize_bytes(self, _: &[u8]) -> Result<(), Error> {
        Ok(())
    }
    fn serialize_none(self) -> Result<(), Error> {
        Ok(())
    }
    fn serialize_some<T: Serialize + ?Sized>(self, value: &T) -> Result<(), Error> {
        value.serialize(self)
    }
    fn serialize_unit(self) -> Result<(), Error> {
        Ok(())
    }
    fn serialize_unit_struct(self, _: &'static str) -> Result<(), Error> {
        Ok(())
    }
    fn serialize_unit_variant(self, _: &'static str, _: u32, _: &'static str) -> Result<(), Error> {
        Ok(())
    }
    fn serialize_newtype_struct<T: Serialize + ?Sized>(
        self,
        _: &'static str,
        v: &T,
    ) -> Result<(), Error> {
        v.serialize(self)
    }
    fn serialize_newtype_variant<T: Serialize + ?Sized>(
        self,
        _: &'static str,
        _: u32,
        _: &'static str,
        v: &T,
    ) -> Result<(), Error> {
        v.serialize(self)
    }
    fn serialize_seq(self, _: Option<usize>) -> Result<Self, Error> {
        Ok(self)
    }
    fn serialize_tuple(self, _: usize) -> Result<Self, Error> {
        Ok(self)
    }
    fn serialize_tuple_struct(self, _: &'static str, _: usize) -> Result<Self, Error> {
        Ok(self)
    }
    fn serialize_tuple_variant(
        self,
        _: &'static str,
        _: u32,
        _: &'static str,
        _: usize,
    ) -> Result<Self, Error> {
        Ok(self)
    }
    fn serialize_map(self, _: Option<usize>) -> Result<Self, Error> {
        Ok(self)
    }
    fn serialize_struct(self, _: &'static str, _: usize) -> Result<Self, Error> {
        Ok(self)
    }
    fn serialize_struct_variant(
        self,
        _: &'static str,
        _: u32,
        _: &'static str,
        _: usize,
    ) -> Result<Self, Error> {
        Ok(self)
    }
}

macro_rules! sequence {
    ($trait:ident, $element:ident) => {
        impl ser::$trait for &mut Scan<'_> {
            type Ok = ();
            type Error = Error;
            fn $element<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), Error> {
                value.serialize(&mut **self)
            }
            fn end(self) -> Result<(), Error> {
                Ok(())
            }
        }
    };
}
sequence!(SerializeSeq, serialize_element);
sequence!(SerializeTuple, serialize_element);
sequence!(SerializeTupleStruct, serialize_field);
sequence!(SerializeTupleVariant, serialize_field);

impl ser::SerializeMap for &mut Scan<'_> {
    type Ok = ();
    type Error = Error;
    fn serialize_key<T: Serialize + ?Sized>(&mut self, v: &T) -> Result<(), Error> {
        v.serialize(&mut **self)
    }
    fn serialize_value<T: Serialize + ?Sized>(&mut self, v: &T) -> Result<(), Error> {
        v.serialize(&mut **self)
    }
    fn end(self) -> Result<(), Error> {
        Ok(())
    }
}
macro_rules! structure {
    ($trait:ident) => {
        impl ser::$trait for &mut Scan<'_> {
            type Ok = ();
            type Error = Error;
            fn serialize_field<T: Serialize + ?Sized>(
                &mut self,
                _: &'static str,
                v: &T,
            ) -> Result<(), Error> {
                v.serialize(&mut **self)
            }
            fn end(self) -> Result<(), Error> {
                Ok(())
            }
        }
    };
}
structure!(SerializeStruct);
structure!(SerializeStructVariant);
