//! Source-position-free bytes of an AST value, for cache keys.
//!
//! The encoding writes variant indices, lengths and fixed-width scalars, so
//! two values of one type encode alike exactly when they are equal up to
//! their `Span`s, whose fields are left out. The AST's lazily filled caches
//! are `serde(skip)` and so do not take part either.

use serde::{Serialize, ser};

type Error = serde::de::value::Error;

/// The bytes of `value` without its source positions; `None` when it has
/// a sequence or map of unknown length.
pub(super) fn span_free(value: &(impl Serialize + ?Sized)) -> Option<Box<[u8]>> {
    let mut canon = Canon::default();
    value.serialize(&mut canon).ok()?;
    Some(canon.out.into())
}

#[derive(Default)]
struct Canon {
    out: Vec<u8>,
    in_span: bool,
}

impl Canon {
    fn len(&mut self, len: Option<usize>) -> Result<(), Error> {
        let len = len.ok_or_else(|| ser::Error::custom("unknown length"))?;
        self.out.extend_from_slice(&(len as u64).to_le_bytes());
        Ok(())
    }
}

macro_rules! scalar {
    ($($method:ident($ty:ty)),* $(,)?) => {$(
        fn $method(self, v: $ty) -> Result<(), Error> {
            self.out.extend_from_slice(&v.to_le_bytes());
            Ok(())
        }
    )*};
}

impl ser::Serializer for &mut Canon {
    type Ok = ();
    type Error = Error;
    type SerializeSeq = Self;
    type SerializeTuple = Self;
    type SerializeTupleStruct = Self;
    type SerializeTupleVariant = Self;
    type SerializeMap = Self;
    type SerializeStruct = Self;
    type SerializeStructVariant = Self;

    scalar! { serialize_i8(i8), serialize_i16(i16), serialize_i32(i32), serialize_i64(i64),
    serialize_i128(i128), serialize_u8(u8), serialize_u16(u16), serialize_u32(u32),
    serialize_u64(u64), serialize_u128(u128), serialize_f32(f32), serialize_f64(f64) }
    fn serialize_bool(self, v: bool) -> Result<(), Error> {
        self.serialize_u8(v as u8)
    }
    fn serialize_char(self, v: char) -> Result<(), Error> {
        self.serialize_u32(v as u32)
    }
    fn serialize_str(self, v: &str) -> Result<(), Error> {
        self.serialize_bytes(v.as_bytes())
    }
    fn serialize_bytes(self, v: &[u8]) -> Result<(), Error> {
        self.len(Some(v.len()))?;
        self.out.extend_from_slice(v);
        Ok(())
    }
    fn serialize_none(self) -> Result<(), Error> {
        self.serialize_u8(0)
    }
    fn serialize_some<T: Serialize + ?Sized>(self, v: &T) -> Result<(), Error> {
        self.out.push(1);
        v.serialize(self)
    }
    fn serialize_unit(self) -> Result<(), Error> {
        Ok(())
    }
    fn serialize_unit_struct(self, _: &'static str) -> Result<(), Error> {
        Ok(())
    }
    fn serialize_unit_variant(self, _: &'static str, i: u32, _: &'static str) -> Result<(), Error> {
        self.serialize_u32(i)
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
        i: u32,
        _: &'static str,
        v: &T,
    ) -> Result<(), Error> {
        self.out.extend_from_slice(&i.to_le_bytes());
        v.serialize(self)
    }
    fn serialize_seq(self, len: Option<usize>) -> Result<Self, Error> {
        self.len(len)?;
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
        i: u32,
        _: &'static str,
        _: usize,
    ) -> Result<Self, Error> {
        self.out.extend_from_slice(&i.to_le_bytes());
        Ok(self)
    }
    fn serialize_map(self, len: Option<usize>) -> Result<Self, Error> {
        self.len(len)?;
        Ok(self)
    }
    fn serialize_struct(self, name: &'static str, _: usize) -> Result<Self, Error> {
        self.in_span = name == "Span";
        Ok(self)
    }
    fn serialize_struct_variant(
        self,
        _: &'static str,
        i: u32,
        _: &'static str,
        _: usize,
    ) -> Result<Self, Error> {
        self.out.extend_from_slice(&i.to_le_bytes());
        Ok(self)
    }
}

macro_rules! sequence {
    ($trait:ident, $element:ident) => {
        impl ser::$trait for &mut Canon {
            type Ok = ();
            type Error = Error;
            fn $element<T: Serialize + ?Sized>(&mut self, v: &T) -> Result<(), Error> {
                v.serialize(&mut **self)
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

impl ser::SerializeMap for &mut Canon {
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
        impl ser::$trait for &mut Canon {
            type Ok = ();
            type Error = Error;
            fn serialize_field<T: Serialize + ?Sized>(
                &mut self,
                _: &'static str,
                v: &T,
            ) -> Result<(), Error> {
                // A `Span` holds only its two offsets.
                if self.in_span {
                    return Ok(());
                }
                v.serialize(&mut **self)
            }
            fn end(self) -> Result<(), Error> {
                self.in_span = false;
                Ok(())
            }
        }
    };
}
structure!(SerializeStruct);
structure!(SerializeStructVariant);

#[cfg(test)]
mod tests {
    use super::span_free;
    use crate::ast::decl::ModuleItem;

    /// §6.20.3 (aionhw/xezim#721): a type written at two places, one of them
    /// already width-inferred, is one type; another type is not.
    #[test]
    fn a_type_written_twice_encodes_alike() {
        let result = crate::parse_str(
            "module m; logic [W-1:0] a; logic  [W-1:0] b; logic [W:0] c; endmodule",
        )
        .unwrap();
        let crate::ast::Description::Module(module) = &result.source.descriptions[0] else {
            panic!("missing module");
        };
        let types: Vec<_> = module
            .items
            .iter()
            .filter_map(|item| match item {
                ModuleItem::DataDeclaration(d) => Some(&d.data_type),
                _ => None,
            })
            .collect();
        if let crate::ast::types::DataType::IntegerVector { dimensions, .. } = types[1]
            && let crate::ast::types::PackedDimension::Range { left, .. } = &dimensions[0]
        {
            left.cached_width.set(Some(32));
        } else {
            panic!("unexpected shape: {:?}", types[1]);
        }
        assert_eq!(span_free(types[0]), span_free(types[1]));
        assert_ne!(span_free(types[0]), span_free(types[2]));
    }
}
