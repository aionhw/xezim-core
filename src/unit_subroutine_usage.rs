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
    qualified_components: bool,
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
            qualified_components: false,
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

    /// §3.12.1 / §6.20: retain unit constants reached through types, values,
    /// or other constants, including dependencies within grouped declarations.
    pub(crate) fn parameters(parameters: &[crate::ast::decl::ParameterDeclaration]) -> Self {
        use crate::ast::decl::ParameterKind;
        let declaration_names = |p: &crate::ast::decl::ParameterDeclaration| -> Vec<String> {
            match &p.kind {
                ParameterKind::Data { assignments, .. } => {
                    assignments.iter().map(|a| a.name.name.clone()).collect()
                }
                ParameterKind::Type { assignments } => {
                    assignments.iter().map(|a| a.name.name.clone()).collect()
                }
            }
        };
        let mut usage = Self {
            names: parameters.iter().flat_map(declaration_names).collect(),
            deps: HashMap::default(),
            qualified_components: true,
        };
        for parameter in parameters {
            match &parameter.kind {
                ParameterKind::Data {
                    data_type,
                    assignments,
                } => {
                    for assignment in assignments {
                        let refs = usage.references(&(data_type, assignment));
                        usage
                            .deps
                            .entry(assignment.name.name.clone())
                            .or_default()
                            .extend(refs);
                    }
                }
                ParameterKind::Type { assignments } => {
                    for assignment in assignments {
                        let refs = usage.references(assignment);
                        usage
                            .deps
                            .entry(assignment.name.name.clone())
                            .or_default()
                            .extend(refs);
                    }
                }
            }
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
            qualified_components: self.qualified_components,
            collect_direct: false,
            indirect: false,
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
    qualified_components: bool,
    collect_direct: bool,
    indirect: bool,
}

/// Direct constant bindings mentioned anywhere in a declaration. Calls and
/// named types may read additional definitions, so those keep the full scope.
pub(crate) fn direct_parameter_reads<T: Serialize + ?Sized>(value: &T) -> Option<HashSet<String>> {
    let names = HashSet::default();
    let mut found = HashSet::default();
    let mut scan = Scan {
        names: &names,
        found: &mut found,
        qualified_components: true,
        collect_direct: true,
        indirect: false,
    };
    if value.serialize(&mut scan).is_err() || scan.indirect { None } else { Some(found) }
}

impl Scan<'_> {
    fn variant(&mut self, variant: &str) {
        if self.collect_direct && matches!(variant, "Call" | "SystemCall" | "TypeReference" | "Specialization") {
            self.indirect = true;
        }
    }
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
        if self.collect_direct {
            self.found.insert(v.to_string());
            self.found.extend(v.split(['.', ':', '[', ']']).map(str::to_string));
            return Ok(());
        }
        if let Some(name) = self.names.get(v) {
            self.found.insert(name.clone());
        }
        // Qualified identifiers can be encoded as one AST string, notably
        // `$unit::P`. Hierarchical references must retain the target constant
        // even if its declaring module contains no direct reference to it.
        if self.qualified_components {
            if let Some(name) = v.strip_prefix("$unit::").and_then(|bare| self.names.get(bare)) {
                self.found.insert(name.clone());
            }
            for component in v.split(['.', ':', '[', ']']) {
                if let Some(name) = self.names.get(component) {
                    self.found.insert(name.clone());
                }
            }
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
    fn serialize_unit_variant(self, _: &'static str, _: u32, variant: &'static str) -> Result<(), Error> {
        self.variant(variant);
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
        variant: &'static str,
        v: &T,
    ) -> Result<(), Error> {
        self.variant(variant);
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
        variant: &'static str,
        _: usize,
    ) -> Result<Self, Error> {
        self.variant(variant);
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
        variant: &'static str,
        _: usize,
    ) -> Result<Self, Error> {
        self.variant(variant);
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn escaped_qualified_parameter_name_is_preserved() {
        let usage = Usage {
            names: ["escaped.name".to_string()].into_iter().collect(),
            deps: HashMap::default(),
            qualified_components: true,
        };
        assert!(usage.references(&"$unit::escaped.name").contains("escaped.name"));
    }

    #[test]
    fn qualified_parameter_names_and_dependencies_are_conservative() {
        let usage = Usage {
            names: ["WIDTH", "BASE", "HIER", "UNUSED"]
                .map(str::to_owned)
                .into_iter()
                .collect(),
            deps: [(
                "WIDTH".to_owned(),
                ["BASE".to_owned()].into_iter().collect(),
            )]
            .into_iter()
            .collect(),
            qualified_components: true,
        };
        let found = usage.close(usage.references(&["$unit::WIDTH", "top.g[2].leaf.HIER"]));
        assert_eq!(
            found,
            ["WIDTH", "BASE", "HIER"]
                .map(str::to_owned)
                .into_iter()
                .collect()
        );
    }
}
