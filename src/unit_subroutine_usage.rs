//! IEEE 1800-2023 §3.12.1: retain a compilation-unit subroutine only where used.
//!
//! This conservative scan visits every serialized AST value, including type
//! dimensions, defaults and rarely used declaration kinds. A matching string
//! literal can retain an extra body; missing an AST field must never drop one.
//! No AST is cloned and no serialized buffer is built.

use crate::hasher::{HashMap, HashSet};
use serde::{Serialize, ser};

type Error = serde::de::value::Error;

/// The SystemVerilog name a DPI import declares (§35.5.4).
pub(crate) fn dpi_import_name(import: &crate::ast::decl::DPIImport) -> String {
    match &import.proto {
        crate::ast::decl::DPIProto::Function(f) => f.name.name.name.clone(),
        crate::ast::decl::DPIProto::Task(t) => t.name.name.name.clone(),
    }
}

pub(crate) struct Usage {
    names: HashSet<String>,
    deps: HashMap<String, HashSet<String>>,
    qualified_components: bool,
}

impl Usage {
    pub(crate) fn new(
        functions: &[crate::ast::decl::FunctionDeclaration],
        tasks: &[crate::ast::decl::TaskDeclaration],
        dpi_imports: &[crate::ast::decl::DPIImport],
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
            .chain(dpi_imports.iter().map(dpi_import_name))
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
        // §35.5.4: an import has no body, but its prototype can read another
        // unit subroutine (a default argument). Its own name is not a use.
        for import in dpi_imports {
            let name = dpi_import_name(import);
            let mut refs = usage.references(import);
            refs.remove(&name);
            usage.deps.entry(name).or_default().extend(refs);
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

    /// §3.12.1 / §16.8 / §16.12: unit assertion declarations are shared
    /// lexical declarations. Follow sequence/property dependencies without
    /// treating their own names as uses in unrelated module definitions.
    pub(crate) fn assertions(declarations: &[crate::ast::decl::ModuleItem]) -> Self {
        use crate::ast::decl::ModuleItem;
        let name = |item: &ModuleItem| match item {
            ModuleItem::PropertyDeclaration(p) => Some(p.name.name.clone()),
            ModuleItem::SequenceDeclaration(s) => Some(s.name.name.clone()),
            _ => None,
        };
        let mut usage = Self {
            names: declarations.iter().filter_map(name).collect(),
            deps: HashMap::default(),
            qualified_components: true,
        };
        for declaration in declarations {
            if let Some(name) = name(declaration) {
                let references = usage.references(declaration);
                usage.deps.entry(name).or_default().extend(references);
            }
        }
        usage
    }

    /// §3.12.1 / §6.7 / §6.8: compilation-unit variables and nets, with the
    /// unit storage each declarator's type, dimensions, delays and
    /// initializer read. Qualified (`$unit::v`) and hierarchical spellings
    /// count as uses.
    pub(crate) fn storage(
        variables: &[crate::ast::decl::DataDeclaration],
        nets: &[crate::ast::decl::NetDeclaration],
    ) -> Self {
        let mut usage = Self {
            names: variables
                .iter()
                .flat_map(|d| d.declarators.iter().map(|v| v.name.name.clone()))
                .chain(
                    nets.iter()
                        .flat_map(|n| n.declarators.iter().map(|v| v.name.name.clone())),
                )
                .collect(),
            deps: HashMap::default(),
            qualified_components: true,
        };
        for d in variables {
            for v in &d.declarators {
                let refs = usage.references(&(&d.data_type, v));
                usage.deps.entry(v.name.name.clone()).or_default().extend(refs);
            }
        }
        for n in nets {
            for v in &n.declarators {
                let refs = usage.references(&(
                    &n.data_type,
                    (&n.delay, &n.delay_fall, &n.delay_off),
                    v,
                ));
                usage.deps.entry(v.name.name.clone()).or_default().extend(refs);
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
            heads: None,
            frames: Vec::new(),
            in_bind: 0,
        };
        // AST Serialize implementations are derived and infallible. If a new
        // custom implementation declines traversal, preserve every candidate.
        if value.serialize(&mut scan).is_err() {
            return self.names.clone();
        }
        found
    }

    /// The names `value` reads, split by how it reads them: `.0` as
    /// [`Usage::references`] reports them, except the names it reads only as
    /// the head of a reference of its own (`P`, `P[i]`, `P.m`), which are
    /// `.1`. A head resolves in the scope it is written in (§23.9), so it
    /// asks nothing of any other definition; every other spelling (the tail
    /// of a hierarchical name such as `u.P`, a type name, a named
    /// connection, anything inside a bind directive, which is elaborated in
    /// its target) may be resolved from elsewhere and stays in `.0`.
    pub(crate) fn references_by_scope<T: Serialize + ?Sized>(
        &self,
        value: &T,
    ) -> (HashSet<String>, HashSet<String>) {
        let mut found = HashSet::default();
        let mut heads = HashSet::default();
        if self.names.is_empty() {
            return (found, heads);
        }
        let mut scan = Scan {
            names: &self.names,
            found: &mut found,
            qualified_components: self.qualified_components,
            collect_direct: false,
            indirect: false,
            heads: Some(&mut heads),
            frames: Vec::new(),
            in_bind: 0,
        };
        if value.serialize(&mut scan).is_err() {
            return (self.names.clone(), HashSet::default());
        }
        (found, heads)
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
    /// When set, a name read as the head of a reference (`P`, `P[i]`,
    /// `P.m`) outside a bind directive is collected here instead of `found`.
    heads: Option<&'a mut HashSet<String>>,
    /// The enclosing compound values, innermost last; kept only for `heads`.
    frames: Vec<Frame>,
    /// How many enclosing values are bind directives.
    in_bind: u32,
}

/// One compound value being visited.
#[derive(Clone, Copy)]
struct Frame {
    kind: FrameKind,
    /// The struct field being visited.
    field: &'static str,
    /// The sequence element being visited.
    index: usize,
}

#[derive(Clone, Copy, PartialEq)]
enum FrameKind {
    HierarchicalIdentifier,
    HierPathSegment,
    Identifier,
    BindDirective,
    Sequence,
    Other,
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
        heads: None,
        frames: Vec::new(),
        in_bind: 0,
    };
    if value.serialize(&mut scan).is_err() || scan.indirect { None } else { Some(found) }
}

impl Scan<'_> {
    /// Enter a compound value (tracked only when heads are collected).
    fn enter(&mut self, kind: FrameKind) {
        if self.heads.is_some() {
            if kind == FrameKind::BindDirective {
                self.in_bind += 1;
            }
            self.frames.push(Frame {
                kind,
                field: "",
                index: usize::MAX,
            });
        }
    }

    fn leave(&mut self) {
        if self.heads.is_some()
            && let Some(frame) = self.frames.pop()
            && frame.kind == FrameKind::BindDirective
        {
            self.in_bind -= 1;
        }
    }

    fn enter_struct(&mut self, name: &str) {
        self.enter(match name {
            "HierarchicalIdentifier" => FrameKind::HierarchicalIdentifier,
            "HierPathSegment" => FrameKind::HierPathSegment,
            "Identifier" => FrameKind::Identifier,
            "BindDirective" => FrameKind::BindDirective,
            _ => FrameKind::Other,
        });
    }

    /// Whether the string being visited is the name of the first segment of
    /// a hierarchical identifier, outside every bind directive:
    /// `HierarchicalIdentifier.path[0].name.name`.
    fn at_reference_head(&self) -> bool {
        let [.., hier, path, segment, ident] = self.frames.as_slice() else {
            return false;
        };
        self.in_bind == 0
            && ident.kind == FrameKind::Identifier
            && ident.field == "name"
            && segment.kind == FrameKind::HierPathSegment
            && segment.field == "name"
            && path.kind == FrameKind::Sequence
            && path.index == 0
            && hier.kind == FrameKind::HierarchicalIdentifier
            && hier.field == "path"
    }

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
            if self.at_reference_head()
                && let Some(heads) = self.heads.as_deref_mut()
            {
                heads.insert(name.clone());
                return Ok(());
            }
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
        self.enter(FrameKind::Sequence);
        Ok(self)
    }
    fn serialize_tuple(self, _: usize) -> Result<Self, Error> {
        self.enter(FrameKind::Other);
        Ok(self)
    }
    fn serialize_tuple_struct(self, _: &'static str, _: usize) -> Result<Self, Error> {
        self.enter(FrameKind::Other);
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
        self.enter(FrameKind::Other);
        Ok(self)
    }
    fn serialize_map(self, _: Option<usize>) -> Result<Self, Error> {
        self.enter(FrameKind::Other);
        Ok(self)
    }
    fn serialize_struct(self, name: &'static str, _: usize) -> Result<Self, Error> {
        self.enter_struct(name);
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
        self.enter(FrameKind::Other);
        Ok(self)
    }
}

macro_rules! sequence {
    ($trait:ident, $element:ident) => {
        impl ser::$trait for &mut Scan<'_> {
            type Ok = ();
            type Error = Error;
            fn $element<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), Error> {
                if let Some(frame) = self.frames.last_mut() {
                    frame.index = frame.index.wrapping_add(1);
                }
                value.serialize(&mut **self)
            }
            fn end(self) -> Result<(), Error> {
                self.leave();
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
        self.leave();
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
                key: &'static str,
                v: &T,
            ) -> Result<(), Error> {
                if let Some(frame) = self.frames.last_mut() {
                    frame.field = key;
                }
                v.serialize(&mut **self)
            }
            fn end(self) -> Result<(), Error> {
                self.leave();
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

    /// §23.9 (#721): a name read as the head of a reference belongs to the
    /// definition that writes it. The tail of a hierarchical name, a named
    /// connection and anything in a bind directive may be resolved from
    /// another scope and stay with the conservative set.
    #[test]
    fn reference_heads_are_split_from_names_another_scope_may_resolve() {
        let parsed = crate::parse(
            "module m;\n\
               localparam int R = LOCAL + ARR[2] + u.TAIL + BOTH;\n\
               logic [TYPEW-1:0] w;\n\
               leaf #(.NAMED(1)) u ();\n\
               initial $display(\"%0d\", u.BOTH);\n\
               bind tgt chk #(.W(BOUND)) k ();\n\
             endmodule",
        );
        assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
        let crate::ast::Description::Module(module) = &parsed.source.descriptions[0] else {
            panic!("module expected");
        };
        let usage = Usage {
            names: [
                "LOCAL", "ARR", "TAIL", "BOTH", "TYPEW", "NAMED", "BOUND", "UNUSED",
            ]
            .map(str::to_owned)
            .into_iter()
            .collect(),
            deps: HashMap::default(),
            qualified_components: true,
        };
        let set =
            |names: &[&str]| -> HashSet<String> { names.iter().map(|n| n.to_string()).collect() };
        let (elsewhere, heads) = usage.references_by_scope(module);
        assert_eq!(heads, set(&["LOCAL", "ARR", "TYPEW", "BOTH"]));
        assert_eq!(elsewhere, set(&["TAIL", "BOTH", "NAMED", "BOUND"]));
        // The undivided scan reports the union.
        assert_eq!(
            usage.references(module),
            set(&["LOCAL", "ARR", "TYPEW", "TAIL", "BOTH", "NAMED", "BOUND"])
        );
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
