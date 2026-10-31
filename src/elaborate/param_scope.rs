//! IEEE 1800-2023 §23.10, §26.3: the package, `$unit` and top-module
//! parameters an inlined instance's scope holds.
//!
//! Every instance used to be elaborated in a copy of the whole parameter
//! table taken when inlining begins, with the parameters of the instances
//! above it and its own laid over it; the cache key of its prepared body
//! rendered that copy and its subroutine formals got a substitution entry for
//! every integer in it. A design with P package parameters and N instances
//! paid P x N for all three, even for parameters no module names.
//!
//! The table does not change while instances are inlined, so it is held here
//! once and a scope takes from it only the entries whose name its definition
//! can spell. A definition's words are read from every string of its syntax
//! tree (a `serde` serializer, as in `unit_subroutine_usage`), so no node kind
//! can be missed. Read with it, because their text is evaluated in the
//! definition's scope too:
//!
//! - the definitions it names (a parent sizes a child's ports for an
//!   instance array, an interface port names its interface),
//! - every scope above it (`sub_merged_params` starts from the parent's
//!   scope, so a type parameter written in the parent keeps its names),
//! - the items of every package other than its parameters' names and
//!   initializers (a package typedef, function or class body read through a
//!   package name), the file-scope classes, typedefs and `let`s, and every resolved
//!   `bind` with the definition it binds (its overrides and connections are
//!   evaluated in the target's scope, §23.11).
//!
//! A name nothing spells is read by no expression of the scope, and a
//! constant-evaluation miss still finds it in `PARAM_FALLBACK_TLS`. A
//! definition that is not a module, interface or program, or whose syntax
//! cannot be read to the end, takes the whole table, as before.

use super::Definition;
use crate::hasher::{HashMap, HashSet};
use crate::value::Value;
use serde::{Serialize, ser};
use std::cell::RefCell;
use std::rc::Rc;

/// What a definition's syntax spells: the table entries named by one of its
/// words, and the instantiable definitions it names. `None` stands for the
/// whole table.
type Spelled = Option<(Vec<u32>, Vec<String>)>;

pub(super) struct ParamScope {
    entries: Vec<(String, Value)>,
    /// Word of an entry's key (`W` of `pkg::W`, `LIM` of `pkg::LIM[3]`,
    /// `Cfg` and `VLEN` of `pkg::Cfg.VLEN`) to the entries it names.
    by_word: HashMap<String, Vec<u32>>,
    /// Module, interface and program names.
    instantiable: HashSet<String>,
    /// Entries every scope holds: keys without a word, and the names the
    /// packages, file-scope declarations and binds spell.
    common: Vec<u32>,
    spelled: RefCell<HashMap<(String, usize), Rc<Spelled>>>,
    selected: RefCell<HashMap<(String, usize), Rc<[u32]>>>,
}

impl ParamScope {
    pub(super) fn new(
        table: &HashMap<String, Value>,
        definitions: &HashMap<String, Definition>,
        binds: &HashMap<String, Vec<crate::ast::decl::BindDirective>>,
        lets: &HashMap<String, crate::ast::decl::LetDeclaration>,
    ) -> Self {
        let mut entries: Vec<(String, Value)> =
            table.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
        // A fixed order, so the scopes built from it are the same each run.
        entries.sort_unstable_by(|a, b| a.0.cmp(&b.0));
        let mut by_word: HashMap<String, Vec<u32>> = HashMap::default();
        let mut common = Vec::new();
        for (i, (key, _)) in entries.iter().enumerate() {
            let mut any = false;
            for w in key_words(key) {
                any = true;
                let slot = by_word.entry(w.to_string()).or_default();
                if slot.last() != Some(&(i as u32)) {
                    slot.push(i as u32);
                }
            }
            if !any {
                common.push(i as u32);
            }
        }
        let instantiable = definitions
            .iter()
            .filter(|(_, d)| instantiable(d))
            .map(|(n, _)| n.clone())
            .collect();
        let mut scope = Self {
            entries,
            by_word,
            instantiable,
            common,
            spelled: RefCell::default(),
            selected: RefCell::default(),
        };
        let mut found = HashSet::default();
        let mut named = HashSet::default();
        let mut all = false;
        let mut read = |v: &dyn erased::Scannable, scope: &ParamScope| {
            all |= !scope.scan(v, &mut found, &mut named);
        };
        for def in definitions.values() {
            match def {
                Definition::Package(p) => {
                    for item in &p.items {
                        match item {
                            crate::ast::decl::PackageItem::Parameter(pd) => match &pd.kind {
                                crate::ast::decl::ParameterKind::Data {
                                    data_type,
                                    assignments,
                                } => {
                                    read(data_type, &scope);
                                    for a in assignments {
                                        read(&a.dimensions, &scope);
                                    }
                                }
                                crate::ast::decl::ParameterKind::Type { .. } => read(pd, &scope),
                            },
                            other => read(other, &scope),
                        }
                    }
                }
                Definition::Class(c) => read(*c, &scope),
                Definition::Covergroup(c) => read(*c, &scope),
                Definition::Typedef(t) => read(*t, &scope),
                _ => {}
            }
        }
        // A `let` body is expanded where it is used (§11.12).
        for l in lets.values() {
            read(l, &scope);
        }
        for list in binds.values() {
            for b in list {
                read(&b.instantiation, &scope);
            }
        }
        // The definitions binds instantiate are read in their targets' scope.
        let bound: Vec<String> = named.drain().collect();
        for name in bound {
            if let Some(def) = definitions.get(&name)
                && let Some(spelled) = &*scope.spelled_by(def)
            {
                found.extend(spelled.0.iter().copied());
            } else if definitions.contains_key(&name) {
                all = true;
            }
        }
        if all {
            scope.common = (0..scope.entries.len() as u32).collect();
        } else {
            scope.common.extend(found);
            scope.common.sort_unstable();
            scope.common.dedup();
        }
        scope
    }

    /// The scope of an instance of `def` at the top of the hierarchy.
    pub(super) fn top_scope(
        &self,
        def: Definition,
        definitions: &HashMap<String, Definition>,
    ) -> HashMap<String, Value> {
        let mut m = HashMap::default();
        self.extend_scope(def, definitions, &mut m);
        m
    }

    /// Add to `scope` (the parent's scope with the instance's own parameters
    /// laid over it) the table entries `def` can name and `scope` lacks: an
    /// entry already there is the instance's or an enclosing one's, which
    /// hides the table's (or is the table's, carried down).
    pub(super) fn extend_scope(
        &self,
        def: Definition,
        definitions: &HashMap<String, Definition>,
        scope: &mut HashMap<String, Value>,
    ) {
        for &i in self.selection(def, definitions).iter() {
            let (k, v) = &self.entries[i as usize];
            if !scope.contains_key(k) {
                scope.insert(k.clone(), v.clone());
            }
        }
    }

    fn selection(&self, def: Definition, definitions: &HashMap<String, Definition>) -> Rc<[u32]> {
        let key = def_key(&def);
        if let Some(s) = self.selected.borrow().get(&key) {
            return Rc::clone(s);
        }
        let own = self.spelled_by(&def);
        let sel: Rc<[u32]> = match &*own {
            Some((ids, named)) => {
                let mut sel: Vec<u32> = self.common.clone();
                sel.extend(ids.iter().copied());
                let mut whole = false;
                for name in named {
                    if name == def.name() {
                        continue;
                    }
                    let Some(child) = definitions.get(name) else {
                        continue;
                    };
                    match &*self.spelled_by(child) {
                        Some((ids, _)) => sel.extend(ids.iter().copied()),
                        None => whole = true,
                    }
                }
                if whole {
                    (0..self.entries.len() as u32).collect()
                } else {
                    sel.sort_unstable();
                    sel.dedup();
                    sel.into()
                }
            }
            None => (0..self.entries.len() as u32).collect(),
        };
        self.selected.borrow_mut().insert(key, Rc::clone(&sel));
        sel
    }

    fn spelled_by(&self, def: &Definition) -> Rc<Spelled> {
        let key = def_key(def);
        if let Some(s) = self.spelled.borrow().get(&key) {
            return Rc::clone(s);
        }
        let mut found = HashSet::default();
        let mut named = HashSet::default();
        let ok = match def {
            Definition::Module(m) => self.scan(*m, &mut found, &mut named),
            Definition::Interface(i) => self.scan(*i, &mut found, &mut named),
            Definition::Program(p) => self.scan(*p, &mut found, &mut named),
            _ => false,
        };
        let spelled: Rc<Spelled> = Rc::new(ok.then(|| {
            let mut ids: Vec<u32> = found.into_iter().collect();
            ids.sort_unstable();
            let mut named: Vec<String> = named.into_iter().collect();
            named.sort_unstable();
            (ids, named)
        }));
        self.spelled.borrow_mut().insert(key, Rc::clone(&spelled));
        spelled
    }

    /// Read every string of `v`; false when the traversal stopped early.
    fn scan(
        &self,
        v: &dyn erased::Scannable,
        found: &mut HashSet<u32>,
        named: &mut HashSet<String>,
    ) -> bool {
        let mut scan = Scan {
            scope: self,
            found,
            named,
        };
        v.scan(&mut scan).is_ok()
    }

    fn note(&self, word: &str, found: &mut HashSet<u32>, named: &mut HashSet<String>) {
        if let Some(ids) = self.by_word.get(word) {
            found.extend(ids.iter().copied());
        }
        if self.instantiable.contains(word) {
            named.insert(word.to_string());
        }
    }
}

fn instantiable(d: &Definition) -> bool {
    matches!(
        d,
        Definition::Module(_) | Definition::Interface(_) | Definition::Program(_)
    )
}

fn def_key(def: &Definition) -> (String, usize) {
    let addr = match def {
        Definition::Module(m) => *m as *const _ as usize,
        Definition::Interface(i) => *i as *const _ as usize,
        Definition::Program(p) => *p as *const _ as usize,
        Definition::Class(c) => *c as *const _ as usize,
        Definition::Covergroup(c) => *c as *const _ as usize,
        Definition::Package(p) => *p as *const _ as usize,
        Definition::Typedef(t) => *t as *const _ as usize,
        Definition::Udp(u) => *u as *const _ as usize,
    };
    (def.name().to_string(), addr)
}

/// The identifier words of a table key after its last `::`.
fn key_words(key: &str) -> impl Iterator<Item = &str> {
    let leaf = key.rsplit_once("::").map_or(key, |(_, l)| l);
    words(leaf)
}

/// Identifier words of a string: runs of `[A-Za-z0-9_$]` that do not start
/// with a digit.
fn words(s: &str) -> impl Iterator<Item = &str> {
    s.split(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == '$'))
        .filter(|w| w.chars().next().is_some_and(|c| !c.is_ascii_digit()))
}

mod erased {
    /// `Serialize` for a `&dyn`: the scanner is the only serializer.
    pub(super) trait Scannable {
        fn scan(&self, s: &mut super::Scan<'_>) -> Result<(), super::Error>;
    }
    impl<T: serde::Serialize + ?Sized> Scannable for T {
        fn scan(&self, s: &mut super::Scan<'_>) -> Result<(), super::Error> {
            self.serialize(s)
        }
    }
}

type Error = serde::de::value::Error;

struct Scan<'a> {
    scope: &'a ParamScope,
    found: &'a mut HashSet<u32>,
    named: &'a mut HashSet<String>,
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
    serialize_f64(f64) }
    fn serialize_char(self, c: char) -> Result<(), Error> {
        let mut buf = [0u8; 4];
        let s: &str = c.encode_utf8(&mut buf);
        self.serialize_str(s)
    }
    fn serialize_str(self, v: &str) -> Result<(), Error> {
        // A string is a name, or a text holding names (a dotted path, a
        // string literal, a macro body): look up each of its words.
        for w in words(v) {
            self.scope.note(w, self.found, self.named);
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

#[cfg(test)]
mod tests {
    use super::{key_words, words};

    #[test]
    fn a_key_is_named_by_the_words_after_its_package() {
        let w = |k| key_words(k).collect::<Vec<_>>();
        assert_eq!(w("pk::BASE"), ["BASE"]);
        assert_eq!(w("BASE"), ["BASE"]);
        assert_eq!(w("pk::LIM[3]"), ["LIM"]);
        assert_eq!(w("pk::Cfg.VLEN"), ["Cfg", "VLEN"]);
        assert_eq!(w("cls::inner::N"), ["N"]);
    }

    #[test]
    fn a_text_is_read_as_its_words() {
        let w = |s| words(s).collect::<Vec<_>>();
        assert_eq!(w("a.b[2]"), ["a", "b"]);
        assert_eq!(w("%0d FILL_3"), ["FILL_3"]);
        assert_eq!(w("8'hFF"), ["hFF"]);
        assert_eq!(w("$unit::X"), ["$unit", "X"]);
    }
}
