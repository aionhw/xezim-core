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
//! - the file-scope `let`s (a `let` body is expanded where it is used,
//!   §11.12), and every resolved `bind` with the definition it binds (its
//!   overrides and connections are evaluated in the target's scope, §23.11).
//!
//! Package items and file-scope classes, covergroups and typedefs are
//! evaluated where they are declared, so their words are not read here.
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
    by_name: HashMap<String, u32>,
    /// Module, interface and program names.
    instantiable: HashSet<String>,
    /// Entries every scope holds: keys without a word, and the names the
    /// file-scope `let`s and the binds spell.
    common: Vec<u32>,
    spelled: RefCell<HashMap<(String, usize), Rc<Spelled>>>,
    selected: RefCell<HashMap<(String, usize), Rc<[u32]>>>,
    /// The words the file-scope `let`s and the binds spell (`None`: one
    /// could not be read to the end).
    common_words: Rc<Option<HashSet<String>>>,
    /// Per definition, only its own and its immediate children's words.
    words: RefCell<HashMap<(String, usize), Rc<ScopeWords>>>,
    /// Absence from a scope matters too. Share identical absence masks instead
    /// of retaining a copy of the immutable table in each prepared-body key.
    missing: RefCell<HashSet<Rc<[u64]>>>,
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
        let by_name = entries
            .iter()
            .enumerate()
            .map(|(i, (name, _))| (name.clone(), i as u32))
            .collect();
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
            by_name,
            instantiable,
            common,
            spelled: RefCell::default(),
            selected: RefCell::default(),
            common_words: Rc::new(None),
            words: RefCell::default(),
            missing: RefCell::default(),
        };
        let mut found = HashSet::default();
        let mut named = HashSet::default();
        let mut words = HashSet::default();
        let mut all = false;
        let mut read = |v: &dyn erased::Scannable, scope: &ParamScope| {
            all |= !scope.scan_into(v, &mut found, &mut named, Some(&mut words));
        };
        // The items of packages and the file-scope classes, covergroups and
        // typedefs are evaluated where they are declared, and a name no scope
        // spells is answered by `PARAM_FALLBACK_TLS`, so what they spell is
        // not part of every scope. Reading it made a design whose packages
        // spell most package parameters give every instance nearly the whole
        // table again, and key every prepared body by it (aionhw/xezim#870).
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
            scope.common_words = Rc::new(Some(words));
        }
        scope
    }

    /// Every word an expression in `def`'s scope can be written with: its
    /// own syntax, that of the definitions it names (an instance array's
    /// ports are sized in the parent), and what the file-scope `let`s and
    /// the binds spell. `None` when one of them could not be
    /// read to the end. A parameter none of these words names is read by no
    /// expression the scope evaluates.
    pub(super) fn scope_words(
        &self,
        def: Definition,
        definitions: &HashMap<String, Definition>,
    ) -> Rc<ScopeWords> {
        let key = def_key(&def);
        if let Some(w) = self.words.borrow().get(&key) {
            return Rc::clone(w);
        }
        let mut words = self
            .common_words
            .as_ref()
            .as_ref()
            .map(|_| HashSet::default());
        let mut named = HashSet::default();
        let mut read = |d: &Definition, named: &mut HashSet<String>| {
            let Some(out) = words.as_mut() else {
                return;
            };
            let mut found = HashSet::default();
            let ok = match d {
                Definition::Module(m) => self.scan_into(*m, &mut found, named, Some(out)),
                Definition::Interface(i) => self.scan_into(*i, &mut found, named, Some(out)),
                Definition::Program(p) => self.scan_into(*p, &mut found, named, Some(out)),
                _ => false,
            };
            if !ok {
                words = None;
            }
        };
        read(&def, &mut named);
        for name in std::mem::take(&mut named) {
            if name != def.name()
                && let Some(child) = definitions.get(&name)
            {
                read(child, &mut HashSet::default());
            }
        }
        let words = Rc::new(ScopeWords {
            common: Rc::clone(&self.common_words),
            local: words,
        });
        self.words.borrow_mut().insert(key, Rc::clone(&words));
        words
    }

    /// An exact key relative to the immutable table held by this scope.
    /// Unchanged entries need no payload. Missing eligible entries are retained
    /// explicitly: an absent bare name must not alias a visible package value.
    pub(super) fn prepared_key(
        &self,
        def: Definition,
        definitions: &HashMap<String, Definition>,
        params: &HashMap<String, Value>,
    ) -> (PreparedKey, usize) {
        let words = self.scope_words(def, definitions);
        let mut changed = Vec::new();
        for (name, value) in params {
            if words.spells(name)
                && !self
                    .by_name
                    .get(name)
                    .is_some_and(|&i| self.entries[i as usize].1 == *value)
            {
                changed.push((name.clone(), value.clone()));
            }
        }
        changed.sort_unstable_by(|a, b| a.0.cmp(&b.0));
        let mut missing = Vec::new();
        for (i, (name, _)) in self.entries.iter().enumerate() {
            if words.spells(name) && !params.contains_key(name) {
                if missing.is_empty() {
                    missing.resize(self.entries.len().div_ceil(64), 0u64);
                }
                missing[i / 64] |= 1 << (i % 64);
            }
        }
        while missing.last() == Some(&0) {
            missing.pop();
        }
        // Rc<[u64]> hashes and compares its complete contents. This interner
        // is collision-safe; a digest alone would not be a valid cache key.
        let mut masks = self.missing.borrow_mut();
        let (missing, shared_bytes) = if let Some(mask) = masks.get(missing.as_slice()) {
            (Rc::clone(mask), 0)
        } else {
            let bytes = missing.len() * size_of::<u64>();
            let mask: Rc<[u64]> = missing.into();
            masks.insert(Rc::clone(&mask));
            (mask, bytes)
        };
        let key = PreparedKey {
            definition: def_key(&def),
            missing,
            changed,
        };
        let bytes = key.retained_bytes() + shared_bytes;
        (key, bytes)
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
        self.scan_into(v, found, named, None)
    }

    /// `scan`, also collecting every word into `words`.
    fn scan_into(
        &self,
        v: &dyn erased::Scannable,
        found: &mut HashSet<u32>,
        named: &mut HashSet<String>,
        words: Option<&mut HashSet<String>>,
    ) -> bool {
        let mut scan = Scan {
            scope: self,
            found,
            named,
            words,
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

/// The common words have one owner for the whole inlining pass. Keeping them
/// separate from local words avoids one large package-word clone per definition.
pub(super) struct ScopeWords {
    common: Rc<Option<HashSet<String>>>,
    local: Option<HashSet<String>>,
}

impl ScopeWords {
    fn spells(&self, key: &str) -> bool {
        let (Some(common), Some(local)) = (&*self.common, &self.local) else {
            return true;
        };
        let mut any = false;
        for word in key_words(key) {
            any = true;
            if common.contains(word) || local.contains(word) {
                return true;
            }
        }
        !any
    }
}

/// Complete semantic parameter values, relative to one immutable ParamScope.
/// The cache and scope have the same lifetime; IDs never escape that pass.
#[derive(Debug, PartialEq, Eq, Hash)]
pub(super) struct PreparedKey {
    definition: (String, usize),
    missing: Rc<[u64]>,
    changed: Vec<(String, Value)>,
}

impl PreparedKey {
    /// Retained key payload, excluding separately counted interned masks and
    /// allocator/hash-table overhead. Wide values include both complete planes.
    fn retained_bytes(&self) -> usize {
        size_of::<Self>()
            + self.definition.0.len()
            + self
                .changed
                .iter()
                .map(|(name, value)| {
                    size_of::<(String, Value)>()
                        + name.len()
                        + if value.width > 64 {
                            value.width.div_ceil(64) as usize * 16
                        } else {
                            0
                        }
                })
                .sum::<usize>()
    }
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
    words: Option<&'a mut HashSet<String>>,
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
            if let Some(out) = self.words.as_mut() {
                out.insert(w.to_string());
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
    use super::{ParamScope, key_words, words};
    use crate::ast::Description;
    use crate::elaborate::Definition;
    use crate::hasher::HashMap;
    use crate::value::Value;

    /// aionhw/xezim#870: what a package's own functions spell is no part of
    /// an instance's scope. Only the module's own words select entries, so a
    /// package whose items spell most of its parameters does not hand every
    /// instance the whole table again.
    #[test]
    fn package_items_do_not_widen_every_scope() {
        let src = "package pkg;
  localparam int A = 1;
  localparam int FILL = 3;
  function automatic int f(); return FILL; endfunction
  typedef logic [FILL-1:0] t_t;
  class c; static function int g(); return FILL; endfunction endclass
endpackage
module top; localparam int X = pkg::A + pkg::f(); endmodule
";
        let parsed = crate::parse(src);
        assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
        let mut defs: HashMap<String, Definition> = HashMap::default();
        for d in &parsed.source.descriptions {
            match d {
                Description::Module(m) => {
                    defs.insert(m.name.name.clone(), Definition::Module(m));
                }
                Description::Package(p) => {
                    defs.insert(p.name.name.clone(), Definition::Package(p));
                }
                _ => {}
            }
        }
        let mut table: HashMap<String, Value> = HashMap::default();
        table.insert("pkg::A".into(), Value::from_u64(1, 32));
        table.insert("pkg::FILL".into(), Value::from_u64(3, 32));
        let scope = ParamScope::new(&table, &defs, &HashMap::default(), &HashMap::default());
        let top = scope.top_scope(defs["top"], &defs);
        assert!(top.contains_key("pkg::A"), "{top:?}");
        assert!(!top.contains_key("pkg::FILL"), "{top:?}");
    }

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

    fn definitions(
        source: &crate::ast::SourceText,
    ) -> crate::hasher::HashMap<String, super::Definition<'_>> {
        source
            .descriptions
            .iter()
            .filter_map(|description| {
                let definition = match description {
                    crate::ast::Description::Module(m) => super::Definition::Module(m),
                    crate::ast::Description::Package(p) => super::Definition::Package(p),
                    _ => return None,
                };
                Some((definition.name().to_string(), definition))
            })
            .collect()
    }

    /// §11.12, §23.10: file-scope let bodies contribute shared words, while
    /// their immutable spelling set and unchanged values are retained once (#721).
    #[test]
    fn common_words_and_absence_masks_are_shared_across_definitions() {
        use super::{ParamScope, Value};
        use crate::hasher::HashMap;
        use std::rc::Rc;
        let mut text = String::from("package pk;\n");
        let mut table = HashMap::default();
        for i in 0..2048 {
            text.push_str(&format!("localparam int P_{i} = {i};\n"));
            table.insert(format!("pk::P_{i}"), Value::from_u64(i, 32));
        }
        text.push_str("endpackage\nlet shared_values = {");
        for i in 0..2048 {
            if i > 0 {
                text.push_str(", ");
            }
            text.push_str(&format!("pk::P_{i}"));
        }
        text.push_str("};\n");
        for i in 0..64 {
            text.push_str(&format!(
                "module m{i} #(parameter int W=1); logic[W-1:0] a; endmodule\n"
            ));
        }
        let parsed = crate::parse_str(&text).unwrap();
        let defs = definitions(&parsed.source);
        let lets: HashMap<_, _> = parsed
            .source
            .descriptions
            .iter()
            .filter_map(|description| match description {
                Description::PackageItem(crate::ast::decl::PackageItem::Let(decl)) => {
                    Some((decl.name.name.clone(), decl.clone()))
                }
                _ => None,
            })
            .collect();
        assert_eq!(lets.len(), 1);
        let scope = ParamScope::new(&table, &defs, &HashMap::default(), &lets);
        let empty = HashMap::default();
        let mut previous_mask = None;
        let mut bytes = 0;
        for i in 0..64 {
            let def = defs[&format!("m{i}")];
            let words = scope.scope_words(def, &defs);
            assert!(Rc::ptr_eq(&scope.common_words, &words.common));
            assert!(words.local.as_ref().unwrap().len() < 16);
            assert!(words.spells("pk::P_2047"));
            let (key, added) = scope.prepared_key(def, &defs, &empty);
            assert!(key.changed.is_empty());
            if let Some(mask) = &previous_mask {
                assert!(Rc::ptr_eq(mask, &key.missing));
            }
            previous_mask = Some(Rc::clone(&key.missing));
            bytes += added;
            let mut params = table.clone();
            params.insert("W".to_string(), Value::from_u64(i + 1, 32));
            let (present, added) = scope.prepared_key(def, &defs, &params);
            assert_eq!(present.changed.len(), 1);
            assert!(present.missing.is_empty());
            assert!(added < 512, "key retained {added} bytes");
        }
        assert_eq!(scope.missing.borrow().len(), 2);
        assert!(
            bytes < 16 * 1024,
            "shared masks/keys retained {bytes} bytes"
        );
    }

    /// §6.20, §23.10: a local/ancestor override, an absent name and an
    /// unchanged visible package value denote distinct scope states.
    #[test]
    fn prepared_keys_preserve_absence_and_parameter_shadowing() {
        use super::{ParamScope, Value};
        use crate::hasher::HashMap;
        let parsed = crate::parse_str("module m; logic[P-1:0] a; endmodule").unwrap();
        let defs = definitions(&parsed.source);
        let table = HashMap::from_iter([("P".into(), Value::from_u64(3, 32))]);
        let scope = ParamScope::new(&table, &defs, &HashMap::default(), &HashMap::default());
        let def = defs["m"];
        let (visible, _) = scope.prepared_key(def, &defs, &table);
        let (absent, _) = scope.prepared_key(def, &defs, &HashMap::default());
        assert_ne!(visible, absent);
        let mut local = table.clone();
        local.insert("P".into(), Value::from_u64(9, 32));
        let (shadowed, _) = scope.prepared_key(def, &defs, &local);
        assert_ne!(visible, shadowed);
        assert_ne!(absent, shadowed);
        assert_eq!(shadowed.changed.len(), 1);
        local.insert("UNREAD".into(), Value::from_u64(23, 32));
        assert_eq!(shadowed, scope.prepared_key(def, &defs, &local).0);
        local.insert("P".into(), Value::from_u64(3, 32));
        assert_eq!(visible, scope.prepared_key(def, &defs, &local).0);
    }

    /// §5.7, §6.20: cache equality must compare the whole value, including
    /// context-sensitive fill/sign/real flags and both planes above bit 63.
    #[test]
    fn prepared_keys_compare_complete_parameter_values() {
        use super::{ParamScope, Value};
        use crate::hasher::{HashMap, HashSet};
        use crate::value::LogicBit;
        let parsed = crate::parse_str("module m; localparam Q=P; endmodule").unwrap();
        let defs = definitions(&parsed.source);
        let table = HashMap::from_iter([("P".into(), Value::from_u64(1, 1))]);
        let scope = ParamScope::new(&table, &defs, &HashMap::default(), &HashMap::default());
        let one = Value::from_u64(1, 1);
        let mut signed = one.clone();
        signed.is_signed = true;
        let mut real = one.clone();
        real.is_real = true;
        let wide = Value::from_u64(1, 128);
        let mut high = wide.clone();
        high.set_bit(90, LogicBit::One);
        let mut x = wide.clone();
        x.set_bit(90, LogicBit::X);
        let mut z = wide.clone();
        z.set_bit(90, LogicBit::Z);
        let values = [
            one,
            Value::fill_of('1'),
            signed,
            real,
            Value::from_u64(1, 32),
            wide,
            high,
            x,
            z,
            Value::from_string("first___same_low"),
            Value::from_string("other___same_low"),
        ];
        let mut keys = HashSet::default();
        for value in &values {
            let params = HashMap::from_iter([("P".into(), value.clone())]);
            assert!(keys.insert(scope.prepared_key(defs["m"], &defs, &params).0));
        }
        assert_eq!(keys.len(), values.len());
        // A cache hit uses equality as well as hashing, including baseline
        // omissions; constructing the key again finds the same prepared body.
        let mut cache = HashMap::default();
        let (key, _) = scope.prepared_key(defs["m"], &defs, &table);
        cache.insert(key, 42);
        assert_eq!(
            cache.get(&scope.prepared_key(defs["m"], &defs, &table).0),
            Some(&42)
        );
    }
}
