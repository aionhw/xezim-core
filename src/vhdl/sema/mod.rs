//! Semantic analysis of VHDL (IEEE 1076-2008): design libraries, visibility,
//! types, overload resolution and static evaluation, producing the typed
//! HIR (`hir`) the lowering works from.
//!
//! Design units are analysed on demand: a reference to `ieee.numeric_std`
//! analyses that package (and what it depends on) first, so the order of the
//! source files does not matter.

mod config;
mod decl;
mod expr;
pub mod hir;
mod predefined;
mod stmt;

use std::collections::{BTreeMap, HashMap};

use super::ast::{self, Ident, LibraryUnit, Name, NameKind, Span};
use super::cst::{self, SourceFile};
use hir::*;

/// A named entity visible in a declarative region.
#[derive(Clone, Debug, PartialEq)]
pub enum Sym {
    Type(TypeId),
    Obj(ObjId),
    Sub(SubId),
    /// An enumeration literal: its type and position.
    EnumLit(TypeId, u32),
    /// A physical unit: its type and value in base units.
    Unit(TypeId, i64),
    Library(String),
    Package(PkgKey),
    Entity(String, String),
    Component(usize),
    /// A loop or statement label (for `exit`/`next`).
    Label(usize),
    /// An alias of an object name (index into `Design::aliases`).
    Alias(usize),
    Attribute(TypeId),
}

impl Sym {
    /// Subprograms and enumeration literals can be overloaded (§4.5.1).
    fn overloadable(&self) -> bool {
        matches!(self, Sym::Sub(_) | Sym::EnumLit(..))
    }
}

/// A package by library and name.
pub type PkgKey = (String, String);

pub type RegionId = usize;

#[derive(Clone, Debug)]
pub enum UseItem {
    /// `use lib.pkg.all`
    All(PkgKey),
    /// `use lib.pkg.name`
    Named(PkgKey, String),
    /// `use lib.unit` (a unit name made directly visible).
    Unit(String, String),
}

#[derive(Default, Debug)]
pub struct Region {
    pub parent: Option<RegionId>,
    pub syms: HashMap<String, Vec<Sym>>,
    pub uses: Vec<UseItem>,
}

/// Where a design unit's source is.
#[derive(Clone, Debug)]
struct UnitSrc {
    file: FileId,
    index: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum State {
    Analyzing,
    Done,
}

/// Types of package STANDARD the analysis refers to directly.
#[derive(Clone, Debug, Default)]
pub struct StdTypes {
    pub boolean: TypeId,
    pub bit: TypeId,
    pub character: TypeId,
    pub severity_level: TypeId,
    pub integer: TypeId,
    pub natural: TypeId,
    pub positive: TypeId,
    pub real: TypeId,
    pub time: TypeId,
    pub delay_length: TypeId,
    pub string: TypeId,
    pub bit_vector: TypeId,
    pub boolean_vector: TypeId,
    pub file_open_kind: TypeId,
    pub file_open_status: TypeId,
    pub universal_integer: TypeId,
    pub universal_real: TypeId,
    /// IEEE.STD_LOGIC_1164.STD_ULOGIC, once that package is analysed (the
    /// matching operators are predefined for it, §9.2.3).
    pub std_ulogic: Option<TypeId>,
}

/// The whole analysed design.
pub struct Design {
    pub files: Vec<SourceFile>,
    asts: Vec<Option<ast::DesignFile>>,
    pub types: Vec<TypeInfo>,
    pub objects: Vec<ObjInfo>,
    pub subprograms: Vec<SubInfo>,
    pub regions: Vec<Region>,
    pub packages: BTreeMap<PkgKey, (Package, RegionId)>,
    /// Package region by key, for packages being analysed.
    pkg_regions: HashMap<PkgKey, RegionId>,
    pub entities: BTreeMap<(String, String), EntityInfo>,
    pub archs: Vec<Architecture>,
    pub components: Vec<ComponentInfo>,
    /// Block configurations being applied (`config::BlockCfg`).
    pub block_configs: Vec<config::BlockCfg>,
    /// Configuration specifications by declarative region, with their
    /// library and file.
    cfg_specs: Vec<(RegionId, ast::ConfigSpec, String, FileId)>,
    /// The block configuration of the architecture or block being
    /// analysed.
    cur_cfg: Option<usize>,
    /// The names alias declarations stand for.
    pub aliases: Vec<HExpr>,
    /// Labels of loops (by `Sym::Label` id) — names only, for diagnostics.
    pub labels: Vec<String>,
    /// Library → unit name → sources (primary units; later wins).
    units: BTreeMap<String, BTreeMap<String, UnitSrc>>,
    bodies: BTreeMap<PkgKey, UnitSrc>,
    arch_srcs: BTreeMap<(String, String), Vec<(String, UnitSrc)>>,
    state: HashMap<(String, String, u8), State>,
    pub std: StdTypes,
    /// Architectures analysed for generic bindings: (arch, generics, ports).
    bound_archs: HashMap<String, (usize, Vec<ObjId>, Vec<ObjId>)>,
    /// Predefined operation instances by name and profile.
    pre_cache: HashMap<String, SubId>,
    /// Library subprogram bodies not analysed yet.
    lazy_bodies: HashMap<SubId, LazyBody>,
    pub errors: Vec<(Loc, String)>,
    /// The library of the unit being analysed (for `work`).
    cur_lib: String,
    cur_file: FileId,
}

/// A library subprogram body kept for analysis on first use.
#[derive(Clone, Debug)]
pub struct LazyBody {
    pub body: ast::SubprogramBody,
    pub region: RegionId,
    pub path: String,
    pub lib: String,
    pub file: FileId,
}

#[derive(Clone, Debug)]
pub struct EntityInfo {
    pub library: String,
    pub name: String,
    pub generics: Vec<ObjId>,
    pub ports: Vec<ObjId>,
    pub region: RegionId,
    pub loc: Loc,
    pub stmts_src: (FileId, usize),
}

#[derive(Clone, Debug)]
pub struct ComponentInfo {
    pub name: String,
    pub generics: Vec<ObjId>,
    pub ports: Vec<ObjId>,
}

/// Result of analysing the configured design: the design and its top
/// architecture (index into `archs`).
pub struct Analysed {
    pub design: Design,
    pub top: usize,
}

impl Design {
    fn new() -> Self {
        Design {
            files: Vec::new(),
            asts: Vec::new(),
            types: Vec::new(),
            objects: Vec::new(),
            subprograms: Vec::new(),
            regions: Vec::new(),
            packages: BTreeMap::new(),
            pkg_regions: HashMap::new(),
            entities: BTreeMap::new(),
            archs: Vec::new(),
            components: Vec::new(),
            block_configs: Vec::new(),
            cfg_specs: Vec::new(),
            cur_cfg: None,
            aliases: Vec::new(),
            labels: Vec::new(),
            units: BTreeMap::new(),
            bodies: BTreeMap::new(),
            arch_srcs: BTreeMap::new(),
            state: HashMap::new(),
            std: StdTypes::default(),
            bound_archs: HashMap::new(),
            pre_cache: HashMap::new(),
            lazy_bodies: HashMap::new(),
            errors: Vec::new(),
            cur_lib: "work".into(),
            cur_file: 0,
        }
    }

    /// The universal types (§5.2.3.1, §5.2.5.1), before package STANDARD.
    fn add_universal_types(&mut self) {
        self.std.universal_integer = self.add_type(
            "universal_integer",
            TypeKind::UniversalInteger,
            Some(StaticRange {
                left: Value::Int(i64::MIN),
                dir: ast::Dir::To,
                right: Value::Int(i64::MAX),
            }),
            None,
        );
        self.std.universal_real = self.add_type(
            "universal_real",
            TypeKind::UniversalReal,
            Some(StaticRange {
                left: Value::Real(-f64::MAX),
                dir: ast::Dir::To,
                right: Value::Real(f64::MAX),
            }),
            None,
        );
    }

    // ---- diagnostics -----------------------------------------------------------

    pub fn loc(&self, span: Span) -> Loc {
        Loc {
            file: self.cur_file,
            span,
        }
    }

    pub fn error(&mut self, span: Span, msg: impl Into<String>) {
        let loc = self.loc(span);
        self.errors.push((loc, msg.into()));
    }

    /// The errors, rendered `file:line:col: error: …` with the source line.
    pub fn render_errors(&self) -> Vec<String> {
        let mut out: Vec<String> = self
            .errors
            .iter()
            .map(|(loc, m)| {
                self.files[loc.file].render(&cst::Diagnostic {
                    span: loc.span.clone(),
                    message: format!("VHDL: {}", m),
                })
            })
            .collect();
        out.dedup();
        out
    }

    /// `file:line` of a location (GHDL's check-failure format).
    pub fn file_line(&self, loc: &Loc) -> (String, usize, usize) {
        let f = &self.files[loc.file];
        let (l, c) = f.line_col(loc.span.start);
        let name = std::path::Path::new(&f.path)
            .file_name()
            .map(|s| s.to_string_lossy().into_owned())
            .unwrap_or_else(|| f.path.clone());
        (name, l, c)
    }

    // ---- arenas -------------------------------------------------------------------

    pub fn add_type(
        &mut self,
        name: &str,
        kind: TypeKind,
        range: Option<StaticRange>,
        loc: Option<Loc>,
    ) -> TypeId {
        self.types.push(TypeInfo {
            name: name.to_string(),
            kind,
            range,
            loc,
        });
        self.types.len() - 1
    }

    pub fn add_obj(&mut self, info: ObjInfo) -> ObjId {
        self.objects.push(info);
        self.objects.len() - 1
    }

    pub fn add_sub(&mut self, info: SubInfo) -> SubId {
        self.subprograms.push(info);
        self.subprograms.len() - 1
    }

    pub fn new_region(&mut self, parent: Option<RegionId>) -> RegionId {
        self.regions.push(Region {
            parent,
            ..Default::default()
        });
        self.regions.len() - 1
    }

    pub fn declare(&mut self, region: RegionId, name: &str, sym: Sym) {
        self.regions[region]
            .syms
            .entry(name.to_string())
            .or_default()
            .push(sym);
    }

    // ---- visibility ---------------------------------------------------------------

    /// The named entities `name` denotes in `region` (§12.3, §12.4):
    /// directly visible declarations, inner hiding outer, then the names use
    /// clauses make potentially visible. Overloadable names accumulate.
    pub fn lookup(&mut self, region: RegionId, name: &str) -> Vec<Sym> {
        let mut out: Vec<Sym> = Vec::new();
        let mut r = Some(region);
        while let Some(id) = r {
            if let Some(syms) = self.regions[id].syms.get(name) {
                for s in syms.clone() {
                    if !s.overloadable() {
                        if out.is_empty() {
                            return vec![s];
                        }
                        return out;
                    }
                    if !out.contains(&s) {
                        out.push(s);
                    }
                }
            }
            r = self.regions[id].parent;
        }
        // Potentially visible through use clauses.
        let mut r = Some(region);
        let mut found_non_overloadable: Vec<Sym> = Vec::new();
        while let Some(id) = r {
            let uses = self.regions[id].uses.clone();
            for u in uses {
                let syms = match &u {
                    UseItem::All(pkg) => self.pkg_syms(pkg, name),
                    UseItem::Named(pkg, n) if n == name => self.pkg_syms(pkg, name),
                    UseItem::Unit(lib, unit) if unit == name => {
                        self.unit_sym(lib, unit).into_iter().collect()
                    }
                    _ => Vec::new(),
                };
                for s in syms {
                    if s.overloadable() {
                        if !out.contains(&s) {
                            out.push(s);
                        }
                    } else if !found_non_overloadable.contains(&s) {
                        found_non_overloadable.push(s);
                    }
                }
            }
            r = self.regions[id].parent;
        }
        if out.is_empty() && found_non_overloadable.len() == 1 {
            return found_non_overloadable;
        }
        if out.is_empty() {
            // Library names: `work`, `std` and those of library clauses.
            if name == "work" {
                let lib = self.cur_lib.clone();
                return vec![Sym::Library(lib)];
            }
        }
        out
    }

    /// The declarations named `name` in a package (analysing it on demand).
    fn pkg_syms(&mut self, pkg: &PkgKey, name: &str) -> Vec<Sym> {
        let Some(region) = self.package_region(pkg) else {
            return Vec::new();
        };
        self.regions[region]
            .syms
            .get(name)
            .cloned()
            .unwrap_or_default()
    }

    /// The region of a package, analysing the package if needed.
    pub fn package_region(&mut self, pkg: &PkgKey) -> Option<RegionId> {
        if let Some(r) = self.pkg_regions.get(pkg) {
            return Some(*r);
        }
        self.analyze_package(&pkg.0, &pkg.1);
        self.pkg_regions.get(pkg).copied()
    }

    /// A unit name selected from a library (`ieee.std_logic_1164`).
    pub fn unit_sym(&mut self, lib: &str, unit: &str) -> Option<Sym> {
        self.ensure_library(lib);
        let src = self.units.get(lib)?.get(unit)?.clone();
        let kind = self.unit_kind(&src)?;
        match kind {
            UnitKind::Package => Some(Sym::Package((lib.to_string(), unit.to_string()))),
            UnitKind::Entity => Some(Sym::Entity(lib.to_string(), unit.to_string())),
            UnitKind::Other => None,
        }
    }

    // ---- libraries ------------------------------------------------------------------

    /// Index a user source file's design units into `library`.
    fn add_file(&mut self, library: &str, parsed: cst::Parsed) {
        let file = self.files.len();
        let ast = parsed.ast;
        if let Some(df) = &ast {
            for (index, u) in df.units.iter().enumerate() {
                let src = UnitSrc { file, index };
                let name = u.unit.name().name.clone();
                match &u.unit {
                    LibraryUnit::PackageBody(_) => {
                        self.bodies.insert((library.to_string(), name), src);
                    }
                    LibraryUnit::Architecture(a) => {
                        self.arch_srcs
                            .entry((library.to_string(), a.entity.name.clone()))
                            .or_default()
                            .push((name, src));
                    }
                    _ => {
                        self.units
                            .entry(library.to_string())
                            .or_default()
                            .insert(name, src);
                    }
                }
            }
        }
        self.files.push(parsed.file);
        self.asts.push(ast);
    }

    /// Make the vendored `std`/`ieee` sources of `lib` known (parsed on
    /// first use of the library).
    fn ensure_library(&mut self, lib: &str) {
        let key = (lib.to_string(), String::new(), 9u8);
        if !matches!(lib, "std" | "ieee") || self.state.contains_key(&key) {
            return;
        }
        self.state.insert(key, State::Done);
        for s in super::libraries::SOURCES
            .iter()
            .filter(|s| s.library == lib)
        {
            let p = cst::parse(SourceFile::new(
                format!("{}/{}", lib, s.file),
                s.text.to_vec(),
            ));
            self.add_file(lib, p);
        }
    }

    fn unit_ast(&self, src: &UnitSrc) -> Option<&ast::DesignUnit> {
        self.asts[src.file].as_ref()?.units.get(src.index)
    }

    fn unit_kind(&self, src: &UnitSrc) -> Option<UnitKind> {
        Some(match &self.unit_ast(src)?.unit {
            LibraryUnit::Package(_) | LibraryUnit::PackageInst(_) => UnitKind::Package,
            LibraryUnit::Entity(_) => UnitKind::Entity,
            _ => UnitKind::Other,
        })
    }

    // ---- unit analysis --------------------------------------------------------------

    /// Run `f` with the current library/file set to those of a unit.
    fn in_unit<R>(&mut self, lib: &str, file: FileId, f: impl FnOnce(&mut Self) -> R) -> R {
        let saved = (
            std::mem::replace(&mut self.cur_lib, lib.to_string()),
            self.cur_file,
        );
        self.cur_file = file;
        let r = f(self);
        self.cur_lib = saved.0;
        self.cur_file = saved.1;
        r
    }

    /// The region of a unit's context clause: `library std, work; use
    /// std.standard.all;` implicitly (§13.2), then the unit's own items.
    fn context_region(&mut self, context: &[ast::ContextItem]) -> RegionId {
        let r = self.new_region(None);
        self.declare(r, "std", Sym::Library("std".into()));
        let work = self.cur_lib.clone();
        self.declare(r, "work", Sym::Library(work.clone()));
        if work != "std" || self.cur_file_is_not_standard() {
            self.regions[r]
                .uses
                .push(UseItem::All(("std".into(), "standard".into())));
        }
        self.apply_context(r, context);
        r
    }

    fn cur_file_is_not_standard(&self) -> bool {
        !self.files[self.cur_file].path.ends_with("standard.vhdl")
    }

    fn apply_context(&mut self, r: RegionId, context: &[ast::ContextItem]) {
        for item in context {
            match item {
                ast::ContextItem::Library(names) => {
                    for n in names {
                        self.ensure_library(&n.name);
                        self.declare(r, &n.name, Sym::Library(n.name.clone()));
                    }
                }
                ast::ContextItem::Use(names) => {
                    for n in names {
                        self.use_clause(r, n);
                    }
                }
                ast::ContextItem::Context(names) => {
                    for n in names {
                        self.context_reference(r, n);
                    }
                }
            }
        }
    }

    /// `use lib.pkg.all`, `use lib.pkg.name`, `use work.pkg` (§12.4).
    pub fn use_clause(&mut self, r: RegionId, n: &Name) {
        let NameKind::Selected(prefix, suffix) = &n.kind else {
            self.error(n.span.clone(), "a use clause names a selected name");
            return;
        };
        let target = self.resolve_static_name(r, prefix);
        match (target, suffix) {
            (Some(Sym::Package(pkg)), ast::Suffix::All(_)) => {
                if self.package_region(&pkg).is_some() {
                    self.regions[r].uses.push(UseItem::All(pkg));
                }
            }
            (Some(Sym::Package(pkg)), ast::Suffix::Ident(i)) => {
                self.package_region(&pkg);
                self.regions[r]
                    .uses
                    .push(UseItem::Named(pkg, i.name.clone()));
            }
            (Some(Sym::Package(pkg)), ast::Suffix::Op(op, _)) => {
                self.package_region(&pkg);
                self.regions[r]
                    .uses
                    .push(UseItem::Named(pkg, format!("\"{}\"", op)));
            }
            (Some(Sym::Package(pkg)), ast::Suffix::Char(c, _)) => {
                self.package_region(&pkg);
                self.regions[r]
                    .uses
                    .push(UseItem::Named(pkg, format!("'{}'", *c as char)));
            }
            (Some(Sym::Library(lib)), ast::Suffix::Ident(i)) => {
                self.regions[r]
                    .uses
                    .push(UseItem::Unit(lib, i.name.clone()));
            }
            (Some(Sym::Library(lib)), ast::Suffix::All(_)) => {
                self.ensure_library(&lib);
                let names: Vec<String> = self
                    .units
                    .get(&lib)
                    .map(|u| u.keys().cloned().collect())
                    .unwrap_or_default();
                for u in names {
                    self.regions[r].uses.push(UseItem::Unit(lib.clone(), u));
                }
            }
            _ => self.error(
                n.span.clone(),
                "this use clause does not name a package or library",
            ),
        }
    }

    fn context_reference(&mut self, r: RegionId, n: &Name) {
        match self.resolve_context(r, n) {
            Some(items) => self.apply_context(r, &items),
            None => self.error(n.span.clone(), "not a context declaration"),
        }
    }

    fn resolve_context(&mut self, r: RegionId, n: &Name) -> Option<Vec<ast::ContextItem>> {
        let NameKind::Selected(prefix, ast::Suffix::Ident(i)) = &n.kind else {
            return None;
        };
        let Some(Sym::Library(lib)) = self.resolve_static_name(r, prefix) else {
            return None;
        };
        self.ensure_library(&lib);
        let src = self.units.get(&lib)?.get(&i.name)?.clone();
        match &self.unit_ast(&src)?.unit {
            LibraryUnit::Context(c) => Some(c.items.clone()),
            _ => None,
        }
    }

    /// Resolve a name made of selected parts denoting a library, package or
    /// unit (used by use clauses and selected names).
    pub fn resolve_static_name(&mut self, r: RegionId, n: &Name) -> Option<Sym> {
        match &n.kind {
            NameKind::Simple(i) => {
                let syms = self.lookup(r, &i.name);
                syms.into_iter().next()
            }
            NameKind::Selected(prefix, ast::Suffix::Ident(i)) => {
                match self.resolve_static_name(r, prefix)? {
                    Sym::Library(lib) => self.unit_sym(&lib, &i.name),
                    Sym::Package(pkg) => self.pkg_syms(&pkg, &i.name).into_iter().next(),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Analyse a package declaration (on demand).
    pub fn analyze_package(&mut self, lib: &str, name: &str) {
        let key = (lib.to_string(), name.to_string(), 0u8);
        match self.state.get(&key) {
            Some(State::Done) => return,
            Some(State::Analyzing) => return,
            None => {}
        }
        self.ensure_library(lib);
        let Some(src) = self.units.get(lib).and_then(|u| u.get(name)).cloned() else {
            return;
        };
        self.state.insert(key.clone(), State::Analyzing);
        let Some(du) = self.unit_ast(&src).cloned() else {
            return;
        };
        self.in_unit(lib, src.file, |d| match &du.unit {
            LibraryUnit::Package(p) => {
                let ctx = d.context_region(&du.context);
                d.package_decl(lib, p, ctx);
            }
            LibraryUnit::PackageInst(p) => {
                d.error(p.span.clone(), "package instantiation is not supported yet");
            }
            _ => {}
        });
        self.state.insert(key, State::Done);
    }

    /// Analyse a package body (needed to lower its subprograms).
    pub fn analyze_package_body(&mut self, lib: &str, name: &str) {
        let key = (lib.to_string(), name.to_string(), 1u8);
        if self.state.contains_key(&key) {
            return;
        }
        self.state.insert(key.clone(), State::Analyzing);
        let pkg = (lib.to_string(), name.to_string());
        let Some(src) = self.bodies.get(&pkg).cloned() else {
            self.state.insert(key, State::Done);
            return;
        };
        let Some(du) = self.unit_ast(&src).cloned() else {
            return;
        };
        let Some(pkg_region) = self.package_region(&pkg) else {
            return;
        };
        self.in_unit(lib, src.file, |d| {
            if let LibraryUnit::PackageBody(b) = &du.unit {
                let ctx = d.context_region(&du.context);
                let r = d.new_region(Some(pkg_region));
                d.regions[r].uses = d.regions[ctx].uses.clone();
                for (n, s) in d.regions[ctx].syms.clone() {
                    for x in s {
                        d.declare(r, &n, x);
                    }
                }
                let mut objs = Vec::new();
                let mut subs = Vec::new();
                d.decls(
                    r,
                    &b.decls,
                    &mut objs,
                    &mut subs,
                    &format!("{}.{}", lib, name),
                );
                if let Some((p, _)) = d.packages.get_mut(&pkg) {
                    p.objects.extend(objs);
                    p.subprograms.extend(subs);
                }
            }
        });
        self.state.insert(key, State::Done);
    }

    fn package_decl(&mut self, lib: &str, p: &ast::PackageDecl, ctx: RegionId) {
        if !p.generics.is_empty() {
            self.error(
                p.name.span.clone(),
                "generic packages are not supported yet",
            );
        }
        let r = self.new_region(Some(ctx));
        let key = (lib.to_string(), p.name.name.clone());
        self.pkg_regions.insert(key.clone(), r);
        let mut objs = Vec::new();
        let mut subs = Vec::new();
        self.decls(
            r,
            &p.decls,
            &mut objs,
            &mut subs,
            &format!("{}.{}", lib, p.name.name),
        );
        if lib == "std" && p.name.name == "standard" {
            self.record_std_types(r);
        }
        if lib == "ieee"
            && p.name.name == "std_logic_1164"
            && let Some(Sym::Type(t)) = self.regions[r]
                .syms
                .get("std_ulogic")
                .and_then(|v| v.first())
        {
            self.std.std_ulogic = Some(*t);
        }
        self.packages.insert(
            key.clone(),
            (
                Package {
                    library: lib.to_string(),
                    name: p.name.name.clone(),
                    objects: objs,
                    subprograms: subs,
                },
                r,
            ),
        );
    }

    fn record_std_types(&mut self, r: RegionId) {
        let ty = |d: &mut Self, n: &str| -> TypeId {
            match d.regions[r].syms.get(n).and_then(|v| v.first()) {
                Some(Sym::Type(t)) => *t,
                _ => 0,
            }
        };
        self.std.boolean = ty(self, "boolean");
        self.std.bit = ty(self, "bit");
        self.std.character = ty(self, "character");
        self.std.severity_level = ty(self, "severity_level");
        self.std.integer = ty(self, "integer");
        self.std.natural = ty(self, "natural");
        self.std.positive = ty(self, "positive");
        self.std.real = ty(self, "real");
        self.std.time = ty(self, "time");
        self.std.delay_length = ty(self, "delay_length");
        self.std.string = ty(self, "string");
        self.std.bit_vector = ty(self, "bit_vector");
        self.std.boolean_vector = ty(self, "boolean_vector");
        self.std.file_open_kind = ty(self, "file_open_kind");
        self.std.file_open_status = ty(self, "file_open_status");
    }

    /// Analyse an entity (on demand).
    pub fn analyze_entity(&mut self, lib: &str, name: &str) -> Option<EntityInfo> {
        let k = (lib.to_string(), name.to_string());
        if let Some(e) = self.entities.get(&k) {
            return Some(e.clone());
        }
        let info = self.entity_with(lib, name, &[])?;
        self.entities.insert(k, info.clone());
        Some(info)
    }

    /// Analyse an entity with generic values (by name) in place of the
    /// defaults: its ports and declarations see them (§14.4.2.2).
    fn entity_with(
        &mut self,
        lib: &str,
        name: &str,
        binding: &[(String, Value)],
    ) -> Option<EntityInfo> {
        self.ensure_library(lib);
        let src = self.units.get(lib)?.get(name)?.clone();
        let du = self.unit_ast(&src)?.clone();
        let LibraryUnit::Entity(e) = &du.unit else {
            return None;
        };
        let info = self.in_unit(lib, src.file, |d| {
            let ctx = d.context_region(&du.context);
            let r = d.new_region(Some(ctx));
            let path = format!("{}.{}", lib, name);
            let generics = d.interface_list(r, &e.generics, decl::IfaceKind::Generic, &path);
            for g in &generics {
                let gname = d.objects[*g].name.clone();
                if let Some((_, v)) = binding.iter().find(|(n, _)| *n == gname) {
                    let o = &mut d.objects[*g];
                    o.static_val = Some(v.clone());
                    o.init = Some(decl::lit_expr(v.clone(), o.ty, o.loc.clone()));
                }
            }
            let ports = d.interface_list(r, &e.ports, decl::IfaceKind::Port, &path);
            let mut objs = Vec::new();
            let mut subs = Vec::new();
            d.decls(r, &e.decls, &mut objs, &mut subs, &path);
            EntityInfo {
                library: lib.to_string(),
                name: name.to_string(),
                generics,
                ports,
                region: r,
                loc: d.loc(e.name.span.clone()),
                stmts_src: (src.file, src.index),
            }
        });
        Some(info)
    }

    /// The architecture of an instance whose generic map gives values
    /// other than the defaults: analysed again for those values, once per
    /// distinct binding (§14.5.2). Returns it and its entity's ports.
    pub(super) fn analyze_bound_arch(
        &mut self,
        inst: &Instance,
        binding: Vec<(String, Value)>,
    ) -> Option<(usize, Vec<ObjId>, Vec<ObjId>)> {
        let key = format!(
            "{}.{}({:?}){:?}{:?}",
            inst.library, inst.entity, inst.arch, binding, inst.config
        );
        if let Some(r) = self.bound_archs.get(&key) {
            return Some(r.clone());
        }
        let ent = self.entity_with(&inst.library, &inst.entity, &binding)?;
        let list = self
            .arch_srcs
            .get(&(inst.library.clone(), inst.entity.clone()))?
            .clone();
        let (_, src) = match &inst.arch {
            Some(a) => list.iter().rev().find(|(n, _)| n == a)?.clone(),
            None => list.last()?.clone(),
        };
        let du = self.unit_ast(&src)?.clone();
        let LibraryUnit::Architecture(a) = &du.unit else {
            return None;
        };
        let lib = inst.library.clone();
        let cfg = inst.config;
        let arch = self.in_unit(&lib, src.file, |d| {
            let ctx = d.context_region(&du.context);
            let r = d.new_region(Some(ent.region));
            d.regions[r].uses = d.regions[ctx].uses.clone();
            for (n, s) in d.regions[ctx].syms.clone() {
                for x in s {
                    d.declare(r, &n, x);
                }
            }
            let saved = std::mem::replace(&mut d.cur_cfg, cfg);
            let arch = d.architecture(r, &ent, a);
            d.cur_cfg = saved;
            arch
        });
        self.archs.push(arch);
        let res = (
            self.archs.len() - 1,
            ent.generics.clone(),
            ent.ports.clone(),
        );
        self.bound_archs.insert(key, res.clone());
        Some(res)
    }

    /// Analyse the architecture of an entity: `arch` or the most recently
    /// analysed one (the default binding, §7.3.3).
    pub fn analyze_arch(&mut self, lib: &str, entity: &str, arch: Option<&str>) -> Option<usize> {
        let ent = self.analyze_entity(lib, entity)?;
        let list = self
            .arch_srcs
            .get(&(lib.to_string(), entity.to_string()))?
            .clone();
        let (aname, src) = match arch {
            Some(a) => list.iter().rev().find(|(n, _)| n == a)?.clone(),
            None => list.last()?.clone(),
        };
        // The default analysis (not one for a generic binding).
        let bound: Vec<usize> = self.bound_archs.values().map(|b| b.0).collect();
        if let Some(i) = self.archs.iter().enumerate().position(|(i, a)| {
            a.library == lib
                && a.entity == entity
                && a.name == aname
                && !a.nested
                && !bound.contains(&i)
        }) {
            return Some(i);
        }
        let du = self.unit_ast(&src)?.clone();
        let LibraryUnit::Architecture(a) = &du.unit else {
            return None;
        };
        let arch = self.in_unit(lib, src.file, |d| {
            let ctx = d.context_region(&du.context);
            let r = d.new_region(Some(ent.region));
            d.regions[r].uses = d.regions[ctx].uses.clone();
            for (n, s) in d.regions[ctx].syms.clone() {
                for x in s {
                    d.declare(r, &n, x);
                }
            }
            let saved = d.cur_cfg.take();
            let arch = d.architecture(r, &ent, a);
            d.cur_cfg = saved;
            arch
        });
        self.archs.push(arch);
        Some(self.archs.len() - 1)
    }
}

enum UnitKind {
    Package,
    Entity,
    Other,
}

/// Analyse the configured VHDL files: index every design unit, then analyse
/// the top entity (the last entity of the last file that is not
/// instantiated by another, or `top` when given) and what it depends on.
pub fn analyze(
    files: Vec<(String, cst::Parsed)>,
    top: Option<&str>,
) -> Result<Analysed, Vec<String>> {
    let mut d = Design::new();
    d.add_universal_types();
    d.ensure_library("std");
    d.analyze_package("std", "standard");
    // Entities and configurations of the user's files: (library, name,
    // is a configuration).
    let mut user_units = Vec::new();
    let mut configured = Vec::new();
    for (lib, p) in files {
        if let Some(df) = &p.ast {
            for u in &df.units {
                match &u.unit {
                    LibraryUnit::Entity(e) => {
                        user_units.push((lib.clone(), e.name.name.clone(), false));
                    }
                    LibraryUnit::Configuration(c) => {
                        user_units.push((lib.clone(), c.name.name.clone(), true));
                        configured.extend(last_ident(&c.entity).map(|i| i.name.clone()));
                    }
                    _ => {}
                }
            }
        }
        d.add_file(&lib, p);
    }
    // The top: named, or the last entity no architecture instantiates and
    // no configuration configures, or the last configuration (§14.2).
    let instantiated: Vec<String> = d.instantiated_entities();
    let top_unit = match top {
        Some(t) => user_units
            .iter()
            .find(|(_, n, _)| n == &t.to_ascii_lowercase())
            .cloned(),
        None => user_units
            .iter()
            .rev()
            .find(|(_, n, cfg)| !instantiated.contains(n) && (*cfg || !configured.contains(n)))
            .cloned(),
    };
    let Some((lib, name, is_cfg)) = top_unit else {
        return Err(vec!["VHDL: no top-level entity found".to_string()]);
    };
    let top = if is_cfg {
        match d.config_by_name(&lib, &name) {
            Some((elib, ename, arch, config)) => {
                let inst = Instance {
                    label: String::new(),
                    library: elib,
                    entity: ename,
                    arch,
                    arch_index: None,
                    generic_map: Vec::new(),
                    port_map: Vec::new(),
                    port_conv: Vec::new(),
                    config,
                    loc: Loc {
                        file: 0,
                        span: 0..0,
                    },
                };
                d.analyze_bound_arch(&inst, Vec::new()).map(|r| r.0)
            }
            None => None,
        }
    } else {
        d.analyze_arch(&lib, &name, None)
    };
    if !d.errors.is_empty() {
        return Err(d.render_errors());
    }
    let Some(top) = top else {
        return Err(vec![format!("VHDL: entity '{}' has no architecture", name)]);
    };
    // Analyse the architectures the design instantiates.
    let mut i = 0;
    while i < d.archs.len() {
        let insts = d.archs[i].instances.clone();
        for (j, inst) in insts.iter().enumerate() {
            if inst.arch_index.is_some() {
                // A block or generate iteration, analysed in place.
                continue;
            }
            // Generic values other than the defaults: a bound analysis.
            let mut binding = Vec::new();
            for (f, e) in &inst.generic_map {
                let fo = &d.objects[*f];
                match d.eval(e) {
                    Some(v) => {
                        if fo.static_val.as_ref() != Some(&v) {
                            binding.push((fo.name.clone(), v));
                        }
                    }
                    None => d
                        .errors
                        .push((e.loc.clone(), "a generic actual must be static here".into())),
                }
            }
            if binding.is_empty() && inst.config.is_none() {
                let a = d.analyze_arch(&inst.library, &inst.entity, inst.arch.as_deref());
                d.archs[i].instances[j].arch_index = a;
                continue;
            }
            let Some(default) = d.analyze_entity(&inst.library, &inst.entity) else {
                continue;
            };
            if let Some((a, gens, ports)) = d.analyze_bound_arch(inst, binding) {
                // The formals of the bound entity, by position.
                let remap = |o: ObjId, from: &[ObjId], to: &[ObjId]| {
                    from.iter()
                        .position(|x| *x == o)
                        .map(|p| to[p])
                        .unwrap_or(o)
                };
                let ins = &mut d.archs[i].instances[j];
                ins.arch_index = Some(a);
                for (f, _) in ins.generic_map.iter_mut() {
                    *f = remap(*f, &default.generics, &gens);
                }
                for (f, _) in ins.port_map.iter_mut() {
                    *f = remap(*f, &default.ports, &ports);
                }
                let objs = &d.objects;
                for pc in ins.port_conv.iter_mut() {
                    let to = remap(pc.formal, &default.ports, &ports);
                    let side = if pc.mode == ast::Mode::In {
                        &mut pc.target
                    } else {
                        &mut pc.value
                    };
                    *side = config::map_objs(side, &mut |o| {
                        (o == pc.formal).then(|| HExpr {
                            kind: HExprKind::Obj(to),
                            ty: objs[to].ty,
                            loc: objs[to].loc.clone(),
                        })
                    });
                    pc.formal = to;
                }
            }
        }
        i += 1;
    }
    // Package bodies of every package used, then the library subprogram
    // bodies the design reaches.
    let pkgs: Vec<PkgKey> = d.packages.keys().cloned().collect();
    for (lib, name) in pkgs {
        d.analyze_package_body(&lib, &name);
    }
    d.analyze_reachable_bodies();
    if !d.errors.is_empty() {
        return Err(d.render_errors());
    }
    Ok(Analysed { design: d, top })
}

impl Design {
    /// Entity names that some architecture instantiates (`entity work.x`
    /// or a component named like an entity).
    fn instantiated_entities(&self) -> Vec<String> {
        let mut out = Vec::new();
        for df in self.asts.iter().flatten() {
            for u in &df.units {
                if let LibraryUnit::Architecture(a) = &u.unit {
                    collect_instantiated(&a.stmts, &mut out);
                }
            }
        }
        out
    }
}

fn collect_instantiated(stmts: &[ast::ConcStmt], out: &mut Vec<String>) {
    for s in stmts {
        match &s.kind {
            ast::ConcKind::Instance { unit, .. } => {
                let n = match unit {
                    ast::InstUnit::Entity(n, _) | ast::InstUnit::Component(n) => n,
                    ast::InstUnit::Configuration(n) => n,
                };
                if let Some(i) = last_ident(n) {
                    out.push(i.name.clone());
                }
            }
            ast::ConcKind::Block { stmts, .. } | ast::ConcKind::ForGenerate { stmts, .. } => {
                collect_instantiated(stmts, out)
            }
            ast::ConcKind::IfGenerate(b) | ast::ConcKind::CaseGenerate { branches: b, .. } => {
                for x in b {
                    collect_instantiated(&x.stmts, out);
                }
            }
            _ => {}
        }
    }
}

pub fn last_ident(n: &Name) -> Option<&Ident> {
    match &n.kind {
        NameKind::Simple(i) => Some(i),
        NameKind::Selected(_, ast::Suffix::Ident(i)) => Some(i),
        _ => None,
    }
}

impl Design {
    /// Analyse the lazily kept library subprogram bodies the design calls,
    /// transitively: from the processes, instance maps, object initial
    /// values and resolution functions.
    fn analyze_reachable_bodies(&mut self) {
        let mut work: Vec<SubId> = Vec::new();
        let mut calls = Vec::new();
        for a in &self.archs {
            for p in &a.processes {
                calls_in_stmts(&p.stmts, &mut calls);
                for s in p.sens.iter().flatten() {
                    calls_in_expr(s, &mut calls);
                }
            }
            for i in &a.instances {
                for (_, e) in &i.generic_map {
                    calls_in_expr(e, &mut calls);
                }
                for (_, e) in i.port_map.iter() {
                    if let Some(e) = e {
                        calls_in_expr(e, &mut calls);
                    }
                }
                for pc in &i.port_conv {
                    calls_in_expr(&pc.target, &mut calls);
                    calls_in_expr(&pc.value, &mut calls);
                }
            }
        }
        for o in &self.objects {
            if let Some(e) = &o.init {
                calls_in_expr(e, &mut calls);
            }
        }
        for t in &self.types {
            if let TypeKind::Subtype {
                resolution: Some(f),
                ..
            } = &t.kind
            {
                calls.push(*f);
            }
        }
        work.extend(calls);
        let mut seen = std::collections::HashSet::new();
        while let Some(f) = work.pop() {
            if !seen.insert(f) {
                continue;
            }
            if let Some(lb) = self.lazy_bodies.remove(&f) {
                let saved = (
                    std::mem::replace(&mut self.cur_lib, lb.lib.clone()),
                    self.cur_file,
                );
                self.cur_file = lb.file;
                self.analyze_body(f, lb.region, &lb.body, &lb.path);
                self.cur_lib = saved.0;
                self.cur_file = saved.1;
            }
            let mut more = Vec::new();
            if let Some(b) = &self.subprograms[f].body {
                calls_in_stmts(&b.stmts, &mut more);
                for l in &b.locals {
                    if let Some(e) = &self.objects[*l].init {
                        calls_in_expr(e, &mut more);
                    }
                }
            }
            for p in &self.subprograms[f].params {
                if let Some(e) = &self.objects[*p].init {
                    calls_in_expr(e, &mut more);
                }
            }
            work.extend(more);
        }
    }
}

/// Every subprogram an expression calls.
pub fn calls_in_expr(e: &HExpr, out: &mut Vec<SubId>) {
    match &e.kind {
        HExprKind::Call(f, args) => {
            out.push(*f);
            for a in args {
                calls_in_expr(a, out);
            }
        }
        HExprKind::Index(b, i) => {
            calls_in_expr(b, out);
            for x in i {
                calls_in_expr(x, out);
            }
        }
        HExprKind::Slice(b, r) => {
            calls_in_expr(b, out);
            calls_in_range(r, out);
        }
        HExprKind::Field(b, _)
        | HExprKind::Convert(b)
        | HExprKind::Qualified(b)
        | HExprKind::Deref(b) => calls_in_expr(b, out),
        HExprKind::ArrayAgg(items) => {
            for (cs, v) in items {
                for c in cs {
                    match c {
                        HChoice::Expr(x) => calls_in_expr(x, out),
                        HChoice::Range(r) => calls_in_range(r, out),
                        HChoice::Others => {}
                    }
                }
                calls_in_expr(v, out);
            }
        }
        HExprKind::RecordAgg(v) => {
            for x in v {
                calls_in_expr(x, out);
            }
        }
        HExprKind::Attr(_, p, param) => {
            if let AttrPrefix::Expr(x) = p.as_ref() {
                calls_in_expr(x, out);
            }
            if let Some(x) = param {
                calls_in_expr(x, out);
            }
        }
        HExprKind::New(Some(x)) => calls_in_expr(x, out),
        _ => {}
    }
}

fn calls_in_range(r: &HRange, out: &mut Vec<SubId>) {
    calls_in_expr(&r.left, out);
    calls_in_expr(&r.right, out);
    if let Some((o, _, _)) = &r.of_obj {
        calls_in_expr(o, out);
    }
}

pub fn calls_in_stmts(stmts: &[HStmt], out: &mut Vec<SubId>) {
    for s in stmts {
        match &s.kind {
            HStmtKind::Wait { on, until, timeout } => {
                for x in on.iter().chain(until).chain(timeout) {
                    calls_in_expr(x, out);
                }
            }
            HStmtKind::Assert {
                cond,
                report,
                severity,
            } => {
                for x in [cond, report, severity].into_iter().flatten() {
                    calls_in_expr(x, out);
                }
            }
            HStmtKind::SignalAssign {
                target,
                delay,
                waves,
            } => {
                calls_in_expr(target, out);
                if let Some(HDelay::Inertial(Some(x))) = delay {
                    calls_in_expr(x, out);
                }
                for w in waves {
                    for x in [&w.value, &w.after].into_iter().flatten() {
                        calls_in_expr(x, out);
                    }
                }
            }
            HStmtKind::VarAssign { target, value } => {
                calls_in_expr(target, out);
                calls_in_expr(value, out);
            }
            HStmtKind::Call(f, a) => {
                out.push(*f);
                for x in a {
                    calls_in_expr(x, out);
                }
            }
            HStmtKind::If(bs, e) => {
                for (c, b) in bs {
                    calls_in_expr(c, out);
                    calls_in_stmts(b, out);
                }
                if let Some(e) = e {
                    calls_in_stmts(e, out);
                }
            }
            HStmtKind::Case { expr, alts } => {
                calls_in_expr(expr, out);
                for (cs, b) in alts {
                    for c in cs {
                        match c {
                            HChoice::Expr(x) => calls_in_expr(x, out),
                            HChoice::Range(r) => calls_in_range(r, out),
                            HChoice::Others => {}
                        }
                    }
                    calls_in_stmts(b, out);
                }
            }
            HStmtKind::Loop { scheme, body, .. } => {
                match scheme {
                    HLoop::While(c) => calls_in_expr(c, out),
                    HLoop::For(_, r) => calls_in_range(r, out),
                    HLoop::Plain => {}
                }
                calls_in_stmts(body, out);
            }
            HStmtKind::Next(_, Some(c))
            | HStmtKind::Exit(_, Some(c))
            | HStmtKind::Return(Some(c)) => calls_in_expr(c, out),
            _ => {}
        }
    }
}
