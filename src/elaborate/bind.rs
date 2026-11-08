//! §23.9, §26.3, §23.8.1: bind each simple name of a definition to the
//! declaration it names, in every position, before expansion. The head of a
//! `HierarchicalIdentifier` gets `bound`, a `disable` target its task. Names in
//! other AST shapes (type names, event identifiers) are only reported by the
//! audit.
//!
//! Procedural, subroutine and class scopes are not tree scopes: nothing outside
//! them can name their contents by a simple name, so the walk tracks them as
//! hidden names, and such a reference has no `bound`.
//!
//! `XEZIM_BIND_AUDIT` compares each binding with the generate rename
//! (`rename_decls_in_iter`), run over a copy of the definition.

use super::{GenRename, gen_scope_name, rename_decls_in_iter};
use crate::ast::binding::{Bound, DeclId, DeclKind, ScopeId};
use crate::ast::decl::*;
use crate::ast::expr::{
    AssignmentPatternItem, ExprKind, Expression, HierPathSegment, HierarchicalIdentifier,
    NumberBase, NumberLiteral,
};
use crate::ast::module::PortList;
use crate::ast::stmt::*;
use crate::ast::types::{DataType, PackedDimension, UnpackedDimension};
use crate::ast::{Description, Identifier, Span};
use crate::hasher::{HashMap, HashSet};
use crate::scope_tree::{
    ScopeKind, ScopeTree, class_type_name, for_each_block_label, for_each_enum_member,
};

pub fn audit_enabled() -> bool {
    std::env::var_os("XEZIM_BIND_AUDIT").is_some()
}

/// What a name resolves to beyond the current definition's tree.
#[derive(Default)]
pub struct DesignNames {
    /// §26.2: names each package declares, and the packages it exports from.
    packages: HashMap<String, HashSet<String>>,
    exports: HashMap<String, Vec<(String, Option<String>)>>,
    /// §3.12.1: names of the compilation unit, and its wildcard imports.
    unit: HashSet<String>,
    unit_wildcards: Vec<String>,
    classes: HashMap<String, ClassNames>,
    /// Every class member of the design: a receiver or base unknown here may
    /// declare any of them (§18.7, §8.25).
    any_member: HashSet<String>,
    /// §23.9: module, interface, program, package, checker and primitive
    /// names, which can start a path.
    definitions: HashSet<String>,
}

#[derive(Default)]
struct ClassNames {
    base: Option<String>,
    members: HashSet<String>,
}

impl DesignNames {
    pub fn collect(descs: &[Description]) -> Self {
        let mut n = Self::default();
        for d in descs {
            let def = match d {
                Description::Module(m) => Some(&m.name),
                Description::Interface(m) => Some(&m.name),
                Description::Program(m) => Some(&m.name),
                Description::Package(p) => Some(&p.name),
                Description::PackageItem(PackageItem::Checker(c)) => Some(&c.name),
                Description::Udp(u) => Some(&u.name),
                _ => None,
            };
            n.definitions.extend(def.map(|i| i.name.clone()));
            match d {
                Description::Package(p) => {
                    let mut names = HashSet::default();
                    let mut exports = Vec::new();
                    for item in &p.items {
                        if let PackageItem::Export(e) = item {
                            exports.extend(e.items.iter().map(|i| {
                                (
                                    i.package.name.clone(),
                                    i.item.as_ref().map(|n| n.name.clone()),
                                )
                            }));
                        }
                        package_item_names(item, &mut names);
                        n.classes_in_package_item(item);
                    }
                    n.packages.insert(p.name.name.clone(), names);
                    n.exports.insert(p.name.name.clone(), exports);
                }
                Description::Module(m) => n.classes_in_items(&m.items),
                Description::Interface(m) => n.classes_in_items(&m.items),
                Description::Program(m) => n.classes_in_items(&m.items),
                Description::Class(c) => {
                    n.unit.insert(c.name.name.clone());
                    n.class(c);
                }
                Description::TypedefDecl(t) => {
                    typedef_names(t, &mut n.unit);
                }
                Description::ImportDecl(i) => n.unit_import(i),
                Description::DPIImport(i) => {
                    n.unit.insert(dpi_name(&i.proto).to_string());
                }
                Description::PackageItem(item) => {
                    if let PackageItem::Import(i) = item {
                        n.unit_import(i);
                    }
                    let mut names = std::mem::take(&mut n.unit);
                    package_item_names(item, &mut names);
                    n.unit = names;
                    n.classes_in_package_item(item);
                }
                _ => {}
            }
        }
        n
    }

    fn unit_import(&mut self, i: &ImportDeclaration) {
        for it in &i.items {
            match &it.item {
                Some(name) => {
                    self.unit.insert(name.name.clone());
                }
                None => self.unit_wildcards.push(it.package.name.clone()),
            }
        }
    }

    fn classes_in_package_item(&mut self, item: &PackageItem) {
        match item {
            PackageItem::Class(c) => self.class(c),
            PackageItem::Checker(c) => self.classes_in_items(&c.items),
            _ => {}
        }
    }

    fn classes_in_items(&mut self, items: &[ModuleItem]) {
        for item in items {
            match item {
                ModuleItem::ClassDeclaration(c) => self.class(c),
                ModuleItem::GenerateRegion(g) => self.classes_in_items(&g.items),
                ModuleItem::GenerateFor(g) => self.classes_in_items(&g.items),
                ModuleItem::GenerateIf(g) => g
                    .branches
                    .iter()
                    .for_each(|(_, b)| self.classes_in_items(b)),
                ModuleItem::GenerateCase(g) => {
                    g.arms.iter().for_each(|a| self.classes_in_items(&a.items))
                }
                ModuleItem::NestedModule(m) => self.classes_in_items(&m.items),
                ModuleItem::CheckerDeclaration(c) => self.classes_in_items(&c.items),
                _ => {}
            }
        }
    }

    fn class(&mut self, c: &ClassDeclaration) {
        let mut members = HashSet::default();
        class_member_names(c, &mut |n| {
            members.insert(n.to_string());
        });
        self.any_member.extend(members.iter().cloned());
        let base = c
            .extends
            .as_ref()
            .and_then(|e| e.name.name.rsplit("::").next().map(str::to_string));
        self.classes
            .insert(c.name.name.clone(), ClassNames { base, members });
        for item in &c.items {
            if let ClassItem::Class(inner) = item {
                self.class(inner);
            }
        }
    }

    /// §26.3: `name` is visible through a wildcard import of `package`, its
    /// own or exported (§26.6).
    fn package_declares(&self, package: &str, name: &str) -> bool {
        self.package_declares_at(package, name, 0)
    }

    fn package_declares_at(&self, package: &str, name: &str, depth: u32) -> bool {
        if self.packages.get(package).is_some_and(|n| n.contains(name)) {
            return true;
        }
        if depth > 16 {
            return false;
        }
        self.exports.get(package).is_some_and(|ex| {
            ex.iter().any(|(from, item)| {
                from != package
                    && item.as_ref().is_none_or(|i| i == name)
                    && self.package_declares_at(from, name, depth + 1)
            })
        })
    }

    fn unit_declares(&self, name: &str) -> bool {
        self.unit.contains(name)
            || self
                .unit_wildcards
                .iter()
                .any(|p| self.package_declares(p, name))
    }
}

fn dpi_name(p: &DPIProto) -> &str {
    match p {
        DPIProto::Function(f) => &f.name.name.name,
        DPIProto::Task(t) => &t.name.name.name,
    }
}

fn typedef_names(t: &TypedefDeclaration, out: &mut HashSet<String>) {
    out.insert(t.name.name.clone());
    for_each_enum_member(&t.data_type, &mut |n| {
        out.insert(n.name.clone());
    });
}

fn param_names(p: &ParameterDeclaration, f: &mut dyn FnMut(&str)) {
    match &p.kind {
        ParameterKind::Data {
            data_type,
            assignments,
        } => {
            for_each_enum_member(data_type, &mut |n| f(&n.name));
            assignments.iter().for_each(|a| f(&a.name.name));
        }
        ParameterKind::Type { assignments } => assignments.iter().for_each(|a| f(&a.name.name)),
    }
}

fn package_item_names(item: &PackageItem, out: &mut HashSet<String>) {
    let mut add = |n: &str| {
        out.insert(n.to_string());
    };
    match item {
        PackageItem::Parameter(p) => param_names(p, &mut add),
        PackageItem::Typedef(t) => typedef_names(t, out),
        PackageItem::Function(f) => add(&f.name.name.name),
        PackageItem::Task(t) => add(&t.name.name.name),
        PackageItem::DPIImport(i) => add(dpi_name(&i.proto)),
        PackageItem::Data(d) => {
            for_each_enum_member(&d.data_type, &mut |n| add(&n.name));
            d.declarators.iter().for_each(|v| add(&v.name.name));
        }
        PackageItem::Class(c) => add(&c.name.name),
        PackageItem::Checker(c) => add(&c.name.name),
        PackageItem::Let(l) => add(&l.name.name),
        PackageItem::Nettype(n) => {
            for_each_enum_member(&n.data_type, &mut |m| add(&m.name));
            add(&n.name.name);
        }
        PackageItem::Property(p) => add(&p.name.name),
        PackageItem::Sequence(s) => add(&s.name.name),
        PackageItem::Covergroup(c) => add(&c.name.name),
        PackageItem::Net(n) => {
            for_each_enum_member(&n.data_type, &mut |m| add(&m.name));
            n.declarators.iter().for_each(|v| add(&v.name.name));
        }
        PackageItem::Import(_)
        | PackageItem::DPIExport(_)
        | PackageItem::Null
        | PackageItem::Export(_)
        | PackageItem::TimeunitsDecl(_) => {}
    }
}

/// §8.3: the names a class body declares, itself excluded.
fn class_member_names(c: &ClassDeclaration, f: &mut dyn FnMut(&str)) {
    c.params.iter().for_each(|p| param_names(p, f));
    for item in &c.items {
        match item {
            ClassItem::Property(p) => {
                for_each_enum_member(&p.data_type, &mut |n| f(&n.name));
                p.declarators.iter().for_each(|d| f(&d.name.name));
            }
            ClassItem::Method(m) => match &m.kind {
                ClassMethodKind::Function(d)
                | ClassMethodKind::PureVirtual(d)
                | ClassMethodKind::Extern(d) => f(&d.name.name.name),
                ClassMethodKind::Task(d) => f(&d.name.name.name),
            },
            ClassItem::Constraint(k) => f(&k.name.name),
            ClassItem::Typedef(t) => {
                for_each_enum_member(&t.data_type, &mut |n| f(&n.name));
                f(&t.name.name);
            }
            ClassItem::Parameter(p) => param_names(p, f),
            ClassItem::Class(i) => f(&i.name.name),
            ClassItem::Covergroup(g) => f(&g.name.name),
            ClassItem::Import(i) => i
                .items
                .iter()
                .filter_map(|it| it.item.as_ref())
                .for_each(|n| f(&n.name)),
            ClassItem::Empty => {}
        }
    }
}

/// Why a name has no tree binding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Hide {
    /// §13.5: subroutine formals, and those of a let, property or covergroup.
    Formal,
    /// §12.7, §27.4 and generate loop variables.
    Loop,
    /// §6.21: a variable of a procedural block.
    Local,
    /// §9.3.5: a block label.
    Label,
    /// §6.19, §6.18.
    Type,
    /// §7.12 `with` iterators.
    Iterator,
    /// §12.6 pattern variables.
    Pattern,
    /// §8: a class member, or a name a class of unknown shape may declare.
    Member,
    /// §26.3, §3.12.1: an import or `$unit`.
    Import,
    /// A scoped, rooted or built-in name: no lexical lookup applies.
    Qualified,
    /// §23.4: a name of the definition a nested one is declared in.
    Outer,
}

/// The outcome of resolving one name.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Outcome {
    Decl(DeclId),
    Upward,
    None(Hide),
}

/// One name position the walk visited.
#[derive(Debug, Clone)]
struct Mention {
    span: Span,
    name: String,
    outcome: Outcome,
    binding: String,
    /// The spelling the rename should give the name's declaration.
    want: Option<String>,
    /// The spellings of this name in the scopes around its declaration.
    outer_keys: Vec<String>,
    /// What the tree declares under this name, hiding aside.
    target: Option<DeclKind>,
    pos: &'static str,
    /// The name is the callee of a call.
    call: bool,
}

/// Positions the rename never rewrites: items `rename_item_decls` copies and
/// parts `rewrite_stmt` and `rewrite_expr` copy. Group B of the audit.
const UNVISITED: &[&str] = &[
    "alias",
    "assign-delay",
    "clocking-signal",
    "defparam",
    "dpi-export",
    "dpi-import",
    "instance-dim",
    "modport",
    "nettype",
    "tagged",
    "shallow-copy",
    "specify",
    "event-name",
    "wait-order",
];

/// Positions the rename gives part of a block's names: a declared constraint
/// its subroutines and types (§18.5), a process local's type its parameters
/// and types (§6.21).
/// The rest there is group B.
fn partly_renamed(pos: &str, target: Option<DeclKind>) -> bool {
    match pos {
        "constraint" => !matches!(
            target,
            Some(DeclKind::Function | DeclKind::Task | DeclKind::Typedef)
        ),
        "local-dim" => !matches!(target, Some(DeclKind::Param | DeclKind::Typedef)),
        _ => false,
    }
}

/// A hidden name, why, and the class its declared type may name.
type Hidden = (String, Hide, Option<String>);

/// The class `randomize() with` searches first (§18.7).
enum Receiver {
    /// Scope randomization or a bare call (§18.12).
    None,
    Class(String),
    /// An object whose class is not looked up.
    Unknown,
}

/// The walk over one definition.
struct Binder<'a> {
    tree: &'a ScopeTree,
    names: &'a DesignNames,
    /// Nested definitions' trees of this description.
    others: &'a [ScopeTree],
    scope: ScopeId,
    /// Per scope, the next child block: the walk visits generate blocks in
    /// the order the tree was built.
    next_child: Vec<u32>,
    hidden: Vec<Hidden>,
    /// Depth of class bodies with an unknown base and inline constraints.
    unknown_members: u32,
    /// §23.4: the scopes a nested definition is declared in, innermost last.
    outer: Vec<(&'a ScopeTree, ScopeId)>,
    /// The formals before the default being visited (§13.5.3).
    formals: Vec<String>,
    /// The next head is the callee of a call.
    callee: bool,
    pos: &'static str,
    mentions: Option<Vec<Mention>>,
}

/// §26.7, Annex G: the classes of `std`, wildcard imported into every
/// compilation unit.
const STD_CLASSES: &[&str] = &["process", "mailbox", "semaphore", "weak_reference"];

impl<'a> Binder<'a> {
    fn with_pos(&mut self, pos: &'static str, f: impl FnOnce(&mut Self)) {
        let old = std::mem::replace(&mut self.pos, pos);
        f(self);
        self.pos = old;
    }

    fn hide(&mut self, name: &str, why: Hide) {
        self.hidden.push((name.to_string(), why, None));
    }

    fn hide_typed(&mut self, name: &str, why: Hide, dt: &DataType) {
        self.hidden
            .push((name.to_string(), why, class_type_name(dt)));
    }

    fn hide_enums(&mut self, dt: &DataType) {
        for_each_enum_member(dt, &mut |n| {
            self.hidden.push((n.name.clone(), Hide::Type, None))
        });
    }

    /// §23.9: innermost first. §26.3: at each scope, its declarations, then
    /// its explicit imports, then its wildcard imports. Then `$unit`, then
    /// the hierarchy (§23.8.1).
    fn resolve(&self, name: &str) -> Outcome {
        // A.2.2.3: the delay value `1step` is carried as a name.
        if name.is_empty()
            || name.contains("::")
            || name.starts_with('$')
            || is_keyword_name(name)
            || name == crate::ast::decl::CLOCKING_ONE_STEP
        {
            return Outcome::None(Hide::Qualified);
        }
        if let Some((_, why, _)) = self.hidden.iter().rev().find(|(h, ..)| h == name) {
            return Outcome::None(*why);
        }
        if self.unknown_members > 0 && self.names.any_member.contains(name) {
            return Outcome::None(Hide::Member);
        }
        // §6.10: an implicit net is declared only where no other name is
        // found.
        let mut implicit = None;
        let chains =
            std::iter::once((self.tree, self.scope)).chain(self.outer.iter().rev().copied());
        for (depth, (tree, from)) in chains.enumerate() {
            let mut at = Some(from);
            while let Some(s) = at {
                let scope = &tree.scopes[s.0 as usize];
                if let Some(d) = scope.by_name.get(name) {
                    match tree.decls[d.0 as usize].kind {
                        DeclKind::ImplicitNet if depth == 0 => implicit = Some(*d),
                        _ if depth == 0 => return Outcome::Decl(*d),
                        // §23.8.1: a call finds the subroutine upward.
                        DeclKind::Function | DeclKind::Task => return Outcome::Upward,
                        _ => return Outcome::None(Hide::Outer),
                    }
                }
                if scope.explicit_imports.contains_key(name)
                    || scope
                        .wildcard_imports
                        .iter()
                        .any(|p| self.names.package_declares(p, name))
                {
                    return Outcome::None(Hide::Import);
                }
                at = scope.parent;
            }
        }
        if self.names.unit_declares(name) || STD_CLASSES.contains(&name) {
            return Outcome::None(Hide::Import);
        }
        // §26.3: `p::x` reaches here with the package as its head.
        if name == "std"
            || self.names.packages.contains_key(name)
            || (!self.callee && self.names.definitions.contains(name))
        {
            return Outcome::None(Hide::Qualified);
        }
        if let Some(d) = implicit {
            return Outcome::Decl(d);
        }
        if self.formals.iter().any(|f| f == name) {
            return Outcome::None(Hide::Formal);
        }
        Outcome::Upward
    }

    fn note(&mut self, span: Span, name: &str, outcome: Outcome) {
        let pos = self.pos;
        let tree = self.tree;
        let bare = crate::sv_parser::strip_unit_scope_name(name).unwrap_or(name);
        let target = tree
            .lookup(self.scope, bare)
            .map(|d| tree.decls[d.0 as usize].kind);
        if let Some(m) = &mut self.mentions {
            let (want, outer_keys) = match outcome {
                Outcome::Decl(d) => {
                    let decl = &tree.decls[d.0 as usize];
                    (
                        renamed_key(tree, decl.scope, &decl.name, decl.kind),
                        outer_keys(tree, decl.scope, &decl.name),
                    )
                }
                _ => (None, Vec::new()),
            };
            m.push(Mention {
                span,
                name: name.to_string(),
                outcome,
                binding: binding_text(tree, outcome),
                want,
                outer_keys,
                target,
                pos,
                call: self.callee,
            });
        }
    }

    /// A name with no `bound` field to write.
    fn ident(&mut self, id: &Identifier) {
        let outcome = self.resolve(&id.name);
        self.note(id.span, &id.name, outcome);
    }

    fn head(&mut self, h: &mut HierarchicalIdentifier) {
        let Some(first) = h.path.first() else { return };
        // `NO_TARGET` here is the parser's `$unit::f(...)` (§3.12.1).
        let outcome = if h.root.is_some() || h.bound == Bound::NO_TARGET {
            Outcome::None(Hide::Qualified)
        } else {
            self.resolve(&first.name.name)
        };
        h.bound = match outcome {
            Outcome::Decl(d) => Bound::decl(d),
            Outcome::Upward => Bound::UPWARD,
            Outcome::None(_) => Bound::NO_TARGET,
        };
        if self.mentions.is_some() {
            let name = first.name.name.clone();
            self.note(h.span, &name, outcome);
        }
        self.callee = false;
    }

    /// §9.6.2, §23.9: a `disable` target, resolved from where it is written.
    /// A task (or, ill-formed, a function) gets `bound`, its declaration. A
    /// path through generate blocks to a task becomes one segment, the task's
    /// key in the definition (`g.t`, `g[1].h.t`). A block, a path the tree
    /// cannot follow, or one whose head is found inside a loop block, is
    /// `NO_TARGET` and keeps its spelling.
    fn disable(&mut self, h: &mut HierarchicalIdentifier) {
        let tree = self.tree;
        // Already keyed: the audit's walk after the rename.
        if let [seg] = &h.path[..]
            && let Some(d) = h.bound.as_decl()
            && tree.decls[d.0 as usize].name != seg.name.name
        {
            let key = seg.name.name.clone();
            self.note_key(h.span, &key, d);
            return;
        }
        let Some(first) = h.path.first() else { return };
        let head = first.name.name.clone();
        let outcome = if h.root.is_some() {
            Outcome::None(Hide::Qualified)
        } else {
            self.resolve(&head)
        };
        if h.path.len() == 1 {
            h.bound = match outcome {
                Outcome::Decl(d)
                    if matches!(
                        tree.decls[d.0 as usize].kind,
                        DeclKind::Task | DeclKind::Function
                    ) =>
                {
                    Bound::decl(d)
                }
                Outcome::Upward => Bound::UPWARD,
                _ => Bound::NO_TARGET,
            };
            self.note(h.span, &head, outcome);
            return;
        }
        h.bound = Bound::NO_TARGET;
        let Outcome::Decl(at) = outcome else { return };
        let from = tree.decls[at.0 as usize].scope;
        // §27.6: a path through an implicit block name keeps its spelling.
        if tree.decls[at.0 as usize].kind == DeclKind::Label
            && tree.scopes[from.0 as usize].children.iter().any(|c| {
                let sc = &tree.scopes[c.0 as usize];
                sc.seg.as_deref() == Some(head.as_str())
                    && matches!(sc.kind, ScopeKind::Generate { label: None, .. })
            })
        {
            return;
        }
        let Some((d, key)) = path_task(tree, from, &h.path) else {
            return;
        };
        let mut up = Some(from);
        while let Some(s) = up {
            let sc = &tree.scopes[s.0 as usize];
            if matches!(sc.kind, ScopeKind::Generate { indexed: true, .. }) {
                return;
            }
            up = sc.parent;
        }
        let outer = tree.path(from);
        let key = if outer.is_empty() {
            key
        } else {
            format!("{outer}.{key}")
        };
        h.path.truncate(1);
        h.path[0].name.name = key.clone();
        h.path[0].selects.clear();
        h.bound = Bound::decl(d);
        self.note_key(h.span, &key, d);
    }

    /// A `disable` target that is the key `key` of task `d`: the rename leaves
    /// it as it is.
    fn note_key(&mut self, span: Span, key: &str, d: DeclId) {
        let (pos, tree) = (self.pos, self.tree);
        if let Some(m) = &mut self.mentions {
            m.push(Mention {
                span,
                name: key.to_string(),
                outcome: Outcome::Decl(d),
                binding: binding_text(tree, Outcome::Decl(d)),
                want: None,
                outer_keys: Vec::new(),
                target: Some(DeclKind::Task),
                pos,
                call: false,
            });
        }
    }

    /// The current scope's declaration of `name`.
    fn own_decl(&self, name: &str) -> Bound {
        self.tree.scopes[self.scope.0 as usize]
            .by_name
            .get(name)
            .map_or(Bound::UNSET, |d| Bound::decl(*d))
    }

    /// The class of a `randomize` receiver that is one name: a local, a
    /// formal or block-level data, declared with a class's own name.
    fn receiver(&self, call: &Expression) -> Receiver {
        if !has_receiver(call) {
            return Receiver::None;
        }
        let Some(name) = receiver_name(call) else {
            return Receiver::Unknown;
        };
        let class = match self.hidden.iter().rev().find(|(h, ..)| h == name) {
            Some((_, _, class)) => class.clone(),
            None => match self.resolve(name) {
                Outcome::Decl(d) => self.tree.decl_types.get(&d).cloned(),
                _ => None,
            },
        };
        match class {
            Some(c) if self.names.classes.contains_key(&c) => Receiver::Class(c),
            _ => Receiver::Unknown,
        }
    }

    /// Hide the members of a `randomize` receiver's class (§18.7, §18.11).
    fn receiver_members(&mut self, target: &Expression) {
        match self.receiver(target) {
            Receiver::None => {}
            Receiver::Class(c) => self.hide_class_chain(Some(c)),
            Receiver::Unknown => self.unknown_members += 1,
        }
    }

    fn enter_child(&mut self) -> ScopeId {
        let parent = self.scope;
        let at = &mut self.next_child[parent.0 as usize];
        let child = self.tree.scopes[parent.0 as usize]
            .children
            .get(*at as usize)
            .copied();
        *at += 1;
        debug_assert!(child.is_some(), "a generate block the tree does not have");
        self.scope = child.unwrap_or(parent);
        parent
    }

    fn block(&mut self, items: &mut [ModuleItem]) {
        let parent = self.enter_child();
        self.items(items);
        self.scope = parent;
    }

    fn items(&mut self, items: &mut [ModuleItem]) {
        for item in items {
            self.item(item);
        }
    }

    /// Exhaustive so a new item kind has to decide.
    fn item(&mut self, item: &mut ModuleItem) {
        match item {
            ModuleItem::PortDeclaration(d) => {
                self.data_type(&mut d.data_type);
                self.var_declarators(&mut d.declarators);
                for v in &mut d.declarators {
                    v.decl = self.own_decl(&v.name.name);
                }
            }
            ModuleItem::NetDeclaration(d) => {
                self.data_type(&mut d.data_type);
                [&mut d.delay, &mut d.delay_fall, &mut d.delay_off]
                    .into_iter()
                    .flatten()
                    .for_each(|e| self.expr(e));
                for v in &mut d.declarators {
                    v.decl = self.own_decl(&v.name.name);
                    self.unpacked(&mut v.dimensions);
                    if let Some(e) = &mut v.init {
                        self.expr(e);
                    }
                }
            }
            ModuleItem::DataDeclaration(d) => {
                self.data_type(&mut d.data_type);
                self.var_declarators(&mut d.declarators);
                for v in &mut d.declarators {
                    v.decl = self.own_decl(&v.name.name);
                }
            }
            ModuleItem::ParameterDeclaration(p) | ModuleItem::LocalparamDeclaration(p) => {
                if let ParameterKind::Data { assignments, .. } = &mut p.kind {
                    for a in assignments {
                        a.decl = self.own_decl(&a.name.name);
                    }
                }
                self.parameter(p)
            }
            ModuleItem::TypedefDeclaration(t) => {
                self.with_pos("typedef", |b| {
                    b.data_type(&mut t.data_type);
                    b.unpacked(&mut t.dimensions);
                });
            }
            ModuleItem::AlwaysConstruct(a) => self.stmt(&mut a.stmt),
            ModuleItem::InitialConstruct(a) => self.stmt(&mut a.stmt),
            ModuleItem::FinalConstruct(a) => self.with_pos("final", |b| b.stmt(&mut a.stmt)),
            ModuleItem::ContinuousAssign(c) => {
                [&mut c.delay, &mut c.delay_fall, &mut c.delay_off]
                    .into_iter()
                    .flatten()
                    .for_each(|e| self.with_pos("assign-delay", |b| b.expr(e)));
                for (l, r) in &mut c.assignments {
                    self.with_pos("assign-lhs", |b| b.expr(l));
                    self.expr(r);
                }
            }
            ModuleItem::ModuleInstantiation(m) => {
                // §23.8.1: an upward call from the instance searches here first.
                m.scope = Some(self.scope);
                for p in m.params.iter_mut().flatten() {
                    let value = match p {
                        ParamConnection::Ordered(v) => v,
                        ParamConnection::Named { value, .. } => value,
                    };
                    match value {
                        Some(ParamValue::Expr(e)) => self.expr(e),
                        Some(ParamValue::Type(t)) => self.data_type(t),
                        None => {}
                    }
                }
                for i in &mut m.instances {
                    i.decl = self.own_decl(&i.name.name);
                    self.with_pos("instance-dim", |b| b.unpacked(&mut i.dimensions));
                    for c in &mut i.connections {
                        if let PortConnection::Named { expr: Some(e), .. }
                        | PortConnection::Ordered(Some(e)) = c
                        {
                            self.with_pos("port", |b| b.expr(e));
                        }
                    }
                }
            }
            ModuleItem::GateInstantiation(g) => self.with_pos("gate", |b| {
                [&mut g.delay, &mut g.delay_fall]
                    .into_iter()
                    .flatten()
                    .for_each(|e| b.expr(e));
                for i in &mut g.instances {
                    i.terminals.iter_mut().for_each(|t| b.expr(t));
                }
            }),
            ModuleItem::GenerateRegion(g) => self.items(&mut g.items),
            ModuleItem::GenerateIf(g) => {
                for (bi, (cond, branch)) in g.branches.iter_mut().enumerate() {
                    if let Some(c) = cond {
                        self.expr(c);
                    }
                    if g.branch_direct.get(bi) == Some(&true) {
                        self.item(&mut branch[0]);
                    } else {
                        self.block(branch);
                    }
                }
            }
            ModuleItem::GenerateCase(g) => {
                self.expr(&mut g.selector);
                for arm in &mut g.arms {
                    arm.values.iter_mut().for_each(|v| self.expr(v));
                    if arm.direct {
                        self.item(&mut arm.items[0]);
                    } else {
                        self.block(&mut arm.items);
                    }
                }
            }
            ModuleItem::GenerateFor(g) => {
                let mark = self.hidden.len();
                self.hide(&g.var, Hide::Loop);
                if let Some(i) = &mut g.init {
                    self.expr(i);
                }
                self.expr(&mut g.cond);
                self.expr(&mut g.incr);
                self.block(&mut g.items);
                self.hidden.truncate(mark);
            }
            ModuleItem::FunctionDeclaration(f) => {
                if f.name.scopes.is_empty() {
                    f.decl = self.own_decl(&f.name.name.name);
                    self.with_pos("subroutine", |b| b.function(f));
                } else {
                    self.out_of_block(&f.name.scopes[0].name.name.clone(), |b| b.function(f));
                }
            }
            ModuleItem::TaskDeclaration(t) => {
                if t.name.scopes.is_empty() {
                    t.decl = self.own_decl(&t.name.name.name);
                    self.with_pos("subroutine", |b| b.task(t));
                } else {
                    self.out_of_block(&t.name.scopes[0].name.name.clone(), |b| b.task(t));
                }
            }
            ModuleItem::ClassDeclaration(c) => self.with_pos("class", |b| b.class(c)),
            ModuleItem::AssertionItem(a) => self.with_pos("assertion", |b| b.assertion(a)),
            ModuleItem::ModportDeclaration(m) => self.with_pos("modport", |b| {
                for p in m.items.iter_mut().flat_map(|i| i.ports.iter_mut()) {
                    if let Some(e) = &mut p.expr {
                        b.expr(e);
                    }
                }
            }),
            ModuleItem::PropertyDeclaration(p) => self.with_pos("property", |b| {
                b.assertion_decl(&p.ports, &mut p.items, &mut p.body)
            }),
            ModuleItem::SequenceDeclaration(s) => self.with_pos("sequence", |b| {
                b.assertion_decl(&s.ports, &mut s.items, &mut s.body)
            }),
            ModuleItem::CovergroupDeclaration(c) => {
                self.with_pos("covergroup", |b| b.covergroup(c))
            }
            ModuleItem::ClockingDeclaration(c) => self.with_pos("clocking", |b| b.clocking(c)),
            ModuleItem::LetDeclaration(l) => self.with_pos("let", |b| b.let_decl(l)),
            ModuleItem::NettypeDeclaration(n) => self.with_pos("nettype", |b| {
                b.data_type(&mut n.data_type);
                if let Some(r) = &n.resolver {
                    b.ident(r);
                }
            }),
            ModuleItem::SpecifyBlock(s) => self.with_pos("specify", |b| b.specify(s)),
            ModuleItem::DPIImport(i) => self.with_pos("dpi-import", |b| match &mut i.proto {
                DPIProto::Function(f) => {
                    b.data_type(&mut f.return_type);
                    b.formal_types(&mut f.ports);
                }
                DPIProto::Task(t) => b.formal_types(&mut t.ports),
            }),
            ModuleItem::DPIExport(e) => self.with_pos("dpi-export", |b| {
                let n = match &e.proto {
                    DPIProto::Function(f) => &f.name.name,
                    DPIProto::Task(t) => &t.name.name,
                };
                b.ident(n);
            }),
            ModuleItem::OutOfClassConstraint {
                class_name, items, ..
            } => {
                let class = class_name.clone();
                self.out_of_block(&class, |b| {
                    b.with_pos("constraint", |b| b.constraints(items))
                });
            }
            ModuleItem::Defparam(d) => self.with_pos("defparam", |b| {
                for (l, r) in d {
                    b.expr(l);
                    b.expr(r);
                }
            }),
            ModuleItem::AliasDecl(a) => self.with_pos("alias", |b| {
                a.iter_mut().for_each(|e| b.expr(e));
            }),
            // Other definitions with their own trees: §23.4, §17.2. Their
            // lexically enclosing names are found upward (§23.8.1).
            ModuleItem::NestedModule(m) => {
                let def = self.tree.nested_def(self.scope, &m.name.name);
                self.nested(&def, &mut m.params, &mut m.ports, &mut m.items);
            }
            ModuleItem::CheckerDeclaration(c) => {
                let def = self.tree.nested_def(self.scope, &c.name.name);
                self.nested(&def, &mut [], &mut c.ports, &mut c.items);
            }
            // §23.11: a bind's actuals belong to its target's scope.
            ModuleItem::Bind(_)
            | ModuleItem::GenvarDeclaration(_)
            | ModuleItem::ImportDeclaration(_)
            | ModuleItem::TimeunitsDecl(_)
            | ModuleItem::Null => {}
        }
    }

    fn nested(
        &mut self,
        def: &str,
        params: &mut [ParameterDeclaration],
        ports: &mut PortList,
        items: &mut [ModuleItem],
    ) {
        let Some(tree) = self.others.iter().rev().find(|t| t.def == def) else {
            debug_assert!(false, "nested definition {def} without a tree");
            return;
        };
        let mentions = self.mentions.take();
        let mut outer = self.outer.clone();
        outer.push((self.tree, self.scope));
        let mut inner = Binder {
            tree,
            names: self.names,
            others: self.others,
            scope: tree.root,
            next_child: vec![0; tree.scopes.len()],
            hidden: Vec::new(),
            unknown_members: 0,
            outer,
            formals: Vec::new(),
            callee: false,
            pos: self.pos,
            mentions,
        };
        inner.definition(params, ports, items);
        self.mentions = inner.mentions.take();
    }

    /// §8.24: a class's method or constraint defined outside its body sees
    /// the class's members.
    fn out_of_block(&mut self, class: &str, f: impl FnOnce(&mut Self)) {
        let mark = self.hidden.len();
        let unknown = self.unknown_members;
        let c = class.rsplit("::").next().unwrap_or(class);
        self.hide_class_chain(Some(c.to_string()));
        self.with_pos("class", f);
        self.unknown_members = unknown;
        self.hidden.truncate(mark);
    }

    /// §8.13: hide the members of `class` and its bases. A base this design
    /// has no class for has unknown members.
    fn hide_class_chain(&mut self, class: Option<String>) {
        let mut at = class;
        let mut depth = 0;
        while let Some(name) = at {
            depth += 1;
            let names = self.names;
            let Some(c) = names.classes.get(&name).filter(|_| depth < 64) else {
                self.unknown_members += 1;
                return;
            };
            self.hidden
                .extend(c.members.iter().map(|m| (m.clone(), Hide::Member, None)));
            at = c.base.clone();
        }
    }

    fn class(&mut self, c: &mut ClassDeclaration) {
        let mark = self.hidden.len();
        let unknown = self.unknown_members;
        class_member_names(c, &mut |n| self.hide(n, Hide::Member));
        // A type parameter as base is not a class of the design either way.
        self.hide_class_chain(c.extends.as_ref().map(|e| e.name.name.clone()));
        for p in &mut c.params {
            self.parameter(p);
        }
        if let Some(e) = &mut c.extends {
            for a in &mut e.args {
                match a {
                    ParamValue::Expr(x) => self.expr(x),
                    ParamValue::Type(t) => self.data_type(t),
                }
            }
        }
        for item in &mut c.items {
            match item {
                ClassItem::Property(p) => {
                    self.data_type(&mut p.data_type);
                    self.var_declarators(&mut p.declarators);
                }
                ClassItem::Method(m) => match &mut m.kind {
                    ClassMethodKind::Function(f)
                    | ClassMethodKind::PureVirtual(f)
                    | ClassMethodKind::Extern(f) => self.function(f),
                    ClassMethodKind::Task(t) => self.task(t),
                },
                ClassItem::Constraint(k) => {
                    self.with_pos("constraint", |b| b.constraints(&mut k.items))
                }
                ClassItem::Typedef(t) => {
                    self.data_type(&mut t.data_type);
                    self.unpacked(&mut t.dimensions);
                }
                ClassItem::Parameter(p) => self.parameter(p),
                ClassItem::Class(i) => self.class(i),
                ClassItem::Covergroup(g) => self.covergroup(g),
                ClassItem::Import(i) => {
                    for it in &i.items {
                        if it.item.is_none() {
                            if let Some(names) = self.names.packages.get(&it.package.name) {
                                self.hidden
                                    .extend(names.iter().map(|n| (n.clone(), Hide::Import, None)));
                            }
                        }
                    }
                }
                ClassItem::Empty => {}
            }
        }
        self.unknown_members = unknown;
        self.hidden.truncate(mark);
    }

    fn parameter(&mut self, p: &mut ParameterDeclaration) {
        match &mut p.kind {
            ParameterKind::Data {
                data_type,
                assignments,
            } => {
                self.data_type(data_type);
                for a in assignments {
                    self.unpacked(&mut a.dimensions);
                    if let Some(e) = &mut a.init {
                        self.expr(e);
                    }
                }
            }
            ParameterKind::Type { assignments } => {
                for a in assignments {
                    if let Some(t) = &mut a.init {
                        self.data_type(t);
                    }
                }
            }
        }
    }

    fn var_declarators(&mut self, declarators: &mut [VarDeclarator]) {
        for d in declarators {
            self.unpacked(&mut d.dimensions);
            if let Some(e) = &mut d.init {
                self.expr(e);
            }
        }
    }

    /// §13.5.3: types and defaults bind in the declaring scope. A name
    /// found nowhere there may be a formal before it.
    fn formal_types(&mut self, ports: &mut [FunctionPort]) {
        let mark = self.formals.len();
        for p in ports {
            self.data_type(&mut p.data_type);
            self.unpacked(&mut p.dimensions);
            if let Some(d) = &mut p.default {
                self.expr(d);
            }
            self.formals.push(p.name.name.clone());
        }
        self.formals.truncate(mark);
    }

    fn function(&mut self, f: &mut FunctionDeclaration) {
        self.data_type(&mut f.return_type);
        self.subroutine(&mut f.ports, &f.strict_body_ports, &mut f.items);
    }

    fn task(&mut self, t: &mut TaskDeclaration) {
        self.subroutine(&mut t.ports, &t.strict_body_ports, &mut t.items);
    }

    /// §13.5: formals hide outer names in the body. The function's own name
    /// is not hidden: §13.4.1 makes it the result variable of the declaration
    /// the lookup finds, for calls and member paths alike.
    fn subroutine(
        &mut self,
        ports: &mut [FunctionPort],
        strict: &[Identifier],
        body: &mut crate::ast::shared_vec::SharedVec<Statement>,
    ) {
        let mark = self.hidden.len();
        self.formal_types(ports);
        for p in ports.iter() {
            self.hide_typed(&p.name.name, Hide::Formal, &p.data_type);
        }
        for p in strict {
            self.hide(&p.name, Hide::Formal);
        }
        self.block_labels(body);
        for s in body.iter_mut() {
            self.stmt(s);
        }
        self.hidden.truncate(mark);
    }

    fn assertion_decl(
        &mut self,
        ports: &[Identifier],
        items: &mut [Statement],
        body: &mut Option<Expression>,
    ) {
        let mark = self.hidden.len();
        for p in ports {
            self.hide(&p.name, Hide::Formal);
        }
        items.iter_mut().for_each(|s| self.stmt(s));
        if let Some(e) = body {
            self.expr(e);
        }
        self.hidden.truncate(mark);
    }

    fn let_decl(&mut self, l: &mut LetDeclaration) {
        let mark = self.hidden.len();
        match &mut l.ports {
            PortList::Empty => {}
            PortList::NonAnsi(ids) => {
                for p in ids.iter() {
                    self.hide(&p.name, Hide::Formal);
                }
            }
            PortList::Ansi(ps) => {
                for p in ps.iter_mut() {
                    if let Some(t) = &mut p.data_type {
                        self.data_type(t);
                    }
                    if let Some(d) = &mut p.default {
                        self.expr(d);
                    }
                }
                for p in ps.iter() {
                    self.hide(&p.name.name, Hide::Formal);
                }
            }
        }
        self.expr(&mut l.expr);
        self.hidden.truncate(mark);
    }

    fn clocking(&mut self, c: &mut ClockingDeclaration) {
        if let Some(s) = &c.clock_signal {
            self.ident(s);
        }
        [&mut c.default_input_skew, &mut c.default_output_skew]
            .into_iter()
            .flatten()
            .for_each(|e| self.expr(e));
        for s in &mut c.signals {
            if let Some(e) = &mut s.skew {
                self.expr(e);
            }
            match &mut s.bound_to {
                Some(e) => self.expr(e),
                // §14.3: the clockvar names its signal; the rename keeps it.
                None => self.with_pos("clocking-signal", |b| b.ident(&s.name)),
            }
        }
        c.items.iter_mut().for_each(|s| self.stmt(s));
    }

    fn covergroup(&mut self, c: &mut CovergroupDeclaration) {
        let mark = self.hidden.len();
        self.formal_types(&mut c.ports);
        self.formal_types(&mut c.sample_ports);
        for p in c.ports.iter().chain(&c.sample_ports) {
            self.hide(&p.name.name, Hide::Formal);
        }
        for it in &c.items {
            let name = match it {
                CovergroupItem::Coverpoint(p) => p.name.as_ref(),
                CovergroupItem::Cross(x) => x.name.as_ref(),
                _ => None,
            };
            if let Some(n) = name {
                self.hide(&n.name, Hide::Local);
            }
        }
        c.for_each_expr_mut(&mut |e| self.expr(e));
        // §19.5.1.2: `with` covers a bin's values through `item`.
        self.hide("item", Hide::Iterator);
        for it in &mut c.items {
            if let CovergroupItem::Coverpoint(p) = it {
                for b in &mut p.bins {
                    if let Some(e) = &mut b.with_filter {
                        self.expr(e);
                    }
                    if let Some(e) = &mut b.iff_guard {
                        self.expr(e);
                    }
                }
            }
        }
        self.hidden.truncate(mark);
    }

    fn specify(&mut self, s: &mut SpecifyBlock) {
        for p in &mut s.paths {
            if let Some(c) = &mut p.cond {
                self.expr(c);
            }
            p.delays.iter_mut().for_each(|d| self.expr(d));
        }
        for t in &mut s.timing_checks {
            for a in t.args.iter_mut().flatten() {
                self.expr(&mut a.expr);
                if let Some(c) = &mut a.cond {
                    self.expr(c);
                }
            }
        }
    }

    fn data_type(&mut self, dt: &mut DataType) {
        match dt {
            DataType::IntegerVector { dimensions, .. } | DataType::Implicit { dimensions, .. } => {
                self.packed(dimensions)
            }
            DataType::Struct(s) => {
                for m in &mut s.members {
                    self.data_type(&mut m.data_type);
                    for d in &mut m.declarators {
                        self.unpacked(&mut d.dimensions);
                        if let Some(e) = &mut d.init {
                            self.expr(e);
                        }
                    }
                }
                self.packed(&mut s.dimensions);
            }
            DataType::Enum(e) => {
                if let Some(b) = &mut e.base_type {
                    self.data_type(b);
                }
                for m in &mut e.members {
                    if let Some((l, r)) = &mut m.range {
                        self.expr(l);
                        self.expr(r);
                    }
                    if let Some(i) = &mut m.init {
                        self.expr(i);
                    }
                }
                self.packed(&mut e.dimensions);
            }
            DataType::TypeReference {
                name,
                dimensions,
                type_args,
                ..
            } => {
                if name.scopes.is_empty() {
                    self.ident(&name.name);
                }
                for s in &mut name.scopes {
                    s.type_args.iter_mut().for_each(|a| self.expr(a));
                }
                type_args.iter_mut().for_each(|a| self.expr(a));
                self.packed(dimensions);
            }
            DataType::Interface { type_args, .. } => {
                type_args.iter_mut().for_each(|a| self.expr(a))
            }
            DataType::IntegerAtom { .. }
            | DataType::Real { .. }
            | DataType::Simple { .. }
            | DataType::Void(_) => {}
        }
    }

    fn packed(&mut self, dims: &mut [PackedDimension]) {
        for d in dims {
            if let PackedDimension::Range { left, right, .. } = d {
                self.expr(left);
                self.expr(right);
            }
        }
    }

    fn unpacked(&mut self, dims: &mut [UnpackedDimension]) {
        for d in dims {
            match d {
                UnpackedDimension::Range { left, right, .. } => {
                    self.expr(left);
                    self.expr(right);
                }
                UnpackedDimension::Expression { expr, .. } => self.expr(expr),
                UnpackedDimension::Queue {
                    max_size: Some(e), ..
                } => self.expr(e),
                UnpackedDimension::Associative {
                    data_type: Some(t), ..
                } => self.data_type(t),
                UnpackedDimension::Unsized(_)
                | UnpackedDimension::Queue { .. }
                | UnpackedDimension::Associative { .. } => {}
            }
        }
    }

    /// §9.3.4: a labelled block is a name of the block around it.
    fn block_labels(&mut self, stmts: &[Statement]) {
        for s in stmts {
            for_each_block_label(s, &mut |n| {
                self.hide(&n.name, Hide::Label);
            });
        }
    }

    fn stmt(&mut self, stmt: &mut Statement) {
        let mark = self.hidden.len();
        match &mut stmt.kind {
            StatementKind::Null
            | StatementKind::ScopePop
            | StatementKind::LoopStep
            | StatementKind::DisableFork
            | StatementKind::WaitFork
            | StatementKind::Break
            | StatementKind::Continue
            | StatementKind::RsReturn => {}
            StatementKind::Expr(e) => self.expr(e),
            StatementKind::BlockingAssign { lvalue, rvalue } => {
                self.expr(lvalue);
                self.expr(rvalue);
            }
            StatementKind::NonblockingAssign {
                lvalue,
                delay,
                rvalue,
            } => {
                self.expr(lvalue);
                if let Some(d) = delay {
                    self.expr(d);
                }
                self.expr(rvalue);
            }
            StatementKind::If {
                condition,
                then_stmt,
                else_stmt,
                ..
            } => {
                self.expr(condition);
                // §12.6.2: `matches` variables are in scope in the true branch.
                self.condition_patterns(condition);
                self.stmt(then_stmt);
                self.hidden.truncate(mark);
                if let Some(e) = else_stmt {
                    self.stmt(e);
                }
            }
            StatementKind::Case { expr, items, .. } => {
                self.expr(expr);
                for item in items {
                    let m = self.hidden.len();
                    item.patterns.iter_mut().for_each(|p| self.expr(p));
                    if let Some(p) = &mut item.pattern {
                        self.pattern(p);
                    }
                    if let Some(g) = &mut item.guard {
                        self.expr(g);
                    }
                    self.stmt(&mut item.stmt);
                    self.hidden.truncate(m);
                }
            }
            StatementKind::For {
                init,
                condition,
                step,
                body,
            } => {
                for i in init {
                    match i {
                        ForInit::VarDecl {
                            data_type,
                            name,
                            init,
                        } => {
                            self.with_pos("local-dim", |b| b.data_type(data_type));
                            self.expr(init);
                            self.hide_typed(&name.name, Hide::Loop, data_type);
                        }
                        ForInit::Assign { lvalue, rvalue } => {
                            self.expr(lvalue);
                            self.expr(rvalue);
                        }
                    }
                }
                if let Some(c) = condition {
                    self.expr(c);
                }
                step.iter_mut().for_each(|s| self.expr(s));
                self.stmt(body);
            }
            StatementKind::Foreach { array, vars, body } => {
                self.expr(array);
                for v in vars.iter().flatten() {
                    self.hide(&v.name, Hide::Loop);
                }
                self.stmt(body);
            }
            StatementKind::ForeachTail { loop_var, body, .. } => {
                if let Some(v) = loop_var {
                    self.hide(v, Hide::Loop);
                }
                self.stmt(body);
            }
            StatementKind::While { condition, body } => {
                self.expr(condition);
                self.stmt(body);
            }
            StatementKind::DoWhile { body, condition } => {
                self.stmt(body);
                self.expr(condition);
            }
            StatementKind::Repeat { count, body } => {
                self.expr(count);
                self.stmt(body);
            }
            StatementKind::Forever { body }
            | StatementKind::ForeverTail { body }
            | StatementKind::RsAction { body } => self.stmt(body),
            StatementKind::SeqBlock { name, stmts }
            | StatementKind::ParBlock { name, stmts, .. } => {
                if let Some(n) = name {
                    self.hide(&n.name, Hide::Label);
                }
                self.block_labels(stmts);
                stmts.iter_mut().for_each(|s| self.stmt(s));
            }
            StatementKind::TimingControl { control, stmt } => {
                match control {
                    TimingControl::Delay(d) => self.expr(d),
                    TimingControl::Event(ev) => self.event_control(ev),
                }
                self.stmt(stmt);
            }
            StatementKind::EventTrigger { name, target, .. } => match target {
                Some(t) => self.expr(t),
                None => self.with_pos("event-name", |b| b.ident(name)),
            },
            StatementKind::Wait { condition, stmt } => {
                self.expr(condition);
                self.stmt(stmt);
            }
            StatementKind::Disable(h) => self.disable(h),
            StatementKind::Return(e) => {
                if let Some(e) = e {
                    self.expr(e);
                }
            }
            StatementKind::Assertion(a) => self.assertion(a),
            StatementKind::ProceduralContinuous(pc) => match pc {
                ProceduralContinuous::Assign { lvalue, rvalue }
                | ProceduralContinuous::Force { lvalue, rvalue } => {
                    self.expr(lvalue);
                    self.expr(rvalue);
                }
                ProceduralContinuous::Deassign(e) | ProceduralContinuous::Release(e) => {
                    self.expr(e)
                }
            },
            // §6.5: a declaration hides from its point to the block's end.
            StatementKind::VarDecl {
                data_type,
                declarators,
                ..
            } => {
                self.with_pos("local-dim", |b| b.data_type(data_type));
                for d in declarators.iter_mut() {
                    self.with_pos("local-dim", |b| b.unpacked(&mut d.dimensions));
                    if let Some(init) = &mut d.init {
                        self.expr(init);
                    }
                    self.hide_typed(&d.name.name, Hide::Local, data_type);
                }
                self.hide_enums(data_type);
                return;
            }
            StatementKind::RandCase { items } => {
                for (weight, s) in items {
                    self.expr(weight);
                    self.stmt(s);
                }
            }
            StatementKind::Typedef(t) => {
                self.with_pos("local-dim", |b| {
                    b.data_type(&mut t.data_type);
                    b.unpacked(&mut t.dimensions);
                });
                self.hide(&t.name.name, Hide::Type);
                self.hide_enums(&t.data_type);
                return;
            }
            StatementKind::Coverpoint { expr, .. } => self.with_pos("covergroup", |b| b.expr(expr)),
            StatementKind::Cross { items, .. } => {
                self.with_pos("covergroup", |b| items.iter_mut().for_each(|e| b.expr(e)))
            }
            StatementKind::WaitOrder {
                events, pass, fail, ..
            } => {
                self.with_pos("wait-order", |b| events.iter().for_each(|e| b.ident(e)));
                if let Some(s) = pass {
                    self.stmt(s);
                }
                if let Some(s) = fail {
                    self.stmt(s);
                }
            }
        }
        self.hidden.truncate(mark);
    }

    fn condition_patterns(&mut self, e: &Expression) {
        match &e.kind {
            ExprKind::Matches { pattern, .. } => pattern_vars(pattern, &mut self.hidden),
            ExprKind::Binary { left, right, .. } => {
                self.condition_patterns(left);
                self.condition_patterns(right);
            }
            ExprKind::Paren(x) => self.condition_patterns(x),
            _ => {}
        }
    }

    /// §12.6: constants bind; `.name` declares.
    fn pattern(&mut self, p: &mut Pattern) {
        self.pattern_exprs(p);
        pattern_vars(p, &mut self.hidden);
    }

    fn pattern_exprs(&mut self, p: &mut Pattern) {
        match p {
            Pattern::Wildcard | Pattern::Binding(_) => {}
            Pattern::Tagged { inner, .. } => {
                if let Some(i) = inner {
                    self.pattern_exprs(i);
                }
            }
            Pattern::Expr(e) => self.expr(e),
            Pattern::Struct(items) => items.iter_mut().for_each(|(_, i)| self.pattern_exprs(i)),
        }
    }

    fn event_control(&mut self, ev: &mut EventControl) {
        match ev {
            EventControl::Star | EventControl::ParenStar => {}
            EventControl::Identifier(id) => self.ident(id),
            EventControl::HierIdentifier(e) => self.expr(e),
            EventControl::EventExpr(list) => list.iter_mut().for_each(|e| self.event_expr(e)),
        }
    }

    fn event_expr(&mut self, ev: &mut EventExpr) {
        self.expr(&mut ev.expr);
        if let Some(i) = &mut ev.iff {
            self.expr(i);
        }
    }

    fn assertion(&mut self, a: &mut AssertionStatement) {
        self.expr(&mut a.expr);
        if let Some(s) = &mut a.action {
            self.stmt(s);
        }
        if let Some(s) = &mut a.else_action {
            self.stmt(s);
        }
        if let Some(c) = &mut a.inferred_clock {
            self.event_expr(c);
        }
    }

    /// §18.5 and §18.7.
    fn constraints(&mut self, items: &mut [ConstraintItem]) {
        items.iter_mut().for_each(|i| self.constraint(i));
    }

    fn constraint_ranges(&mut self, ranges: &mut [ConstraintRange]) {
        for r in ranges {
            r.for_each_expr_mut(&mut |e| self.expr(e));
        }
    }

    fn constraint(&mut self, c: &mut ConstraintItem) {
        match c {
            ConstraintItem::Expr(e) => self.expr(e),
            ConstraintItem::Inside {
                expr,
                range,
                dist_weights,
                ..
            } => {
                self.expr(expr);
                self.constraint_ranges(range);
                for w in dist_weights.iter_mut().flatten() {
                    match w {
                        DistWeight::Each(e) | DistWeight::Total(e) => self.expr(e),
                    }
                }
            }
            ConstraintItem::Implication {
                condition,
                constraint,
                ..
            } => {
                self.expr(condition);
                self.constraint(constraint);
            }
            ConstraintItem::IfElse {
                condition,
                then_item,
                else_item,
                ..
            } => {
                self.expr(condition);
                self.constraint(then_item);
                if let Some(e) = else_item {
                    self.constraint(e);
                }
            }
            ConstraintItem::Foreach {
                array, vars, item, ..
            } => {
                self.expr(array);
                let mark = self.hidden.len();
                for v in vars.iter().flatten() {
                    self.hide(&v.name, Hide::Loop);
                }
                self.constraint(item);
                self.hidden.truncate(mark);
            }
            ConstraintItem::Solve {
                before_paths,
                after_paths,
                ..
            } => before_paths
                .iter_mut()
                .chain(after_paths.iter_mut())
                .for_each(|e| self.expr(e)),
            ConstraintItem::Soft(i) => self.constraint(i),
            ConstraintItem::Block(items) => self.constraints(items),
            ConstraintItem::Unique { exprs, .. } => exprs.iter_mut().for_each(|e| self.expr(e)),
        }
    }

    fn expr(&mut self, e: &mut Expression) {
        match &mut e.kind {
            ExprKind::Number(_)
            | ExprKind::StringLiteral(_)
            | ExprKind::Dollar
            | ExprKind::Null
            | ExprKind::This
            | ExprKind::Empty => {}
            ExprKind::TypeLiteral(t) => self.data_type(t),
            ExprKind::Ident(h) => {
                self.head(h);
                for seg in &mut h.path {
                    seg.selects.iter_mut().for_each(|s| self.expr(s));
                }
            }
            ExprKind::Unary { operand, .. } => self.expr(operand),
            ExprKind::Binary { left, right, .. } => {
                self.expr(left);
                self.expr(right);
            }
            ExprKind::Conditional {
                condition,
                then_expr,
                else_expr,
            } => {
                self.expr(condition);
                let mark = self.hidden.len();
                self.condition_patterns(condition);
                self.expr(then_expr);
                self.hidden.truncate(mark);
                self.expr(else_expr);
            }
            ExprKind::Concatenation(parts) => parts.iter_mut().for_each(|p| self.expr(p)),
            ExprKind::Replication { count, exprs } => {
                self.expr(count);
                exprs.iter_mut().for_each(|p| self.expr(p));
            }
            ExprKind::AssignmentPattern(items) => {
                for item in items {
                    match item {
                        AssignmentPatternItem::Ordered(v)
                        | AssignmentPatternItem::Named(_, v)
                        | AssignmentPatternItem::Default(v) => self.expr(v),
                        AssignmentPatternItem::Typed(t, v) => {
                            self.data_type(t);
                            self.expr(v);
                        }
                        AssignmentPatternItem::Keyed(k, v) => {
                            self.expr(k);
                            self.expr(v);
                        }
                    }
                }
            }
            ExprKind::Call { func, args } => {
                self.callee = matches!(func.kind, ExprKind::Ident(_));
                self.expr(func);
                self.callee = false;
                // §18.11: the arguments of `obj.randomize(a)` name its members.
                let mark = self.hidden.len();
                let unknown = self.unknown_members;
                if is_randomize(func) {
                    self.receiver_members(func);
                }
                args.iter_mut().for_each(|a| self.expr(a));
                self.unknown_members = unknown;
                self.hidden.truncate(mark);
            }
            // §16.10: `$sva_locals(<locals>..., body)` carries an assertion's
            // local variables, each visible after its declaration.
            ExprKind::SystemCall { name, args } => {
                let mark = self.hidden.len();
                for a in args.iter_mut() {
                    if let ExprKind::SystemCall {
                        name: n,
                        args: decl,
                    } = &a.kind
                        && n == "$sva_local"
                        && name == "$sva_locals"
                        && let Some(ExprKind::Ident(h)) = decl.get(1).map(|d| &d.kind)
                    {
                        let local = h.path[0].name.name.clone();
                        self.hide(&local, Hide::Local);
                    }
                    self.expr(a);
                }
                self.hidden.truncate(mark);
            }
            ExprKind::NamedArg { expr, .. } => {
                if let Some(v) = expr {
                    self.expr(v);
                }
            }
            ExprKind::Inside { expr, ranges } => {
                self.expr(expr);
                ranges.iter_mut().for_each(|r| self.expr(r));
            }
            ExprKind::Matches { expr, pattern } => {
                self.expr(expr);
                self.pattern_exprs(pattern);
            }
            ExprKind::MemberAccess { expr, .. } => self.expr(expr),
            ExprKind::Specialization { base, .. } => self.expr(base),
            ExprKind::Index { expr, index } => {
                self.expr(expr);
                self.expr(index);
            }
            ExprKind::RangeSelect {
                expr, left, right, ..
            } => {
                self.expr(expr);
                self.expr(left);
                self.expr(right);
            }
            ExprKind::Range(l, r) => {
                self.expr(l);
                self.expr(r);
            }
            ExprKind::Paren(x) => self.expr(x),
            // §7.12: the iterators, named or not, are in scope for the filter.
            ExprKind::WithClause { expr, filter } => {
                let mark = self.hidden.len();
                self.hide("item", Hide::Iterator);
                self.hide("index", Hide::Iterator);
                if let ExprKind::Call { args, .. } = &expr.kind {
                    for a in args {
                        if let ExprKind::Ident(h) = &a.kind {
                            if h.path.len() == 1 {
                                self.hide(&h.path[0].name.name, Hide::Iterator);
                            }
                        }
                    }
                }
                self.expr(expr);
                self.expr(filter);
                self.hidden.truncate(mark);
            }
            // §18.7: an object's class comes first. Where the class is not
            // found, any name a class declares stays unbound.
            ExprKind::RandomizeWith { call, constraints } => {
                self.expr(call);
                let mark = self.hidden.len();
                let unknown = self.unknown_members;
                self.receiver_members(randomize_target(call));
                self.constraints(constraints);
                self.unknown_members = unknown;
                self.hidden.truncate(mark);
            }
            ExprKind::AssignExpr { lvalue, rvalue } => {
                self.expr(lvalue);
                self.expr(rvalue);
            }
            ExprKind::StreamOp {
                slice_size, exprs, ..
            } => {
                if let Some(s) = slice_size {
                    self.expr(s);
                }
                exprs.iter_mut().for_each(|x| self.expr(x));
            }
            ExprKind::Tagged { inner, .. } => {
                if let Some(i) = inner {
                    self.with_pos("tagged", |b| b.expr(i));
                }
            }
            ExprKind::SvaClocked { events, body } => {
                events.iter_mut().for_each(|ev| self.event_expr(ev));
                self.expr(body);
            }
            ExprKind::ShallowCopy { source } => self.with_pos("shallow-copy", |b| b.expr(source)),
            ExprKind::TypedPattern { ty, pattern } => {
                self.data_type(ty);
                self.expr(pattern);
            }
        }
    }

    fn definition(
        &mut self,
        params: &mut [ParameterDeclaration],
        ports: &mut PortList,
        items: &mut [ModuleItem],
    ) {
        params.iter_mut().for_each(|p| self.parameter(p));
        if let PortList::Ansi(ps) = ports {
            for p in ps {
                if let Some(t) = &mut p.data_type {
                    self.data_type(t);
                }
                self.unpacked(&mut p.dimensions);
                if let Some(d) = &mut p.default {
                    self.expr(d);
                }
            }
        }
        self.items(items);
    }
}

/// A keyword the parser hands over as a name: a built-in method, or a built-in
/// type as a class type argument (`K #(int)`).
fn is_keyword_name(name: &str) -> bool {
    matches!(
        name,
        "this"
            | "super"
            | "new"
            | "randomize"
            | "bit"
            | "logic"
            | "reg"
            | "byte"
            | "shortint"
            | "int"
            | "longint"
            | "integer"
            | "time"
            | "real"
            | "shortreal"
            | "realtime"
            | "string"
            | "chandle"
            | "event"
    )
}

/// The method a `randomize` call or a bare `obj.randomize` names.
fn randomize_target(call: &Expression) -> &Expression {
    match &call.kind {
        ExprKind::Call { func, .. } => func,
        _ => call,
    }
}

fn is_randomize(target: &Expression) -> bool {
    match &target.kind {
        ExprKind::Ident(h) => h.path.last().is_some_and(|s| s.name.name == "randomize"),
        ExprKind::MemberAccess { member, .. } => member.name == "randomize",
        _ => false,
    }
}

/// Whether a `randomize` method is on an object, not `std::randomize` or bare.
fn has_receiver(target: &Expression) -> bool {
    match &target.kind {
        ExprKind::Ident(h) => h.path.len() > 1 && h.path[0].name.name != "std",
        ExprKind::MemberAccess { expr, .. } => {
            !matches!(&expr.kind, ExprKind::Ident(h) if h.path[0].name.name == "std")
        }
        _ => false,
    }
}

/// The receiver of `r.randomize()`, when it is one name with no select.
fn receiver_name(target: &Expression) -> Option<&str> {
    let head = |h: &'_ HierarchicalIdentifier| h.root.is_none() && h.path[0].selects.is_empty();
    match &target.kind {
        ExprKind::Ident(h)
            if h.path.len() == 2 && h.path[1].name.name == "randomize" && head(h) =>
        {
            Some(&h.path[0].name.name)
        }
        ExprKind::MemberAccess { expr, member } if member.name == "randomize" => match &expr.kind {
            ExprKind::Ident(h) if h.path.len() == 1 && head(h) => Some(&h.path[0].name.name),
            _ => None,
        },
        _ => None,
    }
}

fn pattern_vars(p: &Pattern, out: &mut Vec<Hidden>) {
    match p {
        Pattern::Binding(n) => out.push((n.name.clone(), Hide::Pattern, None)),
        Pattern::Tagged { inner: Some(i), .. } => pattern_vars(i, out),
        Pattern::Struct(items) => items.iter().for_each(|(_, i)| pattern_vars(i, out)),
        Pattern::Wildcard | Pattern::Tagged { .. } | Pattern::Expr(_) => {}
    }
}

fn run<'a>(
    tree: &'a ScopeTree,
    others: &'a [ScopeTree],
    names: &'a DesignNames,
    record: bool,
) -> Binder<'a> {
    Binder {
        tree,
        names,
        others,
        scope: tree.root,
        next_child: vec![0; tree.scopes.len()],
        hidden: Vec::new(),
        unknown_members: 0,
        outer: Vec::new(),
        formals: Vec::new(),
        callee: false,
        pos: "process",
        mentions: record.then(Vec::new),
    }
}

type DefinitionParts<'d> = (
    &'d str,
    &'d mut [ParameterDeclaration],
    &'d mut PortList,
    &'d mut [ModuleItem],
);

fn definition_parts(d: &mut Description) -> Option<DefinitionParts<'_>> {
    match d {
        Description::Module(m) => Some((&m.name.name, &mut m.params, &mut m.ports, &mut m.items)),
        Description::Interface(m) => {
            Some((&m.name.name, &mut m.params, &mut m.ports, &mut m.items))
        }
        Description::Program(m) => Some((&m.name.name, &mut m.params, &mut m.ports, &mut m.items)),
        Description::PackageItem(PackageItem::Checker(c)) => {
            Some((&c.name.name, &mut [], &mut c.ports, &mut c.items))
        }
        _ => None,
    }
}

/// Bind one description that is a definition; `trees` ends with its tree and
/// holds those of its nested definitions.
pub fn bind_description(
    d: &mut Description,
    trees: &[ScopeTree],
    names: &DesignNames,
    audit: bool,
) {
    let Some((name, params, ports, items)) = definition_parts(d) else {
        return;
    };
    bind_definition(name, params, ports, items, trees, names, audit);
}

/// See `bind_description`.
pub fn bind_definition(
    name: &str,
    params: &mut [ParameterDeclaration],
    ports: &mut PortList,
    items: &mut [ModuleItem],
    trees: &[ScopeTree],
    names: &DesignNames,
    audit: bool,
) {
    let lines = bind_and_compare(params, ports, items, trees, names, audit);
    for l in &lines {
        eprintln!(
            "[bind-audit] {}",
            l.render(&super::audit_location(name, l.span))
        );
    }
}

fn bind_and_compare(
    params: &mut [ParameterDeclaration],
    ports: &mut PortList,
    items: &mut [ModuleItem],
    trees: &[ScopeTree],
    names: &DesignNames,
    audit: bool,
) -> Vec<AuditLine> {
    let Some((tree, others)) = trees.split_last() else {
        return Vec::new();
    };
    let mut b = run(tree, others, names, audit);
    b.definition(params, ports, items);
    let Some(mentions) = b.mentions.take() else {
        return Vec::new();
    };
    let mut copy = items.to_vec();
    rename_like_expansion(&mut copy);
    let mut after = run(tree, others, names, true);
    after.definition(&mut params.to_vec(), &mut ports.clone(), &mut copy);
    compare(
        &tree.def,
        mentions,
        after.mentions.take().unwrap_or_default(),
    )
}

/// Run the generate rename over `items` as expansion does: each block of each
/// arm, outermost first, with `[@]` for a loop index (§27.4). Dead arms too,
/// and without the genvar substitution, which changes no name position.
fn rename_like_expansion(items: &mut Vec<ModuleItem>) {
    for item in items.iter_mut() {
        match item {
            ModuleItem::GenerateRegion(g) => rename_like_expansion(&mut g.items),
            ModuleItem::NestedModule(m) => rename_like_expansion(&mut m.items),
            ModuleItem::CheckerDeclaration(c) => rename_like_expansion(&mut c.items),
            ModuleItem::GenerateIf(g) => {
                for (bi, (_, branch)) in g.branches.iter_mut().enumerate() {
                    if g.branch_direct.get(bi) != Some(&true) {
                        let label = g.branch_labels.get(bi).cloned().flatten();
                        *branch = rename_arm(branch, label.as_ref(), &g.implicit_name);
                    }
                    rename_like_expansion(branch);
                }
            }
            ModuleItem::GenerateCase(g) => {
                for arm in &mut g.arms {
                    if !arm.direct {
                        arm.items = rename_arm(&arm.items, arm.label.as_ref(), &g.implicit_name);
                    }
                    rename_like_expansion(&mut arm.items);
                }
            }
            ModuleItem::GenerateFor(g) => {
                let scope = format!("{}[@]", gen_scope_name(g.name.as_ref(), &g.implicit_name));
                g.items = rename_decls_in_iter(&g.items, &GenRename::Scope(&scope));
                rename_like_expansion(&mut g.items);
            }
            _ => {}
        }
    }
}

fn rename_arm(items: &[ModuleItem], label: Option<&String>, implicit: &str) -> Vec<ModuleItem> {
    rename_decls_in_iter(items, &GenRename::Scope(&gen_scope_name(label, implicit)))
}

/// §27.5: the task `path` names from scope `from`: each segment but the last
/// a generate block of the scope before (any arm of that label), a loop
/// block with one literal index (§27.4). With the path joined as the key.
fn path_task(
    tree: &ScopeTree,
    from: ScopeId,
    path: &[HierPathSegment],
) -> Option<(DeclId, String)> {
    let (last, blocks) = path.split_last()?;
    let mut scopes = vec![from];
    let mut key = Vec::new();
    for seg in blocks {
        let name = seg.name.name.as_str();
        let index = match &seg.selects[..] {
            [] => None,
            [e] => Some(literal_index(e)?),
            _ => return None,
        };
        scopes = scopes
            .iter()
            .flat_map(|s| tree.scopes[s.0 as usize].children.iter().copied())
            .filter(|c| {
                let sc = &tree.scopes[c.0 as usize];
                sc.seg.as_deref() == Some(name)
                    && matches!(sc.kind, ScopeKind::Generate { indexed, .. } if indexed == index.is_some())
            })
            .collect();
        key.push(match index {
            Some(i) => format!("{name}[{i}]"),
            None => name.to_string(),
        });
    }
    if !last.selects.is_empty() || scopes.iter().all(|s| *s == from) {
        return None;
    }
    let d = scopes.iter().find_map(|s| {
        tree.scopes[s.0 as usize]
            .by_name
            .get(&last.name.name)
            .copied()
            .filter(|d| tree.decls[d.0 as usize].kind == DeclKind::Task)
    })?;
    key.push(last.name.name.clone());
    Some((d, key.join(".")))
}

/// An unsized decimal literal.
fn literal_index(e: &Expression) -> Option<i64> {
    match &e.kind {
        ExprKind::Number(NumberLiteral::Integer {
            size: None,
            base: NumberBase::Decimal,
            value,
            ..
        }) => value.replace('_', "").parse().ok(),
        _ => None,
    }
}

/// The verdict on one name: which way the rename and the binding differ.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Disagree {
    /// The rename rewrites a name to an outer declaration: a hiding name has
    /// no tree binding, or its declaration is deeper than the rename's key.
    Hiding,
    /// The rename does not reach a name that binds to a renamed declaration.
    Unvisited,
    /// Neither.
    Other,
}

/// One line of the audit.
#[derive(Debug, Clone)]
pub struct AuditLine {
    pub span: Span,
    pub name: String,
    /// `Decl(<def>[.<scope path>], <kind>)`, `Upward` or `none`.
    pub binding: String,
    pub outcome: Outcome,
    /// What the rename made of the name, when it changed it.
    pub renamed: Option<String>,
    pub pos: &'static str,
    /// The name is the callee of a call.
    pub call: bool,
    /// What the tree declares under this name, hiding aside.
    pub target: Option<DeclKind>,
    pub disagree: Option<Disagree>,
}

impl AuditLine {
    fn render(&self, location: &str) -> String {
        let mut s = format!("{location} {} -> {}", self.name, self.binding);
        match &self.renamed {
            Some(r) => s.push_str(&format!(" rename: yes({r})")),
            None => s.push_str(" rename: no"),
        }
        s.push_str(&format!(" pos={}", self.pos));
        if self.call {
            s.push_str("/call");
        }
        match self.target {
            Some(k) => s.push_str(&format!(" target={k:?}")),
            None => s.push_str(" target=-"),
        }
        if let Outcome::None(why) = self.outcome {
            s.push_str(&format!(" why={why:?}"));
        }
        match self.disagree {
            Some(Disagree::Hiding) => s.push_str(" disagree=A"),
            Some(Disagree::Unvisited) => s.push_str(" disagree=B"),
            Some(Disagree::Other) => s.push_str(" disagree=?"),
            None => {}
        }
        s
    }
}

/// The name the rename gives a declaration, when it renames that kind: a
/// block's subroutines, data, nets, parameters, instances, properties,
/// sequences and typedefs (§27.5, §27.6).
fn renamed_key(tree: &ScopeTree, scope: ScopeId, name: &str, kind: DeclKind) -> Option<String> {
    let key = match kind {
        DeclKind::Function
        | DeclKind::Task
        | DeclKind::Data
        | DeclKind::Net
        | DeclKind::Param
        | DeclKind::Instance
        | DeclKind::Property
        | DeclKind::Sequence
        | DeclKind::Typedef => tree.key(scope, name, &[]),
        _ => return None,
    };
    (key != name).then_some(key)
}

fn outer_keys(tree: &ScopeTree, s: ScopeId, name: &str) -> Vec<String> {
    let mut keys = Vec::new();
    let mut at = tree.scopes[s.0 as usize].parent;
    while let Some(a) = at {
        keys.push(tree.key(a, name, &[]));
        at = tree.scopes[a.0 as usize].parent;
    }
    keys
}

fn compare(def: &str, before: Vec<Mention>, after: Vec<Mention>) -> Vec<AuditLine> {
    if before.len() != after.len() {
        eprintln!(
            "[bind-audit] unaligned {def} {} {}",
            before.len(),
            after.len()
        );
    }
    before
        .into_iter()
        .zip(after)
        .map(|(m, a)| {
            // §3.12.1: the rewrite drops a `$unit::` it finds unshadowed.
            let bare = crate::sv_parser::strip_unit_scope_name(&m.name).unwrap_or(&m.name);
            let renamed = (a.name != m.name && a.name != bare).then(|| a.name.clone());
            let disagree = match (&renamed, &m.want) {
                (None, None) => None,
                (Some(r), Some(w)) if r == w => None,
                (Some(r), _) => Some(match m.outcome {
                    Outcome::None(why) if why != Hide::Qualified => Disagree::Hiding,
                    Outcome::Decl(_) if m.outer_keys.contains(r) => Disagree::Hiding,
                    _ => Disagree::Other,
                }),
                (None, Some(_)) if UNVISITED.contains(&m.pos) => Some(Disagree::Unvisited),
                (None, Some(_)) if partly_renamed(m.pos, m.target) => Some(Disagree::Unvisited),
                (None, Some(_)) => Some(Disagree::Other),
            };
            AuditLine {
                span: m.span,
                name: m.name,
                binding: m.binding,
                outcome: m.outcome,
                renamed,
                pos: m.pos,
                call: m.call,
                target: m.target,
                disagree,
            }
        })
        .collect()
}

fn binding_text(tree: &ScopeTree, o: Outcome) -> String {
    match o {
        Outcome::Decl(d) => {
            let decl = &tree.decls[d.0 as usize];
            let path = tree.path(decl.scope);
            if path.is_empty() {
                format!("Decl({}, {:?})", tree.def, decl.kind)
            } else {
                format!("Decl({}.{path}, {:?})", tree.def, decl.kind)
            }
        }
        Outcome::Upward => "Upward".to_string(),
        Outcome::None(_) => "none".to_string(),
    }
}

/// The audit of a whole parsed design, stamping and binding it on the way.
pub fn audit_design(descs: &mut [Description]) -> Vec<AuditLine> {
    let names = DesignNames::collect(descs);
    let mut out = Vec::new();
    for d in descs.iter_mut() {
        let mut trees = Vec::new();
        let Some(tree) = crate::scope_tree::build_one(d, &mut trees) else {
            continue;
        };
        trees.push(tree);
        let Some((_, params, ports, items)) = definition_parts(d) else {
            continue;
        };
        out.extend(bind_and_compare(params, ports, items, &trees, &names, true));
    }
    out
}
