//! §23.9, §27.5, §27.6: the lexical scopes of one definition, before any
//! expansion: the definition body and its generate blocks, all arms included,
//! with the names each scope declares.
//!
//! Building a tree also writes each construct's implicit block name into the
//! AST (`implicit_name`). Both expansion paths and the VPI model read that
//! name, so one rule names a scope everywhere.

use crate::ast::Description;
use crate::ast::binding::{DeclId, DeclKind, ScopeId};
use crate::ast::decl::{
    DPIProto, GenerateCase, GenerateIf, ModuleItem, PackageItem, ParameterDeclaration,
    ParameterKind, PortConnection,
};
use crate::ast::expr::{ExprKind, Expression};
use crate::ast::module::PortList;
use crate::ast::stmt::{Statement, StatementKind};
use crate::ast::types::DataType;
use crate::ast::{Identifier, Span};
use crate::elaborate::bind::{self, DesignNames};
use crate::hasher::HashMap;
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScopeKind {
    Definition,
    /// `ordinal` is the §27.6 number of the block's construct in its parent.
    Generate {
        label: Option<String>,
        ordinal: u32,
        indexed: bool,
    },
}

/// The last segment of a named type, which may be a class.
pub(crate) fn class_type_name(dt: &DataType) -> Option<String> {
    match dt {
        DataType::TypeReference { name, .. } => {
            name.name.name.rsplit("::").next().map(str::to_string)
        }
        _ => None,
    }
}

#[derive(Debug, Clone)]
pub struct Decl {
    pub kind: DeclKind,
    pub name: String,
    pub span: Span,
    pub scope: ScopeId,
}

#[derive(Debug, Clone)]
pub struct Scope {
    pub kind: ScopeKind,
    pub parent: Option<ScopeId>,
    pub children: Vec<ScopeId>,
    /// Path segment from the parent: the label or `genblk<n>`; None at the root.
    pub seg: Option<String>,
    pub decls: Vec<DeclId>,
    pub by_name: HashMap<String, DeclId>,
    /// §26.3: packages of `import p::*` in this scope.
    pub wildcard_imports: Vec<String>,
    /// §26.3: name to package for `import p::name` in this scope.
    pub explicit_imports: HashMap<String, String>,
    /// §27.5: blocks with the same group exclude each other at elaboration.
    pub arm_group: Option<u32>,
}

#[derive(Debug, Clone)]
pub struct ScopeTree {
    pub def: String,
    pub root: ScopeId,
    pub scopes: Vec<Scope>,
    pub decls: Vec<Decl>,
    /// The class a data or port declaration's type may name (§8.3).
    pub decl_types: HashMap<DeclId, String>,
}

impl ScopeTree {
    /// Build the tree of one definition and stamp `implicit_name` on its
    /// constructs. Trees of nested modules and checkers go to `others`.
    pub fn build(
        def: &str,
        params: &[ParameterDeclaration],
        ports: &PortList,
        items: &mut [ModuleItem],
        others: &mut Vec<ScopeTree>,
    ) -> ScopeTree {
        let mut b = Builder {
            tree: ScopeTree {
                def: def.to_string(),
                root: ScopeId(0),
                scopes: Vec::new(),
                decls: Vec::new(),
                decl_types: HashMap::default(),
            },
            groups: 0,
            loop_vars: Vec::new(),
            others,
        };
        let root = b.open(None, ScopeKind::Definition, None, None);
        for p in params {
            b.declare_param(root, p);
        }
        match ports {
            PortList::Empty => {}
            PortList::Ansi(ps) => {
                for p in ps {
                    match &p.data_type {
                        Some(dt) => b.declare_typed(root, &p.name.name, p.name.span, dt),
                        None => b.declare(root, DeclKind::Data, &p.name.name, p.name.span),
                    }
                }
            }
            PortList::NonAnsi(ids) => {
                for p in ids {
                    b.declare(root, DeclKind::Data, &p.name, p.span);
                }
            }
        }
        b.fill(root, items);
        b.tree
    }

    /// §23.9: the declaration of `name` in the innermost scope on the chain
    /// from `from` that declares it.
    pub fn lookup(&self, from: ScopeId, name: &str) -> Option<DeclId> {
        let mut at = Some(from);
        while let Some(s) = at {
            let scope = &self.scopes[s.0 as usize];
            if let Some(d) = scope.by_name.get(name) {
                return Some(*d);
            }
            at = scope.parent;
        }
        None
    }

    /// §23.4: a nested definition's tree is keyed by where it is declared, so
    /// same-named nested modules of two parents stay apart.
    pub fn nested_def(&self, s: ScopeId, name: &str) -> String {
        format!("{}.{}", self.def, self.key(s, name, &[]))
    }

    /// Scope path from the definition, `[@]` for an indexed scope: `g[@].h`.
    pub fn path(&self, s: ScopeId) -> String {
        self.joined(s, &mut std::iter::repeat_with(|| None))
    }

    /// The flat key of `name` in scope `s`, with `indices` filling the indexed
    /// scopes from the outermost in: `g[1].h.x`.
    pub fn key(&self, s: ScopeId, name: &str, indices: &[i64]) -> String {
        let mut it = indices.iter().map(|i| Some(*i));
        let path = self.joined(s, &mut it);
        if path.is_empty() {
            name.to_string()
        } else {
            format!("{path}.{name}")
        }
    }

    fn joined(&self, s: ScopeId, indices: &mut dyn Iterator<Item = Option<i64>>) -> String {
        let mut chain = Vec::new();
        let mut at = Some(s);
        while let Some(id) = at {
            let scope = &self.scopes[id.0 as usize];
            chain.push(scope);
            at = scope.parent;
        }
        let mut segs = Vec::new();
        for scope in chain.iter().rev() {
            let Some(seg) = &scope.seg else { continue };
            if matches!(scope.kind, ScopeKind::Generate { indexed: true, .. }) {
                match indices.next().flatten() {
                    Some(i) => segs.push(format!("{seg}[{i}]")),
                    None => segs.push(format!("{seg}[@]")),
                }
            } else {
                segs.push(seg.clone());
            }
        }
        segs.join(".")
    }
}

struct Builder<'a> {
    tree: ScopeTree,
    groups: u32,
    /// Generate loop variables of the enclosing loops (§27.4).
    loop_vars: Vec<String>,
    others: &'a mut Vec<ScopeTree>,
}

impl Builder<'_> {
    fn open(
        &mut self,
        parent: Option<ScopeId>,
        kind: ScopeKind,
        seg: Option<String>,
        arm_group: Option<u32>,
    ) -> ScopeId {
        let id = ScopeId(self.tree.scopes.len() as u32);
        self.tree.scopes.push(Scope {
            kind,
            parent,
            children: Vec::new(),
            seg,
            decls: Vec::new(),
            by_name: HashMap::default(),
            wildcard_imports: Vec::new(),
            explicit_imports: HashMap::default(),
            arm_group,
        });
        if let Some(p) = parent {
            self.tree.scopes[p.0 as usize].children.push(id);
        }
        id
    }

    /// Declarations first: a name declared after a construct still conflicts
    /// with its implicit name (§27.6).
    fn fill(&mut self, s: ScopeId, items: &mut [ModuleItem]) {
        self.declare_items(s, items);
        self.declare_implicit_nets(s, items);
        let mut next = 0;
        let mut implicit = Vec::new();
        self.number_items(s, items, &mut next, &mut implicit);
        // §27.6: an unnamed block's implicit name is a name of the scope.
        for (name, span) in implicit {
            self.declare(s, DeclKind::Label, &name, span);
        }
    }

    /// §6.10: a name in a port connection, a gate terminal or the left-hand
    /// side of a continuous assignment, and §31.9 a delayed signal, that no
    /// scope on the chain declares is an implicit net of this scope.
    fn declare_implicit_nets(&mut self, s: ScopeId, items: &[ModuleItem]) {
        let mut uses = Vec::new();
        implicit_net_uses(items, &mut uses);
        for (name, span) in uses {
            if !self.loop_vars.iter().any(|v| v == name) && self.tree.lookup(s, name).is_none() {
                self.declare(s, DeclKind::ImplicitNet, name, span);
            }
        }
    }

    fn declare(&mut self, s: ScopeId, kind: DeclKind, name: &str, span: Span) {
        if name.is_empty() || self.tree.scopes[s.0 as usize].by_name.contains_key(name) {
            return;
        }
        let id = DeclId(self.tree.decls.len() as u32);
        self.tree.decls.push(Decl {
            kind,
            name: name.to_string(),
            span,
            scope: s,
        });
        let scope = &mut self.tree.scopes[s.0 as usize];
        scope.decls.push(id);
        scope.by_name.insert(name.to_string(), id);
    }

    /// A data declaration, with the class its type may name.
    fn declare_typed(&mut self, s: ScopeId, name: &str, span: Span, dt: &DataType) {
        let at = self.tree.decls.len();
        self.declare(s, DeclKind::Data, name, span);
        if self.tree.decls.len() > at
            && let Some(class) = class_type_name(dt)
        {
            self.tree.decl_types.insert(DeclId(at as u32), class);
        }
    }

    fn declare_param(&mut self, s: ScopeId, p: &ParameterDeclaration) {
        match &p.kind {
            ParameterKind::Data {
                assignments,
                data_type,
            } => {
                self.declare_enum_members(s, data_type);
                for a in assignments {
                    self.declare(s, DeclKind::Param, &a.name.name, a.name.span);
                }
            }
            ParameterKind::Type { assignments } => {
                for a in assignments {
                    self.declare(s, DeclKind::TypeParam, &a.name.name, a.name.span);
                }
            }
        }
    }

    fn declare_enum_members(&mut self, s: ScopeId, dt: &DataType) {
        for_each_enum_member(dt, &mut |n| {
            self.declare(s, DeclKind::EnumMember, &n.name, n.span)
        });
    }

    /// The names `items` declare in scope `s`. A generate region (§27.3) opens
    /// no scope, and a directly nested construct's blocks belong to the outer
    /// construct (§27.5), so their labels are declared here too.
    fn declare_items(&mut self, s: ScopeId, items: &[ModuleItem]) {
        use DeclKind as K;
        for item in items {
            match item {
                ModuleItem::PortDeclaration(d) => {
                    self.declare_enum_members(s, &d.data_type);
                    for v in &d.declarators {
                        self.declare_typed(s, &v.name.name, v.name.span, &d.data_type);
                    }
                }
                ModuleItem::NetDeclaration(d) => {
                    self.declare_enum_members(s, &d.data_type);
                    for v in &d.declarators {
                        self.declare(s, K::Net, &v.name.name, v.name.span);
                    }
                }
                ModuleItem::DataDeclaration(d) => {
                    self.declare_enum_members(s, &d.data_type);
                    for v in &d.declarators {
                        self.declare_typed(s, &v.name.name, v.name.span, &d.data_type);
                    }
                }
                ModuleItem::ParameterDeclaration(p) | ModuleItem::LocalparamDeclaration(p) => {
                    self.declare_param(s, p)
                }
                // §6.18: a forward declaration names the type a later
                // typedef or class declares.
                ModuleItem::TypedefDeclaration(t) if matches!(t.data_type, DataType::Void(_)) => {}
                ModuleItem::TypedefDeclaration(t) => {
                    self.declare_enum_members(s, &t.data_type);
                    self.declare(s, K::Typedef, &t.name.name, t.name.span);
                }
                ModuleItem::GenvarDeclaration(g) => {
                    for n in &g.names {
                        self.declare(s, K::Genvar, &n.name, n.span);
                    }
                }
                ModuleItem::ModuleInstantiation(m) => {
                    for i in &m.instances {
                        self.declare(s, K::Instance, &i.name.name, i.name.span);
                    }
                }
                ModuleItem::GateInstantiation(g) => {
                    for n in g.instances.iter().filter_map(|i| i.name.as_ref()) {
                        self.declare(s, K::Gate, &n.name, n.span);
                    }
                }
                // An out-of-block class method belongs to the class.
                ModuleItem::FunctionDeclaration(f) if f.name.scopes.is_empty() => {
                    let n = &f.name.name;
                    self.declare(s, K::Function, &n.name, n.span);
                }
                ModuleItem::TaskDeclaration(t) if t.name.scopes.is_empty() => {
                    let n = &t.name.name;
                    self.declare(s, K::Task, &n.name, n.span);
                }
                ModuleItem::DPIImport(d) => {
                    let n = match &d.proto {
                        DPIProto::Function(f) => &f.name.name,
                        DPIProto::Task(t) => &t.name.name,
                    };
                    self.declare(s, K::DpiImport, &n.name, n.span);
                }
                ModuleItem::ClassDeclaration(c) => {
                    self.declare(s, K::Class, &c.name.name, c.name.span)
                }
                ModuleItem::CovergroupDeclaration(c) => {
                    self.declare(s, K::Covergroup, &c.name.name, c.name.span)
                }
                ModuleItem::ClockingDeclaration(c) => {
                    self.declare(s, K::Clocking, &c.name.name, c.name.span)
                }
                ModuleItem::CheckerDeclaration(c) => {
                    self.declare(s, K::Checker, &c.name.name, c.name.span)
                }
                ModuleItem::LetDeclaration(l) => self.declare(s, K::Let, &l.name.name, l.name.span),
                ModuleItem::PropertyDeclaration(p) => {
                    self.declare(s, K::Property, &p.name.name, p.name.span)
                }
                ModuleItem::SequenceDeclaration(q) => {
                    self.declare(s, K::Sequence, &q.name.name, q.name.span)
                }
                ModuleItem::NettypeDeclaration(n) => {
                    self.declare_enum_members(s, &n.data_type);
                    self.declare(s, K::Nettype, &n.name.name, n.name.span)
                }
                // §16.2: a module-level assertion's label names a scope.
                ModuleItem::AssertionItem(a) => {
                    if let Some(l) = &a.label {
                        self.declare(s, K::Label, &l.name, l.span);
                    }
                }
                ModuleItem::ModportDeclaration(m) => {
                    for i in &m.items {
                        self.declare(s, K::Modport, &i.name.name, i.name.span);
                    }
                }
                ModuleItem::NestedModule(m) => {
                    self.declare(s, K::Module, &m.name.name, m.name.span)
                }
                ModuleItem::ImportDeclaration(d) => {
                    let scope = &mut self.tree.scopes[s.0 as usize];
                    for i in &d.items {
                        match &i.item {
                            Some(n) => {
                                scope
                                    .explicit_imports
                                    .insert(n.name.clone(), i.package.name.clone());
                            }
                            None => scope.wildcard_imports.push(i.package.name.clone()),
                        }
                    }
                }
                ModuleItem::AlwaysConstruct(a) => self.declare_block_name(s, &a.stmt),
                ModuleItem::InitialConstruct(a) => self.declare_block_name(s, &a.stmt),
                ModuleItem::FinalConstruct(a) => self.declare_block_name(s, &a.stmt),
                ModuleItem::GenerateRegion(g) => self.declare_items(s, &g.items),
                ModuleItem::GenerateIf(g) => {
                    for l in g.branch_labels.iter().flatten() {
                        self.declare(s, K::Label, l, g.span);
                    }
                    for (bi, (_, branch)) in g.branches.iter().enumerate() {
                        if g.branch_direct.get(bi) == Some(&true) {
                            self.declare_items(s, branch);
                        }
                    }
                }
                ModuleItem::GenerateCase(g) => {
                    for arm in &g.arms {
                        if let Some(l) = &arm.label {
                            self.declare(s, K::Label, l, g.span);
                        }
                        if arm.direct {
                            self.declare_items(s, &arm.items);
                        }
                    }
                }
                ModuleItem::GenerateFor(g) => {
                    if let Some(l) = &g.name {
                        self.declare(s, K::Label, l, g.span);
                    }
                }
                _ => {}
            }
        }
    }

    /// §9.3.4: a process's named block is a name in the enclosing scope.
    fn declare_block_name(&mut self, s: ScopeId, stmt: &Statement) {
        for_each_block_label(stmt, &mut |n| {
            self.declare(s, DeclKind::Label, &n.name, n.span)
        });
    }

    /// §27.6: `genblk<n>`, with leading zeros on `n` until no explicitly
    /// declared name of the scope conflicts.
    fn implicit_name(&self, s: ScopeId, ordinal: u32) -> String {
        let by_name = &self.tree.scopes[s.0 as usize].by_name;
        let explicit = |n: &str| {
            by_name
                .get(n)
                .is_some_and(|d| self.tree.decls[d.0 as usize].kind != DeclKind::ImplicitNet)
        };
        let mut name = format!("genblk{ordinal}");
        while explicit(&name) {
            name.insert(6, '0');
        }
        name
    }

    /// §27.6: each construct of the scope takes the next number, in source
    /// order, through generate regions (§27.3). `implicit` gets the names
    /// that name a block.
    fn number_items(
        &mut self,
        s: ScopeId,
        items: &mut [ModuleItem],
        next: &mut u32,
        implicit: &mut Vec<(String, Span)>,
    ) {
        for item in items {
            match item {
                ModuleItem::GenerateRegion(g) => self.number_items(s, &mut g.items, next, implicit),
                ModuleItem::GenerateIf(_) | ModuleItem::GenerateCase(_) => {
                    *next += 1;
                    let name = self.implicit_name(s, *next);
                    self.groups += 1;
                    let group = self.groups;
                    let span = match item {
                        ModuleItem::GenerateIf(g) => g.span,
                        ModuleItem::GenerateCase(g) => g.span,
                        _ => unreachable!(),
                    };
                    let before = self.tree.scopes[s.0 as usize].children.len();
                    self.conditional(s, item, *next, &name, group);
                    let unnamed = self.tree.scopes[s.0 as usize].children[before..]
                        .iter()
                        .any(|c| {
                            matches!(
                                self.tree.scopes[c.0 as usize].kind,
                                ScopeKind::Generate { label: None, .. }
                            )
                        });
                    if unnamed {
                        implicit.push((name, span));
                    }
                }
                ModuleItem::GenerateFor(g) => {
                    *next += 1;
                    g.implicit_name = self.implicit_name(s, *next);
                    if g.name.is_none() {
                        implicit.push((g.implicit_name.clone(), g.span));
                    }
                    let seg = g.name.clone().unwrap_or_else(|| g.implicit_name.clone());
                    let kind = ScopeKind::Generate {
                        label: g.name.clone(),
                        ordinal: *next,
                        indexed: true,
                    };
                    let child = self.open(Some(s), kind, Some(seg), None);
                    self.loop_vars.push(g.var.clone());
                    self.fill(child, &mut g.items);
                    self.loop_vars.pop();
                }
                ModuleItem::NestedModule(m) => {
                    let def = self.tree.nested_def(s, &m.name.name);
                    let tree =
                        ScopeTree::build(&def, &m.params, &m.ports, &mut m.items, self.others);
                    self.others.push(tree);
                }
                ModuleItem::CheckerDeclaration(c) => {
                    let def = self.tree.nested_def(s, &c.name.name);
                    let tree = ScopeTree::build(&def, &[], &c.ports, &mut c.items, self.others);
                    self.others.push(tree);
                }
                _ => {}
            }
        }
    }

    /// One conditional construct: `item` is the construct, or a construct
    /// directly nested in it (§27.5), whose blocks take the same number and
    /// name and exclude the outer construct's blocks.
    fn conditional(
        &mut self,
        s: ScopeId,
        item: &mut ModuleItem,
        ordinal: u32,
        name: &str,
        group: u32,
    ) {
        match item {
            ModuleItem::GenerateIf(g) => self.if_arms(s, g, ordinal, name, group),
            ModuleItem::GenerateCase(g) => self.case_arms(s, g, ordinal, name, group),
            _ => {}
        }
    }

    fn if_arms(&mut self, s: ScopeId, g: &mut GenerateIf, ordinal: u32, name: &str, group: u32) {
        g.implicit_name = name.to_string();
        for (bi, (_, branch)) in g.branches.iter_mut().enumerate() {
            if g.branch_direct.get(bi) == Some(&true) {
                self.conditional(s, &mut branch[0], ordinal, name, group);
            } else {
                let label = g.branch_labels.get(bi).cloned().flatten();
                self.arm(s, label, branch, ordinal, name, group);
            }
        }
    }

    fn case_arms(
        &mut self,
        s: ScopeId,
        g: &mut GenerateCase,
        ordinal: u32,
        name: &str,
        group: u32,
    ) {
        g.implicit_name = name.to_string();
        for arm in &mut g.arms {
            if arm.direct {
                self.conditional(s, &mut arm.items[0], ordinal, name, group);
            } else {
                self.arm(s, arm.label.clone(), &mut arm.items, ordinal, name, group);
            }
        }
    }

    fn arm(
        &mut self,
        s: ScopeId,
        label: Option<String>,
        items: &mut [ModuleItem],
        ordinal: u32,
        name: &str,
        group: u32,
    ) {
        let seg = label.clone().unwrap_or_else(|| name.to_string());
        let kind = ScopeKind::Generate {
            label,
            ordinal,
            indexed: false,
        };
        let child = self.open(Some(s), kind, Some(seg), Some(group));
        self.fill(child, items);
    }
}

/// §9.3.4: the named blocks `stmt` declares in the scope around it. An unnamed
/// block opens a scope only if it directly holds a block item declaration.
pub(crate) fn for_each_block_label(stmt: &Statement, f: &mut dyn FnMut(&Identifier)) {
    match &stmt.kind {
        StatementKind::SeqBlock { name: Some(n), .. }
        | StatementKind::ParBlock { name: Some(n), .. } => f(n),
        StatementKind::SeqBlock { name: None, stmts }
        | StatementKind::ParBlock {
            name: None, stmts, ..
        } => {
            let opens_scope = stmts.iter().any(|s| {
                matches!(
                    s.kind,
                    StatementKind::VarDecl { .. } | StatementKind::Typedef(_)
                )
            });
            if !opens_scope {
                stmts.iter().for_each(|s| for_each_block_label(s, f));
            }
        }
        StatementKind::TimingControl { stmt, .. } => for_each_block_label(stmt, f),
        _ => {}
    }
}

/// §6.19: the labels of `dt`'s enums, struct members included. They are names
/// of the scope that declares the type.
pub(crate) fn for_each_enum_member(dt: &DataType, f: &mut dyn FnMut(&Identifier)) {
    match dt {
        DataType::Enum(e) => {
            for m in &e.members {
                let Some((lo, hi)) = &m.range else {
                    f(&m.name);
                    continue;
                };
                // §6.19.2: `A[N]` names A0 to A(N-1), `A[N:M]` AN to AM.
                let eval = |e| crate::elaborate::const_eval_i64_with_params(e, None);
                let Some(lo) = eval(lo) else { continue };
                let hi = eval(hi).unwrap_or(lo);
                for i in lo.min(hi)..=lo.max(hi) {
                    f(&Identifier {
                        name: format!("{}{i}", m.name.name),
                        span: m.name.span,
                    });
                }
            }
        }
        DataType::Struct(s) => {
            for m in &s.members {
                for_each_enum_member(&m.data_type, f);
            }
        }
        _ => {}
    }
}

/// The names `items` use at the positions of §6.10 and §31.9 in the scope
/// they belong to.
fn implicit_net_uses<'i>(items: &'i [ModuleItem], out: &mut Vec<(&'i str, Span)>) {
    fn bare(e: &Expression) -> Option<(&str, Span)> {
        match &e.kind {
            ExprKind::Ident(h)
                if h.root.is_none()
                    && h.path.len() == 1
                    && h.path[0].selects.is_empty()
                    && !h.path[0].name.name.contains("::") =>
            {
                Some((h.path[0].name.name.as_str(), h.path[0].name.span))
            }
            _ => None,
        }
    }
    for item in items {
        match item {
            ModuleItem::ContinuousAssign(c) => {
                out.extend(c.assignments.iter().filter_map(|(l, _)| bare(l)))
            }
            ModuleItem::ModuleInstantiation(m) => {
                for c in m.instances.iter().flat_map(|i| &i.connections) {
                    if let PortConnection::Named { expr: Some(e), .. }
                    | PortConnection::Ordered(Some(e)) = c
                    {
                        out.extend(bare(e));
                    }
                }
            }
            ModuleItem::GateInstantiation(g) => out.extend(
                g.instances
                    .iter()
                    .flat_map(|i| &i.terminals)
                    .filter_map(bare),
            ),
            ModuleItem::SpecifyBlock(b) => {
                for (net, _) in &b.delayed_nets {
                    out.push((net.as_str(), b.span));
                }
            }
            ModuleItem::GenerateRegion(g) => implicit_net_uses(&g.items, out),
            ModuleItem::GenerateIf(g) => {
                for (bi, (_, branch)) in g.branches.iter().enumerate() {
                    if g.branch_direct.get(bi) == Some(&true) {
                        implicit_net_uses(branch, out);
                    }
                }
            }
            ModuleItem::GenerateCase(g) => {
                for arm in g.arms.iter().filter(|a| a.direct) {
                    implicit_net_uses(&arm.items, out);
                }
            }
            _ => {}
        }
    }
}

thread_local! {
    /// The trees of the design being elaborated, by definition path: `top`,
    /// `top.inner` for a nested definition.
    static DESIGN_TREES: std::cell::RefCell<HashMap<String, Rc<ScopeTree>>> =
        std::cell::RefCell::new(HashMap::default());
    /// What binding reads beyond one definition, for a library adopted later.
    static DESIGN_NAMES: std::cell::RefCell<Rc<DesignNames>> =
        std::cell::RefCell::new(Rc::default());
}

/// The tree of a definition of the design elaborated last.
pub fn tree_of(def: &str) -> Option<Rc<ScopeTree>> {
    DESIGN_TREES.with(|t| t.borrow().get(def).cloned())
}

/// The tree of one description that is a definition. Trees of nested
/// definitions go to `others`.
pub(crate) fn build_one(d: &mut Description, others: &mut Vec<ScopeTree>) -> Option<ScopeTree> {
    let (def, params, ports, items) = match d {
        Description::Module(m) => (&m.name, &m.params[..], &m.ports, &mut m.items),
        Description::Interface(m) => (&m.name, &m.params[..], &m.ports, &mut m.items),
        Description::Program(m) => (&m.name, &m.params[..], &m.ports, &mut m.items),
        // A compilation-unit checker elaborates as a definition (§17.2).
        Description::PackageItem(PackageItem::Checker(c)) => {
            (&c.name, &[][..], &c.ports, &mut c.items)
        }
        _ => return None,
    };
    Some(ScopeTree::build(&def.name, params, ports, items, others))
}

/// Build the tree of every definition in `descs` and stamp the constructs.
pub fn build_all(descs: &mut [Description]) -> Vec<ScopeTree> {
    let mut trees = Vec::new();
    for d in descs.iter_mut() {
        if let Some(tree) = build_one(d, &mut trees) {
            trees.push(tree);
        }
    }
    trees
}

/// Build and keep the trees of a design and bind its definitions. A later
/// definition of a name replaces an earlier one, as in the definitions map
/// (§3.3).
pub fn build_design(descs: &mut [Description]) {
    let names = Rc::new(DesignNames::collect(descs));
    let audit = bind::audit_enabled();
    let mut all = Vec::new();
    for i in 0..descs.len() {
        let mut trees = Vec::new();
        if let Some(tree) = build_one(&mut descs[i], &mut trees) {
            trees.push(tree);
            bind::bind_description(&mut descs[i], &trees, &names, audit);
            all.append(&mut trees);
        }
    }
    DESIGN_TREES.with(|t| t.borrow_mut().clear());
    DESIGN_NAMES.with(|n| *n.borrow_mut() = names);
    keep(all);
}

/// Stamp and bind a definition adopted from a library after `build_design`,
/// and keep its tree: a reader of its bindings needs it as for any other.
pub fn adopt(def: &mut crate::SourceDefinition) {
    use crate::SourceDefinition as D;
    let mut trees = Vec::new();
    let names = DESIGN_NAMES.with(|n| n.borrow().clone());
    let audit = bind::audit_enabled();
    macro_rules! adopt_definition {
        ($m:expr) => {{
            let m = Rc::make_mut($m);
            let tree =
                ScopeTree::build(&m.name.name, &m.params, &m.ports, &mut m.items, &mut trees);
            trees.push(tree);
            bind::bind_definition(
                &m.name.name,
                &mut m.params,
                &mut m.ports,
                &mut m.items,
                &trees,
                &names,
                audit,
            );
        }};
    }
    match def {
        D::Module(m) => adopt_definition!(m),
        D::Interface(m) => adopt_definition!(m),
        D::Program(m) => adopt_definition!(m),
        _ => return,
    }
    keep(trees);
}

fn keep(trees: Vec<ScopeTree>) {
    DESIGN_TREES.with(|t| {
        let mut t = t.borrow_mut();
        for tree in trees {
            t.insert(tree.def.clone(), Rc::new(tree));
        }
    });
}
