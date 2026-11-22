use super::*;

/// Construct an unsized integer-literal `Expression` for a genvar value.
/// Used by `substitute_genvar_in_items` to inject a constant in place of
/// the genvar identifier so downstream constant-evaluation, edge-block
/// resolution, and bit-select compilation see the resolved index.
pub(super) fn genvar_const_expr(value: i64) -> Expression {
    // §27.4: the implicit genvar localparam is a signed integer.
    Expression::new(
        ExprKind::Number(NumberLiteral::Integer {
            size: Some(32),
            signed: true,
            base: NumberBase::Decimal,
            value: value.to_string(),
            cached_val: crate::ast::cache::LiteralCache::new(Some((value as u64, 0u64, 32u32))),
        }),
        Span::dummy(),
    )
}

/// §27.4: an iteration's genvar is a localparam of its block; replace bare
/// references to `var` with `value` throughout the items, nested generate
/// constructs included, before unrolling.
pub(super) fn substitute_genvar_in_items(
    items: &[ModuleItem],
    var: &str,
    value: i64,
) -> Vec<ModuleItem> {
    let mut genvar = HashMap::default();
    genvar.insert(var.to_string(), genvar_const_expr(value));
    gen_walk(
        items,
        GenRename {
            genvar,
            ..Default::default()
        },
    )
}

/// §6.19: the labels of every enum type a definition declares something
/// with in its own scope: a header or body parameter, an ANSI port, a port,
/// net, data or nettype declaration, or a typedef (struct members' enums
/// too, via `for_each_enum_member`). Each label is a constant of the scope
/// declaring the type, as the scope tree records them. A generate region
/// (§27.3) opens no scope, so its declarations count; a generate block's
/// (§27.5) are its own, named only from inside it (or by a path through
/// it), so a label declared there leaves the definition's same-named
/// implicit net (§6.10) in place.
pub(super) fn visit_declared_enum_members(
    params: &[ParameterDeclaration],
    ports: &PortList,
    items: &[ModuleItem],
    f: &mut dyn FnMut(&Identifier),
) {
    use crate::scope_tree::for_each_enum_member;
    fn param(p: &ParameterDeclaration, f: &mut dyn FnMut(&Identifier)) {
        if let ParameterKind::Data { data_type, .. } = &p.kind {
            for_each_enum_member(data_type, f);
        }
    }
    fn body(items: &[ModuleItem], f: &mut dyn FnMut(&Identifier)) {
        for item in items {
            match item {
                ModuleItem::TypedefDeclaration(t) => for_each_enum_member(&t.data_type, f),
                ModuleItem::DataDeclaration(d) => for_each_enum_member(&d.data_type, f),
                ModuleItem::NetDeclaration(d) => for_each_enum_member(&d.data_type, f),
                ModuleItem::PortDeclaration(d) => for_each_enum_member(&d.data_type, f),
                ModuleItem::NettypeDeclaration(n) => for_each_enum_member(&n.data_type, f),
                ModuleItem::ParameterDeclaration(p) | ModuleItem::LocalparamDeclaration(p) => {
                    param(p, f)
                }
                ModuleItem::GenerateRegion(g) => body(&g.items, f),
                _ => {}
            }
        }
    }
    params.iter().for_each(|p| param(p, f));
    if let PortList::Ansi(ps) = ports {
        for dt in ps.iter().filter_map(|p| p.data_type.as_ref()) {
            for_each_enum_member(dt, f);
        }
    }
    body(items, f);
}

/// The declarations a generate rename applies to: data, nets, parameters,
/// instances, subroutines, properties, sequences and typedefs (§23.9, §27.5:
/// a generate block's declarations belong to its scope, so `g_a.look` and
/// `g_b.look` are two tasks). `visit` gets the name, the declaration's own
/// id, and its kind.
pub(super) fn visit_renamed_decls(
    items: &[ModuleItem],
    visit: &mut dyn FnMut(&str, Bound, DeclKind),
) {
    for item in items {
        match item {
            ModuleItem::DataDeclaration(dd) => {
                for d in &dd.declarators {
                    visit(&d.name.name, d.decl, DeclKind::Data);
                }
            }
            ModuleItem::NetDeclaration(nd) => {
                for d in &nd.declarators {
                    visit(&d.name.name, d.decl, DeclKind::Net);
                }
            }
            ModuleItem::PortDeclaration(pd) => {
                for d in &pd.declarators {
                    visit(&d.name.name, d.decl, DeclKind::Data);
                }
            }
            ModuleItem::ParameterDeclaration(pd) | ModuleItem::LocalparamDeclaration(pd) => {
                if let ParameterKind::Data { assignments, .. } = &pd.kind {
                    for a in assignments {
                        visit(&a.name.name, a.decl, DeclKind::Param);
                    }
                }
            }
            ModuleItem::ModuleInstantiation(mi) => {
                for hi in &mi.instances {
                    visit(&hi.name.name, hi.decl, DeclKind::Instance);
                    for c in &hi.connections {
                        if let PortConnection::Named { expr: Some(e), .. }
                        | PortConnection::Ordered(Some(e)) = c
                        {
                            visit_block_implicit_nets(e, visit);
                        }
                    }
                }
            }
            // An out-of-block class method (`function C::m`) is the class's,
            // not the block's.
            ModuleItem::FunctionDeclaration(fd) if fd.name.scopes.is_empty() => {
                visit(&fd.name.name.name, fd.decl, DeclKind::Function);
            }
            ModuleItem::TaskDeclaration(td) if td.name.scopes.is_empty() => {
                visit(&td.name.name.name, td.decl, DeclKind::Task);
            }
            // §16.12, §16.8.
            ModuleItem::PropertyDeclaration(p) => visit(&p.name.name, p.decl, DeclKind::Property),
            ModuleItem::SequenceDeclaration(p) => visit(&p.name.name, p.decl, DeclKind::Sequence),
            // §14.3: a clocking block is a declaration of the block, so each
            // copy of a generate block has its own (`g[1].cb`), as a block's
            // data does. A designation (`default clocking cb;`) declares
            // none; it takes the block's key when the block is the block's.
            ModuleItem::ClockingDeclaration(c)
                if c.clock_signal.is_some() || !c.signals.is_empty() || !c.is_default =>
            {
                visit(&c.name.name, c.decl, DeclKind::Clocking)
            }
            // §6.18. A forward declaration keeps its name: it may name a
            // class, and classes keep theirs.
            ModuleItem::TypedefDeclaration(t) if !matches!(t.data_type, DataType::Void(_)) => {
                visit(&t.name.name, t.decl, DeclKind::Typedef)
            }
            // §6.10: an implicit net a block's continuous assignment, port
            // actual or gate terminal declares is the block's, as a declared
            // net is (`g[0].n`).
            ModuleItem::ContinuousAssign(ca) => {
                for (lhs, _) in &ca.assignments {
                    visit_block_implicit_nets(lhs, visit);
                }
            }
            ModuleItem::GateInstantiation(gi) => {
                for t in gi.instances.iter().flat_map(|i| &i.terminals) {
                    visit_block_implicit_nets(t, visit);
                }
            }
            // Nested generate constructs declare their own scope; we recurse
            // and rename names declared in the unconditional bodies, since a
            // nested generate-if may declare a name that the parent's other
            // siblings reference.
            ModuleItem::GenerateRegion(gr) => visit_renamed_decls(&gr.items, visit),
            // §27.6: a nested block's label is a name of the block, so a path
            // through it (`h.V`) takes the block's path like a declaration.
            ModuleItem::GenerateIf(gi) => {
                for (l, d) in gi.branch_labels.iter().zip(&gi.branch_label_decls) {
                    visit_block_label(l.as_deref(), *d, visit);
                }
                for (_cond, branch) in &gi.branches {
                    visit_renamed_decls(branch, visit);
                }
            }
            ModuleItem::GenerateCase(gc) => {
                for arm in &gc.arms {
                    visit_block_label(arm.label.as_deref(), arm.label_decl, visit);
                    visit_renamed_decls(&arm.items, visit);
                }
            }
            // A NESTED generate-for's body decls must also be uniquified by the
            // OUTER iteration's suffix — otherwise an inner `localparam X` (or
            // signal) collides across outer iterations (its inner-loop rename
            // only varies by the inner genvar), so every outer iteration reuses
            // the FIRST-registered value. That silently collapsed
            // `for(a) for(b) localparam Idx = f(a,b)` to `f(0,b)` — the
            // rr_arb_tree binary-tree index bug. The inner loop's own rename
            // then composes a second suffix, giving a distinct name per (a,b).
            ModuleItem::GenerateFor(gf) => {
                visit_block_label(gf.name.as_deref(), gf.name_decl, visit);
                visit_renamed_decls(&gf.items, visit)
            }
            _ => {}
        }
    }
}

/// A generate block's explicit label, when the binder found its declaration.
fn visit_block_label(
    label: Option<&str>,
    decl: Bound,
    visit: &mut dyn FnMut(&str, Bound, DeclKind),
) {
    if let Some(l) = label.filter(|_| decl.as_decl().is_some()) {
        visit(l, decl, DeclKind::Label);
    }
}

/// The implicit nets of a generate block (`Bound::block_implicit_net`) that
/// an implicit-net position names: a bare name, or each member of a
/// concatenation (§6.10).
fn visit_block_implicit_nets(e: &Expression, visit: &mut dyn FnMut(&str, Bound, DeclKind)) {
    match &e.kind {
        ExprKind::Ident(h)
            if h.root.is_none() && h.path.len() == 1 && h.bound.is_block_implicit_net() =>
        {
            visit(&h.path[0].name.name, h.bound, DeclKind::ImplicitNet)
        }
        ExprKind::Concatenation(parts) => parts
            .iter()
            .for_each(|p| visit_block_implicit_nets(p, visit)),
        _ => {}
    }
}

/// §23.9, §27.6: the generate rename in progress: the block's scope and, per
/// renamed declaration, its kind and its spelling so far; or an iteration's
/// genvar substitution.
#[derive(Default)]
pub(super) struct GenRename {
    scope: String,
    renamed: HashMap<DeclId, (DeclKind, String)>,
    /// §27.4: the iteration's genvar and its value, replaced by name.
    genvar: HashMap<String, Expression>,
    /// Whether a process local's type can take a renamed declaration.
    local_kinds: bool,
    /// The kinds the position being rewritten takes, when not all.
    part: std::cell::Cell<Option<fn(DeclKind) -> bool>>,
    /// Whether the position is in a class body.
    class: std::cell::Cell<bool>,
}

/// §18.5: a constraint takes a block's subroutines and types; the solver
/// reads data by its bare name.
pub(crate) fn constraint_takes(k: DeclKind) -> bool {
    matches!(k, DeclKind::Function | DeclKind::Task | DeclKind::Typedef)
}

/// §6.21: a process local's type and dimensions take a block's parameters
/// and types.
pub(crate) fn local_type_takes(k: DeclKind) -> bool {
    matches!(k, DeclKind::Param | DeclKind::Typedef)
}

/// §27.6: `n` of block `scope` is `scope.n`; a name an enclosing block
/// renamed takes the scope before its last segment (`outer[0].x` in
/// `inner[1]` is `outer[0].inner[1].x`), the LRM path.
fn compose_scope(scope: &str, n: &str) -> String {
    match n.rsplit_once('.') {
        Some((outer, base)) => format!("{outer}.{scope}.{base}"),
        None => format!("{scope}.{n}"),
    }
}

/// §3.12.1: whether the generate rename in progress renames a declaration
/// `name` of its block, so the plain name there is the block's.
pub(super) fn gen_rename_declares(name: &str) -> bool {
    GEN_RENAME_TLS.with(|g| {
        g.borrow()
            .iter()
            .any(|f| f.renamed.values().any(|(_, spelled)| spelled == name))
    })
}

/// The key the generate rename in progress gives `name`, bound as `bound`,
/// when it binds to a renamed declaration of a kind both `kinds` and the
/// position take, spelled as that declaration is so far. An instance and a
/// generate block's label keep their declarators' names, so only their
/// references carry the enclosing renames.
pub(super) fn gen_renamed(bound: Bound, name: &str, kinds: fn(DeclKind) -> bool) -> Option<String> {
    let d = bound.as_decl()?;
    GEN_RENAME_TLS.with(|g| {
        let g = g.borrow();
        let f = g.last()?;
        let (kind, spelled) = f.renamed.get(&d)?;
        let takes = kinds(*kind) && f.part.get().is_none_or(|p| p(*kind));
        (takes && (matches!(kind, DeclKind::Instance | DeclKind::Label) || spelled == name))
            .then(|| compose_scope(&f.scope, name))
    })
}

/// Whether `bound` is a nested generate block's label that the rename in
/// progress renames.
pub(super) fn gen_renamed_label(bound: Bound) -> bool {
    bound.as_decl().is_some_and(|d| {
        GEN_RENAME_TLS.with(|g| {
            g.borrow()
                .last()
                .and_then(|f| f.renamed.get(&d))
                .is_some_and(|(k, _)| *k == DeclKind::Label)
        })
    })
}

/// §13.5, §8.3: in a genvar substitution, a name the binding gives another
/// target (a formal, a class member) keeps it.
pub(super) fn genvar_hidden(bound: Bound) -> bool {
    !bound.is_unset()
        && bound != Bound::GENVAR
        && GEN_RENAME_TLS.with(|g| g.borrow().last().is_some_and(|f| !f.genvar.is_empty()))
}

/// Whether a process local's type is being renamed (`local_type_takes`).
pub(super) fn gen_renames_local_types(prefix: &str) -> bool {
    prefix.is_empty() && GEN_RENAME_TLS.with(|g| g.borrow().last().is_some_and(|f| f.local_kinds))
}

/// `f` with the rename taking only the kinds `part` takes.
pub(super) fn with_gen_part<R>(part: fn(DeclKind) -> bool, f: impl FnOnce() -> R) -> R {
    let old = GEN_RENAME_TLS.with(|g| g.borrow().last().map(|t| t.part.replace(Some(part))));
    let out = f();
    if let Some(old) = old {
        GEN_RENAME_TLS.with(|g| g.borrow().last().map(|t| t.part.set(old)));
    }
    out
}

/// A class body under the genvar substitution keeps its member selects
/// as written (§8); the rename pass still folds them.
pub(super) fn gen_in_class() -> bool {
    GEN_RENAME_TLS.with(|g| {
        g.borrow()
            .last()
            .is_some_and(|f| f.class.get() && !f.genvar.is_empty())
    })
}

/// `f` with the genvar map of the substitution in progress.
fn with_genvar<R>(f: impl FnOnce(&HashMap<String, Expression>) -> R) -> R {
    let none = HashMap::default();
    GEN_RENAME_TLS.with(|g| f(g.borrow().last().map_or(&none, |t| &t.genvar)))
}

fn gen_expr(e: &Expression) -> Expression {
    with_genvar(|m| rewrite_expr(e, "", m, &Default::default(), &HashMap::default()))
}

fn gen_stmt(s: &Statement) -> Statement {
    with_genvar(|m| rewrite_stmt(s, "", m, &Default::default(), &HashMap::default()))
}

pub(super) fn gen_type(t: &DataType) -> DataType {
    with_genvar(|m| rewrite_data_type_genvar(t, m, &Default::default(), &HashMap::default()))
}

pub(super) fn gen_dims(d: &[UnpackedDimension]) -> Vec<UnpackedDimension> {
    with_genvar(|m| rewrite_unpacked_dims_genvar(d, m, &Default::default(), &HashMap::default()))
}

fn gen_constraint(c: &ConstraintItem) -> ConstraintItem {
    with_genvar(|m| rewrite_constraint_item(c, "", m, &Default::default(), &HashMap::default()))
}

/// A declarator the rename in progress renames gets its key.
pub(super) fn gen_rename(decl: Bound, name: &mut String) {
    if let Some(k) = gen_renamed(decl, name, |_| true) {
        *name = k;
    }
}

/// Rename the declarations of one generate block (or generate-for
/// iteration) of scope `scope`, and every reference to them from inside the
/// block, to `<scope>.<name>`. A function or task is a declaration of the
/// block like its data (§23.9, §27.6): the declaration becomes `<scope>.f`,
/// and a bare call to `f` from the block — a process, a continuous assign,
/// another of the block's subroutines, a nested block, a `disable` — binds to
/// the innermost enclosing block that declares `f`, else to the module's `f`
/// (§23.8.1 Example 2). The elaborated module keeps one flat subroutine
/// table, so without the rename the last block's `look` answered every
/// block's calls, and a block's `t` was a false duplicate of the module's.
/// Which references are the block's is the binding's decision.
pub(super) fn rename_decls_in_iter(items: &[ModuleItem], scope: &str) -> Vec<ModuleItem> {
    let mut renamed = HashMap::default();
    visit_renamed_decls(items, &mut |n, stamp, kind| {
        debug_assert!(stamp.as_decl().is_some(), "an unbound declaration {n}");
        if let Some(d) = stamp.as_decl() {
            renamed.insert(d, (kind, n.to_string()));
        }
    });
    if renamed.is_empty() {
        return items.to_vec();
    }
    let local_kinds = renamed.values().any(|(k, _)| local_type_takes(*k));
    gen_walk(
        items,
        GenRename {
            scope: scope.to_string(),
            renamed,
            local_kinds,
            ..Default::default()
        },
    )
}

/// `items` through the one generate walker under `frame`.
fn gen_walk(items: &[ModuleItem], frame: GenRename) -> Vec<ModuleItem> {
    GEN_RENAME_TLS.with(|g| g.borrow_mut().push(frame));
    let out = items.iter().map(rename_item_decls).collect();
    GEN_RENAME_TLS.with(|g| g.borrow_mut().pop());
    out
}

fn rename_item_decls(item: &ModuleItem) -> ModuleItem {
    match item {
        ModuleItem::Bind(b) => {
            let mut b = b.clone();
            for path in std::iter::once(&mut b.target_path).chain(b.extra_paths.iter_mut()) {
                for index in path.iter_mut().flat_map(|s| s.selects.iter_mut()) {
                    *index = gen_expr(index);
                }
            }
            ModuleItem::Bind(b)
        }
        ModuleItem::DataDeclaration(dd) => {
            let mut new_dd = dd.clone();
            // The RANGE may reference a renamed sibling localparam
            // (`localparam NL = 3; logic [2**NL-2:0] vec;` in the same
            // block): the declarator and its INIT were rewritten but the
            // data type's dimensions kept the bare name, which then
            // resolved to nothing and the width clamped to 1 bit — every
            // write past bit 0 silently dropped.
            new_dd.data_type = gen_type(&dd.data_type);
            for d in &mut new_dd.declarators {
                gen_rename(d.decl, &mut d.name.name);
                d.dimensions = gen_dims(&d.dimensions);
                d.init = d.init.as_deref().map(|e| Box::new(gen_expr(e)));
            }
            ModuleItem::DataDeclaration(new_dd)
        }
        ModuleItem::NetDeclaration(nd) => {
            let mut new_nd = nd.clone();
            new_nd.data_type = gen_type(&nd.data_type);
            for d in [
                &mut new_nd.delay,
                &mut new_nd.delay_fall,
                &mut new_nd.delay_off,
            ]
            .into_iter()
            .flatten()
            {
                **d = gen_expr(d);
            }
            for d in &mut new_nd.declarators {
                gen_rename(d.decl, &mut d.name.name);
                d.dimensions = gen_dims(&d.dimensions);
                d.init = d.init.as_deref().map(|e| Box::new(gen_expr(e)));
            }
            ModuleItem::NetDeclaration(new_nd)
        }
        ModuleItem::PortDeclaration(pd) => {
            let mut new_pd = pd.clone();
            new_pd.data_type = gen_type(&pd.data_type);
            for d in &mut new_pd.declarators {
                gen_rename(d.decl, &mut d.name.name);
            }
            ModuleItem::PortDeclaration(new_pd)
        }
        ModuleItem::ParameterDeclaration(pd) | ModuleItem::LocalparamDeclaration(pd) => {
            let mut new_pd = pd.clone();
            if let ParameterKind::Data {
                data_type,
                assignments,
            } = &mut new_pd.kind
            {
                // The type and dimensions may name a renamed sibling
                // localparam, as a data declaration's may.
                *data_type = gen_type(data_type);
                for a in assignments {
                    gen_rename(a.decl, &mut a.name.name);
                    a.dimensions = gen_dims(&a.dimensions);
                    a.init = a.init.as_ref().map(gen_expr);
                }
            }
            // Preserve original variant
            match item {
                ModuleItem::ParameterDeclaration(_) => ModuleItem::ParameterDeclaration(new_pd),
                _ => ModuleItem::LocalparamDeclaration(new_pd),
            }
        }
        ModuleItem::ModuleInstantiation(mi) => {
            let mut new_mi = mi.clone();
            // §27.4: a PARAMETER OVERRIDE expression may reference a
            // generate-scope localparam (`#(.W(MYW))` next to
            // `localparam int MYW = ...`). Those declarations are renamed
            // per-iteration, so the override kept the stale bare name,
            // resolved to nothing, and the child elaborated with 0-width
            // parameters. Only port connections were rewritten here.
            if let Some(params) = &mut new_mi.params {
                for pc in params.iter_mut() {
                    let value = match pc {
                        ParamConnection::Ordered(v) => v,
                        ParamConnection::Named { value, .. } => value,
                    };
                    match value {
                        Some(ParamValue::Expr(e)) => *e = gen_expr(e),
                        // A TYPE override's dimensions too (`.T(logic [W-1:0])`).
                        Some(ParamValue::Type(dt)) => *dt = gen_type(dt),
                        None => {}
                    }
                }
            }
            for hi in &mut new_mi.instances {
                // Instance names are NOT suffixed: each generate-for iteration
                // gets a distinct `scope[i].` prefix (§27.6), which both keeps
                // iterations unique and reports the LRM hierarchical path
                // (`genblk4[0].u_ff`, not `u_ff__gf_i_0_`).
                for conn in &mut hi.connections {
                    match conn {
                        PortConnection::Named { expr: Some(e), .. }
                        | PortConnection::Ordered(Some(e)) => *e = gen_expr(e),
                        _ => {}
                    }
                }
            }
            ModuleItem::ModuleInstantiation(new_mi)
        }
        ModuleItem::AlwaysConstruct(ac) => ModuleItem::AlwaysConstruct(AlwaysConstruct {
            kind: ac.kind,
            stmt: gen_stmt(&ac.stmt),
            span: ac.span,
            gen_scope: ac.gen_scope.clone(),
        }),
        ModuleItem::InitialConstruct(ic) => ModuleItem::InitialConstruct(InitialConstruct {
            stmt: gen_stmt(&ic.stmt),
            span: ic.span,
            gen_scope: ic.gen_scope.clone(),
        }),
        // §27.4/§16.14.1: assertion predicates and actions refer to this
        // iteration's declarations, just like initial/always bodies. Keeping
        // the item unchanged bound a shadowed counter to the parent module.
        ModuleItem::AssertionItem(a) => {
            let st = Statement::new(StatementKind::Assertion(a.clone()), a.span);
            let StatementKind::Assertion(a) = gen_stmt(&st).kind else {
                unreachable!()
            };
            ModuleItem::AssertionItem(a)
        }
        // §23.9 / §27.6: a block's function or task is renamed with its data
        // (`g.f`); its return type and formals may read the block's
        // parameters. Inside the body a formal or a local hides a same-named
        // block declaration (§13.3, §13.4), by its binding. The function's
        // own name in the body is its result variable (`f = ...`) or a
        // recursive call, and both name the renamed function.
        ModuleItem::FunctionDeclaration(fd) => {
            let mut new_fd = fd.clone();
            gen_rename(fd.decl, &mut new_fd.name.name.name);
            new_fd.return_type = gen_type(&fd.return_type);
            rename_subroutine_ports(&mut new_fd.ports);
            new_fd.items = rename_subroutine_body(&fd.items, &fd.ports);
            ModuleItem::FunctionDeclaration(new_fd)
        }
        ModuleItem::TaskDeclaration(td) => {
            let mut new_td = td.clone();
            gen_rename(td.decl, &mut new_td.name.name.name);
            rename_subroutine_ports(&mut new_td.ports);
            new_td.items = rename_subroutine_body(&td.items, &td.ports);
            ModuleItem::TaskDeclaration(new_td)
        }
        // §6.18: a block's typedef is the block's (`a.t`); its type reads the
        // block's parameters and types.
        ModuleItem::TypedefDeclaration(td) => {
            let mut new_td = td.clone();
            gen_rename(td.decl, &mut new_td.name.name);
            new_td.data_type = gen_type(&td.data_type);
            new_td.dimensions = gen_dims(&td.dimensions);
            ModuleItem::TypedefDeclaration(new_td)
        }
        ModuleItem::ContinuousAssign(ca) => {
            let mut new_ca = ca.clone();
            new_ca.assignments = ca
                .assignments
                .iter()
                .map(|(l, r)| (gen_expr(l), gen_expr(r)))
                .collect();
            ModuleItem::ContinuousAssign(new_ca)
        }
        // §10.11: the alias operands name the block's OWN nets, so they take
        // the block's rename like any other reference to them. An operand
        // naming a net from OUTSIDE the block keeps its own name.
        ModuleItem::AliasDecl(terms) => {
            let mut new_terms = terms.clone();
            for t in &mut new_terms {
                *t = gen_expr(t);
            }
            ModuleItem::AliasDecl(new_terms)
        }
        ModuleItem::GenerateRegion(gr) => {
            let mut new_gr = gr.clone();
            new_gr.items = gr.items.iter().map(rename_item_decls).collect();
            ModuleItem::GenerateRegion(new_gr)
        }
        ModuleItem::GenerateIf(gi) => {
            let mut new_gi = gi.clone();
            new_gi.branches = gi
                .branches
                .iter()
                .map(|(cond, branch_items)| {
                    let new_cond = cond.as_ref().map(gen_expr);
                    (
                        new_cond,
                        branch_items.iter().map(rename_item_decls).collect(),
                    )
                })
                .collect();
            ModuleItem::GenerateIf(new_gi)
        }
        ModuleItem::GenerateCase(gc) => {
            let new_arms: Vec<GenerateCaseArm> = gc
                .arms
                .iter()
                .map(|arm| GenerateCaseArm {
                    values: arm.values.iter().map(gen_expr).collect(),
                    items: arm.items.iter().map(rename_item_decls).collect(),
                    label: arm.label.clone(),
                    label_decl: arm.label_decl,
                    direct: arm.direct,
                })
                .collect();
            ModuleItem::GenerateCase(GenerateCase {
                selector: gen_expr(&gc.selector),
                arms: new_arms,
                implicit_name: gc.implicit_name.clone(),
                span: gc.span,
            })
        }
        ModuleItem::GenerateFor(gf) => {
            // Inner generate-for: its own iteration loop renames further.
            let mut new_gf = gf.clone();
            new_gf.init = gf.init.as_ref().map(gen_expr);
            new_gf.cond = gen_expr(&gf.cond);
            new_gf.incr = gen_expr(&gf.incr);
            new_gf.items = gf.items.iter().map(rename_item_decls).collect();
            ModuleItem::GenerateFor(new_gf)
        }
        // §27.4: a defparam value may read the iteration's genvar or a
        // parameter of the block.
        ModuleItem::Defparam(pairs) => ModuleItem::Defparam(
            pairs
                .iter()
                .map(|(target, value)| (target.clone(), gen_expr(value)))
                .collect(),
        ),
        ModuleItem::FinalConstruct(_)
        | ModuleItem::GateInstantiation(_)
        | ModuleItem::PropertyDeclaration(_)
        | ModuleItem::SequenceDeclaration(_)
        | ModuleItem::LetDeclaration(_)
        | ModuleItem::CovergroupDeclaration(_)
        | ModuleItem::ClockingDeclaration(_)
        | ModuleItem::ClassDeclaration(_)
        | ModuleItem::OutOfClassConstraint { .. } => {
            let mut out = rename_item_refs(item);
            match &mut out {
                ModuleItem::PropertyDeclaration(p) => gen_rename(p.decl, &mut p.name.name),
                ModuleItem::SequenceDeclaration(p) => gen_rename(p.decl, &mut p.name.name),
                ModuleItem::ClockingDeclaration(c) => gen_rename(c.decl, &mut c.name.name),
                _ => {}
            }
            out
        }
        other => other.clone(),
    }
}

/// §23.9: a final block (§9.2.3), gate (§28), property or sequence (§16),
/// let (§11.13), covergroup (§19), clocking block (§14.3) or class (§8) in a
/// generate block names the block's declarations by their renamed keys and
/// the iteration's genvar by its value (§27.4).
/// Formals keep their names by their bindings (§16.8). A class body gets the
/// definition-relative key; the inliner adds the instance.
fn rename_item_refs(item: &ModuleItem) -> ModuleItem {
    let mut out = item.clone();
    match &mut out {
        ModuleItem::FinalConstruct(fc) => fc.stmt = gen_stmt(&fc.stmt),
        ModuleItem::GateInstantiation(g) => {
            for d in [&mut g.delay, &mut g.delay_fall, &mut g.delay_off].into_iter().flatten() {
                *d = gen_expr(d);
            }
            for t in g.instances.iter_mut().flat_map(|i| i.terminals.iter_mut()) {
                *t = gen_expr(t);
            }
        }
        ModuleItem::PropertyDeclaration(p) => {
            p.items = p.items.iter().map(gen_stmt).collect();
            p.body = p.body.as_ref().map(gen_expr);
        }
        ModuleItem::SequenceDeclaration(p) => {
            p.items = p.items.iter().map(gen_stmt).collect();
            p.body = p.body.as_ref().map(gen_expr);
        }
        ModuleItem::LetDeclaration(l) => {
            if let PortList::Ansi(ps) = &mut l.ports {
                for p in ps.iter_mut() {
                    p.default = p.default.as_ref().map(gen_expr);
                }
            }
            l.expr = gen_expr(&l.expr);
        }
        ModuleItem::CovergroupDeclaration(c) => rename_covergroup_refs(c),
        ModuleItem::ClockingDeclaration(c) => {
            // §14.3: the clocking event is an expression of the block.
            if let Some(clk) = &mut c.clock_signal {
                gen_rename(c.clock_bound, &mut clk.name);
            }
            for d in [&mut c.default_input_skew, &mut c.default_output_skew]
                .into_iter()
                .flatten()
            {
                **d = gen_expr(d);
            }
            for s in &mut c.signals {
                for e in [&mut s.skew, &mut s.bound_to].into_iter().flatten() {
                    *e = gen_expr(e);
                }
                // §14.3: a clockvar without `= expression` is the signal of
                // its name where the block is declared: the copy's own
                // signal when the generate block declares one (`g[1].a`).
                if s.bound_to.is_none() {
                    gen_rename(s.bound, &mut s.name.name);
                }
            }
            c.items = c.items.iter().map(gen_stmt).collect();
        }
        ModuleItem::ClassDeclaration(c) => {
            let in_class = |v| GEN_RENAME_TLS.with(|g| g.borrow().last().map(|t| t.class.set(v)));
            in_class(true);
            rename_class_refs(c);
            in_class(false);
        }
        ModuleItem::OutOfClassConstraint { items, .. } => {
            *items = with_gen_part(constraint_takes, || {
                items.iter().map(gen_constraint).collect()
            });
        }
        _ => {}
    }
    out
}

/// §19.3, §19.8.1: the formals and `item` (§19.5.1.1) hide outer names in
/// the body, by their bindings.
fn rename_covergroup_refs(c: &mut CovergroupDeclaration) {
    rename_subroutine_ports(&mut c.ports);
    rename_subroutine_ports(&mut c.sample_ports);
    c.for_each_expr_mut(&mut |e| *e = gen_expr(e));
    for it in &mut c.items {
        if let CovergroupItem::Coverpoint(p) = it {
            for b in &mut p.bins {
                for e in [&mut b.with_filter, &mut b.iff_guard].into_iter().flatten() {
                    *e = gen_expr(e);
                }
            }
        }
    }
}

/// §8.3: a class body sees the names around its declaration, after its own
/// members and those of its bases, which the binding reports.
fn rename_class_refs(c: &mut ClassDeclaration) {
    let param = |p: &mut ParameterDeclaration| match &mut p.kind {
        ParameterKind::Data {
            data_type,
            assignments,
        } => {
            *data_type = gen_type(data_type);
            for a in assignments {
                a.dimensions = gen_dims(&a.dimensions);
                a.init = a.init.as_ref().map(gen_expr);
            }
        }
        ParameterKind::Type { assignments } => {
            for a in assignments {
                a.init = a.init.as_ref().map(gen_type);
            }
        }
    };
    c.params.iter_mut().for_each(param);
    if let Some(e) = &mut c.extends {
        if e.scopes.is_empty() {
            if let Some(key) = gen_renamed(e.bound, &e.name.name, |k| k == DeclKind::Typedef) {
                e.name.name = key;
            }
        }
        for a in &mut e.args {
            match a {
                ParamValue::Expr(x) => *x = gen_expr(x),
                ParamValue::Type(t) => *t = gen_type(t),
            }
        }
    }
    for item in &mut c.items {
        match item {
            ClassItem::Property(p) => {
                p.data_type = gen_type(&p.data_type);
                for d in &mut p.declarators {
                    d.dimensions = gen_dims(&d.dimensions);
                    d.init = d.init.as_deref().map(|e| Box::new(gen_expr(e)));
                }
            }
            ClassItem::Method(m) => match &mut m.kind {
                ClassMethodKind::Function(f)
                | ClassMethodKind::PureVirtual(f)
                | ClassMethodKind::Extern(f) => {
                    f.return_type = gen_type(&f.return_type);
                    rename_subroutine_ports(&mut f.ports);
                    f.items = rename_subroutine_body(&f.items, &f.ports);
                }
                ClassMethodKind::Task(t) => {
                    rename_subroutine_ports(&mut t.ports);
                    t.items = rename_subroutine_body(&t.items, &t.ports);
                }
            },
            ClassItem::Constraint(k) => {
                let k = std::sync::Arc::make_mut(k);
                k.items = with_gen_part(constraint_takes, || {
                    k.items.iter().map(gen_constraint).collect()
                });
            }
            ClassItem::Typedef(t) => {
                t.data_type = gen_type(&t.data_type);
                t.dimensions = gen_dims(&t.dimensions);
            }
            ClassItem::Parameter(p) => param(p),
            ClassItem::Class(i) => rename_class_refs(i),
            ClassItem::Covergroup(g) => rename_covergroup_refs(g),
            ClassItem::Import(_) | ClassItem::Empty => {}
        }
    }
}

/// The formals of a generate block's subroutine, with their types,
/// dimensions and defaults rewritten through the block's rename (§27.6).
fn rename_subroutine_ports(ports: &mut [FunctionPort]) {
    for p in ports {
        p.data_type = gen_type(&p.data_type);
        p.dimensions = gen_dims(&p.dimensions);
        p.default = p.default.as_ref().map(gen_expr);
    }
}

/// The body of a generate block's subroutine rewritten through the block's
/// rename. The formals and the body's locals are no scopes
/// (`upward_scope_rewrite`, §13.3, §13.4).
fn rename_subroutine_body(
    items: &[Statement],
    ports: &[FunctionPort],
) -> crate::ast::shared_vec::SharedVec<Statement> {
    let mut own: HashSet<String> = ports.iter().map(|p| p.name.name.clone()).collect();
    own.extend(
        stmt_list_declared_names(items)
            .into_iter()
            .map(str::to_string),
    );
    own.extend(stmt_list_typedef_names(items).map(str::to_string));
    let _locals = push_stmt_locals(own);
    items.iter().map(gen_stmt).collect::<Vec<_>>().into()
}

/// Genvar-substitute the expressions inside unpacked dimensions.
pub(super) fn rewrite_unpacked_dims_genvar(
    dims: &[UnpackedDimension],
    port_map: &HashMap<String, Expression>,
    local_names: &std::collections::HashSet<String>,
    interface_map: &HashMap<String, String>,
) -> Vec<UnpackedDimension> {
    rewrite_unpacked_dims_scoped(dims, "", port_map, local_names, interface_map)
}

/// Genvar-substitute the dimension expressions carried by a data type (packed
/// ranges on vectors/typerefs, and recursively into packed-struct members).
pub(super) fn rewrite_data_type_genvar(
    dt: &DataType,
    port_map: &HashMap<String, Expression>,
    local_names: &std::collections::HashSet<String>,
    interface_map: &HashMap<String, String>,
) -> DataType {
    rewrite_data_type_scoped(dt, "", port_map, local_names, interface_map)
}

/// Genvar-substitute the expressions inside packed dimensions (`[left:right]`).
/// A declaration inside a generate-for can size itself from the genvar
/// (`logic [i*8+7:0] byte_i;`); without this the range keeps the bare genvar
/// ident and resolves to a wrong/underflowed width once the loop var is gone.
/// `prefix` scopes instance-local names (the `*_genvar` wrappers pass none).
fn rewrite_packed_dims_scoped(
    dims: &[PackedDimension],
    prefix: &str,
    port_map: &HashMap<String, Expression>,
    local_names: &std::collections::HashSet<String>,
    interface_map: &HashMap<String, String>,
) -> Vec<PackedDimension> {
    dims.iter()
        .map(|d| match d {
            PackedDimension::Range { left, right, span } => PackedDimension::Range {
                left: Box::new(rewrite_expr(
                    left,
                    prefix,
                    port_map,
                    local_names,
                    interface_map,
                )),
                right: Box::new(rewrite_expr(
                    right,
                    prefix,
                    port_map,
                    local_names,
                    interface_map,
                )),
                span: *span,
            },
            other => other.clone(),
        })
        .collect()
}

pub(super) fn rewrite_unpacked_dims_scoped(
    dims: &[UnpackedDimension],
    prefix: &str,
    port_map: &HashMap<String, Expression>,
    local_names: &std::collections::HashSet<String>,
    interface_map: &HashMap<String, String>,
) -> Vec<UnpackedDimension> {
    dims.iter()
        .map(|d| match d {
            UnpackedDimension::Range { left, right, span } => UnpackedDimension::Range {
                left: Box::new(rewrite_expr(
                    left,
                    prefix,
                    port_map,
                    local_names,
                    interface_map,
                )),
                right: Box::new(rewrite_expr(
                    right,
                    prefix,
                    port_map,
                    local_names,
                    interface_map,
                )),
                span: *span,
            },
            UnpackedDimension::Expression { expr, span } => UnpackedDimension::Expression {
                expr: Box::new(rewrite_expr(
                    expr,
                    prefix,
                    port_map,
                    local_names,
                    interface_map,
                )),
                span: *span,
            },
            UnpackedDimension::Queue { max_size, span } => UnpackedDimension::Queue {
                max_size: max_size.as_ref().map(|e| {
                    Box::new(rewrite_expr(
                        e,
                        prefix,
                        port_map,
                        local_names,
                        interface_map,
                    ))
                }),
                span: *span,
            },
            // `[N]` parses as an associative index until `N` is known not to be
            // a type (`normalize_unpacked_dims`). A generate rename maps a
            // sibling localparam or genvar, which cannot be a type, so bind the
            // name now: later the bare `N` resolves to nothing.
            UnpackedDimension::Associative {
                data_type: Some(dt),
                span,
            } if prefix.is_empty() => match dt.as_ref() {
                DataType::TypeReference {
                    name, dimensions, ..
                } if dimensions.is_empty()
                    && name.scopes.is_empty()
                    && (port_map.contains_key(&name.name.name)
                        || gen_renamed(name.bound, &name.name.name, |_| true).is_some()) =>
                {
                    let mut n = make_ident_expr(&name.name.name);
                    if let ExprKind::Ident(h) = &mut n.kind {
                        h.bound = name.bound;
                    }
                    UnpackedDimension::Expression {
                        expr: Box::new(rewrite_expr(
                            &n,
                            prefix,
                            port_map,
                            local_names,
                            interface_map,
                        )),
                        span: *span,
                    }
                }
                _ => d.clone(),
            },
            other => other.clone(),
        })
        .collect()
}

pub(super) fn rewrite_data_type_scoped(
    dt: &DataType,
    prefix: &str,
    port_map: &HashMap<String, Expression>,
    local_names: &std::collections::HashSet<String>,
    interface_map: &HashMap<String, String>,
) -> DataType {
    match dt {
        DataType::IntegerVector {
            kind,
            signing,
            dimensions,
            span,
        } => DataType::IntegerVector {
            kind: *kind,
            signing: *signing,
            dimensions: rewrite_packed_dims_scoped(
                dimensions,
                prefix,
                port_map,
                local_names,
                interface_map,
            ),
            span: *span,
        },
        DataType::TypeReference {
            name,
            dimensions,
            type_args,
            span,
        } => {
            let mut name = name.clone();
            if name.scopes.is_empty() {
                let typedef = |k| k == crate::ast::binding::DeclKind::Typedef;
                if let Some(key) = gen_renamed(name.bound, &name.name.name, typedef) {
                    name.name.name = key;
                }
            }
            DataType::TypeReference {
                name,
                dimensions: rewrite_packed_dims_scoped(
                    dimensions,
                    prefix,
                    port_map,
                    local_names,
                    interface_map,
                ),
                type_args: type_args
                    .iter()
                    .map(|e| rewrite_expr(e, prefix, port_map, local_names, interface_map))
                    .collect(),
                span: *span,
            }
        }
        DataType::Enum(e) => {
            let mut e = e.clone();
            if let Some(b) = &e.base_type {
                e.base_type = Some(Box::new(rewrite_data_type_scoped(
                    b,
                    prefix,
                    port_map,
                    local_names,
                    interface_map,
                )));
            }
            DataType::Enum(e)
        }
        DataType::Implicit {
            signing,
            dimensions,
            span,
        } => DataType::Implicit {
            signing: *signing,
            dimensions: rewrite_packed_dims_scoped(
                dimensions,
                prefix,
                port_map,
                local_names,
                interface_map,
            ),
            span: *span,
        },
        DataType::Struct(su) => {
            let mut new_su = su.clone();
            new_su.dimensions = rewrite_packed_dims_scoped(
                &su.dimensions,
                prefix,
                port_map,
                local_names,
                interface_map,
            );
            new_su.members = su
                .members
                .iter()
                .map(|m| StructMember {
                    rand_qualifier: m.rand_qualifier,
                    data_type: rewrite_data_type_scoped(
                        &m.data_type,
                        prefix,
                        port_map,
                        local_names,
                        interface_map,
                    ),
                    declarators: m
                        .declarators
                        .iter()
                        .map(|sd| StructDeclarator {
                            name: sd.name.clone(),
                            dimensions: rewrite_unpacked_dims_scoped(
                                &sd.dimensions,
                                prefix,
                                port_map,
                                local_names,
                                interface_map,
                            ),
                            init: sd.init.as_ref().map(|e| {
                                rewrite_expr(e, prefix, port_map, local_names, interface_map)
                            }),
                            span: sd.span,
                        })
                        .collect(),
                    span: m.span,
                })
                .collect();
            DataType::Struct(new_su)
        }
        other => other.clone(),
    }
}

/// §23.2.2.1: the parser names a non-ANSI null port (`(a, , b)`) and an
/// unnamed port expression (`(a[1:0])`, `({a, b})`) with a placeholder that
/// no source identifier can spell. Such a port has no name to connect by
/// (`.*`, §23.3.2.4).
pub fn is_unnamed_port_placeholder(name: &str) -> bool {
    name.starts_with("__xz_null_port_") || name.starts_with("__xz_port_expr_")
}

/// Recursively inline all instantiations found in `source_mod`, using `prefix` for signal naming.
/// Flatten module items by resolving generate-if/else and generate regions.
/// Returns all effective items after evaluating generate conditions.
/// §27.6: a generate block's scope name, its label or the construct's implicit
/// name from the scope tree. Prefix every instance name in a flattened generate
/// block with it so hierarchical paths match the LRM (`u_mod.genblk1.u_ff` —
/// what other simulators report), composing naturally for nested blocks (inner
/// blocks flatten first, so the outer prefix lands leftmost).
pub(super) fn gen_scope_name(label: Option<&String>, implicit: &str) -> String {
    match label {
        Some(l) => l.clone(),
        None => {
            debug_assert!(
                !implicit.is_empty(),
                "generate construct without a scope tree"
            );
            implicit.to_string()
        }
    }
}

/// Prepend `scope.` to the instance names of every module/gate instantiation
/// in an already-flattened item list. Declarations, assigns and processes are
/// left alone: xezim's flattening keeps those in the parent namespace.
///
/// Also sets the `gen_scope` field on AlwaysConstruct and InitialConstruct
/// so that %m reports the full hierarchical path including generate block names.
/// `index` is a generate-for block's loop index, recorded on its instances.
pub(super) fn prefix_gen_scope(items: &mut [ModuleItem], scope: &str, index: Option<i64>) {
    // §23.10.1: a `defparam` of the block names its targets from the block,
    // so a path starting at one of the block's instances gets the scope the
    // instance gets below (`u.P` in `gb` is `gb.u.P`). It matched no instance
    // and was dropped.
    let local_instances: Vec<String> =
        if items.iter().any(|it| matches!(it, ModuleItem::Defparam(_))) {
            items
                .iter()
                .filter_map(|it| match it {
                    ModuleItem::ModuleInstantiation(mi) => Some(mi),
                    _ => None,
                })
                .flat_map(|mi| mi.instances.iter().map(|hi| hi.name.name.clone()))
                .collect()
        } else {
            Vec::new()
        };
    for item in items.iter_mut() {
        match item {
            ModuleItem::Defparam(pairs) => {
                for (target, _) in pairs.iter_mut() {
                    prefix_defparam_target(target, scope, &local_instances);
                }
            }
            ModuleItem::Bind(b) => {
                b.gen_scope = if b.gen_scope.is_empty() {
                    scope.to_string()
                } else {
                    format!("{}.{}", scope, b.gen_scope)
                };
            }
            ModuleItem::ModuleInstantiation(inst) => {
                for hi in &mut inst.instances {
                    hi.name.name = format!("{}.{}", scope, hi.name.name);
                    // Inner blocks were expanded first.
                    if let Some(i) = index {
                        hi.gen_indices.insert(0, i);
                    }
                }
            }
            ModuleItem::GateInstantiation(g) => {
                for gi in &mut g.instances {
                    if let Some(n) = &mut gi.name {
                        n.name = format!("{}.{}", scope, n.name);
                    }
                }
            }
            // §21.2.1.7: generate block scope prefix for the %m hierarchy.
            // Inner blocks were expanded first, so the enclosing block's name
            // goes in front of theirs (`g.h`).
            ModuleItem::AlwaysConstruct(ac) => {
                ac.gen_scope = if ac.gen_scope.is_empty() {
                    scope.to_string()
                } else {
                    format!("{}.{}", scope, ac.gen_scope)
                };
            }
            ModuleItem::InitialConstruct(ic) => {
                ic.gen_scope = if ic.gen_scope.is_empty() {
                    scope.to_string()
                } else {
                    format!("{}.{}", scope, ic.gen_scope)
                };
            }
            ModuleItem::AssertionItem(_) => assertion_item_in_gen_scope(item, scope),
            _ => {}
        }
    }
}

/// See `prefix_gen_scope`: put `scope` in front of a `defparam` target whose
/// first component is one of the block's `instances` (by name, or as the
/// scope of an inner block's instance, `inner.u`).
fn prefix_defparam_target(target: &mut Expression, scope: &str, instances: &[String]) {
    match &mut target.kind {
        ExprKind::MemberAccess { expr, .. } | ExprKind::Index { expr, .. } => {
            prefix_defparam_target(expr, scope, instances)
        }
        ExprKind::Ident(h) if h.root.is_none() => {
            let Some(head) = h.path.first() else {
                return;
            };
            let n = head.name.name.as_str();
            let local = instances
                .iter()
                .any(|i| i == n || i.strip_prefix(n).is_some_and(|r| r.starts_with('.')));
            if local {
                let span = head.name.span;
                h.path.insert(
                    0,
                    crate::ast::expr::HierPathSegment {
                        name: Identifier {
                            name: scope.to_string(),
                            span,
                        },
                        selects: Vec::new(),
                    },
                );
            }
        }
        _ => {}
    }
}

/// §16.14 / §27: a concurrent assertion item of a generate block is a
/// process of that block's scope, like its `initial` and `always`
/// constructs: each generated copy (`lp[0]`, `lp[1]`) is its own assertion,
/// `%m` names the block, and a `default disable iff` of the block (§16.15)
/// applies. Hoisted here as an `initial` of the block, the form the
/// elaborator gives every module-level assertion item.
pub(super) fn assertion_item_in_gen_scope(item: &mut ModuleItem, scope: &str) {
    if let ModuleItem::AssertionItem(a) = item {
        let span = a.span;
        let stmt = crate::ast::stmt::Statement::new(
            crate::ast::stmt::StatementKind::Assertion(a.clone()),
            span,
        );
        *item = ModuleItem::InitialConstruct(crate::ast::decl::InitialConstruct {
            stmt,
            span,
            gen_scope: scope.to_string(),
        });
    }
}

/// `format!("{}{}", a, b)` for two strings, without the formatting
/// machinery (instance flattening builds one such name per identifier).
/// A class specialization argument written in an instantiated module, with
/// every reference to that module's parameters folded to its value for THIS
/// instance (`#(int, P)` in `sub #(9)` becomes `#(int, 9)`). A type argument
/// or anything that does not fold is kept as written.
pub(super) fn fold_class_param_arg(
    arg: &Expression,
    params: &HashMap<String, Value>,
) -> Expression {
    if let ExprKind::NamedArg {
        name,
        expr: Some(x),
    } = &arg.kind
    {
        return Expression::new(
            ExprKind::NamedArg {
                name: name.clone(),
                expr: Some(Box::new(fold_class_param_arg(x, params))),
            },
            arg.span,
        );
    }
    let mut reads_param = false;
    for_each_sub_expr(arg, &mut |e| {
        if let ExprKind::Ident(h) = &e.kind {
            if h.path.len() == 1 && params.contains_key(&h.path[0].name.name) {
                reads_param = true;
            }
        }
    });
    if !reads_param {
        return arg.clone();
    }
    match const_eval_i64_with_params(arg, Some(params)) {
        Some(n) => {
            let lit = Expression::new(
                ExprKind::Number(NumberLiteral::Integer {
                    size: None,
                    signed: false,
                    base: NumberBase::Decimal,
                    value: n.unsigned_abs().to_string(),
                    cached_val: crate::ast::cache::LiteralCache::new(None),
                }),
                arg.span,
            );
            if n < 0 {
                Expression::new(
                    ExprKind::Unary {
                        op: crate::ast::expr::UnaryOp::Minus,
                        operand: Box::new(lit),
                    },
                    arg.span,
                )
            } else {
                lit
            }
        }
        None => arg.clone(),
    }
}

pub(super) fn cat2(a: &str, b: &str) -> String {
    let mut s = String::with_capacity(a.len() + b.len());
    s.push_str(a);
    s.push_str(b);
    s
}

/// `collect_effective_items` for callers that only read the result: items
/// outside any generate construct are borrowed instead of cloned (the
/// per-instance parameter fixpoint expands a module body several times and
/// looks only at its parameter and typedef declarations). Generate-produced
/// items are the same owned values the cloning walk yields, in the same
/// order.
/// Do `items`, at any generate depth and in every branch, declare a
/// parameter, a localparam or a typedef?
pub(super) fn items_declare_params_or_typedefs(items: &[ModuleItem]) -> bool {
    items.iter().any(|item| match item {
        ModuleItem::ParameterDeclaration(_)
        | ModuleItem::LocalparamDeclaration(_)
        | ModuleItem::TypedefDeclaration(_) => true,
        ModuleItem::GenerateRegion(gr) => items_declare_params_or_typedefs(&gr.items),
        ModuleItem::GenerateIf(gi) => gi
            .branches
            .iter()
            .any(|(_, b)| items_declare_params_or_typedefs(b)),
        ModuleItem::GenerateCase(gc) => gc
            .arms
            .iter()
            .any(|a| items_declare_params_or_typedefs(&a.items)),
        ModuleItem::GenerateFor(gf) => items_declare_params_or_typedefs(&gf.items),
        _ => false,
    })
}

pub(super) fn collect_effective_items_ref<'a>(
    items: &'a [ModuleItem],
    params: &HashMap<String, Value>,
) -> Vec<std::borrow::Cow<'a, ModuleItem>> {
    fn walk<'a>(
        items: &'a [ModuleItem],
        params: &HashMap<String, Value>,
        out: &mut Vec<std::borrow::Cow<'a, ModuleItem>>,
    ) {
        for item in items {
            match item {
                ModuleItem::GenerateRegion(gr) => walk(&gr.items, params, out),
                ModuleItem::GenerateIf(_)
                | ModuleItem::GenerateCase(_)
                | ModuleItem::GenerateFor(_) => out.extend(
                    collect_effective_items(std::slice::from_ref(item), params)
                        .into_iter()
                        .map(std::borrow::Cow::Owned),
                ),
                other => out.push(std::borrow::Cow::Borrowed(other)),
            }
        }
    }
    let mut out = Vec::new();
    walk(items, params, &mut out);
    out
}

/// §27.5: a generate-if condition or generate-case selector/value in an
/// instantiated module, where `eval_const_expr` would read a user
/// constant-function call as 0 and silently take the else/default branch
/// (every `if (has_neighbor(r, dir))` became a boundary). Calls go through
/// `const_eval_i64_with_params`, which interprets the function body; the
/// result is compared as the same u64 `eval_const_expr` yields.
pub(super) fn eval_generate_const(expr: &Expression, params: &HashMap<String, Value>) -> u64 {
    if expr_has_call(expr) {
        if let Some(v) = const_eval_i64_with_params(expr, Some(params)) {
            return v as u64;
        }
    }
    eval_const_expr(expr, params)
}
