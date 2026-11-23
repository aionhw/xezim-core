use super::*;

thread_local! {
    /// Recursion-depth guard for re-export resolution in `process_import`
    /// (prevents stack overflow on cyclic `import`/`export` package graphs).
    static IMPORT_DEPTH: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
}

/// The declared name(s) a package item introduces (§26.3 shadow tracking).
/// §24.9 — a `final` block executes like a function once the event loop exits;
/// it may not contain nonblocking assignments. Detect one anywhere in the
/// (possibly nested) statement so elaboration can reject the block.
pub(super) fn stmt_contains_nonblocking(s: &Statement) -> bool {
    match &s.kind {
        StatementKind::NonblockingAssign { .. } => true,
        StatementKind::If {
            then_stmt,
            else_stmt,
            ..
        } => {
            stmt_contains_nonblocking(then_stmt)
                || else_stmt
                    .as_ref()
                    .is_some_and(|e| stmt_contains_nonblocking(e))
        }
        StatementKind::Case { items, .. } => {
            items.iter().any(|it| stmt_contains_nonblocking(&it.stmt))
        }
        StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
            stmts.iter().any(stmt_contains_nonblocking)
        }
        StatementKind::For { body, .. }
        | StatementKind::While { body, .. }
        | StatementKind::DoWhile { body, .. }
        | StatementKind::Forever { body }
        | StatementKind::Repeat { body, .. }
        | StatementKind::Foreach { body, .. } => stmt_contains_nonblocking(body),
        StatementKind::TimingControl { stmt, .. } | StatementKind::Wait { stmt, .. } => {
            stmt_contains_nonblocking(stmt)
        }
        _ => false,
    }
}

/// §26.3: names declared in packages this module does NOT import.
///
/// A package's contents — enum members especially — are registered design-wide
/// under their BARE name, so they are visible to every module whether or not it
/// imported the package. That is only ever too permissive for a REFERENCE, but
/// it is actively wrong for a DECLARATION: a module that never imported the
/// package would get "duplicate declaration" for a perfectly ordinary local
/// variable whose name happens to match a member of some unrelated package
/// elsewhere in the design. No other simulator rejects that, because without an
/// import the package's name is simply not in scope.
///
/// Names collected here let the local declaration win. This can only change
/// behaviour where elaboration previously FAILED, so no working design moves.
pub(super) fn compute_foreign_package_names(
    items: &[ModuleItem],
    defs: &HashMap<String, Definition>,
) -> std::collections::HashSet<String> {
    // Any mention of a package in an import — wildcard or explicit — makes its
    // names legitimately visible here, and a collision with one of those is a
    // real conflict (or, for a wildcard, a legal shadow handled separately).
    let mut imported: std::collections::HashSet<&str> = std::collections::HashSet::default();
    for item in items {
        if let ModuleItem::ImportDeclaration(imp) = item {
            for ii in &imp.items {
                imported.insert(ii.package.name.as_str());
            }
        }
    }
    // Intersected with the module's OWN declarations, exactly as
    // `compute_wildcard_shadowed` is. Keeping only names that are actually
    // declared here matters: the set also suppresses the design-wide
    // registration of these members, and suppressing every unimported
    // package name would break the (over-permissive but relied upon) bare
    // reference to a package member from a module that never imported it.
    // Unlike the wildcard case there is no §26.3 ordering rule to honour —
    // the name was never in scope, so a local declaration wins wherever it
    // appears.
    // No unimported package can collide with a local declaration. Avoid
    // copying the whole module's names for an empty intersection (§26.3).
    if !defs.iter().any(|(name, def)| {
        matches!(def, Definition::Package(_)) && !imported.contains(name.as_str())
    }) {
        return std::collections::HashSet::default();
    }
    let local = collect_local_scope_names(items);
    let mut out = std::collections::HashSet::default();
    for (pkg_name, def) in defs {
        if imported.contains(pkg_name.as_str()) {
            continue;
        }
        if let Definition::Package(pkg) = def {
            for pi in &pkg.items {
                for n in package_item_names(pi) {
                    if local.contains(&n) {
                        out.insert(n);
                    }
                }
            }
        }
    }
    out
}

pub(super) fn package_item_names(pi: &PackageItem) -> Vec<String> {
    match pi {
        PackageItem::Parameter(pd) => match &pd.kind {
            ParameterKind::Data { assignments, .. } => {
                assignments.iter().map(|a| a.name.name.clone()).collect()
            }
            _ => Vec::new(),
        },
        PackageItem::Typedef(td) => {
            let mut v = vec![td.name.name.clone()];
            // §6.19: an enum typedef also introduces each MEMBER name into the
            // enclosing scope, so those are shadowable too (`localparam C = 4`
            // shadowing an imported enum member `C`).
            if let DataType::Enum(en) = &td.data_type {
                for m in &en.members {
                    v.push(m.name.name.clone());
                }
            }
            v
        }
        PackageItem::Function(fd) if fd.name.scopes.is_empty() => vec![fd.name.name.name.clone()],
        PackageItem::Task(td) if td.name.scopes.is_empty() => vec![td.name.name.name.clone()],
        PackageItem::Data(dd) => dd.declarators.iter().map(|d| d.name.name.clone()).collect(),
        PackageItem::Class(cd) => vec![cd.name.name.clone()],
        _ => Vec::new(),
    }
}

/// Names declared LOCALLY in a module scope (§26.3 shadow tracking): params,
/// vars, nets, ports, typedefs, functions, tasks, classes, instances.
pub(super) fn collect_local_scope_names(items: &[ModuleItem]) -> std::collections::HashSet<String> {
    let mut out = std::collections::HashSet::default();
    for item in items {
        match item {
            ModuleItem::DataDeclaration(dd) => {
                for d in &dd.declarators {
                    out.insert(d.name.name.clone());
                }
            }
            ModuleItem::NetDeclaration(nd) => {
                for d in &nd.declarators {
                    out.insert(d.name.name.clone());
                }
            }
            ModuleItem::PortDeclaration(pd) => {
                for d in &pd.declarators {
                    out.insert(d.name.name.clone());
                }
            }
            ModuleItem::ParameterDeclaration(pd) | ModuleItem::LocalparamDeclaration(pd) => {
                if let ParameterKind::Data { assignments, .. } = &pd.kind {
                    for a in assignments {
                        out.insert(a.name.name.clone());
                    }
                }
            }
            ModuleItem::TypedefDeclaration(td) => {
                out.insert(td.name.name.clone());
                if let DataType::Enum(en) = &td.data_type {
                    for m in &en.members {
                        out.insert(m.name.name.clone());
                    }
                }
            }
            ModuleItem::FunctionDeclaration(fd) => {
                out.insert(fd.name.name.name.clone());
            }
            ModuleItem::TaskDeclaration(td) => {
                out.insert(td.name.name.name.clone());
            }
            ModuleItem::ClassDeclaration(cd) => {
                out.insert(cd.name.name.clone());
            }
            ModuleItem::ModuleInstantiation(mi) => {
                for hi in &mi.instances {
                    out.insert(hi.name.name.clone());
                }
            }
            _ => {}
        }
    }
    out
}

/// §26.3: names shadowed by a local declaration over a WILDCARD import. For
/// each `import pkg::*` in `items`, every package name that is ALSO declared
/// locally is a shadow (the local wins). Explicit imports are excluded.
pub(super) fn compute_wildcard_shadowed(
    items: &[ModuleItem],
    params: &[ParameterDeclaration],
    defs: &HashMap<String, Definition>,
) -> std::collections::HashSet<String> {
    // With no wildcard import, there is no imported name to shadow. In
    // particular, explicit imports follow a different conflict rule (§26.3).
    if !items.iter().any(|item| matches!(item,
        ModuleItem::ImportDeclaration(imp) if imp.items.iter().any(|ii| ii.item.is_none())))
    {
        return std::collections::HashSet::default();
    }
    // §26.3 ordering rule: a local declaration only legally SHADOWS a
    // wildcard-imported name if it precedes any use of that name. A name that a
    // procedural/continuous-assign block references BEFORE its local
    // re-declaration is a genuine conflict (error), not a shadow. We approximate
    // "before any use" conservatively as "declared before the first behavioral
    // item": declarations that come after an initial/always/final/assign are NOT
    // treated as shadows, so the duplicate-declaration error still fires for
    // them (matching the CE case where names are used before re-declaration).
    let first_behavior = items.iter().position(|it| {
        matches!(
            it,
            ModuleItem::InitialConstruct(_)
                | ModuleItem::AlwaysConstruct(_)
                | ModuleItem::FinalConstruct(_)
                | ModuleItem::ContinuousAssign(_)
        )
    });
    let decl_items: &[ModuleItem] = match first_behavior {
        Some(idx) => &items[..idx],
        None => items,
    };
    let mut local = collect_local_scope_names(decl_items);
    // Header parameters precede every body item (§23.2, §26.3).
    for pd in params {
        match &pd.kind {
            ParameterKind::Data { assignments, .. } => {
                local.extend(assignments.iter().map(|a| a.name.name.clone()))
            }
            ParameterKind::Type { assignments } => {
                local.extend(assignments.iter().map(|a| a.name.name.clone()))
            }
        }
    }
    let mut out = std::collections::HashSet::default();
    for item in items {
        if let ModuleItem::ImportDeclaration(imp) = item {
            for ii in &imp.items {
                if ii.item.is_some() {
                    continue; // explicit import: not shadowable
                }
                if let Some(Definition::Package(pkg)) = defs.get(&ii.package.name) {
                    for pi in &pkg.items {
                        for n in package_item_names(pi) {
                            if local.contains(&n) {
                                out.insert(n);
                            }
                        }
                    }
                }
            }
        }
    }
    out
}

/// §26.2/§26.3: bind a scope's imported type names into the bare namespace.
///
/// Package typedefs are hoisted into one global bare-name table, so a
/// same-named typedef of an unrelated package can own the bare key. An
/// unqualified reference inside a module resolves to the package that module
/// imports, so the bare keys are re-pointed at the qualified entries before
/// the body is resolved. Only the type tables are rebound: the rest of
/// `process_import` has design-wide effects that must not re-run per instance.
pub(super) fn rebind_imported_typedefs(elab: &mut ElaboratedModule, imports: &[ImportedTypedefs]) {
    let mut changed = false;
    // What the previous scope hid is visible again, unless something has
    // registered the name since.
    for (name, w, t, dims, ew) in std::mem::take(&mut elab.hidden_bare_types) {
        if elab.typedefs.contains_key(&name) || elab.typedef_types.contains_key(&name) {
            continue;
        }
        if let Some(w) = w {
            typedefs_insert_traced(&mut elab.typedefs, "rebind:unhide", name.clone(), w);
            changed = true;
        }
        if let Some(t) = t {
            elab.typedef_types.insert(name.clone(), t);
        }
        if let Some(d) = dims {
            elab.typedef_unpacked_dims.insert(name.clone(), d);
        }
        if let Some(e) = ew {
            elab.typedef_elem_widths.insert(name, e);
        }
    }
    for (name, key) in imports.iter().flat_map(|list| list.iter()) {
        // §26.3: the import binds `name` as a constant of its package. The
        // bare type of that name is another package's, hoisted design-wide,
        // and not visible here: `[N]` with `import p::*` sizes by `p::N`
        // even when a package this scope does not import declares a type N.
        if key.starts_with('=') {
            if elab.typedefs.contains_key(name) || elab.typedef_types.contains_key(name) {
                let hidden = (
                    name.clone(),
                    elab.typedefs.remove(name),
                    elab.typedef_types.remove(name),
                    elab.typedef_unpacked_dims.remove(name),
                    elab.typedef_elem_widths.remove(name),
                );
                changed |= hidden.1.is_some();
                elab.hidden_bare_types.push(hidden);
            }
            continue;
        }
        if let Some(w) = elab.typedefs.get(key).copied()
            && typedefs_insert_traced(&mut elab.typedefs, "rebind:import", name.clone(), w)
                != Some(w)
        {
            changed = true;
        }
        if let Some(t) = elab.typedef_types.get(key).cloned() {
            elab.typedef_types.insert(name.clone(), t);
            // §6.18, §26.3: an import binds the whole type, its shape included;
            // a scalar import clears a displaced shape.
            if let Some(dims) = elab.typedef_unpacked_dims.get(key).cloned() {
                elab.typedef_unpacked_dims.insert(name.clone(), dims);
            } else {
                elab.typedef_unpacked_dims.remove(name);
            }
            if let Some(width) = elab.typedef_elem_widths.get(key).copied() {
                elab.typedef_elem_widths.insert(name.clone(), width);
            } else {
                elab.typedef_elem_widths.remove(name);
            }
        }
    }
    // Keep the const-eval snapshot in step when a width moved.
    if changed {
        type_trace_tls_refresh("rebind_import", &elab.typedefs);
        sync_typedefs_tls(&elab.typedefs);
    }
}

/// Whether package `pkg` declares a parameter or localparam `name`.
pub(super) fn package_declares_constant(
    pkg: &str,
    name: &str,
    definitions: &HashMap<String, Definition>,
) -> bool {
    let Some(Definition::Package(p)) = definitions.get(pkg) else {
        return false;
    };
    p.items.iter().any(|item| {
        matches!(item, PackageItem::Parameter(pd)
            if matches!(&pd.kind, ParameterKind::Data { assignments, .. }
                if assignments.iter().any(|a| a.name.name == name)))
    })
}

/// The types packages and the compilation unit declare: the bare type
/// entries hoisted design-wide.
pub(super) fn design_type_names<'d>(
    definitions: &'d HashMap<String, Definition>,
) -> HashSet<&'d str> {
    let mut out = HashSet::default();
    for d in definitions.values() {
        match d {
            Definition::Typedef(t) => {
                out.insert(t.name.name.as_str());
            }
            Definition::Package(p) => {
                for i in &p.items {
                    if let PackageItem::Typedef(t) = i {
                        out.insert(t.name.name.as_str());
                    }
                }
            }
            _ => {}
        }
    }
    out
}

/// Depth of the import chain `wildcard_typedefs` follows.
const MAX_IMPORT_DEPTH: u32 = 8;

/// The typedefs `import pkg::*` binds: those of `pkg` and, transitively, of
/// the packages it wildcard-imports. §26.6 passes those on only through
/// `export`; following them regardless is an extension. A typedef reached by
/// two paths keeps its last place.
pub(super) fn wildcard_typedefs(
    pkg: &str,
    definitions: &HashMap<String, Definition>,
) -> ImportedTypedefs {
    fn walk(
        pkg: &str,
        definitions: &HashMap<String, Definition>,
        types: &HashSet<&str>,
        depth: u32,
        out: &mut Vec<(String, String)>,
    ) {
        let Some(Definition::Package(p)) = definitions.get(pkg) else {
            return;
        };
        if depth > MAX_IMPORT_DEPTH {
            return;
        }
        for item in &p.items {
            match item {
                PackageItem::Typedef(td) => {
                    out.push((td.name.name.clone(), format!("{pkg}::{}", td.name.name)))
                }
                PackageItem::Parameter(pd) => {
                    if let ParameterKind::Data { assignments, .. } = &pd.kind {
                        // Only a constant some type shares its name with
                        // needs to hide anything (§26.3).
                        for a in assignments
                            .iter()
                            .filter(|a| types.contains(a.name.name.as_str()))
                        {
                            out.push((a.name.name.clone(), format!("={pkg}::{}", a.name.name)));
                        }
                    }
                }
                PackageItem::Import(inner) => {
                    for ii in inner.items.iter().filter(|ii| ii.item.is_none()) {
                        walk(&ii.package.name, definitions, types, depth + 1, out);
                    }
                }
                _ => {}
            }
        }
    }
    let types = design_type_names(definitions);
    let mut all = Vec::new();
    walk(pkg, definitions, &types, 0, &mut all);
    // The key names the pair: keep each one's last place.
    let mut seen = HashSet::default();
    let keep: Vec<bool> = all
        .iter()
        .rev()
        .map(|(_, key)| seen.insert(key.as_str()))
        .collect();
    all.into_iter()
        .zip(keep.into_iter().rev())
        .filter_map(|(pair, keep)| keep.then_some(pair))
        .collect()
}

/// §26.6: does `pkg` EXPORT symbols coming from `src` (by name or `*::*`)?
/// A specific symbol name narrows the check to exports naming that symbol
/// (or wildcard exports).
pub(super) fn package_exports(
    pkg: &crate::ast::module::PackageDeclaration,
    src: &str,
    sym: Option<&str>,
) -> bool {
    pkg.items.iter().any(|pi| {
        if let PackageItem::Export(e) = pi {
            e.items.iter().any(|it| {
                (it.package.name == "*" || it.package.name == src)
                    && match (&it.item, sym) {
                        (None, _) => true,
                        (Some(exp_sym), Some(want)) => exp_sym.name == want,
                        (Some(_), None) => false,
                    }
            })
        } else {
            false
        }
    })
}

/// §26.6 candidacy: bare identifier names REFERENCED in the package's
/// parameter/variable INITIALIZERS — only these become export candidates
/// from a wildcard-exported nested import ("Failed to find" is the
/// reference's error for exporting an unreferenced name). Subroutine bodies
/// are not scanned (initializer references are the overwhelmingly common
/// re-export shape); an explicit `export P::sym` bypasses candidacy.
pub(super) fn package_referenced_names(
    pkg: &crate::ast::module::PackageDeclaration,
) -> crate::hasher::HashSet<String> {
    fn walk_expr(e: &Expression, out: &mut crate::hasher::HashSet<String>) {
        match &e.kind {
            ExprKind::Ident(h) => {
                for seg in &h.path {
                    out.insert(seg.name.name.clone());
                    for sel in &seg.selects {
                        walk_expr(sel, out);
                    }
                }
            }
            ExprKind::Binary { left, right, .. } => {
                walk_expr(left, out);
                walk_expr(right, out);
            }
            ExprKind::Unary { operand, .. } => walk_expr(operand, out),
            ExprKind::Conditional {
                condition,
                then_expr,
                else_expr,
            } => {
                walk_expr(condition, out);
                walk_expr(then_expr, out);
                walk_expr(else_expr, out);
            }
            ExprKind::Paren(inner) => walk_expr(inner, out),
            ExprKind::Concatenation(parts) => {
                for p in parts {
                    walk_expr(p, out);
                }
            }
            ExprKind::Replication { count, exprs } => {
                walk_expr(count, out);
                for p in exprs {
                    walk_expr(p, out);
                }
            }
            ExprKind::Call { func, args } => {
                walk_expr(func, out);
                for a in args {
                    walk_expr(a, out);
                }
            }
            ExprKind::SystemCall { args, .. } => {
                for a in args {
                    walk_expr(a, out);
                }
            }
            ExprKind::Index { expr, index } => {
                walk_expr(expr, out);
                walk_expr(index, out);
            }
            ExprKind::MemberAccess { expr, .. } => walk_expr(expr, out),
            _ => {}
        }
    }
    let mut out = crate::hasher::HashSet::default();
    for pi in &pkg.items {
        match pi {
            PackageItem::Parameter(pd) => {
                if let ParameterKind::Data { assignments, .. } = &pd.kind {
                    for a in assignments {
                        if let Some(init) = &a.init {
                            walk_expr(init, &mut out);
                        }
                    }
                }
            }
            PackageItem::Data(dd) => {
                for d in &dd.declarators {
                    if let Some(init) = &d.init {
                        walk_expr(init, &mut out);
                    }
                }
            }
            _ => {}
        }
    }
    out
}

/// §7.2.1, §26.3: the field layout and member constants (`K.c`) of a
/// struct-typed package parameter `name` imported here, under the bare name
/// the import makes visible. The package registers them only under its own
/// qualified names: a bare registration there reached every scope, so a
/// module's own struct variable `K` read the package's `K.c`.
fn register_bare_struct_param(elab: &mut ElaboratedModule, name: &str, data_type: &DataType) {
    let Some(fields) = flatten_struct_fields(
        data_type,
        &elab.parameters,
        &elab.typedefs,
        &elab.typedef_types,
    ) else {
        return;
    };
    if fields.is_empty() {
        return;
    }
    tls_register_struct_layout(name, &fields);
    if let Some(v) = elab.parameters.get(name).cloned() {
        register_struct_param_members(
            |k, v| {
                elab.set_param(line!(), k, v);
            },
            name,
            &v,
            &fields,
        );
    }
    register_struct_member_elem_widths(name, data_type, &elab.parameters, &elab.typedef_types);
    elab.packed_struct_fields.insert(name.to_string(), fields);
}

pub(super) fn process_import(
    imp: &ImportDeclaration,
    elab: &mut ElaboratedModule,
    defs: &HashMap<String, Definition>,
    inline_only: bool,
) -> Result<(), String> {
    for ii in &imp.items {
        let pkg_name = &ii.package.name;
        if let Some(Definition::Package(pkg)) = defs.get(pkg_name) {
            // §23.3.2, §26.3: an instance's import is inlined into the
            // flattened design, whose bare names are the top-level scope's.
            // A name that scope already declares stays its own; the
            // instance's references are spelled `pkg::name`
            // (`qualify_colliding_package_types`).
            let parent_owned = inline_only
                && ii.item.as_ref().is_some_and(|sym| {
                    elab.parameters.contains_key(&sym.name) || elab.signals.contains_key(&sym.name)
                });
            let mut pkg_overlay = overlay_pkg_params(pkg, elab);
            // §26.3: the initializers this import evaluates read the
            // package's own members, not the `$unit` or local members of the
            // same name that the bare names hold in the importing scope.
            if crate::pkg_scope::any_member_qualified() {
                overlay_pkg_members(pkg, elab, &mut pkg_overlay, |_, nm| {
                    crate::pkg_scope::member_is_qualified(nm)
                });
            }
            let mut imported_params: HashSet<String> = HashSet::default();
            if let Some(sym) = &ii.item {
                let sym_name = &sym.name;
                let mut found = false;
                for pi in &pkg.items {
                    match pi {
                        PackageItem::Parameter(pd) => {
                            if let ParameterKind::Data {
                                data_type,
                                assignments,
                            } = &pd.kind
                            {
                                for assign in assignments {
                                    if &assign.name.name == sym_name {
                                        if parent_owned {
                                            found = true;
                                            break;
                                        }
                                        imported_params.insert(assign.name.name.clone());
                                        if register_visible_array_param(
                                            elab, pkg_name, assign, data_type,
                                        ) {
                                            elab.note_decl_site(
                                                &assign.name.name,
                                                assign.name.span,
                                                &format!("imported from package '{}'", pkg_name),
                                                false,
                                            );
                                            found = true;
                                            continue;
                                        }
                                        let mut width = resolve_type_width(
                                            data_type,
                                            Some(&elab.parameters),
                                            Some(&elab.typedefs),
                                        );
                                        let signed = pkg_param_is_signed(
                                            data_type,
                                            assign.init.as_ref(),
                                            &elab.typedef_types,
                                            &elab.parameters,
                                        );
                                        let is_real = is_type_real_resolved(data_type, &elab.typedef_types);
                                        if matches!(data_type, DataType::Implicit { dimensions, .. } if dimensions.is_empty())
                                        {
                                            // Infer width from sized literal
                                            // initializer (`7'h13` → 7) so the
                                            // parameter doesn't default to 32
                                            // and break concat width math
                                            // (cv32e40p OPCODE_OPIMM = 7'h13).
                                            width = assign
                                                .init
                                                .as_ref()
                                                .and_then(|i| {
                                                    untyped_param_width(i, &elab.parameters)
                                                })
                                                .unwrap_or(32);
                                        }
                                        let v = if let Some(init) = &assign.init {
                                            // §13.4.3 const-function calls.
                                            let subbed_init7;
                                            let init: &Expression = if expr_has_call(init) {
                                                match substitute_const_fn_calls(
                                                    init,Some(&elab.parameters),
                                                    elab,
                                                    0,
                                                )
                                                .filter(|e| !expr_has_call(e))
                                                {
                                                    Some(e) => {
                                                        subbed_init7 = e;
                                                        &subbed_init7
                                                    }
                                                    None => init,
                                                }
                                            } else {
                                                init
                                            };
                                            let mut v = if is_string_data_type(data_type) {
                                                string_param_value(init, &elab.parameters)
                                            } else {
                                                eval_param_init(
                                                    data_type,
                                                    init,
                                                    &elab.parameters,
                                                    &elab.typedef_types,
                                                    width,
                                                )
                                            };
                                            if !v.is_real {
                                                v.is_signed = pkg_param_is_signed(
                                                    data_type,
                                                    Some(init),
                                                    &elab.typedef_types,
                                                    &elab.parameters,
                                                );
                                            }
                                            if is_real {
                                                v = Value::from_f64(v.to_f64());
                                            }
                                            v
                                        } else {
                                            Value::zero(width)
                                        };
                                        // A name that arrived by import is the
                                        // most confusing thing to collide with —
                                        // it is declared nowhere the reader is
                                        // looking. Name the package.
                                        elab.note_decl_site(
                                            &assign.name.name,
                                            assign.name.span,
                                            &format!("imported from package '{}'", pkg_name),
                                            false,
                                        );
                                        alias_pkg_param(elab, pkg_name, &assign.name.name, &v);
                                        register_pkg_param_elem(
                                            elab,
                                            pkg_name,
                                            &assign.name.name,
                                            data_type,
                                        );
                                        param_fallback_set(&assign.name.name, &v);

                                        elab.set_param(
                                            line!(),
                                            assign.name.name.clone(),
                                            v.clone(),
                                        );
                                        signals_insert_traced(
                                            &mut elab.signals,
                                            line!(),
                                            assign.name.name.clone(),
                                            Signal {
                                                is_const: false,
                                                name: assign.name.name.clone().into(),
                                                width,
                                                is_signed: signed,
                                                is_real,
                                                direction: None,
                                                value: v,
                                                type_name: get_type_name(data_type),
                                            },
                                        );
                                        register_bare_struct_param(
                                            elab,
                                            &assign.name.name,
                                            data_type,
                                        );
                                        found = true;
                                        break;
                                    }
                                }
                            }
                        }
                        PackageItem::Nettype(nd) if &nd.name.name == sym_name => {
                            // §26.3 / §6.6.7: accept the explicitly imported
                            // nettype. The shared nettype pre-pass registers
                            // its data type and package-bound resolver for
                            // explicit, wildcard and qualified references.
                            found = true;
                        }
                        PackageItem::Typedef(td) if &td.name.name == sym_name => {
                            process_typedef(td, elab);
                            if matches!(&td.data_type, DataType::Enum(_))
                                && let Some(members) = elab.enum_members.get(&td.name.name)
                            {
                                for (m, _) in members {
                                    if !elab.local_decl_displaces(m) {
                                        imported_params.insert(m.clone());
                                    }
                                }
                            }
                            found = true;
                        }
                        // §26.2.2: an enum MEMBER can be imported by name —
                        // `import ep::BUSY;` makes just that member visible.
                        // Only typedef NAMES matched here before, so a member
                        // import died with "Symbol not found in package".
                        // Register the one member (bare-name constant+signal,
                        // exactly as a wildcard import would) plus the
                        // typedef's ordered member list, which `.name()` /
                        // `.next()` resolve through.
                        PackageItem::Typedef(td) if matches!(&td.data_type, DataType::Enum(_)) => {
                            if let DataType::Enum(et) = &td.data_type {
                                let base_width = et
                                    .base_type
                                    .as_ref()
                                    .map(|bt| {
                                        resolve_type_width(
                                            bt,
                                            Some(&elab.parameters),
                                            Some(&elab.typedefs),
                                        )
                                    })
                                    .unwrap_or(32);
                                let mut next_val: u64 = 0;
                                let mut members_ordered: Vec<(String, u64)> = Vec::new();
                                let wide_vals = (base_width > 64)
                                    .then(|| wide_enum_value_map(et, base_width, &elab.parameters));
                                for member in &et.members {
                                    let (entries, nv) =
                                        expand_enum_member(member, next_val, &elab.parameters);
                                    next_val = nv;
                                    for (nm, val) in entries {
                                        if &nm == sym_name && parent_owned {
                                            found = true;
                                        } else if &nm == sym_name {
                                            let v = wide_vals
                                                .as_ref()
                                                .and_then(|m| m.get(&nm))
                                                .cloned()
                                                .unwrap_or_else(|| {
                                                    Value::from_u64(val, base_width)
                                                });
                                            elab.note_decl_site(
                                                &nm,
                                                member.name.span,
                                                &format!("imported from package '{}'", pkg_name),
                                                false,
                                            );
                                            imported_params.insert(nm.clone());
                                            elab.set_param(line!(), nm.clone(), v.clone());
                                            signals_insert_traced(
                                                &mut elab.signals,
                                                line!(),
                                                nm.clone(),
                                                Signal {
                                                    is_const: false,
                                                    name: nm.clone().into(),
                                                    width: base_width,
                                                    is_signed: false,
                                                    is_real: false,
                                                    direction: None,
                                                    value: v,
                                                    type_name: Some(td.name.name.clone()),
                                                },
                                            );
                                            found = true;
                                        }
                                        members_ordered.push((nm, val));
                                    }
                                }
                                if found {
                                    if !elab.typedefs.contains_key(&td.name.name) {
                                        typedefs_insert_traced(
                                            &mut elab.typedefs,
                                            "insert:import_enum",
                                            td.name.name.clone(),
                                            base_width,
                                        );
                                    }
                                    elab.enum_members
                                        .entry(td.name.name.clone())
                                        .or_insert(members_ordered);
                                }
                            }
                        }
                        PackageItem::Function(fd)
                            if &fd.name.name.name == sym_name
                                && fd.name.scopes.is_empty() =>
                        {
                            elab.functions.insert(fd.name.name.name.clone(), fd.clone());
                            elab.functions
                                .insert(format!("{}::{}", pkg_name, fd.name.name.name), fd.clone());
                            elab.pkg_subr_owner
                                .insert(fd.name.name.name.clone(), pkg_name.clone());
                            elab.func_decl_scope
                                .insert(fd.name.name.name.clone(), pkg_name.clone());
                            found = true;
                        }
                        PackageItem::Task(td)
                            if &td.name.name.name == sym_name
                                && td.name.scopes.is_empty() =>
                        {
                            elab.tasks.insert(td.name.name.name.clone(), td.clone());
                            elab.tasks
                                .insert(format!("{}::{}", pkg_name, td.name.name.name), td.clone());
                            elab.pkg_subr_owner
                                .insert(td.name.name.name.clone(), pkg_name.clone());
                            elab.func_decl_scope
                                .insert(td.name.name.name.clone(), pkg_name.clone());
                            found = true;
                        }
                        PackageItem::DPIImport(di) if &dpi_proto_sv_name(&di.proto) == sym_name => {
                            register_dpi_import(di, elab, Some(pkg_name.as_str()))?;
                            found = true;
                        }
                        PackageItem::DPIExport(e) if &dpi_proto_sv_name(&e.proto) == sym_name => {
                            register_dpi_export(e, elab);
                            found = true;
                        }
                        // §26.3 / §11.13: a let is a package item, so
                        // `import P::my_let;` names it.
                        PackageItem::Let(l) if &l.name.name == sym_name => {
                            elab.lets.insert(l.name.name.clone(), l.clone());
                            found = true;
                        }
                        // §16.8, §16.12, §26.3: so are a named sequence and
                        // property; the import binds the bare name to this
                        // package's declaration.
                        PackageItem::Property(PropertyDeclaration {
                            name,
                            ports,
                            port_defaults,
                            body,
                            ..
                        })
                        | PackageItem::Sequence(SequenceDeclaration {
                            name,
                            ports,
                            port_defaults,
                            body,
                            ..
                        }) if &name.name == sym_name => {
                            elab.sequences.insert(name.name.clone());
                            if let Some(body) = body {
                                elab.property_decls.insert(name.name.clone(), Rc::new(body.clone()));
                                elab.property_params.insert(
                                    name.name.clone(),
                                    ports.iter().map(|p| p.name.clone()).collect(),
                                );
                                register_sva_port_defaults(elab, &name.name, port_defaults);
                            }
                            found = true;
                        }
                        PackageItem::Class(c) if &c.name.name == sym_name => {
                            register_class_enum_members(c, elab);
                            register_class_scoped_typedef_aliases(c, Some(&pkg_name), elab);
                            elab.classes.insert(
                                c.name.name.clone(),
                                std::sync::Arc::new(elaborate_class_with_params(
                                    c,
                                    Some(&elab.parameters),
                                )),
                            );
                            found = true;
                        }
                        PackageItem::Data(dd)
                            if dd
                                .declarators
                                .iter()
                                .any(|decl| &decl.name.name == sym_name) =>
                        {
                            let width = match &dd.data_type {
                                DataType::TypeReference { name, .. } => {
                                    {
                                        // §26.3: a SCOPED `P::T` prefers the qualified key so
                                        // a module-local `typedef ... T` cannot capture it.
                                        let scoped_w = specialized_class_scope_width(name, &elab)
                                            .or_else(|| {
                                                lookup_scoped_type(name, &elab.typedefs).copied()
                                            });
                                        scoped_w
                                            .or_else(|| elab.typedefs.get(&name.name.name).copied())
                                            .unwrap_or_else(|| {
                                                resolve_type_width(
                                                    &dd.data_type,
                                                    Some(&elab.parameters),
                                                    Some(&elab.typedefs),
                                                )
                                            })
                                    }
                                }
                                _ => resolve_type_width(
                                    &dd.data_type,
                                    Some(&elab.parameters),
                                    Some(&elab.typedefs),
                                ),
                            };
                            let is_signed =
                                is_type_signed_resolved(&dd.data_type, &elab.typedef_types);
                            let is_real = is_type_real_resolved(&dd.data_type, &elab.typedef_types);
                            let is_string = matches!(
                                &dd.data_type,
                                DataType::Simple {
                                    kind: SimpleType::String,
                                    ..
                                }
                            );
                            for decl in &dd.declarators {
                                if &decl.name.name == sym_name {
                                    if is_string {
                                        elab.string_signals.insert(decl.name.name.clone());
                                    }
                                    let v = if let Some(init) = &decl.init {
                                        let v = eval_init_for_target(
                                            init,
                                            &elab.parameters,
                                            width,
                                            is_real,
                                        );
                                        if is_real {
                                            v
                                        } else {
                                            package_var_init_value(
                                                v,
                                                &dd.data_type,
                                                &elab.typedef_types,
                                            )
                                        }
                                    } else {
                                        Value::zero(width)
                                    };
                                    signals_insert_traced(
                                        &mut elab.signals,
                                        line!(),
                                        decl.name.name.clone(),
                                        Signal {
                                            is_const: dd.const_kw,
                                            name: decl.name.name.clone().into(),
                                            width,
                                            is_signed,
                                            is_real,
                                            direction: None,
                                            value: v,
                                            type_name: get_type_name(&dd.data_type),
                                        },
                                    );
                                    if matches!(
                                        resolve_typedef_chain(&dd.data_type, &elab.typedef_types),
                                        DataType::Struct(su) if !su.packed
                                    ) {
                                        register_unpacked_aggregate(
                                            elab,
                                            &decl.name.name,
                                            &dd.data_type,
                                        );
                                    }
                                }
                            }
                            found = true;
                        }
                        _ => {}
                    }
                    if found {
                        break;
                    }
                }
                pkg_overlay.retain(|(k, _)| {
                    !imported_params.contains(k)
                        && !imported_params
                            .iter()
                            .any(|p| k.starts_with(&format!("{p}[")) || k.starts_with(&format!("{p}.")))
                });
                restore_overlay(elab, pkg_overlay);
                if !found {
                    // §26.6 re-export: `package P2; import P1::x; export P1::*;`
                    // makes P1's `x` visible to importers of P2. Non-DPI exports
                    // aren't modeled directly, but P2 must `import` what it
                    // re-exports — so resolve the symbol by following P2's own
                    // imports to the source package (one synthetic explicit
                    // import per candidate; depth-guarded against cyclic
                    // re-export).
                    found = IMPORT_DEPTH.with(|d| {
                        if d.get() >= 32 { return false; }
                        d.set(d.get() + 1);
                        let mut ok = false;
                        for pi in &pkg.items {
                            if let PackageItem::Import(inner) = pi {
                                for ii2 in &inner.items {
                                    let provides = match &ii2.item {
                                        Some(s) => s.name == *sym_name, // import Src::sym
                                        None => true,                   // import Src::*
                                    };
                                    if !provides { continue; }
                                    // §26.6 (measured): only exported names are
                                    // re-exposed; a wildcard export covers only
                                    // names the package itself references.
                                    let explicit = pkg.items.iter().any(|pi| {
                                        matches!(pi, PackageItem::Export(e) if e.items.iter().any(|it|
                                            (it.package.name == "*" || it.package.name == ii2.package.name)
                                                && it.item.as_ref().is_some_and(|i| i.name == *sym_name)))
                                    });
                                    // An explicit `import Src::sym` actually imports
                                    // the name (§26.3); a wildcard import only makes
                                    // it a candidate until it is referenced.
                                    let wild_ok = package_exports(pkg, &ii2.package.name, None)
                                        && (ii2.item.is_some()
                                            || package_referenced_names(pkg)
                                                .contains(sym_name.as_str()));
                                    if !explicit && !wild_ok { continue; }
                                    let synth = ImportDeclaration {
                                        items: vec![ImportItem {
                                            package: ii2.package.clone(),
                                            item: Some(Identifier { name: sym_name.clone(), span: Span::dummy() }),
                                            span: Span::dummy(),
                                        }],
                                        span: Span::dummy(),
                                    };
                                    if process_import(&synth, elab, defs, inline_only).is_ok() { ok = true; break; }
                                }
                            }
                            if ok { break; }
                        }
                        d.set(d.get() - 1);
                        ok
                    });
                }
                if !found {
                    return Err(format!(
                        "Symbol '{}' not found in package '{}'",
                        sym_name, pkg_name
                    ));
                }
            } else {
                // Wildcard import
                // §13.4.3: package sizing functions must be registered before
                // the parameters that call them are evaluated.
                for pi in &pkg.items {
                    if let PackageItem::Function(fd) = pi
                        && fd.name.scopes.is_empty()
                    {
                        elab.functions
                            .insert_if_absent_with(fd.name.name.name.clone(), || fd.clone());
                    }
                }
                set_funcs_tls(&elab.functions);
                for pi in &pkg.items {
                    match pi {
                        PackageItem::Parameter(pd) => {
                            if let ParameterKind::Data {
                                data_type,
                                assignments,
                            } = &pd.kind
                            {
                                let base_width = resolve_type_width(
                                    data_type,
                                    Some(&elab.parameters),
                                    Some(&elab.typedefs),
                                );
                                let is_real = is_type_real_resolved(data_type, &elab.typedef_types);
                                let is_implicit = matches!(data_type, DataType::Implicit { dimensions, .. } if dimensions.is_empty());
                                for assign in assignments {
                                    if elab.local_decl_displaces(&assign.name.name) {
                                        continue;
                                    }
                                    imported_params.insert(assign.name.name.clone());
                                    if register_visible_array_param(
                                        elab, pkg_name, assign, data_type,
                                    ) {
                                        elab.note_decl_site(
                                            &assign.name.name,
                                            assign.name.span,
                                            &format!("imported from package '{}'", pkg_name),
                                            false,
                                        );
                                        continue;
                                    }
                                    let signed = pkg_param_is_signed(
                                        data_type,
                                        assign.init.as_ref(),
                                        &elab.typedef_types,
                                        &elab.parameters,
                                    );
                                    // Per-assignment width: implicit-typed
                                    // parameters take the sized-literal
                                    // initializer width when available
                                    // (`7'h13` → 7) instead of forcing 32-bit.
                                    let width = if is_implicit {
                                        assign
                                            .init
                                            .as_ref()
                                            .and_then(|i| untyped_param_width(i, &elab.parameters))
                                            .unwrap_or(32)
                                    } else {
                                        base_width
                                    };
                                    register_packed_array_elem_w(
                                        &assign.name.name,
                                        data_type,
                                        &elab.typedefs,
                                        &elab.parameters,
                                    );
                                    if let Some(init) = &assign.init {
                                        // §13.4.3 const-function calls.
                                        let subbed_init8;
                                        let init: &Expression = if expr_has_call(init) {
                                            match substitute_const_fn_calls(
                                                init,Some(&elab.parameters),
                                                elab,
                                                0,
                                            )
                                            .filter(|e| !expr_has_call(e))
                                            {
                                                Some(e) => {
                                                    subbed_init8 = e;
                                                    &subbed_init8
                                                }
                                                None => init,
                                            }
                                        } else {
                                            init
                                        };
                                        let mut v = eval_param_value(
                                            data_type,
                                            init,
                                            &elab.parameters,
                                            &elab.typedefs,
                                            &elab.typedef_types,
                                            width,
                                        );
                                        if !v.is_real {
                                            v.is_signed = pkg_param_is_signed(
                                                data_type,
                                                Some(init),
                                                &elab.typedef_types,
                                                &elab.parameters,
                                            );
                                        }
                                        if is_real {
                                            v = Value::from_f64(v.to_f64());
                                        }
                                        // A name that arrived by import is the
                                        // most confusing thing to collide with —
                                        // it is declared nowhere the reader is
                                        // looking. Name the package.
                                        elab.note_decl_site(
                                            &assign.name.name,
                                            assign.name.span,
                                            &format!("imported from package '{}'", pkg_name),
                                            false,
                                        );
                                        alias_pkg_param(elab, pkg_name, &assign.name.name, &v);
                                        register_pkg_param_elem(
                                            elab,
                                            pkg_name,
                                            &assign.name.name,
                                            data_type,
                                        );
                                        param_fallback_set(&assign.name.name, &v);

                                        elab.set_param(
                                            line!(),
                                            assign.name.name.clone(),
                                            v.clone(),
                                        );
                                        signals_insert_traced(
                                            &mut elab.signals,
                                            line!(),
                                            assign.name.name.clone(),
                                            Signal {
                                                is_const: false,
                                                name: assign.name.name.clone().into(),
                                                width,
                                                is_signed: signed,
                                                is_real,
                                                direction: None,
                                                value: v,
                                                type_name: get_type_name(data_type),
                                            },
                                        );
                                        // §7.2.1: STRUCT-typed package param —
                                        // register its field layout, or member
                                        // selects (`CDEF.a`) read x at runtime
                                        // and 0 in const context.
                                        register_bare_struct_param(
                                            elab,
                                            &assign.name.name,
                                            data_type,
                                        );
                                    }
                                }
                            }
                        }
                        PackageItem::Typedef(td) if !inline_only => {
                            process_typedef(td, elab);
                            if matches!(&td.data_type, DataType::Enum(_))
                                && let Some(members) = elab.enum_members.get(&td.name.name)
                            {
                                for (m, _) in members {
                                    if !elab.local_decl_displaces(m) {
                                        imported_params.insert(m.clone());
                                    }
                                }
                            }
                        }
                        PackageItem::Function(fd) if fd.name.scopes.is_empty() && !inline_only => {
                            elab.func_decl_scope
                                .insert(fd.name.name.name.clone(), pkg_name.clone());
                            elab.functions.insert(fd.name.name.name.clone(), fd.clone());
                            elab.functions
                                .insert(format!("{}::{}", pkg_name, fd.name.name.name), fd.clone());
                            elab.pkg_subr_owner
                                .insert(fd.name.name.name.clone(), pkg_name.clone());
                        }
                        PackageItem::Task(td) if td.name.scopes.is_empty() && !inline_only => {
                            elab.func_decl_scope
                                .insert(td.name.name.name.clone(), pkg_name.clone());
                            elab.tasks.insert(td.name.name.name.clone(), td.clone());
                            elab.tasks
                                .insert(format!("{}::{}", pkg_name, td.name.name.name), td.clone());
                            elab.pkg_subr_owner
                                .insert(td.name.name.name.clone(), pkg_name.clone());
                        }
                        PackageItem::DPIImport(di) if !inline_only => {
                            register_dpi_import(di, elab, Some(pkg_name.as_str()))?;
                        }
                        PackageItem::DPIExport(e) if !inline_only => {
                            register_dpi_export(e, elab);
                        }
                        // §26.3 / §11.13: a wildcard import makes a package
                        // `let` visible by its bare name, as the explicit
                        // import above does.
                        PackageItem::Let(l) if !inline_only => {
                            elab.lets.insert(l.name.name.clone(), l.clone());
                        }
                        PackageItem::Class(c) if !inline_only => {
                            register_class_enum_members(c, elab);
                            register_class_scoped_typedef_aliases(c, Some(&pkg_name), elab);
                            elab.classes.insert(
                                c.name.name.clone(),
                                std::sync::Arc::new(elaborate_class_with_params(
                                    c,
                                    Some(&elab.parameters),
                                )),
                            );
                        }
                        PackageItem::Data(dd) if !inline_only => {
                            // §26.2: a package net is registered as a net, so a
                            // supply net reads its constant and a wired net
                            // resolves its drivers (#610). The bare name is the
                            // net only where no local declaration displaces it
                            // (§26.3): a module's own `logic w` stays a variable.
                            if let Some(nt) = dd.net_type {
                                for decl in &dd.declarators {
                                    if !elab.local_decl_displaces(&decl.name.name) {
                                        register_net_type(
                                            elab,
                                            &decl.name.name,
                                            nt,
                                            Some(&dd.data_type),
                                        );
                                    }
                                    register_net_type(
                                        elab,
                                        &format!("{}::{}", pkg_name, decl.name.name),
                                        nt,
                                        Some(&dd.data_type),
                                    );
                                }
                            }
                            let width = match &dd.data_type {
                                DataType::TypeReference { name, .. } => {
                                    {
                                        // §26.3: a SCOPED `P::T` prefers the qualified key so
                                        // a module-local `typedef ... T` cannot capture it.
                                        let scoped_w = specialized_class_scope_width(name, &elab)
                                            .or_else(|| {
                                                lookup_scoped_type(name, &elab.typedefs).copied()
                                            });
                                        scoped_w
                                            .or_else(|| elab.typedefs.get(&name.name.name).copied())
                                            .unwrap_or_else(|| {
                                                resolve_type_width(
                                                    &dd.data_type,
                                                    Some(&elab.parameters),
                                                    Some(&elab.typedefs),
                                                )
                                            })
                                    }
                                }
                                _ => resolve_type_width(
                                    &dd.data_type,
                                    Some(&elab.parameters),
                                    Some(&elab.typedefs),
                                ),
                            };
                            let is_signed =
                                is_type_signed_resolved(&dd.data_type, &elab.typedef_types);
                            let is_real = is_type_real_resolved(&dd.data_type, &elab.typedef_types);
                            // Register the packed-struct field layout for an
                            // imported struct variable so a package subroutine's
                            // member write (`s.v = ...` in an imported task)
                            // resolves the field instead of missing the shared
                            // storage (§26.3).
                            let struct_fields = flatten_struct_fields(
                                &dd.data_type,
                                &elab.parameters,
                                &elab.typedefs,
                                &elab.typedef_types,
                            )
                            .filter(|f| !f.is_empty());
                            // An ANONYMOUS enum's members must be registered
                            // BEFORE the initializer evaluates — `enum { A, B }
                            // e = B;` otherwise read B as an unknown (0). Also
                            // key the member list by the VARIABLE name so
                            // `e.first/next` resolve (§6.19.6).
                            register_anonymous_enum_members(&dd.data_type, elab);
                            let anon_members =
                                anon_enum_members_ordered(&dd.data_type, &elab.parameters);
                            let is_string = matches!(
                                &dd.data_type,
                                DataType::Simple {
                                    kind: SimpleType::String,
                                    ..
                                }
                            );
                            for decl in &dd.declarators {
                                let qualified =
                                    if decl.name.name.starts_with(&format!("{}::", pkg_name)) {
                                        decl.name.name.clone()
                                    } else {
                                        format!("{}::{}", pkg_name, decl.name.name)
                                    };
                                if elab.arrays.contains_key(&qualified)
                                    || elab.arrays_2d.contains_key(&qualified)
                                    || elab.arrays_nd.contains_key(&qualified)
                                    || elab.dynamic_arrays.contains(&qualified)
                                    || elab.associative_arrays.contains_key(&qualified)
                                {
                                    continue;
                                }
                                if is_string {
                                    elab.string_signals.insert(decl.name.name.clone());
                                }
                                if let Some(members) = &anon_members {
                                    elab.enum_members
                                        .entry(decl.name.name.clone())
                                        .or_insert_with(|| members.clone());
                                }
                                // Packed multi-D shape (`reg [1:0][7:0] y`):
                                // element selects `P::y[i]` need these maps.
                                if let Some(ew) = packed_inner_elem_width(
                                    &dd.data_type,
                                    &elab.parameters,
                                    &elab.typedefs,
                                ) {
                                    elab.packed_signal_elem_widths
                                        .entry(decl.name.name.clone())
                                        .or_insert(ew);
                                }
                                if let Some(fd) =
                                    packed_full_dims_of(&dd.data_type, &elab.parameters)
                                {
                                    elab.packed_full_dims
                                        .entry(decl.name.name.clone())
                                        .or_insert(fd);
                                }
                                let v = if let Some(init) = &decl.init {
                                    let real =
                                        is_type_real_resolved(&dd.data_type, &elab.typedef_types);
                                    let v =
                                        eval_init_for_target(init, &elab.parameters, width, real);
                                    if real {
                                        v
                                    } else {
                                        package_var_init_value(
                                            v,
                                            &dd.data_type,
                                            &elab.typedef_types,
                                        )
                                    }
                                } else {
                                    Value::zero(width)
                                };
                                let tn = if anon_members.is_some() {
                                    Some(decl.name.name.clone())
                                } else {
                                    get_type_name(&dd.data_type)
                                };
                                signals_insert_traced(
                                    &mut elab.signals,
                                    line!(),
                                    decl.name.name.clone(),
                                    Signal {
                                        is_const: dd.const_kw,
                                        name: decl.name.name.clone().into(),
                                        width,
                                        is_signed,
                                        is_real,
                                        direction: None,
                                        value: v,
                                        type_name: tn,
                                    },
                                );
                                if let Some(fields) = &struct_fields {
                                    tls_register_struct_layout(&decl.name.name, fields);
                                    elab.packed_struct_fields
                                        .insert(decl.name.name.clone(), fields.clone());
                                }
                                if matches!(
                                    resolve_typedef_chain(&dd.data_type, &elab.typedef_types),
                                    DataType::Struct(su) if !su.packed
                                ) {
                                    register_unpacked_aggregate(
                                        elab,
                                        &decl.name.name,
                                        &dd.data_type,
                                    );
                                }
                            }
                        }
                        _ => {}
                    }
                }
                pkg_overlay.retain(|(k, _)| {
                    !imported_params.contains(k)
                        && !imported_params
                            .iter()
                            .any(|p| k.starts_with(&format!("{p}[")) || k.starts_with(&format!("{p}.")))
                });
                restore_overlay(elab, pkg_overlay);
                // §26.2: follow the package's OWN wildcard imports one hop per
                // level (depth-guarded). `import P::*;` where P itself does
                // `import CHIP::*;` is how large testbenches reach core types —
                // the TB never names CHIP directly. Processing only P's own
                // items left every chained name to whatever the global bare
                // table happened to hold, i.e. unprotected against any
                // transient re-binding. The reference tooling accepts the
                // chained reference, so bind the chained packages here too.
                IMPORT_DEPTH.with(|d| -> Result<(), String> {
                    if d.get() >= 8 {
                        return Ok(());
                    }
                    d.set(d.get() + 1);
                    let r = (|| {
                        // §26.6 (measured): a nested import is only re-exposed
                        // when this package EXPORTS it — and a wildcard export
                        // only covers names the package actually REFERENCES.
                        // The unconditional chase accepted designs the
                        // reference rejects ("Failed to find 'base_val'").
                        let referenced = package_referenced_names(pkg);
                        for pi in &pkg.items {
                            let PackageItem::Import(inner) = pi else {
                                continue;
                            };
                            for ii2 in &inner.items {
                                if ii2.item.is_some() {
                                    continue; // explicit member import: already visible via its own processing
                                }
                                if !package_exports(pkg, &ii2.package.name, None) {
                                    continue;
                                }
                                // Wildcard-exported source: import only the
                                // REFERENCED candidates, per symbol.
                                if let Some(Definition::Package(src)) = defs.get(&ii2.package.name)
                                {
                                    for spi in &src.items {
                                        for n in package_item_names(spi) {
                                            if !referenced.contains(&n) {
                                                continue;
                                            }
                                            let synth = ImportDeclaration {
                                                items: vec![ImportItem {
                                                    package: ii2.package.clone(),
                                                    item: Some(Identifier {
                                                        name: n.clone(),
                                                        span: Span::dummy(),
                                                    }),
                                                    span: Span::dummy(),
                                                }],
                                                span: Span::dummy(),
                                            };
                                            let _ = process_import(&synth, elab, defs, inline_only);
                                        }
                                    }
                                }
                            }
                        }
                        Ok(())
                    })();
                    d.set(d.get() - 1);
                    r
                })?;
            }
        } else if pkg_name != "std" {
            return Err(format!(
                "Package '{}' not found{}",
                pkg_name,
                ignored_library_package_note(pkg_name)
            ));
        }
    }
    Ok(())
}
