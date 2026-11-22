use super::*;

thread_local! {
    /// §25.5.4 modport expression members, keyed `<interface instance>.<member>`
    /// (instance name as it appears in signal names), valued by the member's
    /// expression rewritten to that instance's signals. Filled per module by
    /// `register_modport_expressions` before its sub-instances are inlined,
    /// consulted by the interface-map arm of `rewrite_expr_impl`.
    pub(super) static MODPORT_EXPR_TLS: std::cell::RefCell<HashMap<String, Expression>> =
        std::cell::RefCell::new(HashMap::default());
    /// Set by the three substitution sites when they return a modport
    /// expression, so the `Index` arm knows its base is a packed
    /// part-select it may fold (an unpacked array SLICE keeps its original
    /// indices, so the fold must never apply to arbitrary bases).
    pub(super) static MODPORT_SUBST_FLAG: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Signal names an interface definition declares (ports, nets, variables),
/// so a modport expression's identifiers can be prefixed with the instance.
fn interface_signal_names(
    idef: &crate::ast::module::InterfaceDeclaration,
) -> std::collections::HashSet<String> {
    let mut out = std::collections::HashSet::new();
    match &idef.ports {
        PortList::Ansi(ps) => {
            for p in ps {
                out.insert(p.name.name.clone());
            }
        }
        PortList::NonAnsi(ids) => {
            for id in ids {
                out.insert(id.name.clone());
            }
        }
        PortList::Empty => {}
    }
    for it in &idef.items {
        match it {
            ModuleItem::PortDeclaration(pd) => {
                for d in &pd.declarators {
                    out.insert(d.name.name.clone());
                }
            }
            ModuleItem::NetDeclaration(nd) => {
                for d in &nd.declarators {
                    out.insert(d.name.name.clone());
                }
            }
            ModuleItem::DataDeclaration(dd) => {
                for d in &dd.declarators {
                    out.insert(d.name.name.clone());
                }
            }
            _ => {}
        }
    }
    out
}

/// Register every modport EXPRESSION member of the interface instances a
/// module declares (`ifc i();` with `modport lo8 (output .b(word[7:0]))`)
/// under `<prefix><inst>.<member>`, each expression rewritten onto the
/// instance's signals. Must run before the module's sub-instances are inlined
/// so a child's `p.b` (through `ifc.lo8 p`) can substitute it.
fn register_modport_expressions(
    items: &[ModuleItem],
    prefix: &str,
    definitions: &HashMap<String, Definition>,
) {
    for it in items {
        let ModuleItem::ModuleInstantiation(inst) = it else {
            continue;
        };
        let Some(Definition::Interface(idef)) = definitions.get(&inst.module_name.name) else {
            continue;
        };
        let has_exprs = idef.items.iter().any(|item| {
            matches!(item, ModuleItem::ModportDeclaration(md)
                if md.items.iter().any(|mp| mp.ports.iter().any(|p| p.expr.is_some())))
        });
        if !has_exprs {
            continue;
        }
        let names = interface_signal_names(idef);
        let empty_pm: HashMap<String, Expression> = HashMap::default();
        let empty_if: HashMap<String, String> = HashMap::default();
        for hi in &inst.instances {
            let inst_name = cat2(&prefix, &hi.name.name);
            let inst_prefix = format!("{}.", inst_name);
            for item in &idef.items {
                let ModuleItem::ModportDeclaration(md) = item else {
                    continue;
                };
                for mp in &md.items {
                    for p in &mp.ports {
                        let Some(e) = &p.expr else { continue };
                        let rewritten = rewrite_expr(e, &inst_prefix, &empty_pm, &names, &empty_if);
                        MODPORT_EXPR_TLS.with(|m| {
                            m.borrow_mut()
                                .insert(format!("{}.{}", inst_name, p.name.name), rewritten);
                        });
                    }
                }
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
/// §26.3: bind the bare names that `def`'s own `import P::*` / `import P::x`
/// items bring into scope, for the const-eval of `def`'s body during inlining.
/// Mirrors what `elaborate_module_with_defs` does for the top module's own
/// imports but runs once per inlined definition so a flattened submodule's
/// localparams and dimensions can name its imported package parameters.
pub(super) fn bind_inlined_import_params(
    elab: &mut ElaboratedModule,
    def: Definition,
    definitions: &HashMap<String, Definition>,
) -> Result<(), String> {
    let mut imports: Vec<(String, Option<String>)> = Vec::new();
    for item in def.items() {
        if let ModuleItem::ImportDeclaration(imp) = item {
            process_import(imp, elab, definitions, true)?;
            for ii in &imp.items {
                let entry = (ii.package.name.clone(), ii.item.as_ref().map(|i| i.name.clone()));
                if !imports.contains(&entry) {
                    imports.push(entry);
                }
            }
        }
    }
    if !imports.is_empty() {
        DEF_IMPORTS_TLS.with(|c| {
            c.borrow_mut()
                .insert(def.name().to_string(), imports.into());
        });
    }
    Ok(())
}

impl BindTargetFilter {
    pub(super) fn collect(
        top_def_name: &str,
        unit_binds: &[BindDirective],
        definitions: &HashMap<String, Definition>,
        checker_decls: &HashMap<String, crate::ast::decl::CheckerDeclaration>,
    ) -> Option<Self> {
        let mut filter = Self {
            target_defs: HashSet::default(),
            target_leaf_names: HashSet::default(),
            can_target_top: false,
            has_non_plain_bind: false,
        };
        let mut any = false;
        let mut note_bind = |b: &BindDirective| {
            any = true;
            if b.target_path.is_empty() {
                filter.target_defs.insert(b.target_module.name.clone());
                filter
                    .target_leaf_names
                    .insert(b.target_module.name.clone());
                if b.target_module.name == top_def_name {
                    filter.can_target_top = true;
                }
            } else {
                for path in std::iter::once(&b.target_path).chain(b.extra_paths.iter()) {
                    if let Some(last) = path.last() {
                        filter.target_leaf_names.insert(last.name.name.clone());
                        if (path.len() == 1 && last.name.name == top_def_name)
                            || (path.len() == 2
                                && path[0].name.name == "$root"
                                && last.name.name == top_def_name)
                        {
                            filter.can_target_top = true;
                        }
                    }
                }
            }
            let bound_name = &b.instantiation.module_name.name;
            let plain = matches!(
                definitions.get(bound_name),
                Some(Definition::Module(_) | Definition::Interface(_) | Definition::Program(_))
            ) && !checker_decls.contains_key(bound_name);
            if !plain {
                filter.has_non_plain_bind = true;
            }
        };
        for b in unit_binds {
            note_bind(b);
        }
        fn walk_items(items: &[ModuleItem], note_bind: &mut impl FnMut(&BindDirective)) {
            for item in items {
                match item {
                    ModuleItem::Bind(b) => note_bind(b),
                    ModuleItem::GenerateRegion(gr) => walk_items(&gr.items, note_bind),
                    ModuleItem::GenerateFor(gf) => walk_items(&gf.items, note_bind),
                    ModuleItem::GenerateIf(gi) => {
                        for (_, branch) in &gi.branches {
                            walk_items(branch, note_bind);
                        }
                    }
                    ModuleItem::GenerateCase(gc) => {
                        for arm in &gc.arms {
                            walk_items(&arm.items, note_bind);
                        }
                    }
                    ModuleItem::NestedModule(nm) => walk_items(&nm.items, note_bind),
                    _ => {}
                }
            }
        }
        for def in definitions.values() {
            match def {
                Definition::Module(m) => walk_items(&m.items, &mut note_bind),
                Definition::Interface(i) => walk_items(&i.items, &mut note_bind),
                Definition::Program(p) => walk_items(&p.items, &mut note_bind),
                _ => {}
            }
        }
        any.then_some(filter)
    }

    pub(super) fn matches(&self, inst_path: &str, def_name: &str) -> bool {
        if inst_path.is_empty() {
            return self.can_target_top;
        }
        if self.target_defs.contains(def_name) {
            return true;
        }
        let leaf = inst_path.rsplit('.').next().unwrap_or(inst_path);
        let base = if leaf.ends_with(']') {
            leaf.split('[').next().unwrap_or(leaf)
        } else {
            leaf
        };
        self.target_leaf_names.contains(base)
    }
}

/// Active typedef / type-parameter overrides of an elaborated instance while
/// its body was inlined, captured for later incremental `bind` passes.
pub(super) struct TargetTypeOverlay {
    typedef_binds: Vec<(String, Option<u32>, Option<DataType>)>,
    type_shapes: Vec<(String, TypedefShapeSave)>,
    unpacked_dims: Vec<(String, Option<Vec<UnpackedDimension>>)>,
}

type AppliedTypeOverlay = TargetTypeOverlay;

pub(super) fn capture_type_overlay(
    elab: &ElaboratedModule,
    saved_type_binds: &[(String, Option<u32>, Option<DataType>)],
    saved_type_shapes: &[(String, TypedefShapeSave)],
    saved_unpacked_dims: &[(String, Option<Vec<UnpackedDimension>>)],
) -> Option<Box<TargetTypeOverlay>> {
    if saved_type_binds.is_empty()
        && saved_type_shapes.is_empty()
        && saved_unpacked_dims.is_empty()
    {
        return None;
    }
    let mut seen = HashSet::default();
    let mut typedef_binds = Vec::with_capacity(saved_type_binds.len());
    for (name, _, _) in saved_type_binds {
        if seen.insert(name.as_str()) {
            typedef_binds.push((
                name.clone(),
                elab.typedefs.get(name).copied(),
                elab.typedef_types.get(name).cloned(),
            ));
        }
    }
    seen.clear();
    let mut type_shapes = Vec::with_capacity(saved_type_shapes.len());
    for (name, _) in saved_type_shapes {
        if seen.insert(name.as_str()) {
            type_shapes.push((name.clone(), tls_typedef_shape(name)));
        }
    }
    seen.clear();
    let mut unpacked_dims = Vec::with_capacity(saved_unpacked_dims.len());
    for (name, _) in saved_unpacked_dims {
        if seen.insert(name.as_str()) {
            unpacked_dims.push((name.clone(), elab.typedef_unpacked_dims.get(name).cloned()));
        }
    }
    Some(Box::new(TargetTypeOverlay {
        typedef_binds,
        type_shapes,
        unpacked_dims,
    }))
}

fn apply_type_overlay(
    elab: &mut ElaboratedModule,
    overlay: &TargetTypeOverlay,
) -> AppliedTypeOverlay {
    let mut prev_binds = Vec::with_capacity(overlay.typedef_binds.len());
    for (name, w, dt) in &overlay.typedef_binds {
        prev_binds.push((
            name.clone(),
            elab.typedefs.get(name).copied(),
            elab.typedef_types.get(name).cloned(),
        ));
        match w {
            Some(width) => {
                elab.typedefs.insert_if_changed(name.clone(), *width);
            }
            None => {
                elab.typedefs.remove(name);
            }
        }
        match dt {
            Some(t) => {
                elab.typedef_types.insert(name.clone(), t.clone());
            }
            None => {
                elab.typedef_types.remove(name);
            }
        }
    }
    let mut prev_shapes = Vec::with_capacity(overlay.type_shapes.len());
    for (name, shape) in &overlay.type_shapes {
        prev_shapes.push((name.clone(), tls_typedef_shape(name)));
        tls_restore_typedef_shape(name, shape.clone());
    }
    let mut prev_dims = Vec::with_capacity(overlay.unpacked_dims.len());
    for (name, dims) in &overlay.unpacked_dims {
        prev_dims.push((name.clone(), elab.typedef_unpacked_dims.get(name).cloned()));
        match dims {
            Some(d) => {
                elab.typedef_unpacked_dims.insert(name.clone(), d.clone());
            }
            None => {
                elab.typedef_unpacked_dims.remove(name);
            }
        }
    }
    AppliedTypeOverlay {
        typedef_binds: prev_binds,
        type_shapes: prev_shapes,
        unpacked_dims: prev_dims,
    }
}

fn restore_type_overlay(elab: &mut ElaboratedModule, prev: AppliedTypeOverlay) {
    for (name, shape) in prev.type_shapes.into_iter().rev() {
        tls_restore_typedef_shape(&name, shape);
    }
    for (name, dims) in prev.unpacked_dims.into_iter().rev() {
        match dims {
            Some(d) => {
                elab.typedef_unpacked_dims.insert(name, d);
            }
            None => {
                elab.typedef_unpacked_dims.remove(&name);
            }
        }
    }
    for (name, w, dt) in prev.typedef_binds.into_iter().rev() {
        match w {
            Some(width) => {
                elab.typedefs.insert_if_changed(name.clone(), width);
            }
            None => {
                elab.typedefs.remove(&name);
            }
        }
        match dt {
            Some(t) => {
                elab.typedef_types.insert(name, t);
            }
            None => {
                elab.typedef_types.remove(&name);
            }
        }
    }
    sync_typedefs_tls(&elab.typedefs);
}

pub(super) fn create_target_implicit_nets(
    elab: &mut ElaboratedModule,
    target_def: Definition,
    inst_prefix: &str,
    mut cands: Vec<String>,
) {
    if cands.is_empty() {
        return;
    }
    let __ta = iprof_now();
    let target_port_names: std::collections::HashSet<String> = match target_def.ports() {
        PortList::Ansi(ps) => ps.iter().map(|p| p.name.name.clone()).collect(),
        PortList::NonAnsi(ps) => ps.iter().map(|p| p.name.clone()).collect(),
        _ => std::collections::HashSet::default(),
    };
    let target_declares: std::collections::HashSet<String> = {
        let mut v = Vec::new();
        visit_renamed_decls(target_def.items(), &mut |n, _, kind| {
            if kind != DeclKind::Label {
                v.push(n.to_string())
            }
        });
        // §6.20: a HEADER parameter (`#(parameter ...)`) is a
        // constant, not a net: `leaf u (.a(VREF));` binds its
        // value. The body items above cover body parameters
        // and localparams but not the header, so such an
        // actual was taken for an undeclared identifier.
        for pd in target_def.params() {
            match &pd.kind {
                ParameterKind::Data { assignments, .. } => {
                    v.extend(assignments.iter().map(|a| a.name.name.clone()))
                }
                ParameterKind::Type { assignments } => {
                    v.extend(assignments.iter().map(|a| a.name.name.clone()))
                }
            }
        }
        // §6.19: an enum's labels are constants of the scope
        // that declares its type, so `.din(st == STREAM)`
        // with a module-local `typedef enum {..., STREAM}`
        // names a declared constant, and §6.10 does not
        // apply. The labels are registered when this
        // module's items are, after this pass, so they need
        // naming here as the parameters above do. Only the
        // module scope's: the actuals checked here are its
        // own (generate-region instances included), and a
        // generate block's label is not visible from them.
        visit_declared_enum_members(
            target_def.params(),
            target_def.ports(),
            target_def.items(),
            &mut |n| v.push(n.name.clone()),
        );
        v.into_iter().collect()
    };
    cands.sort();
    cands.dedup();
    for name in cands {
        // A formal port of the sub-module is bound to the
        // parent's expression, not declared here.
        if target_port_names.contains(&name) {
            continue;
        }
        let scoped = cat2(inst_prefix, &name);
        // §6.10: the implicit net belongs to THIS instance, so
        // the existence test must be SCOPED. A bare
        // `signals.contains_key(name)` skipped creation
        // whenever anything ANYWHERE shared the bare spelling —
        // including an INSTANCE-NAME placeholder, since
        // instantiating `foo c (...)` registers a signal named
        // `c`. A gate library hits this constantly: a cell's
        // `buf IC (clk, dCK);` wants its own implicit `clk`,
        // every design has some other `clk`, and the cell's
        // flops were then never clocked and read x.
        if elab.signals.contains_key(&scoped)
            || elab.parameters.contains_key(&name)
            || elab.parameters.contains_key(&scoped)
            || elab.nets.contains(&scoped)
            || elab.arrays.contains_key(&scoped)
            || elab.arrays_2d.contains_key(&scoped)
            || elab.arrays_nd.contains_key(&scoped)
            || elab.interfaces.contains(&scoped)
        {
            continue;
        }
        // Declared inside the sub-module itself (a net/var
        // declaration or one of its own ports) — the regular
        // inline paths create those.
        if target_declares.contains(&name) {
            continue;
        }
        if crate::implicit_net_warn() {
            crate::elab_diag(format!(
                "[xezim][warning] implicit 1-bit net created for undeclared identifier '{}' \
                 (IEEE 1800-2017 §6.10, instance port connection). Add an explicit declaration to silence.",
                scoped
            ));
        }
        signals_insert_traced(
            &mut elab.signals,
            line!(),
            scoped.clone(),
            Signal {
                is_const: false,
                name: scoped.clone().into(),
                width: 1,
                is_signed: false,
                direction: None,
                value: Value::new(1),
                is_real: false,
                type_name: None,
            },
        );
        elab.implicit_nets.insert(scoped.clone());
        elab.nets.insert(scoped);
    }
    iprof_since("implicit_net_scan", __ta);
}

#[allow(clippy::too_many_arguments)]
pub(super) fn inline_bound_items(
    elab: &mut ElaboratedModule,
    target_path: &str,
    directives: &[BindDirective],
    definitions: &HashMap<String, Definition>,
    cache: &mut InlineCache,
    param_scope: &param_scope::ParamScope,
    bind_state: &mut BindWorklistState,
) -> Result<(), String> {
    let mut scope = bind_state
        .scopes
        .remove(target_path)
        .ok_or_else(|| format!("missing bind target scope '{}'", target_path))?;
    let source_def = *definitions
        .get(&scope.def_name)
        .ok_or_else(|| format!("Bind target definition '{}' not found", scope.def_name))?;
    let prefix = if target_path.is_empty() {
        String::new()
    } else {
        format!("{target_path}.")
    };
    for b in directives {
        if let Some(def) = definitions.get(&b.instantiation.module_name.name) {
            crate::param_override_lists::check_bound_instance(
                &b.instantiation,
                *def,
                source_def.name(),
            )?;
        }
    }
    let chain = {
        let scopes = elab.upward_scopes.borrow();
        let mut rev_chain: Vec<(String, String)> = Vec::new();
        let mut cur = target_path;
        loop {
            let def_name = scopes
                .defs
                .get(cur)
                .map(|d| d.to_string())
                .unwrap_or_else(|| {
                    if cur == target_path {
                        scope.def_name.clone()
                    } else {
                        String::new()
                    }
                });
            let pfx = if cur.is_empty() {
                String::new()
            } else {
                format!("{cur}.")
            };
            rev_chain.push((pfx, def_name));
            if cur.is_empty() {
                break;
            }
            if let Some(parent) = scopes.parents.get(cur) {
                // `parent.path` lives behind `Ref` to `UpwardScopes`; walk via
                // string slice lifetime tied to `scopes`.
                let mut p: &str = &*parent.path;
                while !p.is_empty() && !scopes.defs.contains_key(p) {
                    p = p.rsplit_once('.').map(|(head, _)| head).unwrap_or("");
                }
                cur = p;
            } else {
                let mut p = cur.rsplit_once('.').map(|(head, _)| head).unwrap_or("");
                while !p.is_empty() && !scopes.defs.contains_key(p) {
                    p = p.rsplit_once('.').map(|(head, _)| head).unwrap_or("");
                }
                cur = p;
            }
        }
        rev_chain.reverse();
        rev_chain
    };
    let prev_chain = INLINE_CHAIN_TLS.with(|c| c.replace(chain));
    struct ChainRestore(Vec<(String, String)>);
    impl Drop for ChainRestore {
        fn drop(&mut self) {
            let prev = std::mem::take(&mut self.0);
            INLINE_CHAIN_TLS.with(|c| {
                *c.borrow_mut() = prev;
            });
        }
    }
    let _chain_restore = ChainRestore(prev_chain);

    install_upward_scopes(&elab.upward_scopes);
    let _decl_shapes = install_decl_shapes(source_def);

    let imports = cache.imported_typedefs(elab, source_def, definitions)?;
    rebind_imported_typedefs(elab, &imports);
    if !cache.param_imports_done.contains(source_def.name()) {
        cache
            .param_imports_done
            .insert(source_def.name().to_string());
        bind_inlined_import_params(elab, source_def, definitions)?;
    }

    let applied_overlay = scope
        .type_overlay
        .as_deref()
        .map(|o| apply_type_overlay(elab, o));
    sync_typedefs_tls(&elab.typedefs);

    param_scope.extend_scope_for_binds(directives, definitions, &mut scope.local_params);

    if scope.was_flat_leaf {
        for item in source_def.items() {
            scope.items_end = scope.items_end.max(match item {
                ModuleItem::InitialConstruct(ic) => ic.span.end,
                ModuleItem::AlwaysConstruct(ac) => ac.span.end,
                ModuleItem::AssertionItem(a) => a.span.end,
                ModuleItem::ModuleInstantiation(mi) => mi.span.end,
                _ => 0,
            });
            if let ModuleItem::Defparam(assigns) = item {
                for (lhs, rhs) in assigns {
                    if let Some(path) = defparam_path_segments(lhs) {
                        scope.defparams.push(PendingDefparam {
                            path,
                            value: eval_const_expr_val(rhs, &scope.local_params),
                            span: lhs.span,
                            owner: source_def.name().to_string(),
                        });
                    }
                }
            }
        }
        scope.was_flat_leaf = false;
    }

    let mut bound: Vec<ModuleItem> = directives
        .iter()
        .rev()
        .map(|b| ModuleItem::ModuleInstantiation(b.instantiation.clone()))
        .collect();
    let has_arrays = has_instance_arrays(&bound);
    if has_arrays || scope.local_names.is_none() {
        cache.prepared.enter_instance(&prefix);
        let prepared = prepare_module_items(
            source_def,
            definitions,
            &scope.local_params,
            &elab.typedefs,
            cache,
            param_scope,
        );
        if scope.local_names.is_none() {
            scope.local_names = Some(Rc::clone(&prepared.local_names));
            if !prepared.local_typedefs.is_empty() {
                scope.local_typedefs = Some(Box::new(prepared.local_typedefs.clone()));
            }
        }
        if has_arrays {
            let shapes = ai_scope_shapes(
                &prepared.effective_items,
                source_def,
                &scope.local_params,
                &elab.typedefs,
            );
            ai_expand_instance_arrays(
                &mut bound,
                &shapes,
                definitions,
                &scope.local_params,
                &elab.typedefs,
            );
        }
    }

    let mut cands = Vec::new();
    collect_port_connection_net_candidates(&bound, &mut cands);
    if !cands.is_empty() {
        let local_names = scope
            .local_names
            .get_or_insert_with(|| Rc::new(std::collections::HashSet::default()));
        if cands.iter().any(|n| !local_names.contains(n)) {
            Rc::make_mut(local_names).extend(cands.iter().cloned());
        }
        create_target_implicit_nets(elab, source_def, &prefix, cands);
    }

    register_modport_expressions(&bound, &prefix, definitions);
    let mut sibling_inst_names: std::collections::HashSet<String> = {
        let scopes = elab.upward_scopes.borrow();
        scopes
            .children
            .get(target_path)
            .map(|children| {
                children
                    .iter()
                    .map(|p| UpwardScopes::child_leaf(target_path, p).to_string())
                    .collect()
            })
            .unwrap_or_default()
    };
    for item in &bound {
        if let ModuleItem::ModuleInstantiation(mi) = item {
            for hi in &mi.instances {
                sibling_inst_names.insert(hi.name.name.clone());
            }
        }
    }

    if !prefix.is_empty() {
        for item in &bound {
            if let ModuleItem::ModuleInstantiation(mi) = item
                && definitions
                    .get(&mi.module_name.name)
                    .is_some_and(|d| matches!(d, Definition::Interface(_)))
            {
                for hi in &mi.instances {
                    if elab.interface_port_aliases.iter().any(|(k, v)| {
                        k.starts_with(&prefix)
                            && v.split(|c| c == '.' || c == '[').next()
                                == Some(hi.name.name.as_str())
                    }) {
                        bind_state.needs_full_rebuild = true;
                        break;
                    }
                }
            }
            if bind_state.needs_full_rebuild {
                break;
            }
        }
    }

    let res = if bind_state.needs_full_rebuild {
        Ok(())
    } else {
        let empty_names = std::collections::HashSet::default();
        let parent_local_names: &std::collections::HashSet<String> =
            scope.local_names.as_deref().unwrap_or(&empty_names);
        let parent_local_typedefs: &std::collections::HashSet<String> =
            scope.local_typedefs.as_deref().unwrap_or(&empty_names);
        inline_instantiation_items(
            elab,
            source_def,
            &prefix,
            definitions,
            &mut scope.interface_map,
            &scope.local_params,
            cache,
            &scope.port_map,
            &scope.defparams,
            param_scope,
            parent_local_names,
            parent_local_typedefs,
            &sibling_inst_names,
            &mut scope.items_end,
            &bound,
            Some(bind_state),
        )
    };

    if let Some(prev) = applied_overlay {
        restore_type_overlay(elab, prev);
    } else {
        sync_typedefs_tls(&elab.typedefs);
    }
    bind_state.scopes.insert(target_path.to_string(), scope);
    res
}

#[allow(clippy::too_many_arguments)]
pub(super) fn inline_module_items(
    elab: &mut ElaboratedModule,
    source_def: Definition,
    prefix: &str,
    definitions: &HashMap<String, Definition>,
    interface_map: &mut HashMap<String, String>,
    local_params: &HashMap<String, Value>,
    cache: &mut InlineCache,
    // §23.3.3: THIS instance's formal->actual substitution. The module's own
    // statements are rewritten through it (via `RewriteCtx`), so a nested
    // instantiation's connection ACTUALS must be too: without it
    // `mid(input p); leaf u(.a(p));` connected `leaf.a` to the formal's own
    // signal (`mid_inst.p`) instead of the parent net, and a driver reaching
    // the port from inside — a child's output tied to it, which is what a
    // bound interface's output does — landed on the formal only and never
    // propagated up to the actual (the parent read `z`).
    parent_port_map: &HashMap<String, Expression>,
    // §23.10.1 pending `defparam` overrides targeting instances in THIS scope:
    // The value was already evaluated in the scope that declared the
    // defparam. Path[0] is a child instance name.
    pending_defparams: &[PendingDefparam],
    // §23.10/§26.3: the package, `$unit` and top parameters, from which a
    // child's scope takes the entries its definition can name.
    param_scope: &param_scope::ParamScope,
    mut bind_state: Option<&mut BindWorklistState>,
) -> Result<ModuleInlineMeta, String> {
    // Bind this module's imported type names BEFORE its body is prepared or
    // resolved. The top-module path re-runs its imports
    // (`elaborate_module_with_defs`); the inlined-instance path never processed
    // imports at all, so an unqualified `T [1:0] s;` in a sub-module silently
    // took whichever package last hoisted that bare name.
    let _oom_body = crate::oom_trace::definition(
        source_def,
        "prepare module body",
        prefix.trim_end_matches('.'),
    );
    let imports = cache.imported_typedefs(elab, source_def, definitions)?;
    rebind_imported_typedefs(elab, &imports);
    // §26.3: fold a flattened submodule's OWN imports (bare params, public
    // functions/tasks) into the top-level elaboration once per definition.
    // `elaborate_module_with_defs` processes only the top module's imports;
    // an inlined instance's `import P::*` never reached `process_import`, so
    // its own `localparam X = PW` and dimensions (unpacked `[N]`) read the
    // bare imported name as 0. Type imports are already bound above.
    if !cache.param_imports_done.contains(source_def.name()) {
        cache.param_imports_done.insert(source_def.name().to_string());
        bind_inlined_import_params(elab, source_def, definitions)?;
    }
    INLINE_CHAIN_TLS.with(|c| {
        c.borrow_mut()
            .push((prefix.to_string(), source_def.name().to_string()))
    });
    struct ChainPop;
    impl Drop for ChainPop {
        fn drop(&mut self) {
            INLINE_CHAIN_TLS.with(|c| {
                c.borrow_mut().pop();
            });
        }
    }
    let _chain_pop = ChainPop;
    // §23.8: this definition's declared scopes, and the tree every upward
    // name in its body is resolved against (`upward_scope_rewrite`).
    install_upward_scopes(&elab.upward_scopes);
    {
        let mut scopes = elab.upward_scopes.borrow_mut();
        scopes.declare(&source_def);
        if prefix.is_empty() {
            scopes.set_top(source_def.name());
            scopes.packages.extend(elab.packages.iter().cloned());
        }
    }
    // This body's signals and processes were already elaborated by its
    // caller. A flat leaf has no hierarchy work left, so avoid preparing a
    // second owned copy of its items. Binds and generate constructs still
    // need the complete preparation and active-scope handling below.
    let has_hierarchy_work = source_def.items().iter().any(|item| {
        matches!(
            item,
            ModuleItem::ModuleInstantiation(_)
                | ModuleItem::Bind(_)
                | ModuleItem::GenerateRegion(_)
                | ModuleItem::GenerateIf(_)
                | ModuleItem::GenerateCase(_)
                | ModuleItem::GenerateFor(_)
        )
    }) || elab
        .resolved_binds
        .get(prefix.trim_end_matches('.'))
        .is_some_and(|binds| !binds.is_empty());
    if !has_hierarchy_work {
        for pd in source_def
            .params()
            .iter()
            .chain(item_param_decls(source_def.items()))
        {
            if let ParameterKind::Data { assignments, .. } = &pd.kind {
                for a in assignments {
                    elab.declared_parameters
                        .insert(format!("{}{}", prefix, a.name.name));
                }
            }
        }
        return Ok(ModuleInlineMeta {
            items_end: 0,
            was_flat_leaf: true,
            local_names: None,
            local_typedefs: None,
            defparams: Vec::new(),
        });
    }
    // §20.6.2/§20.7: this body's declarations answer `$bits` and the array
    // queries in its own constant expressions (generate conditions, widths,
    // the parameter overrides it passes to its children).
    let _decl_shapes = install_decl_shapes(source_def);
    cache.prepared.enter_instance(prefix);
    let mut prepared_source = prepare_module_items(
        source_def,
        definitions,
        local_params,
        &elab.typedefs,
        cache,
        param_scope,
    );
    for (name, bounds) in &prepared_source.interface_array_bounds {
        elab.unpacked_decl_dims.insert(cat2(prefix, name), vec![*bounds]);
    }
    // Keep declaration ownership after flattening (§26.3, §21.7.2.3).
    // Imported lookup aliases never enter this set.
    for pd in source_def.params().iter().chain(
        prepared_source.effective_items.iter().filter_map(|item| match item {
            ModuleItem::ParameterDeclaration(pd) | ModuleItem::LocalparamDeclaration(pd) => Some(pd),
            _ => None,
        }),
    ) {
        if let ParameterKind::Data { assignments, .. } = &pd.kind {
            for a in assignments {
                elab.declared_parameters.insert(format!("{}{}", prefix, a.name.name));
            }
        }
    }
    // §23.11/§27: only active generate branches contribute declarations.
    for item in &prepared_source.effective_items {
        if let ModuleItem::Bind(b) = item {
            elab.bind_sites.push((
                format!("{}{}", prefix, b.gen_scope)
                    .trim_end_matches('.')
                    .to_string(),
                b.clone(),
            ));
        }
    }
    if let Some(binds) = elab.resolved_binds.get(prefix.trim_end_matches('.')) {
        for b in binds {
            if let Some(def) = definitions.get(&b.instantiation.module_name.name) {
                crate::param_override_lists::check_bound_instance(
                    &b.instantiation,
                    *def,
                    source_def.name(),
                )?;
            }
        }
        let prepared = Rc::make_mut(&mut prepared_source);
        let mut bound: Vec<ModuleItem> = binds
            .iter()
            .rev()
            .map(|b| ModuleItem::ModuleInstantiation(b.instantiation.clone()))
            .collect();
        // §23.11, §23.3.2: a bound array of instances is expanded like one
        // written here; the body's items were expanded before the binds were
        // known, so the array's elements were never built.
        if has_instance_arrays(&bound) {
            let shapes = ai_scope_shapes(
                &prepared.effective_items,
                source_def,
                local_params,
                &elab.typedefs,
            );
            ai_expand_instance_arrays(
                &mut bound,
                &shapes,
                definitions,
                local_params,
                &elab.typedefs,
            );
        }
        // §23.11/§6.10: an undeclared name in a bound instance's connection
        // is an implicit net of this (the target) scope, as it is for an
        // instance written here, never an object of the bind's scope.
        let mut cands = Vec::new();
        collect_port_connection_net_candidates(&bound, &mut cands);
        if !cands.is_empty() {
            Rc::make_mut(&mut prepared.local_names).extend(cands);
        }
        prepared.effective_items.extend(bound);
    }
    // §23.10: names of THIS module's own sub-instances. A port connection
    // naming a SIBLING instance (`h_leaf lf(li.mp);` where `li` is the same
    // module's interface instance) is not in `local_names`, so the inlining
    // rewrite leaves it unprefixed — the connection then bound the port to a
    // phantom top-level name and, e.g., a whole-struct write through it
    // silently vanished for every NON-top instantiation of the module.
    register_modport_expressions(source_def.items(), prefix, definitions);
    let sibling_inst_names: std::collections::HashSet<String> = prepared_source
        .effective_items
        .iter()
        .filter_map(|it| match it {
            ModuleItem::ModuleInstantiation(mi) => Some(mi),
            _ => None,
        })
        .flat_map(|mi| mi.instances.iter().map(|hi| hi.name.name.clone()))
        .collect();
    // Collect defparams: those propagated in from a parent scope, plus this
    // module's own `defparam` items (RHS evaluated in THIS scope, §23.10.1).
    let mut defparams: Vec<PendingDefparam> = pending_defparams.to_vec();
    for it in &prepared_source.effective_items {
        if let ModuleItem::Defparam(assigns) = it {
            for (lhs, rhs) in assigns {
                if let Some(path) = defparam_path_segments(lhs) {
                    defparams.push(PendingDefparam {
                        path,
                        value: eval_const_expr_val(rhs, local_params),
                        span: lhs.span,
                        owner: source_def.name().to_string(),
                    });
                }
            }
        }
    }
    // End offset of the process/instance items seen so far (see
    // `ElabInstance::src_pos`).
    let mut items_end = 0usize;
    inline_instantiation_items(
        elab,
        source_def,
        prefix,
        definitions,
        interface_map,
        local_params,
        cache,
        parent_port_map,
        &defparams,
        param_scope,
        &prepared_source.local_names,
        &prepared_source.local_typedefs,
        &sibling_inst_names,
        &mut items_end,
        &prepared_source.effective_items,
        bind_state.as_deref_mut(),
    )?;
    if bind_state
        .as_ref()
        .is_some_and(|bs| bs.filter.matches(prefix.trim_end_matches('.'), source_def.name()))
    {
        Ok(ModuleInlineMeta {
            items_end,
            was_flat_leaf: false,
            local_names: Some(Rc::clone(&prepared_source.local_names)),
            local_typedefs: (!prepared_source.local_typedefs.is_empty())
                .then(|| Box::new(prepared_source.local_typedefs.clone())),
            defparams,
        })
    } else {
        Ok(ModuleInlineMeta {
            items_end,
            was_flat_leaf: false,
            local_names: None,
            local_typedefs: None,
            defparams: Vec::new(),
        })
    }
}
