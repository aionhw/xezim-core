use super::*;

/// Pre-built `Rc`-shared sources for the deferred-rewrite kinds (#7).
/// Built once per `(module, params)` cache hit; sibling instances share
/// via `Rc::clone` (refcount bump) instead of cloning the AST per push.
#[derive(Debug, Clone)]
pub(super) enum BodySource {
    ContAssign(Vec<(std::rc::Rc<Expression>, std::rc::Rc<Expression>)>),
    GateInst(Vec<(std::rc::Rc<Expression>, std::rc::Rc<Expression>)>),
    NetInits(Vec<(std::rc::Rc<Expression>, std::rc::Rc<Expression>)>),
    Always(AlwaysKind, std::rc::Rc<Statement>, String),
    Initial(std::rc::Rc<Statement>, String),
    Other,
}

/// Base identifier of an assignment target (`a`, `a[i]`, `a[3:0].b`, and
/// concat elements) — the name whose signal the write ultimately lands on.
fn lvalue_base_names(e: &Expression, out: &mut std::collections::HashSet<String>) {
    match &e.kind {
        ExprKind::Ident(h) => {
            if let Some(seg) = h.path.first() {
                out.insert(seg.name.name.clone());
            }
        }
        ExprKind::Index { expr, .. }
        | ExprKind::RangeSelect { expr, .. }
        | ExprKind::MemberAccess { expr, .. }
        | ExprKind::Paren(expr) => lvalue_base_names(expr, out),
        ExprKind::Concatenation(parts) => {
            for p in parts {
                lvalue_base_names(p, out);
            }
        }
        _ => {}
    }
}

/// Collect assignment targets inside a statement tree. Mirrors the walk in
/// `check_lvalue`'s `walk_stmt`; unhandled statement kinds simply contribute
/// nothing, which is why callers over-approximate elsewhere.
fn collect_driven_in_stmt(s: &Statement, out: &mut std::collections::HashSet<String>) {
    match &s.kind {
        StatementKind::BlockingAssign { lvalue, .. }
        | StatementKind::NonblockingAssign { lvalue, .. } => lvalue_base_names(lvalue, out),
        StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
            for s in stmts {
                collect_driven_in_stmt(s, out);
            }
        }
        StatementKind::If {
            then_stmt,
            else_stmt,
            ..
        } => {
            collect_driven_in_stmt(then_stmt, out);
            if let Some(e) = else_stmt {
                collect_driven_in_stmt(e, out);
            }
        }
        StatementKind::Case { items, .. } => {
            for it in items {
                collect_driven_in_stmt(&it.stmt, out);
            }
        }
        StatementKind::For { body, .. }
        | StatementKind::While { body, .. }
        | StatementKind::DoWhile { body, .. }
        | StatementKind::Repeat { body, .. }
        | StatementKind::Forever { body, .. }
        | StatementKind::Foreach { body, .. } => collect_driven_in_stmt(body, out),
        StatementKind::TimingControl { stmt, .. } => collect_driven_in_stmt(stmt, out),
        _ => {}
    }
}

/// Every name this module's body drives — see `body_driven_ports`.
fn collect_body_driven_names(
    items: &[ModuleItem],
    definitions: &HashMap<String, Definition>,
    out: &mut std::collections::HashSet<String>,
) {
    for item in items {
        match item {
            ModuleItem::ContinuousAssign(ca) => {
                for (lhs, _) in &ca.assignments {
                    lvalue_base_names(lhs, out);
                }
            }
            ModuleItem::AlwaysConstruct(ac) => collect_driven_in_stmt(&ac.stmt, out),
            ModuleItem::InitialConstruct(ic) => collect_driven_in_stmt(&ic.stmt, out),
            ModuleItem::FinalConstruct(fc) => collect_driven_in_stmt(&fc.stmt, out),
            ModuleItem::GateInstantiation(gi) => {
                // §28.3: the OUTPUT terminal comes first on every gate xezim
                // models (pullup/pulldown have only that one).
                for inst in &gi.instances {
                    if let Some(first) = inst.terminals.first() {
                        lvalue_base_names(first, out);
                    }
                }
            }
            ModuleItem::ModuleInstantiation(mi) => {
                let child = definitions.get(&mi.module_name.name);
                // §29.3/§29.7: a UDP's first terminal is its sole output.
                // Definition::ports() is empty for UDPs; treating all of their
                // terminals as unknown marked input reads as body writes and
                // disabled the enclosing formal's §23.3.3 shape preservation.
                if matches!(child, Some(Definition::Udp(_))) {
                    for inst in &mi.instances {
                        if let Some(PortConnection::Ordered(Some(output))) = inst.connections.first()
                        {
                            lvalue_base_names(output, out);
                        }
                    }
                    continue;
                }
                // §23.2.2.1 (#572): a non-ANSI header lists names only; the
                // directions are the body's port declarations. Reading them
                // here keeps an input bound to such a child's input from
                // counting as body-driven, which switched off every shape
                // rule of its own port connection.
                let by_name: Option<HashMap<String, PortDirection>> = child.map(|d| {
                    let mut m: HashMap<String, PortDirection> = HashMap::default();
                    match d.ports() {
                        PortList::Ansi(ps) => {
                            for p in ps {
                                if let Some(dir) = p.direction {
                                    m.insert(p.name.name.clone(), dir);
                                }
                            }
                        }
                        PortList::NonAnsi(_) => {
                            for it in d.items() {
                                if let ModuleItem::PortDeclaration(pd) = it {
                                    for dc in &pd.declarators {
                                        m.insert(dc.name.name.clone(), pd.direction);
                                    }
                                }
                            }
                        }
                        PortList::Empty => {}
                    }
                    m
                });
                let dirs: Option<Vec<Option<PortDirection>>> = child.map(|d| match d.ports() {
                    PortList::Ansi(ps) => ps.iter().map(|p| p.direction).collect(),
                    PortList::NonAnsi(names) => names
                        .iter()
                        .map(|n| by_name.as_ref().and_then(|m| m.get(&n.name).copied()))
                        .collect(),
                    PortList::Empty => Vec::new(),
                });
                let named_dir = |n: &str| -> Option<PortDirection> {
                    by_name.as_ref().and_then(|m| m.get(n).copied())
                };
                for inst in &mi.instances {
                    for (i, conn) in inst.connections.iter().enumerate() {
                        let (dir, expr) = match conn {
                            PortConnection::Named { name, expr, .. } => {
                                (named_dir(&name.name), expr.as_ref())
                            }
                            PortConnection::Ordered(e) => (
                                dirs.as_ref().and_then(|d| d.get(i).copied().flatten()),
                                e.as_ref(),
                            ),
                            // `.*` binds same-named nets; an output among them
                            // drives its net, and the names are not listed
                            // here, so leave those to the child's own pass.
                            PortConnection::Wildcard => (None, None),
                        };
                        let Some(expr) = expr else { continue };
                        // Unknown child (unresolved definition / non-ANSI
                        // ports) => assume it may drive. See the field doc.
                        match dir {
                            Some(PortDirection::Input) => {}
                            _ => lvalue_base_names(expr, out),
                        }
                    }
                }
            }
            ModuleItem::GenerateRegion(gr) => {
                collect_body_driven_names(&gr.items, definitions, out)
            }
            ModuleItem::GenerateFor(gf) => collect_body_driven_names(&gf.items, definitions, out),
            ModuleItem::GenerateIf(gi) => {
                // Every branch counts: which one elaborates is a per-instance
                // parameter decision, and this set is cached per module.
                for (_, items) in &gi.branches {
                    collect_body_driven_names(items, definitions, out);
                }
            }
            ModuleItem::GenerateCase(gc) => {
                for arm in &gc.arms {
                    collect_body_driven_names(&arm.items, definitions, out);
                }
            }
            _ => {}
        }
    }
}

/// The typedefs an import binds, as (bare name, qualified key) in binding
/// order. A key `=pkg::name` marks a constant the import binds (§26.3).
pub(super) type ImportedTypedefs = Rc<[(String, String)]>;

/// A bare type entry hidden by an imported constant (`hidden_bare_types`).
pub type HiddenBareType = (
    String,
    Option<u32>,
    Option<DataType>,
    Option<Vec<UnpackedDimension>>,
    Option<u32>,
);

impl InlineCache {
    #[cfg(test)]
    pub(super) fn len(&self) -> usize { self.prepared.len() }

    pub(super) fn share_callable_source(
        &mut self,
        source: &crate::ast::shared_vec::SharedVec<Statement>,
    ) -> crate::ast::shared_vec::SharedVec<Statement> {
        let ptr = std::sync::Arc::as_ptr(source.as_arc()) as usize;
        if let Some((orig, shared)) = self.shared_callable_sources.get(&ptr)
            && std::sync::Weak::ptr_eq(orig, &std::sync::Arc::downgrade(source.as_arc()))
        {
            return shared.clone();
        }
        let disabled = crate::ast::cache::without_scope_caches(|| source.clone());
        let interned = self.callable_bodies.intern(disabled);
        self.shared_callable_sources.insert(
            ptr,
            (std::sync::Arc::downgrade(source.as_arc()), interned.clone()),
        );
        interned
    }

    /// §26.3: the typedefs the imports of `def` bind, in binding order. An
    /// import of a package the design does not declare is an error, at that
    /// import (the built-in `std` binds no typedefs).
    pub(super) fn imported_typedefs(
        &mut self,
        elab: &ElaboratedModule,
        def: Definition,
        definitions: &HashMap<String, Definition>,
    ) -> Result<Rc<[ImportedTypedefs]>, String> {
        let key = param_scope::def_key(&def);
        if let Some(lists) = self.imports.get(&key) {
            return Ok(Rc::clone(lists));
        }
        let mut lists = Vec::new();
        for item in def.items() {
            let ModuleItem::ImportDeclaration(imp) = item else {
                continue;
            };
            for ii in &imp.items {
                let pkg = &ii.package.name;
                if !matches!(definitions.get(pkg), Some(Definition::Package(_))) {
                    if pkg == "std" {
                        continue;
                    }
                    let msg = format!("Package '{}' not found", pkg);
                    return Err(format!(
                        "{}{}",
                        span_error_of(elab, ii.package.span, def.name(), &msg),
                        ignored_library_package_note(pkg)
                    ));
                }
                lists.push(match &ii.item {
                    Some(sym)
                        if package_declares_constant(pkg, &sym.name, definitions)
                            && design_type_names(definitions).contains(sym.name.as_str()) =>
                    {
                        Rc::from([(sym.name.clone(), format!("={pkg}::{}", sym.name))])
                    }
                    Some(sym) => Rc::from([(sym.name.clone(), format!("{pkg}::{}", sym.name))]),
                    None => match self.wildcards.get(pkg) {
                        Some(list) => Rc::clone(list),
                        None => {
                            let list = wildcard_typedefs(pkg, definitions);
                            self.wildcards.insert(pkg.clone(), Rc::clone(&list));
                            list
                        }
                    },
                });
            }
        }
        // A name the definition declares itself is its own (§26.3): an
        // imported constant of that name hides nothing.
        if lists
            .iter()
            .any(|l| l.iter().any(|(_, k)| k.starts_with('=')))
        {
            let mut local = collect_local_scope_names(def.items());
            for pd in def.params() {
                if let ParameterKind::Data { assignments, .. } = &pd.kind {
                    local.extend(assignments.iter().map(|a| a.name.name.clone()));
                }
            }
            for l in lists.iter_mut() {
                if l.iter()
                    .any(|(n, k)| k.starts_with('=') && local.contains(n))
                {
                    *l = l
                        .iter()
                        .filter(|(n, k)| !(k.starts_with('=') && local.contains(n)))
                        .cloned()
                        .collect();
                }
            }
        }
        let lists: Rc<[ImportedTypedefs]> = lists.into();
        self.imports.insert(key, Rc::clone(&lists));
        Ok(lists)
    }
}

/// `XEZIM_COMPILE_PHASES`: how the prepared-body cache is doing, printed as
/// it goes (an `[elab-stats]` line at each power-of-two miss count and every
/// 10000 misses), so a run killed for its memory still shows whether bodies
/// were shared: hits, misses, retained key payload bytes and the longest added
/// key payload (shared absence masks counted once, allocator overhead excluded).
fn note_prep_lookup(hit: bool, key_len: usize) {
    use std::cell::Cell;
    thread_local! {
        static PREP: Cell<(u64, u64, u64, u64)> = const { Cell::new((0, 0, 0, 0)) };
    }
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    if !*ON.get_or_init(|| std::env::var_os("XEZIM_COMPILE_PHASES").is_some()) {
        return;
    }
    PREP.with(|c| {
        let (mut hits, mut misses, mut bytes, mut longest) = c.get();
        if hit {
            hits += 1;
        } else {
            misses += 1;
            bytes += key_len as u64;
            longest = longest.max(key_len as u64);
            if misses.is_power_of_two() || misses % 10_000 == 0 {
                eprintln!(
                    "[elab-stats] prep_hits={hits} prep_misses={misses} prep_key_bytes={bytes} prep_key_max={longest}"
                );
            }
        }
        c.set((hits, misses, bytes, longest));
    });
}

/// The definition's type parameters as bound, for its prepared-body key;
/// `None` when one has no recorded shape to tell its bindings apart.
fn type_bindings(
    def: Definition,
    typedef_widths: &HashMap<String, u32>,
) -> Option<Vec<param_scope::TypeBinding>> {
    def.params_and_body_types()
        .flat_map(|pd| match &pd.kind {
            ParameterKind::Type { assignments } => assignments.as_slice(),
            _ => &[],
        })
        .map(|a| {
            let name = &a.name.name;
            let shape = TYPEDEF_SHAPES_TLS.with(|c| {
                let c = c.borrow();
                match (c.0.get(name), c.1.get(name)) {
                    (None, None) => None,
                    shape => canonical::span_free(&shape),
                }
            })?;
            Some((name.clone(), typedef_widths.get(name).copied(), shape))
        })
        .collect()
}

/// Whether any instantiation among `items` declares an array of instances.
pub(super) fn has_instance_arrays(items: &[ModuleItem]) -> bool {
    items.iter().any(|it| {
        matches!(it, ModuleItem::ModuleInstantiation(inst)
            if inst.instances.iter().any(|h| !h.dimensions.is_empty()))
    })
}

/// The widths and unpacked shapes of the signals and ports of the scope
/// holding `items` (a definition's body), which an instance array's
/// connections are sliced by.
type ScopeShapes = (
    HashMap<String, u32>,
    HashMap<String, Vec<(i64, i64)>>,
    HashMap<String, (Vec<(i64, i64)>, u32)>,
);

pub(super) fn ai_scope_shapes(
    items: &[ModuleItem],
    source_def: Definition,
    local_params: &HashMap<String, Value>,
    typedef_widths: &HashMap<String, u32>,
) -> ScopeShapes {
    let mut widths = ai_scan_signal_widths(items, local_params, typedef_widths);
    let mut unpacked_shapes = ai_scan_unpacked_shapes(items, local_params);
    if let PortList::Ansi(ports) = source_def.ports() {
        for port in ports {
            let width = port
                .data_type
                .as_ref()
                .map(|dt| resolve_type_width(dt, Some(local_params), Some(typedef_widths)))
                .unwrap_or(1)
                .max(1);
            widths.insert(port.name.name.clone(), width);
            if let Some(shape) = declared_unpacked_dims(&port.dimensions, local_params) {
                unpacked_shapes.insert(port.name.name.clone(), shape);
            }
        }
    }
    let mut packed = ai_scan_packed_shapes(items, local_params, typedef_widths);
    if let PortList::Ansi(ports) = source_def.ports() {
        for port in ports {
            let Some(dt) = &port.data_type else {
                continue;
            };
            if let Some(dims) = packed_full_dims_of(dt, local_params) {
                let width = resolve_type_width(dt, Some(local_params), Some(typedef_widths)).max(1);
                packed.insert(port.name.name.clone(), (dims, width));
            }
        }
    }
    (widths, unpacked_shapes, packed)
}

/// §23.2.3, §23.10: the parameters a module's header ports are sized by in
/// one of its instances: the instantiating scope's `params`, then each
/// header parameter, from the instance's override (evaluated in the
/// instantiating scope) or else from its default.
fn ai_instance_header_params(
    def: &Definition,
    overrides: Option<&[crate::ast::decl::ParamConnection]>,
    params: &HashMap<String, Value>,
) -> HashMap<String, Value> {
    use crate::ast::decl::{ParamConnection as PC, ParamValue as PV};
    let mut env = params.clone();
    let overrides = overrides.unwrap_or_default();
    let mut position = 0usize;
    for decl in def.params() {
        let ParameterKind::Data { assignments, .. } = &decl.kind else {
            if !decl.local {
                position += 1;
            }
            continue;
        };
        for assign in assignments {
            let named = overrides.iter().find_map(|o| match o {
                PC::Named { name, value } if name.name == assign.name.name => Some(value.as_ref()),
                _ => None,
            });
            let positional = (!decl.local)
                .then(|| match overrides.get(position) {
                    Some(PC::Ordered(value)) => Some(value.as_ref()),
                    _ => None,
                })
                .flatten();
            if !decl.local {
                position += 1;
            }
            let value = match named.or(positional) {
                Some(Some(PV::Expr(e))) => const_eval_i64_with_params(e, Some(params)),
                _ => assign
                    .init
                    .as_ref()
                    .and_then(|e| const_eval_i64_with_params(e, Some(&env))),
            };
            // A value this cannot fold keeps what the scope had.
            if let Some(v) = value {
                let mut v = Value::from_u64(v as u64, 32);
                v.is_signed = true;
                env.insert(assign.name.name.clone(), v);
            }
        }
    }
    env
}

/// §23.3.2: replace each array of instances among `items` by its elements.
pub(super) fn ai_expand_instance_arrays(
    items: &mut [ModuleItem],
    (widths, unpacked_shapes, packed): &ScopeShapes,
    definitions: &HashMap<String, Definition>,
    local_params: &HashMap<String, Value>,
    typedef_widths: &HashMap<String, u32>,
) {
    let cx = AiCtx {
        widths,
        packed,
        unpacked: unpacked_shapes,
        params: local_params,
    };
    for item in items.iter_mut() {
        if let ModuleItem::ModuleInstantiation(inst) = item {
            if inst.instances.iter().any(|h| !h.dimensions.is_empty()) {
                let def = definitions.get(&inst.module_name.name);
                // §23.3.3.5: the formals are the child's, sized by its own
                // parameters.
                let header_params = def.map(|d| {
                    ai_instance_header_params(d, inst.params.as_deref(), local_params)
                });
                let header_params = header_params.as_ref().unwrap_or(local_params);
                let port_widths = def
                    .map(|d| ai_module_port_widths(d, header_params, typedef_widths))
                    .unwrap_or_default();
                let port_shapes = def
                    .map(|d| ai_module_port_shapes(d, header_params))
                    .unwrap_or_default();
                let port_names = def.map(ai_module_port_names).unwrap_or_default();
                inst.instances =
                    ai_expand_instances(&inst.instances, &port_widths, &port_shapes, &port_names, cx);
            }
        }
    }
}

pub(super) fn prepare_module_items(
    source_def: Definition,
    definitions: &HashMap<String, Definition>,
    local_params: &HashMap<String, Value>,
    typedef_widths: &HashMap<String, u32>,
    cache: &mut InlineCache,
    param_scope: &param_scope::ParamScope,
) -> Rc<PreparedModuleItems> {
    // §6.20 / §23.10 (#721): these items retain symbolic ranges and
    // initializers until instance elaboration. Preparing them again for each
    // parameter value only clones and compares the same syntax. Keep this
    // whitelist conservative: generate expansion, statement-local dimensions,
    // typedef folding and instance-array expansion consume parameter values.
    let value_independent = *cache.value_independent
        .entry(param_scope::def_key(&source_def))
        .or_insert_with(|| source_def.items().iter().all(|item| matches!(item,
            ModuleItem::DataDeclaration(_)
                | ModuleItem::NetDeclaration(_)
                | ModuleItem::ParameterDeclaration(_)
                | ModuleItem::LocalparamDeclaration(_)
                | ModuleItem::PortDeclaration(_)
                | ModuleItem::ContinuousAssign(_)
        )));
    let cache_key = type_bindings(source_def, typedef_widths)
        .map(|types| if value_independent {
            param_scope::PreparedKey::value_independent(source_def, types)
        } else {
            param_scope.prepared_key(source_def, definitions, local_params, types)
        });
    if let Some(prepared) = cache_key.as_ref().and_then(|(k, _)| cache.prepared.get(k)) {
        note_prep_lookup(true, 0);
        return Rc::clone(prepared);
    }
    note_prep_lookup(false, cache_key.as_ref().map_or(0, |(_, bytes)| *bytes));

    let mut interface_ports = std::collections::HashSet::default();
    if let PortList::Ansi(ports) = source_def.ports() {
        for port in ports {
            if let Some(dt) = &port.data_type {
                if is_interface_type(dt, definitions) {
                    interface_ports.insert(port.name.name.clone());
                }
            }
        }
    }

    let mut effective_items = collect_effective_items(source_def.items(), local_params);
    // §6.18: a generate block's typedef is the module's under its block key.
    let local_typedefs: std::collections::HashSet<String> = effective_items
        .iter()
        .filter_map(|item| match item {
            ModuleItem::TypedefDeclaration(td) => Some(td.name.name.clone()),
            _ => None,
        })
        .collect();

    // Bind this instance's parameters into statement-local declarations while
    // they are still resolvable by their bare names — after elaboration only
    // the instance-qualified keys survive, and a local sized `[DW-1:0]` would
    // silently become 1 bit wide.
    literalize_stmt_decl_dims(&mut effective_items, local_params);

    // §23.3.2: expand arrays of module instances into individual instances with
    // bit-sliced vector connections, before body_sources/driver derivation.
    let mut interface_array_bounds = Vec::new();
    if has_instance_arrays(&effective_items) {
        for item in &effective_items {
            if let ModuleItem::ModuleInstantiation(inst) = item
                && matches!(definitions.get(&inst.module_name.name), Some(Definition::Interface(_)))
            {
                for element in &inst.instances {
                    if let Some(bounds) = declared_unpacked_dims(&element.dimensions, local_params)
                        && let [dim] = bounds.as_slice()
                    {
                        interface_array_bounds.push((element.name.name.clone(), *dim));
                    }
                }
            }
        }
        let shapes = ai_scope_shapes(&effective_items, source_def, local_params, typedef_widths);
        ai_expand_instance_arrays(
            &mut effective_items,
            &shapes,
            definitions,
            local_params,
            typedef_widths,
        );
    }

    let mut port_directions = HashMap::default();
    match source_def.ports() {
        PortList::Ansi(ports) => {
            for port in ports {
                if let Some(dir) = port.direction {
                    port_directions.insert(port.name.name.clone(), dir);
                }
            }
        }
        PortList::NonAnsi(_) => {
            for item in &effective_items {
                if let ModuleItem::PortDeclaration(pd) = item {
                    for decl in &pd.declarators {
                        port_directions.insert(decl.name.name.clone(), pd.direction);
                    }
                }
            }
        }
        PortList::Empty => {}
    }

    let mut local_names = std::collections::HashSet::default();
    for p_decl in source_def.params() {
        if let ParameterKind::Data { assignments, .. } = &p_decl.kind {
            for assign in assignments {
                local_names.insert(assign.name.name.clone());
            }
        }
    }
    match source_def.ports() {
        PortList::Ansi(ports) => {
            for port in ports {
                local_names.insert(port.name.name.clone());
            }
        }
        PortList::NonAnsi(names) => {
            for name in names {
                local_names.insert(name.name.clone());
            }
        }
        PortList::Empty => {}
    }
    for item in &effective_items {
        match item {
            ModuleItem::NetDeclaration(nd) => {
                for decl in &nd.declarators {
                    local_names.insert(decl.name.name.clone());
                }
            }
            ModuleItem::DataDeclaration(dd) => {
                for decl in &dd.declarators {
                    local_names.insert(decl.name.name.clone());
                }
            }
            ModuleItem::PortDeclaration(pd) => {
                for decl in &pd.declarators {
                    local_names.insert(decl.name.name.clone());
                }
            }
            ModuleItem::FunctionDeclaration(fd) => {
                local_names.insert(fd.name.name.name.clone());
            }
            ModuleItem::TaskDeclaration(td) => {
                local_names.insert(td.name.name.name.clone());
            }
            // §23.6: a named block of a process is a scope of this module:
            // `blk.v` names the block's variable in THIS instance, so it takes
            // the instance prefix like a child instance's name.
            ModuleItem::AlwaysConstruct(ac) => collect_block_labels(&ac.stmt, &mut local_names),
            ModuleItem::InitialConstruct(ic) => collect_block_labels(&ic.stmt, &mut local_names),
            // Named properties / sequences are registered per instance.
            ModuleItem::PropertyDeclaration(pd) => {
                local_names.insert(pd.name.name.clone());
            }
            // §14.3: so is a clocking block (`u.cb`): `@(cb)` and `cb.a` in
            // the instance name its own block, not a same-named block of the
            // parent.
            ModuleItem::ClockingDeclaration(cd) => {
                local_names.insert(cd.name.name.clone());
            }
            ModuleItem::SequenceDeclaration(sd) => {
                local_names.insert(sd.name.name.clone());
            }
            // §6.19: enum MEMBERS are named constants of this scope. Absent
            // from this set, an inlined expression kept the bare member name
            // and resolved through the flat first-wins slot, so a later
            // differently-parameterized instance read the FIRST instance's
            // member value (`OTHER = V + 1` stuck at the first V). The
            // instance-scoped entries the rewrite will now point at are
            // registered unconditionally at instance time.
            ModuleItem::TypedefDeclaration(td) => {
                // §6.18 / §6.24.1: casts and $bits name this instance's type.
                local_names.insert(td.name.name.clone());
                if let DataType::Enum(et) = &td.data_type {
                    for m in &et.members {
                        local_names.insert(m.name.name.clone());
                    }
                }
            }
            ModuleItem::ModuleInstantiation(inst) => {
                // §23.6: CHILD INSTANCE names are local names of this module —
                // a downward hierarchical reference (`child.grandchild.sig`,
                // e.g. in an event control's `iff` guard) must take the
                // instance prefix when this module is inlined. They were only
                // added for the typedef-disambiguation corner, so every copy
                // of a multiply-instanced module kept the SAME bare path and
                // all of them resolved to ONE instance's signal: two sibling
                // hierarchies waiting on their own strobes both fired on the
                // first one's, and the second sampled x-data too early.
                for hi in &inst.instances {
                    local_names.insert(hi.name.name.clone());
                    // An expanded instance-array element (`INT[0]`) is
                    // referenced as `INT[0].irq`: the ident's head segment is
                    // the ARRAY name with a select, so that name must prefix
                    // too, or the reference stays unscoped and reads x.
                    if let Some((base, _)) = hi.name.name.split_once('[') {
                        local_names.insert(base.to_string());
                    }
                }
                // §6.10: a bare undeclared identifier used as an instance PORT
                // CONNECTION is an implicit net local to THIS module. It must be
                // in local_names so every reference to it (this connection, a
                // gate terminal, a cont-assign) prefixes to the SAME net during
                // inlining — otherwise the net splits and the value never
                // propagates (e.g. a cell clock driven by a buf but read undriven).
                let mut cand = Vec::new();
                for hi in &inst.instances {
                    for conn in &hi.connections {
                        match conn {
                            PortConnection::Ordered(Some(e))
                            | PortConnection::Named { expr: Some(e), .. } => {
                                collect_implicit_net_candidates(e, &mut cand);
                            }
                            _ => {}
                        }
                    }
                }
                for c in cand {
                    local_names.insert(c);
                }
            }
            ModuleItem::GateInstantiation(gi) => {
                // §6.10: a bare undeclared gate terminal (e.g. a `buf` output) is
                // an implicit local net — register it so it prefixes consistently.
                let mut cand = Vec::new();
                for gi_inst in &gi.instances {
                    for term in &gi_inst.terminals {
                        collect_implicit_net_candidates(term, &mut cand);
                    }
                }
                for c in cand {
                    local_names.insert(c);
                }
            }
            ModuleItem::SpecifyBlock(sb) => {
                // Delayed-net targets/sources are local nets driven by the
                // injected zero-delay assigns; keep them in the same scope.
                for (delayed, source) in &sb.delayed_nets {
                    local_names.insert(delayed.clone());
                    local_names.insert(source.clone());
                }
            }
            ModuleItem::ParameterDeclaration(pd) | ModuleItem::LocalparamDeclaration(pd) => {
                if let ParameterKind::Data { assignments, .. } = &pd.kind {
                    for assign in assignments {
                        local_names.insert(assign.name.name.clone());
                    }
                }
            }
            _ => {}
        }
    }

    // §23.9, §27.5 (aionhw/xezim#1110): a generate block of this module is
    // a scope of it, as a child instance is: `h.a` in the module body names
    // this instance's `h.a`, not a same-named block of the top module. The
    // block's declarations arrive renamed (`h.a`, `g[0].x`); the path's head
    // takes the instance prefix as well.
    let gen_heads: Vec<String> = local_names
        .iter()
        .filter_map(|n| {
            let (head, _) = n.split_once('.')?;
            let base = head.split_once('[').map_or(head, |(b, _)| b);
            (!base.is_empty() && !base.starts_with('\\')).then(|| base.to_string())
        })
        .collect();
    local_names.extend(gen_heads);
    // §23.8: `<own definition name>.x` in a continuous assign is this
    // instance's `x`.
    // A local declaration of that name would be what the head names instead.
    if !local_names.contains(source_def.name()) {
        strip_own_definition_assign_targets(&mut effective_items, source_def.name());
    }
    // IEEE 1800-2017 §6.10: a bare identifier on the LHS of a continuous
    // assign (or gate output) that has no explicit net declaration
    // implicitly declares a 1-bit net in this scope. Register such names in
    // local_names so rewrite_expr prefixes them with the instance path;
    // the matching signal is created later by create_implicit_nets_for_pending.
    {
        let mut implicit: Vec<String> = Vec::new();
        for item in &effective_items {
            match item {
                ModuleItem::ContinuousAssign(ca) => {
                    for (lhs, _) in &ca.assignments {
                        // A dotted lvalue (`top.inst.net`) is a HIERARCHICAL
                        // reference, not an undeclared net. Registering its root
                        // here made `rewrite_expr` prefix it with the instance
                        // path (`wr.top.inst.net`), so the assign wrote a name
                        // that resolves to nothing.
                        collect_implicit_net_candidates(lhs, &mut implicit);
                    }
                }
                ModuleItem::GateInstantiation(gi) => {
                    for (lhs, _) in gate_inst_to_assign_pairs(gi) {
                        collect_implicit_net_candidates(&lhs, &mut implicit);
                    }
                }
                _ => {}
            }
        }
        for name in implicit {
            if !local_names.contains(&name) {
                local_names.insert(name);
            }
        }
    }

    let body_driven_ports = {
        let mut driven = std::collections::HashSet::default();
        collect_body_driven_names(&effective_items, definitions, &mut driven);
        // Keep only PORT names — everything else is a local and irrelevant to
        // the substitution decision.
        driven.retain(|n| port_directions.contains_key(n));
        driven
    };

    // Fill literals before extracting shared sources so pending processes
    // reuse the cached values instead of parsing them in every instance.
    let mut sampled_ports = std::collections::HashSet::new();
    prepare_body_operands(&effective_items, &mut sampled_ports);
    sampled_ports.retain(|n| port_directions.get(n) == Some(&PortDirection::Input));

    // §9.2.1/§9.2.2 (#721): pending processes own the shared source body.
    // Run name/driver analysis and literal prefill before moving it out of
    // the prepared item. Remaining consumers need only the wrapper's kind,
    // span and generate scope; retaining its AST would duplicate every
    // process once per prepared specialization for the whole inline pass.
    let has_subroutines = effective_items.iter().any(|item| matches!(
        item, ModuleItem::FunctionDeclaration(_) | ModuleItem::TaskDeclaration(_)
    ));
    let body_sources: Vec<BodySource> = effective_items
        .iter_mut()
        .map(|item| {
            match item {
                ModuleItem::ContinuousAssign(ca) => BodySource::ContAssign(
                    ca.assignments
                        .iter()
                        .map(|(l, r)| (std::rc::Rc::new(l.clone()), std::rc::Rc::new(r.clone())))
                        .collect(),
                ),
                ModuleItem::GateInstantiation(gi) => BodySource::GateInst(
                    gate_inst_to_assign_pairs(gi)
                        .into_iter()
                        .map(|(l, r)| (std::rc::Rc::new(l), std::rc::Rc::new(r)))
                        .collect(),
                ),
                ModuleItem::NetDeclaration(nd) => BodySource::NetInits(
                    nd.declarators
                        .iter()
                        .filter_map(|d| {
                            d.init.as_deref().map(|init| {
                                (
                                    std::rc::Rc::new(make_ident_expr(&d.name.name)),
                                    std::rc::Rc::new(init.clone()),
                                )
                            })
                        })
                        .collect(),
                ),
                ModuleItem::AlwaysConstruct(ac) => {
                    let placeholder = Statement::new(StatementKind::Null, ac.stmt.span);
                    BodySource::Always(
                        ac.kind,
                        cache.process_bodies.intern(Rc::new(std::mem::replace(&mut ac.stmt, placeholder))),
                        ac.gen_scope.clone(),
                    )
                }
                ModuleItem::InitialConstruct(ic) => {
                    let placeholder = Statement::new(StatementKind::Null, ic.stmt.span);
                    BodySource::Initial(
                        cache.process_bodies.intern(Rc::new(std::mem::replace(&mut ic.stmt, placeholder))),
                        ic.gen_scope.clone(),
                    )
                }
                // §16.5: a concurrent assertion in an INLINED instance (sub-module
                // or interface) travels like the top-level hoist — one synthetic
                // initial statement the runtime registers as a clocked site. It
                // used to fall to `Other` and vanish: no site, no failure, ever.
                ModuleItem::AssertionItem(a) => BodySource::Initial(
                    std::rc::Rc::new(crate::ast::stmt::Statement::new(
                        crate::ast::stmt::StatementKind::Assertion(a.clone()),
                        a.span,
                    )),
                    String::new(),
                ),
                _ => BodySource::Other,
            }
        })
        .collect();

    let mut prepared = Rc::new(PreparedModuleItems {
        interface_array_bounds,
        effective_items,
        body_sources,
        has_subroutines,
        local_typedefs,
        interface_ports,
        port_directions,
        local_names: std::rc::Rc::new(local_names),
        body_driven_ports,
        sampled_ports,
    });
    if let Some((key, _)) = cache_key {
        Rc::make_mut(&mut prepared).effective_items.shrink_to_fit();
        prepared = share_equal_prepared(cache, param_scope::def_key(&source_def), prepared);
        cache.prepared.insert(key, Rc::clone(&prepared));
    }
    prepared
}

/// The canonical copy of a freshly prepared body: an equal body of the same
/// definition prepared earlier (under other parameter values), else `fresh`.
/// Equality compares the complete encoded syntax, spans included, and every
/// derived name set; hashes only select candidates.
fn share_equal_prepared(
    cache: &mut InlineCache,
    def: (String, usize),
    fresh: Rc<PreparedModuleItems>,
) -> Rc<PreparedModuleItems> {
    use std::hash::{BuildHasher, Hasher};
    let entry = cache.equal_prepared.entry(def).or_default();
    let key = |bytes: &[u8]| {
        let mut hash = crate::hasher::DeterministicState::default().build_hasher();
        hash.write(bytes);
        (hash.finish(), bytes.len())
    };
    let encode = |p: &PreparedModuleItems| {
        bincode::serde::encode_to_vec(PreparedView(p), crate::xez_bincode_config()).ok()
    };
    if entry.first.is_none() && entry.by_content.is_empty() {
        entry.first = Some(Rc::downgrade(&fresh));
        return fresh;
    }
    if let Some(first) = entry.first.take().and_then(|first| first.upgrade()) {
        let Some(bytes) = encode(&first) else {
            entry.first = Some(Rc::downgrade(&first));
            return fresh;
        };
        entry
            .by_content
            .entry(key(&bytes))
            .or_default()
            .push(Rc::downgrade(&first));
    }
    let Some(bytes) = encode(&fresh) else {
        return fresh;
    };
    if entry.by_content.len() >= entry.sweep_at {
        entry.by_content.retain(|_, bucket| {
            bucket.retain(|body| body.strong_count() > 0);
            !bucket.is_empty()
        });
        entry.sweep_at = (entry.by_content.len() * 2).max(16);
    }
    let bucket = entry.by_content.entry(key(&bytes)).or_default();
    for candidate in bucket.iter().filter_map(|body| body.upgrade()) {
        let mut compare = crate::ast_intern::CompareWriter::new(&bytes);
        if bincode::serde::encode_into_std_write(
            PreparedView(&candidate),
            &mut compare,
            crate::xez_bincode_config(),
        )
        .is_ok()
            && compare.matched()
        {
            return candidate;
        }
    }
    bucket.push(Rc::downgrade(&fresh));
    fresh
}

impl serde::Serialize for PreparedView<'_> {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeTuple;
        fn sorted<'a>(set: impl IntoIterator<Item = &'a String>) -> Vec<&'a String> {
            let mut v: Vec<_> = set.into_iter().collect();
            v.sort_unstable();
            v
        }
        struct Sources<'a>(&'a [BodySource]);
        impl serde::Serialize for Sources<'_> {
            fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
                use serde::ser::SerializeSeq;
                let mut seq = s.serialize_seq(Some(self.0.len()))?;
                for source in self.0 {
                    match source {
                        BodySource::ContAssign(pairs) => seq.serialize_element(&(0u8, pairs))?,
                        BodySource::GateInst(pairs) => seq.serialize_element(&(1u8, pairs))?,
                        BodySource::NetInits(pairs) => seq.serialize_element(&(2u8, pairs))?,
                        BodySource::Always(kind, stmt, scope) => {
                            seq.serialize_element(&(3u8, kind, stmt, scope))?
                        }
                        BodySource::Initial(stmt, scope) => {
                            seq.serialize_element(&(4u8, stmt, scope))?
                        }
                        BodySource::Other => seq.serialize_element(&5u8)?,
                    }
                }
                seq.end()
            }
        }
        let p = self.0;
        let mut directions: Vec<_> = p.port_directions.iter().collect();
        directions.sort_unstable_by(|a, b| a.0.cmp(b.0));
        let mut t = s.serialize_tuple(10)?;
        t.serialize_element(&p.interface_array_bounds)?;
        t.serialize_element(&p.effective_items)?;
        t.serialize_element(&Sources(&p.body_sources))?;
        t.serialize_element(&p.has_subroutines)?;
        t.serialize_element(&sorted(&p.local_typedefs))?;
        t.serialize_element(&sorted(&p.interface_ports))?;
        t.serialize_element(&directions)?;
        t.serialize_element(&sorted(p.local_names.iter()))?;
        t.serialize_element(&sorted(&p.body_driven_ports))?;
        t.serialize_element(&sorted(&p.sampled_ports))?;
        t.end()
    }
}

/// Fill the value cache of every integer literal reachable from the
/// continuous assignments and procedural blocks of `items` — the value the
/// literal evaluators store there after their first evaluation of the node,
/// computed the same way. A literal that draws the unsized-decimal wrap
/// warning is left alone so the evaluator meeting it first still warns.
/// Also collect input names whose prehistory is observed by a sampled-value function.
fn prepare_body_operands(items: &[ModuleItem], sampled: &mut std::collections::HashSet<String>) {
    fn fill(n: &NumberLiteral) {
        let NumberLiteral::Integer {
            size,
            signed,
            base,
            value,
            cached_val,
            ..
        } = n
        else {
            return;
        };
        if cached_val.get().is_some() {
            return;
        }
        let radix = match base {
            NumberBase::Binary => 2,
            NumberBase::Octal => 8,
            NumberBase::Hex => 16,
            NumberBase::Decimal => 10,
        };
        let w = match size {
            Some(sz) => *sz,
            None => Value::unsized_integer_width(value, radix, *signed),
        };
        if w > 64 {
            return;
        }
        if let Some((vb, xz)) = Value::from_literal_text(value, radix, w).inline_bits() {
            cached_val.set(Some((vb, xz, w)));
        }
    }
    let mut expr = |e: &Expression| {
        for_each_sub_expr(e, &mut |x| match &x.kind {
            ExprKind::Number(n) => fill(n),
            ExprKind::SystemCall { name, args }
                if matches!(name.as_str(), "$past" | "$rose" | "$fell" | "$stable" | "$changed" | "$sampled") =>
            {
                if let Some(operand) = args.first() {
                    for_each_sub_expr(operand, &mut |e| {
                        if let ExprKind::Ident(h) = &e.kind
                            && h.root.is_none()
                            && let Some(seg) = h.path.first()
                        {
                            sampled.insert(seg.name.name.clone());
                        }
                    });
                }
            }
            _ => {}
        });
    };
    for item in items {
        match item {
            ModuleItem::ContinuousAssign(ca) => {
                for (lhs, rhs) in &ca.assignments {
                    expr(lhs);
                    expr(rhs);
                }
            }
            ModuleItem::AlwaysConstruct(ac) => for_each_stmt_expr(&ac.stmt, &mut expr),
            ModuleItem::InitialConstruct(ic) => for_each_stmt_expr(&ic.stmt, &mut expr),
            ModuleItem::FinalConstruct(fc) => for_each_stmt_expr(&fc.stmt, &mut expr),
            ModuleItem::FunctionDeclaration(f) => {
                for stmt in &f.items { for_each_stmt_expr(stmt, &mut expr); }
            }
            ModuleItem::TaskDeclaration(t) => {
                for stmt in &t.items { for_each_stmt_expr(stmt, &mut expr); }
            }
            ModuleItem::AssertionItem(a) => {
                expr(&a.expr);
                for stmt in [&a.action, &a.else_action].into_iter().flatten() {
                    for_each_stmt_expr(stmt, &mut expr);
                }
            }
            ModuleItem::PropertyDeclaration(p) => {
                if let Some(body) = &p.body { expr(body); }
                for stmt in &p.items { for_each_stmt_expr(stmt, &mut expr); }
            }
            ModuleItem::SequenceDeclaration(s) => {
                if let Some(body) = &s.body { expr(body); }
                for stmt in &s.items { for_each_stmt_expr(stmt, &mut expr); }
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod prepared_process_ownership_tests {
    use super::*;

    /// #721, §6.20 / §23.10: symbolic declaration ranges and initializers
    /// share preparation, while value-dependent transformations stay distinct.
    #[test]
    fn symbolic_declarations_use_one_prepared_key() {
        for (body, expected) in [
            ("logic [W-1:0] v = W; wire [W-1:0] n = v; assign out = n;", 1),
            ("if (W == 4) begin:a wire x; end else begin:b wire y; end", 2),
            ("typedef logic [W-1:0] word_t; word_t v;", 2),
            ("initial begin logic [W-1:0] v; v = W; end", 2),
        ] {
            let mut parsed = crate::parse(&format!(
                "module leaf #(parameter W=4)(output logic [W-1:0] out); {body} endmodule"
            ));
            assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
            // Preparation consumes the bound AST in production. Generate
            // declarations need those identities before their scope is renamed.
            let _ = bind::audit_design(&mut parsed.source.descriptions);
            let crate::ast::Description::Module(module) = &parsed.source.descriptions[0] else {
                panic!("module expected");
            };
            let definitions = HashMap::from_iter([("leaf".to_string(), Definition::Module(module))]);
            let empty = HashMap::default();
            let scope = param_scope::ParamScope::new(
                &empty, &definitions, &HashMap::default(), &HashMap::default(),
            );
            let mut cache = InlineCache::default();
            let mut bodies = Vec::new();
            for width in [4, 9, 4] {
                let params = HashMap::from_iter([("W".into(), Value::from_u64(width, 32))]);
                bodies.push(prepare_module_items(definitions["leaf"], &definitions,
                    &params, &HashMap::default(), &mut cache, &scope));
            }
            assert_eq!(cache.len(), expected, "{body}");
            assert_eq!(Rc::ptr_eq(&bodies[0], &bodies[1]), expected == 1, "{body}");
            assert!(Rc::ptr_eq(&bodies[0], &bodies[2]), "{body}");
        }
    }

    /// §23.10/§27.5: each parameter environment keeps its own cache entry.
    /// Environments that prepare equal bodies share one body (#721), and
    /// identical source syntax shares ownership; selecting another branch
    /// must differ.
    #[test]
    fn different_prepared_keys_share_only_identical_process_sources() {
        let parsed = crate::parse(
            "module leaf #(parameter ID=0, SEL=0)(input logic a, output logic y);
               initial y=ID;
               if (SEL) begin: chosen initial y=1; end
               else begin: other initial y=0; end
             endmodule",
        );
        assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
        let crate::ast::Description::Module(module) = &parsed.source.descriptions[0] else {
            panic!("module expected");
        };
        let definitions = HashMap::from_iter([("leaf".to_string(), Definition::Module(module))]);
        let base = HashMap::default();
        let scope = param_scope::ParamScope::new(
            &base, &definitions, &HashMap::default(), &HashMap::default(),
        );
        let mut cache = InlineCache::default();
        let mut prepare = |id, sel| {
            let params = HashMap::from_iter([
                ("ID".into(), Value::from_u64(id, 32)),
                ("SEL".into(), Value::from_u64(sel, 32)),
            ]);
            prepare_module_items(definitions["leaf"], &definitions, &params,
                &HashMap::default(), &mut cache, &scope)
        };
        let a = prepare(1, 0);
        let b = prepare(2, 0);
        let c = prepare(2, 1);
        assert_eq!(cache.len(), 3);
        assert!(Rc::ptr_eq(&a, &b));
        assert!(!Rc::ptr_eq(&b, &c));
        let sources = |prepared: &PreparedModuleItems| {
            prepared.body_sources.iter().filter_map(|body| match body {
                BodySource::Initial(body, _) => Some(Rc::clone(body)),
                _ => None,
            }).collect::<Vec<_>>()
        };
        let a = sources(&a);
        let b = sources(&b);
        let c = sources(&c);
        assert_eq!((a.len(), b.len(), c.len()), (2, 2, 2));
        assert!(Rc::ptr_eq(&a[0], &b[0]));
        assert!(Rc::ptr_eq(&a[1], &b[1]));
        assert!(Rc::ptr_eq(&b[0], &c[0]));
        assert!(!Rc::ptr_eq(&b[1], &c[1]));
    }

    /// #721, IEEE 1800-2023 §9.2.1/§9.2.2 and §23.6: a prepared process
    /// retains one complete source tree, while its ordering/scope wrapper and
    /// name/driver analysis survive. Cache hits and bound-instance copies share
    /// that source rather than retaining another owned statement tree.
    #[test]
    fn prepared_processes_keep_one_body_and_share_it_across_cache_and_bind_copies() {
        let parsed = crate::parse(
            "module leaf(input logic a, output logic [31:0] y, output logic q);
               initial begin : boot y = 8'h2a; y = 3000000000; end
               always_comb begin : drive q = a; end
             endmodule",
        );
        assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
        let crate::ast::Description::Module(module) = &parsed.source.descriptions[0] else {
            panic!("module expected");
        };
        // Compare source syntax, not immutable literal memoization that
        // shared bodies may populate during preparation.
        let original = bincode::serde::encode_to_vec(&module.items, crate::xez_bincode_config()).unwrap();
        let definitions = HashMap::from_iter([("leaf".to_string(), Definition::Module(module))]);
        let params = HashMap::default();
        let scope = param_scope::ParamScope::new(
            &params,
            &definitions,
            &HashMap::default(),
            &HashMap::default(),
        );
        let mut cache = InlineCache::default();
        let prepared = prepare_module_items(
            definitions["leaf"],
            &definitions,
            &params,
            &HashMap::default(),
            &mut cache,
            &scope,
        );
        assert!(prepared.local_names.contains("boot"));
        assert!(prepared.local_names.contains("drive"));
        assert!(prepared.body_driven_ports.contains("y"));
        assert!(prepared.body_driven_ports.contains("q"));
        assert!(!prepared.body_driven_ports.contains("a"));
        let mut sources = Vec::new();
        for (item, body) in prepared.effective_items.iter().zip(&prepared.body_sources) {
            let (placeholder, source, expected_len) = match (item, body) {
                (ModuleItem::InitialConstruct(ic), BodySource::Initial(source, scope)) => {
                    assert_eq!(&ic.gen_scope, scope);
                    (&ic.stmt, source, 2)
                }
                (ModuleItem::AlwaysConstruct(ac), BodySource::Always(kind, source, scope)) => {
                    assert_eq!(&ac.kind, kind);
                    assert_eq!(&ac.gen_scope, scope);
                    (&ac.stmt, source, 1)
                }
                _ => continue,
            };
            assert!(
                matches!(placeholder.kind, StatementKind::Null),
                "prepared item must not retain a second process tree"
            );
            assert_eq!(placeholder.span, source.span);
            let StatementKind::SeqBlock { stmts, .. } = &source.kind else {
                panic!("complete named block expected");
            };
            assert_eq!(stmts.len(), expected_len);
            sources.push(Rc::clone(source));
        }
        assert_eq!(sources.len(), 2);
        // §5.7.1: cache literals in the retained source at their full width,
        // including the sign bit of an unsized decimal magnitude.
        let StatementKind::SeqBlock { stmts, .. } = &sources[0].kind else {
            unreachable!();
        };
        for (stmt, expected) in stmts
            .iter()
            .zip([Some((42, 0, 8)), Some((3_000_000_000, 0, 33))])
        {
            let StatementKind::BlockingAssign { rvalue, .. } = &stmt.kind else {
                panic!("assignment expected");
            };
            let ExprKind::Number(NumberLiteral::Integer { cached_val, .. }) = &rvalue.kind else {
                panic!("integer literal expected");
            };
            assert_eq!(cached_val.get(), expected);
        }
        let hit = prepare_module_items(
            definitions["leaf"],
            &definitions,
            &params,
            &HashMap::default(),
            &mut cache,
            &scope,
        );
        assert!(Rc::ptr_eq(&prepared, &hit));
        assert_eq!(cache.len(), 1);
        // §23.11: resolved binds mutate a private prepared wrapper using
        // make_mut; complete process sources must still be shared.
        let mut bound = Rc::clone(&prepared);
        Rc::make_mut(&mut bound);
        for (old, new) in prepared.body_sources.iter().zip(&bound.body_sources) {
            match (old, new) {
                (BodySource::Initial(a, _), BodySource::Initial(b, _))
                | (BodySource::Always(_, a, _), BodySource::Always(_, b, _)) => {
                    assert!(Rc::ptr_eq(a, b));
                }
                _ => {}
            }
        }
        assert_eq!(
            bincode::serde::encode_to_vec(&module.items, crate::xez_bincode_config()).unwrap(),
            original,
            "preparing an instance must not consume or mutate its source definition"
        );
        drop(bound);
        drop(hit);
        drop(prepared);
        drop(cache);
        // Pending processes own Rc handles after the preparation cache dies.
        assert!(
            sources
                .iter()
                .all(|s| matches!(s.kind, StatementKind::SeqBlock { .. }))
        );
    }
}
