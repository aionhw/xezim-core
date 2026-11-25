use super::*;

#[allow(clippy::too_many_arguments)]
pub(super) fn inline_instantiation_items(
    elab: &mut ElaboratedModule,
    source_def: Definition,
    prefix: &str,
    definitions: &HashMap<String, Definition>,
    interface_map: &mut HashMap<String, String>,
    local_params: &HashMap<String, Value>,
    cache: &mut InlineCache,
    parent_port_map: &HashMap<String, Expression>,
    defparams: &[PendingDefparam],
    param_scope: &param_scope::ParamScope,
    parent_local_names: &std::collections::HashSet<String>,
    parent_local_typedefs: &std::collections::HashSet<String>,
    sibling_inst_names: &std::collections::HashSet<String>,
    items_end: &mut usize,
    items: &[ModuleItem],
    mut bind_state: Option<&mut BindWorklistState>,
) -> Result<(), String> {
    let has_header_elements = matches!(source_def, Definition::Module(m) if m.lexical_parent.is_some())
        || source_def.params().iter().any(|p| matches!(&p.kind, ParameterKind::Data { assignments, .. }
            if assignments.iter().any(|a| !a.dimensions.is_empty())));
    let nonlexical_params: std::cell::OnceCell<HashMap<String, Value>> = std::cell::OnceCell::new();
    let wildcard_interfaces = std::cell::OnceCell::new();
    for item in items {
        let item_floor = *items_end;
        *items_end = (*items_end).max(match item {
            ModuleItem::InitialConstruct(ic) => ic.span.end as usize,
            ModuleItem::AlwaysConstruct(ac) => ac.span.end as usize,
            ModuleItem::AssertionItem(a) => a.span.end as usize,
            ModuleItem::ModuleInstantiation(mi) => mi.span.end as usize,
            _ => 0,
        });
        if let ModuleItem::ModuleInstantiation(inst) = item {
            let sub_mod_name = &inst.module_name.name;
            let __inst_t0 = iprof_now();
            if elab_trace_enabled() {
                eprintln!(
                    "[xezim][elab] visiting prefix='{}' module='{}' instances={}",
                    prefix,
                    sub_mod_name,
                    inst.instances.len()
                );
            }
            let __inst_prof = iprof_enabled();
            let _guard = scopeguard_lite(move || {
                if let Some(t0) = __inst_t0.filter(|_| __inst_prof) {
                    eprintln!("[IPROF] {} {:?}", std::process::id(), t0.elapsed());
                }
            });
            // IEEE 1800-2017 §29: a UDP instance looks exactly like a module
            // instantiation. Lower it into a flattened `UdpInstance` (truth
            // table + resolved terminal nets) instead of inlining module items.
            if let Some(Definition::Udp(udp)) = definitions.get(sub_mod_name).copied() {
                lower_udp_instances(
                    elab,
                    udp,
                    inst,
                    prefix,
                    parent_local_names,
                    interface_map,
                    source_def.default_net_type(),
                )?;
                continue;
            }
            // §23.3.2: only a primitive instance may omit its name.
            if let Some(hi) = inst.instances.iter().find(|hi| hi.name.name.is_empty()) {
                return Err(span_error(
                    elab,
                    hi.span,
                    &format!(
                        "instance of '{}' has no instance name; only gate and UDP instances \
                         may omit it (IEEE 1800-2017 §23.3.2)",
                        sub_mod_name
                    ),
                ));
            }
            let sub_mod = match definitions.get(sub_mod_name) {
                Some(m) => *m,
                None => {
                    // Check if it's a typedef-based variable declaration (happens if parser was unsure)
                    if elab.typedefs.contains_key(sub_mod_name)
                        || parent_local_typedefs.contains(sub_mod_name)
                    {
                        let width = elab.typedefs.get(sub_mod_name).copied().unwrap_or(32);
                        let is_real = sub_mod_name == "real";
                        for hi in &inst.instances {
                            let sig_name = cat2(&prefix, &hi.name.name);
                            signals_insert_traced(
                                &mut elab.signals,
                                line!(),
                                sig_name.clone(),
                                Signal {
                                    is_const: false,
                                    name: sig_name.into(),
                                    width,
                                    is_signed: is_real,
                                    direction: None,
                                    value: if is_real {
                                        Value::from_f64(0.0)
.into()                                    } else {
                                        Value::new(width)
.into()                                    },
                                    is_real,
                                    type_name: Some(sub_mod_name.as_str().into()),
                                },
                            );
                        }
                        continue;
                    }
                    // LRM §17.2: checker instantiation. When the
                    // checker has formal ports, walk the body items
                    // and substitute each formal-name Ident with the
                    // actual arg expression at this instantiation
                    // site, then elaborate the rewritten items.
                    // When no ports, the body was already inlined at
                    // declaration time — just register a stub signal.
                    if let Some(cd) = elab.checker_decls.get(sub_mod_name).cloned() {
                        let has_ports = !matches!(cd.ports, crate::ast::module::PortList::Empty);
                        for hi in &inst.instances {
                            let sig_name = cat2(&prefix, &hi.name.name);
                            signals_insert_traced(
                                &mut elab.signals,
                                line!(),
                                sig_name.clone(),
                                Signal {
                                    is_const: false,
                                    name: sig_name.into(),
                                    width: 1,
                                    is_signed: false,
                                    direction: None,
                                    value: Value::zero(1).into(),
                                    is_real: false,
                                    type_name: Some(sub_mod_name.as_str().into()),
                                },
                            );
                            if has_ports {
                                // Build formal→actual expression map.
                                let formals: Vec<String> = match &cd.ports {
                                    crate::ast::module::PortList::NonAnsi(ns) => {
                                        ns.iter().map(|n| n.name.clone()).collect()
                                    }
                                    crate::ast::module::PortList::Ansi(ps) => {
                                        ps.iter().map(|p| p.name.name.clone()).collect()
                                    }
                                    crate::ast::module::PortList::Empty => Vec::new(),
                                };
                                let mut subst: HashMap<String, Expression> = HashMap::default();
                                for (i, fname) in formals.iter().enumerate() {
                                    if let Some(conn) = hi.connections.get(i) {
                                        if let Some(e) = conn.actual_expr_cloned() {
                                            subst.insert(fname.clone(), e);
                                        }
                                    }
                                }
                                let rewritten: Vec<ModuleItem> = cd
                                    .items
                                    .iter()
                                    .map(|it| rewrite_module_item_subst(it, &subst))
                                    .collect();
                                let prev_default_auto = elab.default_automatic;
                                elab.default_automatic = false;
                                let checker_res = elaborate_items(&rewritten, elab, Some(definitions));
                                elab.default_automatic = prev_default_auto;
                                checker_res?;
                            }
                        }
                        continue;
                    }
                    return Err(format!(
                        "Module '{}' instantiated but not found",
                        sub_mod_name
                    ));
                }
            };
            crate::param_override_lists::check_instance(elab, inst, sub_mod, source_def.name())?;

            for hi in &inst.instances {
                let __th = iprof_now();
                let inst_name = &hi.name.name;
                let inst_prefix = format!("{}{}.", prefix, inst_name);
                let _oom_instance = if crate::oom_trace::enabled() {
                    Some(crate::oom_trace::scope(
                        "inline instance",
                        &audit_location(source_def.name(), hi.name.span),
                        sub_mod_name,
                        inst_prefix.trim_end_matches('.'),
                    ))
                } else {
                    None
                };
                crate::oom_trace::model("prepare instance", elab, Some(cache.prepared.len()));
                elab.upward_scopes.borrow_mut().add_parent(
                    prefix.trim_end_matches('.'),
                    inst_prefix.trim_end_matches('.'),
                    source_def.name(),
                    inst,
                    hi,
                );
                // Bare-name keys this instance adds to the design-wide
                // geometry tables while its body is processed (see the
                // DataDeclaration arm below); removed again when the
                // instance is fully inlined, so they cannot be matched by
                // an unrelated same-named declaration elsewhere.
                let mut inst_bare_keys: Vec<(u8, String)> = Vec::new();
                // §3.3/§23.3.2: one instance name per scope. Accepting a
                // duplicate elaborated BOTH instances and applied the second
                // #() override to each (the override map is name-keyed) —
                // silent parameter cross-contamination. Share one `SharedName`
                // between the collision set and `ElabInstance.path` (#721).
                let inst_path_shared: SharedName = inst_prefix.trim_end_matches('.').into();
                if !elab.seen_instance_paths.insert(inst_path_shared.clone()) {
                    return Err(format!(
                        "duplicate instance name '{}' in the same scope \
                         (IEEE 1800-2017 \u{a7}23.3.2); a second #() override \
                         would silently apply to both instances",
                        inst_name
                    ));
                }
                // §6.8: child-module declaration initializers that are NOT
                // constant expressions are deferred to an initial-block
                // assignment (mirroring the top-level path). Collected during
                // the declaration walk below and emitted once the instance's
                // rewrite context exists.
                let mut deferred_decl_inits: Vec<(String, Expression)> = Vec::new();
                // §6.6.7, §10.3.1: initializers of user-defined nettype nets,
                // by local name; they become net declaration assignments.
                let mut nettype_decl_inits: Vec<(String, Expression)> = Vec::new();
                if elab_trace_enabled() {
                    eprintln!(
                        "[xezim][elab] inline instance path='{}' target='{}'",
                        inst_prefix, sub_mod_name
                    );
                }
                // Was: `let scoped_eval_params = local_params.clone();` — wasted clone, only read.
                let scoped_eval_params: &HashMap<String, Value> = local_params;

                // Bind the SUB-module's own imported type names before any of
                // its items are read. Its declarations are resolved here, in the
                // parent's walk, so rebinding at the recursive call would be too
                // late — an unqualified `T [1:0] s;` in a module that imports
                // `P::*` took whichever package last hoisted that bare name.
                let imports = cache.imported_typedefs(elab, sub_mod, definitions)?;
                rebind_imported_typedefs(elab, &imports);
                if !cache.param_imports_done.contains(sub_mod.name()) {
                    cache
                        .param_imports_done
                        .insert(sub_mod.name().to_string());
                    bind_inlined_import_params(elab, sub_mod, definitions)?;
                }
                // §26.3: until this instance is inlined (the recursive call
                // below), its own imports answer a bare imported array
                // element (`imported_array_element`), except in the
                // overrides this scope evaluates for it.
                let _import_scope = ImportScope::enter(sub_mod.name(), scoped_eval_params);
                // §6.10 implicit nets bound by port connections INSIDE the
                // module being inlined. The top-level pass only sees the top
                // module's instantiations, and the pending pass only sees
                // cont-assign bodies, so a net that exists solely as a port
                // actual one level down (a clock net bound only as an actual
                // inside an instantiated wrapper) was never registered as a
                // signal. Its
                // driver then had NO write id and its reader NO read id: the
                // hop stayed out of the settle dependency graph and updated
                // only when some unrelated change forced a settle, silently
                // dropping most transitions on a fast clock. Register it here,
                // under this instance's prefix, exactly as a declared net.
                {
                    let mut cands: Vec<String> = Vec::new();
                    collect_port_connection_net_candidates(sub_mod.items(), &mut cands);
                    // §23.11: a bound instance is as if present at the end of
                    // this instance, so its connections name nets here too.
                    if let Some(binds) = elab
                        .resolved_binds
                        .get(inst_prefix.trim_end_matches('.'))
                        .or_else(|| cache.unit_module_binds.get(sub_mod_name))
                    {
                        let bound: Vec<ModuleItem> = binds
                            .iter()
                            .map(|b| ModuleItem::ModuleInstantiation(b.instantiation.clone()))
                            .collect();
                        collect_port_connection_net_candidates(&bound, &mut cands);
                    }
                    create_target_implicit_nets(elab, sub_mod, &inst_prefix, cands)?;
                }

                iprof_since("ck1_after_implnet", __th);
                // Build port map and interface map
                let mut port_map = HashMap::default();
                let mut sub_interface_map = HashMap::default();

                // Interface ports of the SUB-module being instantiated. The
                // connection code below must route interface actuals through
                // `sub_interface_map` (not `port_map`) so `<port>.<member>`
                // resolves to the bound instance's members and inlined
                // interface tasks dispatch. `parent_local_names` belongs to
                // the PARENT (whose interface_ports may differ), so compute
                // it from `sub_mod` directly.
                let sub_iface_ports: std::collections::HashSet<String> = {
                    let mut s = std::collections::HashSet::default();
                    if let PortList::Ansi(ports) = sub_mod.ports() {
                        for port in ports {
                            if let Some(dt) = &port.data_type {
                                if is_interface_type(dt, definitions) {
                                    s.insert(port.name.name.clone());
                                }
                            }
                        }
                    }
                    s
                };

                if !hi.connections.is_empty() {
                    // §23.3.2: a connection list is either positional (ordered)
                    // or by-name. By-name lists may mix explicit `.p(e)`,
                    // implicit `.p`, no-connect `.p()`, and one `.*` wildcard.
                    // The wildcard fills every port NOT otherwise listed with a
                    // same-named net; explicit entries always win over `.*`.
                    let has_wildcard = hi
                        .connections
                        .iter()
                        .any(|c| matches!(c, PortConnection::Wildcard));
                    let has_named = hi.connections.iter().any(|c| c.is_named());
                    if has_wildcard || has_named {
                        let mut explicit: std::collections::HashSet<String> =
                            std::collections::HashSet::default();
                        for conn in &hi.connections {
                            let (name, expr_cow, implicit): (
                                &crate::ast::Identifier,
                                Option<std::borrow::Cow<'_, Expression>>,
                                bool,
                            ) = match conn {
                                PortConnection::Named {
                                    name,
                                    expr,
                                    implicit,
                                } => (
                                    name,
                                    expr.as_deref().map(std::borrow::Cow::Borrowed),
                                    *implicit,
                                ),
                                PortConnection::NamedIdent {
                                    name,
                                    actual,
                                    bound,
                                } => (
                                    name,
                                    Some(std::borrow::Cow::Owned(PortConnection::ident_expr(
                                        actual, *bound,
                                    ))),
                                    false,
                                ),
                                _ => continue,
                            };
                            {
                                explicit.insert(name.name.clone());
                                if let Some(e) = expr_cow.as_deref() {
                                    let mut rewritten_e = rewrite_expr(
                                        e,
                                        prefix,
                                        parent_port_map,
                                        parent_local_names,
                                        interface_map,
                                    );
                                    resolve_upward_module_name(
                                        &mut rewritten_e,
                                        parent_local_names,
                                        parent_port_map,
                                        interface_map,
                                        elab,
                                    );
                                    // §27.6: a hierarchical actual that names a net
                                    // inside an indexed SCOPE (`g[1].w`) names that
                                    // WHOLE net. Flatten it to the absolute name the
                                    // signal table uses, so the port connection, the
                                    // child's own drivers and the nettype resolver
                                    // all act on ONE net instead of on a name nothing
                                    // can resolve.
                                    //
                                    // An actual that reaches an INTERFACE member
                                    // is left alone: it resolves through the
                                    // interface binding, which the simulator does
                                    // from the rooted path (§23.3.3.4). Flattening
                                    // it here would bind it to a same-named LOCAL
                                    // instance instead of the connected one.
                                    let if_derived = path_head_name(e)
                                        .is_some_and(|h| interface_map.contains_key(&h));
                                    if !sub_iface_ports.contains(&name.name) && !if_derived {
                                        if let Some(flat) =
                                            scope_indexed_net_name(&rewritten_e, prefix, elab)
                                        {
                                            rewritten_e = make_ident_expr(&flat);
                                        }
                                    }
                                    // Whole-net identity actuals keep the plain
                                    // substitution machinery (port_aliases &
                                    // friends key on un-rooted idents).
                                    if whole_net_ident_name(&rewritten_e).is_none() {
                                        mark_actual_rooted(&mut rewritten_e, &|n| {
                                            elab.packages.contains(n)
                                        });
                                    }
                                    if sub_iface_ports.contains(&name.name) {
                                        if let Some(if_full_path) =
                                            iface_conn_path(&rewritten_e, local_params, definitions)
                                        {
                                            let if_full_path = qualify_sibling_conn(
                                                if_full_path,
                                                prefix,
                                                &sibling_inst_names,
                                            );
                                            sub_interface_map
                                                .insert(name.name.clone(), if_full_path);
                                        }
                                    } else {
                                        port_map.insert(name.name.clone(), rewritten_e);
                                    }
                                } else if implicit {
                                    // `.p` — connect to the same-named parent net.
                                    // §23.3.2: the implicitly-connected actual is the
                                    // same-named net IN THE PARENT SCOPE — which may
                                    // itself be a PORT of the enclosing instance. Resolve
                                    // it through that instance's formal->actual map, as an
                                    // EXPLICIT connection already is. Binding straight to
                                    // `prefix + name` ties the connection to the formal's
                                    // own signal, so a driver reaching it from inside (a
                                    // bound interface output driving an input port) never
                                    // propagated to the real parent net and every reader
                                    // of it read z. `rewrite_expr`'s fallback IS
                                    // `prefix + name`, so the unmapped case is unchanged.
                                    let parent_name = cat2(&prefix, &name.name);
                                    let actual = rewrite_expr(
                                        &make_ident_expr(&name.name),
                                        prefix,
                                        parent_port_map,
                                        parent_local_names,
                                        interface_map,
                                    );
                                    if sub_iface_ports.contains(&name.name) {
                                        sub_interface_map.insert(
                                            name.name.clone(),
                                            whole_net_ident_name(&actual).unwrap_or(parent_name),
                                        );
                                    } else {
                                        port_map.insert(name.name.clone(), actual);
                                    }
                                }
                                // `.p()` — explicit no-connect: leave unbound.
                            }
                        }
                        if has_wildcard {
                            // §23.3.2.4 `.*` fills every port the connection list
                            // does not name, ANSI or non-ANSI. A non-ANSI header
                            // is only a name list (`module m(clk, rst); input clk;`);
                            // the type lives in a later port declaration, so those
                            // ports are connected as nets. Leaving the arm ANSI-only
                            // dropped clk/rst/wr_en on `sfifo_fill`-style instances
                            // and the unconnected inputs read Z.
                            let wildcard_ports: Vec<(String, bool)> = match sub_mod.ports() {
                                PortList::Ansi(ports) => ports
                                    .iter()
                                    .map(|port| {
                                        let is_if_port = port
                                            .data_type
                                            .as_ref()
                                            .map(|dt| is_interface_type(dt, definitions))
                                            .unwrap_or(false);
                                        (port.name.name.clone(), is_if_port)
                                    })
                                    .collect(),
                                // §23.3.2.4: `.*` connects ports that have a
                                // name. A null port (`(a, , b)`) and an unnamed
                                // port expression (`(a[1:0])`, `({a, b})`) carry
                                // the parser's placeholder names; they stay
                                // unconnected, instead of binding to the
                                // placeholder of a non-ANSI parent's own port
                                // expression or to a name that exists nowhere.
                                PortList::NonAnsi(names) => names
                                    .iter()
                                    .filter(|n| !is_unnamed_port_placeholder(&n.name))
                                    .map(|n| (n.name.clone(), false))
                                    .collect(),
                                PortList::Empty => Vec::new(),
                            };
                            for (name, is_if_port) in wildcard_ports {
                                if explicit.contains(&name)
                                    || port_map.contains_key(&name)
                                    || sub_interface_map.contains_key(&name)
                                {
                                    continue;
                                }
                                // §23.3.2: the implicitly-connected actual is the
                                // same-named net IN THE PARENT SCOPE — which may
                                // itself be a PORT of the enclosing instance. Resolve
                                // it through that instance's formal->actual map, as an
                                // EXPLICIT connection already is. Binding straight to
                                // `prefix + name` ties the connection to the formal's
                                // own signal, so a driver reaching it from inside (a
                                // bound interface output driving an input port) never
                                // propagated to the real parent net and every reader
                                // of it read z. `rewrite_expr`'s fallback IS
                                // `prefix + name`, so the unmapped case is unchanged.
                                let parent_name = cat2(prefix, &name);
                                let actual = rewrite_expr(
                                    &make_ident_expr(&name),
                                    prefix,
                                    parent_port_map,
                                    parent_local_names,
                                    interface_map,
                                );
                                if is_if_port {
                                    let sibling_ifaces = wildcard_interfaces.get_or_init(|| {
                                        items.iter()
                                            .filter_map(|item| match item {
                                                ModuleItem::ModuleInstantiation(inst)
                                                    if matches!(definitions.get(&inst.module_name.name), Some(Definition::Interface(_))) => Some(inst),
                                                _ => None,
                                            })
                                            .flat_map(|inst| inst.instances.iter().map(|i| i.name.name.as_str()))
                                            .collect::<std::collections::HashSet<_>>()
                                    });
                                    let mut scope = hi.name.name.rsplit_once('.').map_or("", |(scope, _)| scope);
                                    let sibling = loop {
                                        let candidate = if scope.is_empty() {
                                            name.clone()
                                        } else {
                                            format!("{scope}.{name}")
                                        };
                                        if sibling_ifaces.contains(candidate.as_str()) {
                                            break Some(cat2(prefix, &candidate));
                                        }
                                        if scope.is_empty() {
                                            break None;
                                        }
                                        scope = scope.rsplit_once('.').map_or("", |(outer, _)| outer);
                                    };
                                    let parent_is_port = match source_def.ports() {
                                        PortList::Ansi(ports) => ports.iter().any(|p| p.name.name == name
                                            && p.data_type.as_ref().is_some_and(|dt| is_interface_type(dt, definitions))),
                                        PortList::NonAnsi(ports) => ports.iter().any(|p| p.name == name),
                                        PortList::Empty => false,
                                    };
                                    if sv_parser::strict_checks()
                                        && sibling.is_none()
                                        && !parent_is_port
                                        && !interface_map.contains_key(&name)
                                    {
                                        continue;
                                    }
                                    sub_interface_map.insert(
                                        name,
                                        sibling.unwrap_or_else(|| whole_net_ident_name(&actual).unwrap_or(parent_name)),
                                    );
                                } else {
                                    port_map.insert(name, actual);
                                }
                            }
                        }
                    } else {
                        for (i, conn) in hi.connections.iter().enumerate() {
                            if let PortConnection::Ordered(expr) = conn {
                                if let Some(e) = expr {
                                    let mut rewritten_e = rewrite_expr(
                                        e,
                                        prefix,
                                        parent_port_map,
                                        parent_local_names,
                                        interface_map,
                                    );
                                    // See the named-connection site above.
                                    let if_derived = path_head_name(e)
                                        .is_some_and(|h| interface_map.contains_key(&h));
                                    let iface_port = sub_mod
                                        .ports()
                                        .get(i)
                                        .map(|p| p.name().to_string())
                                        .is_some_and(|pn| sub_iface_ports.contains(&pn));
                                    if !iface_port && !if_derived {
                                        if let Some(flat) =
                                            scope_indexed_net_name(&rewritten_e, prefix, elab)
                                        {
                                            rewritten_e = make_ident_expr(&flat);
                                        }
                                    }
                                    if whole_net_ident_name(&rewritten_e).is_none() {
                                        mark_actual_rooted(&mut rewritten_e, &|n| {
                                            elab.packages.contains(n)
                                        });
                                    }
                                    if let Some(port) = sub_mod.ports().get(i) {
                                        let port_name = port.name();
                                        if sub_iface_ports.contains(port_name) {
                                            if let Some(if_full_path) = iface_conn_path(
                                                &rewritten_e,
                                                local_params,
                                                definitions,
                                            ) {
                                                let if_full_path = qualify_sibling_conn(
                                                    if_full_path,
                                                    prefix,
                                                    &sibling_inst_names,
                                                );
                                                sub_interface_map
                                                    .insert(port_name.to_string(), if_full_path);
                                            }
                                        } else {
                                            port_map.insert(port_name.to_string(), rewritten_e);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }

                // §25.3: an instantiated interface port needs an actual.
                // The synthetic multi-top wrapper treats its children as
                // roots, which may declare interface ports of their own.
                if sv_parser::strict_checks()
                    && !sub_iface_ports.is_empty()
                    && source_def.name() != crate::MULTI_TOP_WRAPPER
                    && let PortList::Ansi(ports) = sub_mod.ports()
                {
                    for (index, port) in ports.iter().enumerate() {
                        let name = &port.name.name;
                        if !sub_iface_ports.contains(name) {
                            continue;
                        }
                        let actual = hi.connections.iter().enumerate().find_map(|(pos, c)| match c {
                            PortConnection::Named { name: n, expr, implicit } if n.name == *name => {
                                Some(expr.is_some() || *implicit)
                            }
                            PortConnection::NamedIdent { name: n, .. } if n.name == *name => {
                                Some(true)
                            }
                            PortConnection::Ordered(e) if pos == index => Some(e.is_some()),
                            _ => None,
                        });
                        if actual.unwrap_or_else(|| sub_interface_map.contains_key(name)) {
                            continue;
                        }
                        let path = inst_prefix.trim_end_matches('.');
                        return Err(span_error_of(elab, hi.span, source_def.name(), &format!(
                            "interface port '{name}' of instance '{path}' (module '{sub_mod_name}') is not connected. Connect it to an interface instance or an interface port (IEEE 1800-2023 §25.3, §23.3.3)"
                        )));
                    }
                }

                // §23.2.2.4: an input port left unconnected (empty ordered
                // slot `dut(,x)`, named `.i()`, or absent from a short
                // connection list) that declares a default value is driven by
                // that default. Its sub-scope constant is substituted for the
                // port name throughout the inlined body.
                let mut port_defaults: Vec<(String, Expression, bool)> = Vec::new();
                if let PortList::Ansi(ports) = sub_mod.ports() {
                    // §22.9: if this module was declared inside an active
                    // `unconnected_drive region, its unconnected INPUT ports
                    // read the pulled value ('1 for pull1, '0 for pull0)
                    // instead of Z.
                    let pulled = sv_parser::unconnected_drive_for(sub_mod_name);
                    for port in ports {
                        let name = &port.name.name;
                        let is_input = !matches!(
                            port.direction,
                            Some(PortDirection::Output) | Some(PortDirection::Inout)
                        );
                        if !is_input
                            || port_map.contains_key(name)
                            || sub_interface_map.contains_key(name)
                        {
                            continue;
                        }
                        if let Some(def) = &port.default {
                            // Resolved below, once this instance's own
                            // parameters are known.
                            let is_string = matches!(
                                port.data_type,
                                Some(DataType::Simple {
                                    kind: crate::ast::types::SimpleType::String,
                                    ..
                                })
                            );
                            port_defaults.push((name.clone(), def.as_ref().clone(), is_string));
                        } else if let Some(pull1) = pulled {
                            let lit = Expression::new(
                                ExprKind::Number(NumberLiteral::UnbasedUnsized(if pull1 {
                                    '1'
                                } else {
                                    '0'
                                })),
                                port.name.span,
                            );
                            port_map.insert(name.clone(), lit);
                        }
                    }
                }

                iprof_since("ck2_after_portmap", __th);
                // §10.11: the child's OWN alias statements. Two of the child's
                // ports that are aliases of each other are ONE net, so their
                // actuals are ONE net too: the second port takes the first
                // one's actual. A group member that is not a port is the
                // child's internal net, unified with the group later.
                apply_child_alias_groups(
                    sub_mod.items(),
                    &inst_prefix,
                    &mut port_map,
                    &mut elab.alias_groups,
                );
                // Short-circuit: gated_clk_cell is a passthrough whose body is
                // `assign clk_out = clk_in;` plus dead enable logic. Inlining
                // it produces a 3-hop cont-assign chain (parent_clk_in →
                // local_clk_in → local_clk_out → parent_clk_out) that takes
                // multiple settle iterations to propagate. For c910 (which
                // has many gated_clk_cell instances on the same coreclk),
                // this introduces NBA-scheduling races between sibling FFs
                // clocked on different "gated" outputs of the same source
                // clock. Replace the entire instance with a single direct
                // cont-assign `parent_clk_out = parent_clk_in` so the
                // gated clock unifies with its source.
                //
                // Only a cell whose body really is that pass-through: other
                // designs use the same name for a real clock gate (Wujian100's
                // `soc/common.v` latches its enable), which this ran as a
                // wire, dropping the gate and its sub-instances.
                if sub_mod_name == "gated_clk_cell" && is_clock_passthrough_cell(&sub_mod) {
                    if let (Some(clk_out_expr), Some(clk_in_expr)) = (
                        port_map.get("clk_out").cloned(),
                        port_map.get("clk_in").cloned(),
                    ) {
                        elab.continuous_assigns.push(ContinuousAssignment::plain(
                            clk_out_expr,
                            clk_in_expr,
                        ));
                        continue;
                    }
                }

                // Resolve parameters for the sub-module
                let mut sub_params = HashMap::default();
                let dbg_param = (sub_mod_name == "ram" || sub_mod_name == "f_spsram_large")
                    && std::env::var("XEZIM_DBG_PARAM").is_ok();
                // Build the effective declared-parameter list for the
                // sub-module: header `#(…)` parameters first, then
                // ParameterDeclaration items in source order (Localparam
                // declarations are NOT overridable per IEEE 1800 §6.20.4).
                // Positional `inst.params` resolution must index into THIS
                // combined list — without it, modules that declare parameters
                // only inside the body (e.g. openc910's ram.v) get their
                // positional overrides silently dropped, leaving the sim
                // running with default sizes (4-element memories instead of
                // 2 M).
                // §6.20.4: a `localparam` in the parameter port list is NOT
                // overridable, so it occupies no positional slot. Exclude it so
                // `#(4, 6)` against `#(parameter A, localparam B, parameter C)`
                // binds A and C (not A and B).
                let mut sub_param_decls: Vec<&ParameterDeclaration> =
                    sub_mod.params().iter().filter(|p| !p.local).collect();
                // §27.3: a `generate ... endgenerate` region only wraps module
                // items, so its parameters take positional slots too.
                fn body_params<'a>(
                    items: &'a [ModuleItem],
                    out: &mut Vec<&'a ParameterDeclaration>,
                ) {
                    for it in items {
                        match it {
                            ModuleItem::ParameterDeclaration(pd) => out.push(pd),
                            ModuleItem::GenerateRegion(gr) => body_params(&gr.items, out),
                            _ => {}
                        }
                    }
                }
                body_params(sub_mod.items(), &mut sub_param_decls);
                if dbg_param {
                    eprintln!(
                        "[DBG_PARAM] inlining {} into prefix='{}', inst.params={:?}, inst_name={}, sub_param_decls={}",
                        sub_mod_name,
                        inst_prefix,
                        inst.params.as_ref().map(|p| p.len()),
                        hi.name.name,
                        sub_param_decls.len()
                    );
                }
                let expr_as_type_ref = |v: &Expression| -> Option<DataType> {
                    if let ExprKind::Ident(hier) = &v.kind {
                        // §26.3 / §8.23: `T`, `pkg::T`, `pkg::cls::T` — the
                        // parser never fills `hier.root` for `::`, and every
                        // `::`/`.` segment lands in `path`. A chain of ANY
                        // length becomes scope links + leaf (a type-param
                        // override position only ever spells `::` chains).
                        // Requiring len()==1/2 silently DROPPED scoped type
                        // overrides, so `#(.T(pkg::wide_t))` left the port
                        // at the DEFAULT type's width.
                        if !hier.path.is_empty() && hier.path.iter().all(|s| s.selects.is_empty()) {
                            let mut scopes: Vec<crate::ast::types::TypeScope> = Vec::new();
                            if let Some(r) = &hier.root {
                                scopes.push(crate::ast::types::TypeScope {
                                    name: Identifier {
                                        name: r.as_str().to_string(),
                                        span: v.span,
                                    },
                                    type_args: Vec::new(),
                                });
                            }
                            for seg in &hier.path[..hier.path.len() - 1] {
                                scopes.push(crate::ast::types::TypeScope {
                                    name: seg.name.clone(),
                                    type_args: Vec::new(),
                                });
                            }
                            return Some(DataType::TypeReference {
                                name: Box::new(TypeName {
                                    scopes,
                                    name: hier.path[hier.path.len() - 1].name.clone(),
                                    span: v.span,
                                    bound: Default::default(),
                                }),
                                dimensions: Vec::new(),
                                type_args: Vec::new(),
                                span: v.span,
                            });
                        }
                    }
                    // Same scoped shape arriving as (possibly nested)
                    // MemberAccess — expression context lowers `pkg::wide_t`
                    // to MemberAccess(Ident(pkg), wide_t) just as it does for
                    // package constants, and `pkg::cls::t` nests one level
                    // deeper.
                    if let Some((scopes, leaf)) = member_access_chain_as_scopes(v) {
                        return Some(DataType::TypeReference {
                            name: Box::new(TypeName {
                                scopes,
                                name: leaf,
                                span: v.span,
                                bound: Default::default(),
                            }),
                            dimensions: Vec::new(),
                            type_args: Vec::new(),
                            span: v.span,
                        });
                    }
                    module_class_scope::type_override(v)
                };
                let formal_is_type_param = |formal: &str| -> bool {
                    sub_param_decls.iter().any(|p| {
                        matches!(&p.kind,
                        ParameterKind::Type { assignments }
                            if assignments.iter().any(|a| a.name.name == formal))
                    })
                };
                let mut type_overrides: Vec<(String, DataType)> = Vec::new();
                // §23.10.2: each VALUE override's expression (parent scope),
                // kept so the conversion to the formal's declared type below
                // can evaluate it in that type's width context. A pattern
                // override, already packed by the formal's type, has none.
                let mut ovr_exprs: HashMap<String, Expression> = HashMap::default();
                // §23.10: ORDERED overrides bind to the flattened assignment
                // list — `parameter A=1, B=2` is ONE declaration with TWO
                // positional slots. Indexing declarations dropped every value
                // after the first of each group.
                enum FlatSlot<'a> {
                    Data(&'a DataType, &'a crate::ast::decl::ParamAssignment),
                    Type(&'a crate::ast::decl::TypeParamAssignment),
                }
                let flat_slots: Vec<FlatSlot> = sub_param_decls
                    .iter()
                    .flat_map(|p| match &p.kind {
                        ParameterKind::Data {
                            data_type,
                            assignments,
                        } => assignments
                            .iter()
                            .map(|a| FlatSlot::Data(data_type, a))
                            .collect::<Vec<_>>(),
                        ParameterKind::Type { assignments } => {
                            assignments.iter().map(FlatSlot::Type).collect()
                        }
                    })
                    .collect();
                if let Some(param_conns) = &inst.params {
                    for (i, conn) in param_conns.iter().enumerate() {
                        match conn {
                            ParamConnection::Named { name, value } => {
                                if let Some(ParamValue::Type(dt)) = value {
                                    type_overrides.push((name.name.clone(), dt.clone()));
                                }
                                if let Some(ParamValue::Expr(v)) = value {
                                    if formal_is_type_param(&name.name) {
                                        if let Some(dt) = expr_as_type_ref(v) {
                                            type_overrides.push((name.name.clone(), dt));
                                            continue;
                                        }
                                    }
                                }
                                if let Some(ParamValue::Expr(v)) = value {
                                    let v = &prebind_bits_of_signals(
                                        v,
                                        &elab.signals,
                                        scoped_eval_params,
                                        prefix,
                                        &elab.typedefs,
                                        &elab.typedef_types,
                                        &elab.packed_struct_fields,
                                        &elab.arrays,
                                    );
                                    // §13.4.3: const function calls in the
                                    // override expression (`.N(pkg::f(5))`)
                                    // — unsubstituted they eval to 0.
                                    let subbed_ov;
                                    let v: &Expression = if expr_has_call(v) {
                                        match substitute_const_fn_calls(
                                            v,Some(scoped_eval_params),
                                            elab,
                                            0,
                                        )
                                        .filter(|e| !expr_has_call(e))
                                        {
                                            Some(e) => {
                                                subbed_ov = e;
                                                &subbed_ov
                                            }
                                            None => v,
                                        }
                                    } else {
                                        v
                                    };
                                    let mut val = eval_const_expr_val(v, scoped_eval_params);
                                    let mut packed_pattern = false;
                                    // Check if target parameter is real or implicit real
                                    for p_decl in sub_mod.params_and_body_types() {
                                        if let ParameterKind::Data {
                                            data_type,
                                            assignments,
                                        } = &p_decl.kind
                                        {
                                            if assignments.iter().any(|a| a.name.name == name.name)
                                            {
                                                if is_type_real_resolved(data_type, &elab.typedef_types) {
                                                    val = Value::from_f64(val.to_f64());
                                                } else if matches!(data_type, DataType::Implicit { dimensions, .. } if dimensions.is_empty())
                                                    && val.is_real
                                                {
                                                    val = Value::from_f64(val.to_f64());
                                                }
                                                // An assignment-pattern override
                                                // (`.M('{8'hAA, 8'hBB})` or a struct
                                                // pattern `.CFG('{tag: ..})`) needs the
                                                // formal's type to pack; the plain
                                                // const-eval above yields 0 for it.
                                                // An unpacked array formal keeps the
                                                // pattern: its elements are built from
                                                // it, not from one packed element.
                                                let unpacked = assignments.iter().any(|a| {
                                                    a.name.name == name.name
                                                        && !a.dimensions.is_empty()
                                                });
                                                let packed = if unpacked {
                                                    None
                                                } else {
                                                    // A packed array of structs
                                                    // packs by element (#817).
                                                    pack_packed_array_const_value(
                                                        data_type,
                                                        v,
                                                        scoped_eval_params,
                                                        &elab.typedefs,
                                                        &elab.typedef_types,
                                                    )
                                                    .or_else(|| {
                                                        pack_packed_vector_pattern(
                                                            data_type,
                                                            v,
                                                            scoped_eval_params,
                                                            &elab.typedef_types,
                                                        )
                                                    })
                                                    .or_else(|| {
                                                        pack_struct_const_value(
                                                            data_type,
                                                            v,
                                                            scoped_eval_params,
                                                            &elab.typedefs,
                                                            &elab.typedef_types,
                                                        )
                                                    })
                                                };
                                                if let Some(pv) = packed {
                                                    val = pv;
                                                    packed_pattern = true;
                                                }
                                                break;
                                            }
                                        }
                                    }
                                    if !packed_pattern {
                                        ovr_exprs.insert(name.name.clone(), v.clone());
                                    }
                                    sub_params.insert(name.name.clone(), val);
                                }
                            }
                            ParamConnection::Ordered(value) => {
                                if dbg_param {
                                    eprintln!(
                                        "[DBG_PARAM]   ordered[{}] value={:?}, sub_param_decls.get(i)={:?}",
                                        i,
                                        value.is_some(),
                                        sub_param_decls.get(i).map(|p| match &p.kind {
                                            ParameterKind::Data { assignments, .. } =>
                                                assignments.first().map(|a| a.name.name.clone()),
                                            _ => None,
                                        })
                                    );
                                }
                                if let Some(ParamValue::Type(dt)) = value {
                                    if let Some(FlatSlot::Type(a)) = flat_slots.get(i) {
                                        type_overrides.push((a.name.name.clone(), dt.clone()));
                                    }
                                }
                                if let Some(ParamValue::Expr(v)) = value {
                                    if let Some(FlatSlot::Type(a)) = flat_slots.get(i) {
                                        if let Some(dt) = expr_as_type_ref(v) {
                                            type_overrides.push((a.name.name.clone(), dt));
                                            continue;
                                        }
                                    }
                                }
                                if let Some(ParamValue::Expr(v)) = value {
                                    if let Some(FlatSlot::Data(data_type, a)) = flat_slots.get(i) {
                                        let data_type: &DataType = data_type;
                                        let v = &prebind_bits_of_signals(
                                            v,
                                            &elab.signals,
                                            scoped_eval_params,
                                            prefix,
                                            &elab.typedefs,
                                            &elab.typedef_types,
                                            &elab.packed_struct_fields,
                                            &elab.arrays,
                                        );
                                        // §13.4.3: const-fn calls, as in the
                                        // Named branch.
                                        let subbed_ov;
                                        let v: &Expression = if expr_has_call(v) {
                                            match substitute_const_fn_calls(
                                                v,Some(scoped_eval_params),
                                                elab,
                                                0,
                                            )
                                            .filter(|e| !expr_has_call(e))
                                            {
                                                Some(e) => {
                                                    subbed_ov = e;
                                                    &subbed_ov
                                                }
                                                None => v,
                                            }
                                        } else {
                                            v
                                        };
                                        let mut val = eval_const_expr_val(v, scoped_eval_params);
                                        if dbg_param {
                                            eprintln!(
                                                "[DBG_PARAM]     eval -> {} = {}",
                                                a.name.name,
                                                val.to_u64().unwrap_or(0)
                                            );
                                        }
                                        if is_type_real_resolved(data_type, &elab.typedef_types) {
                                            val = Value::from_f64(val.to_f64());
                                        } else if matches!(data_type, DataType::Implicit { dimensions, .. } if dimensions.is_empty())
                                            && val.is_real
                                        {
                                            val = Value::from_f64(val.to_f64());
                                        }
                                        // See the Named branch: a pattern
                                        // override needs the formal's type,
                                        // and an unpacked array formal keeps it.
                                        let packed =
                                            if !a.dimensions.is_empty() {
                                                None
                                            } else {
                                                // A packed array of structs
                                                // packs by element (#817).
                                                pack_packed_array_const_value(
                                                    data_type,
                                                    v,
                                                    scoped_eval_params,
                                                    &elab.typedefs,
                                                    &elab.typedef_types,
                                                )
                                                .or_else(|| {
                                                    pack_packed_vector_pattern(
                                                        data_type,
                                                        v,
                                                        scoped_eval_params,
                                                        &elab.typedef_types,
                                                    )
                                                })
                                                .or_else(|| {
                                                    pack_struct_const_value(
                                                        data_type,
                                                        v,
                                                        scoped_eval_params,
                                                        &elab.typedefs,
                                                        &elab.typedef_types,
                                                    )
                                                })
                                            };
                                        if let Some(pv) = packed {
                                            val = pv;
                                        } else {
                                            ovr_exprs.insert(a.name.name.clone(), v.clone());
                                        }
                                        sub_params.insert(a.name.name.clone(), val);
                                    }
                                }
                            }
                        }
                    }
                }

                // §23.10.1 `defparam` overrides for THIS instance. A path
                // `hi.name.PARAM` (2 segs after the instance) sets a parameter
                // of this instance directly; a longer path targets a deeper
                // instance and is propagated into the recursion below. defparam
                // wins over `#(…)` (applied after), matching common tool
                // behavior. Localparams are not overridable, but the sub-module
                // param resolution already excludes those.
                // The instance name may be dotted after generate-scope
                // flattening (`gblk.u`), so match it against the LEADING path
                // segments rather than just path[0].
                // §6.20.4: a `localparam` is NOT overridable. `sub_param_decls`
                // lists exactly the overridable parameters (header non-local +
                // body `parameter`), so a direct target absent from it is a
                // localparam (or unknown) and must be ignored, not applied.
                let overridable: std::collections::HashSet<&str> = sub_param_decls
                    .iter()
                    .flat_map(|p| match &p.kind {
                        ParameterKind::Data { assignments, .. } => assignments
                            .iter()
                            .map(|a| a.name.name.as_str())
                            .collect::<Vec<_>>(),
                        ParameterKind::Type { assignments } => assignments
                            .iter()
                            .map(|a| a.name.name.as_str())
                            .collect::<Vec<_>>(),
                    })
                    .collect();
                let inst_segs: Vec<&str> = hi.name.name.split('.').collect();
                let n_inst = inst_segs.len();
                let mut sub_defparams: Vec<PendingDefparam> = Vec::new();
                for dp in defparams {
                    let path = &dp.path;
                    if path.len() <= n_inst
                        || !path[..n_inst].iter().zip(&inst_segs).all(|(a, b)| a == b)
                    {
                        continue;
                    }
                    let rest = &path[n_inst..];
                    if rest.len() == 1 {
                        // Targets a parameter of this instance directly. The
                        // per-file strict pass misses a child in another file,
                        // so judge the target here (§23.10.1, §6.20.1).
                        crate::param_override_lists::check_defparam(
                            elab, sub_mod, &rest[0], dp.span, &dp.owner,
                        )?;
                        // Apply only if it is overridable (skip localparams,
                        // §6.20.4).
                        if overridable.contains(rest[0].as_str()) {
                            sub_params.insert(rest[0].clone(), dp.value.clone());
                            // §10.8 excludes defparam from assignment-like
                            // contexts: evaluate in its declaring scope first,
                            // then convert to the target's type.
                            ovr_exprs.remove(rest[0].as_str());
                        }
                    } else {
                        // §6.20.1: a parameter of one of the child's generate
                        // blocks (`u.g.P`) is local; it matched no instance
                        // below and was dropped without a message.
                        crate::param_override_lists::check_defparam_path(
                            elab, sub_mod, rest, dp.span, &dp.owner,
                        )?;
                        // Targets a deeper instance — propagate into recursion.
                        sub_defparams.push(PendingDefparam {
                            path: rest.to_vec(),
                            ..dp.clone()
                        });
                    }
                }

                // A forced command-line override (`-GNAME=VALUE`) beats this
                // instance's own `#(…)`/defparam value: drop it so the
                // overridden default applies.
                for name in crate::forced_param_names() {
                    if overridable.contains(name.as_str()) {
                        sub_params.remove(&name);
                    }
                }

                // Internal parameter map for resolving default parameters that depend on each other.
                // Moved (was clone): sub_params is not used after this line.
                let mut sub_local_params = sub_params;

                // Bind collected TYPE parameter overrides as scoped typedefs
                // for the duration of this instance's inlining (including the
                // recursion into ITS sub-instances, so `.T(type_t)` chains
                // resolve). Prior same-named entries saved for restore.
                let mut saved_type_binds: Vec<(String, Option<u32>, Option<DataType>)> = Vec::new();
                // Bare `typedef_unpacked_dims` entries this instance's own
                // typedefs shadow while it is inlined, restored after it.
                let mut saved_unpacked_dims: Vec<(String, Option<Vec<UnpackedDimension>>)> =
                    Vec::new();
                // §20.7: the constant array queries (`localparam L = $left(T)`)
                // read a type's full definition from TYPEDEF_SHAPES_TLS, where
                // an instance's type parameters never went: they answered
                // from the width alone (`[w-1:0]`, no dimension). Each one is
                // registered there for this instance; prior entries restored
                // after it.
                let mut saved_type_shapes: Vec<(String, TypedefShapeSave)> = Vec::new();
                // §6.20.3: capture every actual in the instantiating scope before
                // installing the first child binding. In .A(byte), .B(A), B
                // takes the parent's A, including its original unpacked shape.
                let actuals: Vec<_> = type_overrides
                    .into_iter()
                    .map(|(name, dt)| {
                        let scoped = scope_override_typerefs(
                            &dt,
                            parent_local_typedefs,
                            prefix,
                            &elab.typedef_types,
                        );
                        let resolved = resolve_typedef_chain(&scoped, &elab.typedef_types).clone();
                        let (shape, dims) = type_param_shape(&dt, resolved, scoped_eval_params);
                        let width = resolve_type_width(
                            &shape,
                            Some(scoped_eval_params),
                            Some(&elab.typedefs),
                        );
                        (name, shape, dims, width)
                    })
                    .collect();
                let mut type_overrides = Vec::with_capacity(actuals.len());
                for (tp_name, resolved_dt, dims, w) in actuals {
                    saved_type_binds.push((
                        tp_name.clone(),
                        elab.typedefs.get(&tp_name).copied(),
                        elab.typedef_types.get(&tp_name).cloned(),
                    ));
                    typedefs_insert_traced(
                        &mut elab.typedefs,
                        "insert:submodule_type_param",
                        tp_name.clone(),
                        w,
                    );
                    // The override's dimensions are the parent's expressions.
                    saved_type_shapes.push((tp_name.clone(), tls_typedef_shape(&tp_name)));
                    tls_register_typedef_shape(&tp_name, &resolved_dt, &dims);
                    elab.typedef_types.insert(tp_name.clone(), resolved_dt.clone());
                    type_overrides.push((tp_name, resolved_dt));
                }

                // Helper to add parameters from a list of items.
                //
                // Iterated to a FIXPOINT: `collect_effective_items` expands a
                // generate-for using the params it is handed, so a loop whose
                // bound is a same-scope localparam (e.g. rr_arb_tree's
                // `localparam NumLevels = $clog2(NumIn);` then
                // `for (level < NumLevels) ... localparam Idx0 = 2**level-1+l;`)
                // does NOT expand on the first pass — NumLevels isn't in the map
                // yet — so the per-iteration Idx0 localparams never get
                // registered and read X, collapsing every `assign vec[Idx0]` to
                // bit 0 (floo_router forwarding loss). Re-running after NumLevels
                // is bound lets the loop expand and its body localparams resolve.
                // Declared types of the sub-module's own ports and variables,
                // so a body localparam can size `$bits` of them (§20.7).
                // §20.6.2/§20.7: from here on — the child's body parameters,
                // generate conditions and declaration widths — constant
                // expressions are the CHILD's, so its declarations answer
                // `$bits(v)` / `$size(v)`. The parameter overrides above were
                // the parent's.
                let _child_shapes = install_decl_shapes(sub_mod);
                let (sub_decl_types, sub_decl_elem_types) = {
                    let mut m = HashMap::default();
                    let mut e = HashMap::default();
                    collect_declared_types(sub_mod.ports(), sub_mod.items(), &mut m, &mut e);
                    (m, e)
                };
                let add_params_from_items =
                    |items: &[ModuleItem],
                     local_map: &mut HashMap<String, Value>,
                     elab_ro: &ElaboratedModule,
                     frozen: &HashSet<String>,
                     local_types: &HashMap<String, DataType>| {
                        for _ in 0..64 {
                            let mut changed = false;
                            let before = local_map.len();
                            let effective_items = collect_effective_items_ref(items, local_map);
                            for item in effective_items.iter().map(|c| &**c) {
                                if let ModuleItem::ParameterDeclaration(pd)
                                | ModuleItem::LocalparamDeclaration(pd) = item
                                {
                                    if let ParameterKind::Data {
                                        data_type,
                                        assignments,
                                    } = &pd.kind
                                    {
                                        for assign in assignments {
                                            // §6.20.2: seed each typed element
                                            // before folding dependent body constants.
                                            if !assign.dimensions.is_empty() {
                                                let override_expr =
                                                    ovr_exprs.get(&assign.name.name);
                                                let init = override_expr.or(assign.init.as_ref());
                                                let init_params = if override_expr.is_some() {
                                                    scoped_eval_params
                                                } else {
                                                    &*local_map
                                                };
                                                let packed = if override_expr.is_some_and(|e| {
                                                    !matches!(
                                                        peel_unpacked_typed_pattern(e).kind,
                                                        ExprKind::AssignmentPattern(_)
                                                            | ExprKind::Concatenation(_)
                                                    )
                                                }) || (override_expr.is_none()
                                                    && frozen.contains(&assign.name.name))
                                                {
                                                    local_map.get(&assign.name.name)
                                                } else {
                                                    None
                                                };
                                                // §6.20.2, §7.2.1: the element type may be
                                                // a typedef of this body (not bound yet),
                                                // and the generate constructs read
                                                // `Info[k].variant`: inline the instance's
                                                // types, as the scalar arm below does, and
                                                // register the element layout under the
                                                // array's name.
                                                let inlined = inline_instance_typedefs(data_type);
                                                let elem_dt = inlined.as_ref().unwrap_or(data_type);
                                                if let Some(fields) = packed_struct_field_layout(
                                                    elem_dt,
                                                    local_map,
                                                    &elab_ro.typedefs,
                                                    &elab_ro.typedef_types,
                                                ) {
                                                    tls_register_struct_layout(
                                                        &assign.name.name,
                                                        &fields,
                                                    );
                                                }
                                                if let Some(values) = array_params::elements(
                                                    elab_ro,
                                                    &assign.name.name,
                                                    &assign.dimensions,
                                                    init,
                                                    packed,
                                                    elem_dt,
                                                    local_map,
                                                    init_params,
                                                ) {
                                                    for (name, value) in values {
                                                        changed |=
                                                            local_map.get(&name) != Some(&value);
                                                        local_map.insert(name, value);
                                                    }
                                                    continue;
                                                }
                                            }
                                            // A body localparam may have been
                                            // computed in an earlier round against
                                            // a STALE local-typedef width (its
                                            // fields size by other localparams) —
                                            // recompute non-frozen entries each
                                            // round until stable. Header params /
                                            // overrides stay frozen.
                                            if !local_map.contains_key(&assign.name.name)
                                                || !frozen.contains(&assign.name.name)
                                            {
                                                if let Some(init) = &assign.init {
                                                    // §7.2.1: later body constants can select a
                                                    // field of this parameter while their own
                                                    // initializers are being folded.
                                                    let inlined =
                                                        inline_instance_typedefs(data_type);
                                                    if let Some(fields) = flatten_struct_fields(
                                                        inlined.as_ref().unwrap_or(data_type),
                                                        local_map,
                                                        &elab_ro.typedefs,
                                                        &elab_ro.typedef_types,
                                                    ) {
                                                        tls_register_struct_layout(
                                                            &assign.name.name,
                                                            &fields,
                                                        );
                                                    }
                                                    // §13.4.3 const-function calls.
                                                    let subbed_init;
                                                    let init: &Expression = if expr_has_call(init) {
                                                        match substitute_const_fn_calls(
                                                            init,Some(local_map), elab_ro, 0,
                                                        )
                                                        .filter(|e| !expr_has_call(e))
                                                        {
                                                            Some(e) => {
                                                                subbed_init = e;
                                                                &subbed_init
                                                            }
                                                            None => init,
                                                        }
                                                    } else {
                                                        init
                                                    };
                                                    // §20.7 `$bits(<port>)` /
                                                    // `$bits(port.member)` in a
                                                    // SUB-module body localparam.
                                                    // `local_map` holds parameters
                                                    // only, so these evaluated to 0
                                                    // and sized dependent widths to
                                                    // nothing. The sub-module's own
                                                    // declarations are the authority
                                                    // here.
                                                    let prebound;
                                                    let init: &Expression =
                                                        if expr_mentions_bits(init) {
                                                            prebound =
                                                                prebind_bits_from_declared_types(
                                                                    init,
                                                                    &sub_decl_types,
                                                                    &sub_decl_elem_types,
                                                                    local_map,
                                                                    &elab_ro.typedefs,
                                                                    &elab_ro.typedef_types,
                                                                );
                                                            &prebound
                                                        } else {
                                                            init
                                                        };
                                                    let mut val =
                                                        eval_const_expr_val(init, local_map);
                                                    if is_type_real_resolved(data_type, &elab_ro.typedef_types) {
                                                        val = Value::from_f64(val.to_f64());
                                                    } else if let DataType::Implicit {
                                                        signing,
                                                        dimensions,
                                                        ..
                                                    } = data_type
                                                        && dimensions.is_empty()
                                                    {
                                                        if val.is_real {
                                                            val = Value::from_f64(val.to_f64());
                                                        } else if let Some(s) = signing {
                                                            // §6.20.2: `signed` with no
                                                            // range keeps the value's
                                                            // width, takes the sign.
                                                            val.is_signed =
                                                                matches!(s, Signing::Signed);
                                                        }
                                                    } else if is_string_data_type(data_type) {
                                                        val = val.sv_string_strip_nul();
                                                    } else {
                                                        // §5.7.1/§10.9: a DECLARED
                                                        // shape sizes the init —
                                                        // `localparam [N-1:0] X='1`
                                                        // must fill N bits, not
                                                        // stay a 1-bit fill.
                                                        // §6.20.2/§10.7: the declared
                                                        // type is also the ASSIGNMENT
                                                        // CONTEXT and the authority
                                                        // for signedness: `localparam
                                                        // [1:0] C = 1 + P` is unsigned,
                                                        // and a LOCAL typedef'd signed
                                                        // type (`typedef logic signed
                                                        // [1:0] T; localparam T C = …`)
                                                        // is signed. Widths resolve
                                                        // through the installed
                                                        // instance-local typedef table,
                                                        // signs through `local_types`.
                                                        let target = if assign.dimensions.is_empty()
                                                        {
                                                            typedefs_snapshot(|td| {
                                                                param_integral_target(
                                                                    data_type,
                                                                    local_types,
                                                                    local_map,
                                                                    td.unwrap_or_else(|| {
                                                                        elab_ro.typedefs.as_map()
                                                                    }),
                                                                    &elab_ro.typedef_types,
                                                                )
                                                            })
                                                        } else {
                                                            None
                                                        };
                                                        if let Some(t) = target {
                                                            val = convert_param_value(
                                                                &val,
                                                                Some(init),
                                                                local_map,
                                                                t,
                                                            );
                                                        } else if !val.is_real {
                                                            // An UNPACKED-ARRAY
                                                            // localparam keeps its
                                                            // legacy handling: the packed
                                                            // concat is sliced by the
                                                            // array machinery.
                                                            let w = typedefs_snapshot(|td| {
                                                                resolve_type_width(
                                                                    data_type,
                                                                    Some(local_map),
                                                                    Some(td.unwrap_or_else(|| {
                                                                        elab_ro.typedefs.as_map()
                                                                    })),
                                                                )
                                                            });
                                                            if w > 0
                                                                && (val.is_fill || val.width != w)
                                                            {
                                                                val = val.resize(w);
                                                            }
                                                        }
                                                    }
                                                    // §10.9.2 / §27.4: a struct or multi-dim packed
                                                    // pattern (`localparam id_t Id = '{x: f(r), ..}`
                                                    // in a generate-for body) — the plain const-eval
                                                    // above yields 0; pack it by the declared type
                                                    // like the parameter-default path does.
                                                    // A body typedef reaches `elab_ro` only
                                                    // after the first instance is settled.
                                                    let with_local: HashMap<String, DataType>;
                                                    let typedef_types = match data_type {
                                                        DataType::TypeReference {
                                                            name, ..
                                                        } if !name.has_scope()
                                                            && local_types
                                                                .contains_key(&name.name.name) =>
                                                        {
                                                            with_local = elab_ro
                                                                .typedef_types
                                                                .iter()
                                                                .chain(local_types)
                                                                .map(|(k, v)| {
                                                                    (k.clone(), v.clone())
                                                                })
                                                                .collect();
                                                            &with_local
                                                        }
                                                        _ => &elab_ro.typedef_types,
                                                    };
                                                    // §7.4.5 / §10.9.1: a packed ARRAY of
                                                    // structs packs element by element;
                                                    // the struct packer alone laid the
                                                    // pattern over ONE element (#817).
                                                    if let Some(pv) = typedefs_snapshot(|td| {
                                                        pack_packed_array_const_value(
                                                            data_type,
                                                            init,
                                                            local_map,
                                                            td.unwrap_or_else(|| {
                                                                elab_ro.typedefs.as_map()
                                                            }),
                                                            typedef_types,
                                                        )
                                                    })
                                                    .or_else(|| {
                                                        pack_packed_vector_pattern(
                                                            data_type,
                                                            init,
                                                            local_map,
                                                            typedef_types,
                                                        )
                                                    })
                                                    .or_else(|| {
                                                        typedefs_snapshot(|td| {
                                                            pack_struct_const_value(
                                                                data_type,
                                                                init,
                                                                local_map,
                                                                td.unwrap_or_else(|| {
                                                                    elab_ro.typedefs.as_map()
                                                                }),
                                                                typedef_types,
                                                            )
                                                        })
                                                    }) {
                                                        val = pv;
                                                    }
                                                    // Body localparams are folded
                                                    // here, then generate-if
                                                    // conditions are expanded from
                                                    // this map. `fmt_logic_t` is
                                                    // `logic [0:N]`; without the
                                                    // element geometry,
                                                    // `ACTIVE_FORMATS[FP32]` reads
                                                    // the low bit and the FP32
                                                    // result pack is never built.
                                                    if let Some((ew, msb0, low)) = packed_outer_elem(
                                                        data_type,
                                                        local_map,
                                                        &elab_ro.typedef_types,
                                                    ) {
                                                        tls_register_elem_w(&assign.name.name, ew);
                                                        tls_register_elem_low(&assign.name.name, low);
                                                        if msb0 {
                                                            tls_register_elem_msb0(
                                                                &assign.name.name,
                                                            );
                                                        }
                                                    }
                                                    if local_map.get(&assign.name.name)
                                                        != Some(&val)
                                                    {
                                                        changed = true;
                                                        local_map
                                                            .insert(assign.name.name.clone(), val);
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            // Enum typedef MEMBERS are elaboration constants of
                            // this scope too (§6.19). They were never collected
                            // here, so a member with a parameter-dependent value
                            // (`MAGIC = V`) was absent from the instance's local
                            // environment — the cont-assign const-folder then fell
                            // back to the flat bare slot, which is first-wins
                            // across instances, and every later instance folded
                            // the FIRST instance's value in. Recomputed each
                            // round like the localparams above, so a member
                            // depending on a later-resolved name converges.
                            for item in effective_items.iter().map(|c| &**c) {
                                if let ModuleItem::TypedefDeclaration(td) = item {
                                    if let DataType::Enum(et) = &td.data_type {
                                        let bw = et
                                            .base_type
                                            .as_ref()
                                            .map(|bt| {
                                                resolve_type_width(
                                                    bt,
                                                    Some(local_map),
                                                    Some(&elab_ro.typedefs),
                                                )
                                            })
                                            .unwrap_or(32);
                                        let mut next_val: u64 = 0;
                                        for member in &et.members {
                                            let val = if let Some(init) = &member.init {
                                                eval_const_expr(init, local_map)
                                            } else {
                                                next_val
                                            };
                                            next_val = val.wrapping_add(1);
                                            if frozen.contains(&member.name.name) {
                                                continue;
                                            }
                                            let v = Value::from_u64(val, bw);
                                            let stale = local_map
                                                .get(&member.name.name)
                                                .is_none_or(|p| p.to_u64() != Some(val));
                                            if stale {
                                                local_map.insert(member.name.name.clone(), v);
                                                changed = true;
                                            }
                                        }
                                    }
                                }
                            }
                            if local_map.len() == before && !changed {
                                break;
                            }
                        }
                    };

                // §13.4.3: register the sub-module's function declarations
                // BEFORE the parameter passes so `parameter LOG_X = log2(X)`
                // const-evaluates instead of collapsing to 0.
                for it in sub_mod.items() {
                    if let ModuleItem::FunctionDeclaration(fd) = it
                        && fd.name.scopes.is_empty()
                    {
                        elab.functions
                            .insert_if_absent_with(fd.name.name.name.clone(), || fd.as_ref().clone());
                    }
                }
                // Incremental — the full-snapshot refresh here was O(N²), see
                // funcs_tls_add.
                funcs_tls_add(
                    &elab.functions,
                    sub_mod.items().iter().filter_map(|it| match it {
                        ModuleItem::FunctionDeclaration(fd) if fd.name.scopes.is_empty() => {
                            Some(&fd.name.name.name)
                        }
                        _ => None,
                    }),
                );
                // 1. Parameters from port list
                // §6.20.3: the DEFAULT type of each type parameter this
                // instance does not override, in header order. A value
                // parameter declared with it (`parameter type T = logic
                // [63:0], parameter T P = …`) converts to that type; the
                // global tables only hold overridden type parameters (bound
                // above) and the parent's own names.
                let prev_in_instance = CONST_FN_IN_INSTANCE.with(|c| c.replace(true));
                let _in_instance =
                    scopeguard_lite(move || CONST_FN_IN_INSTANCE.with(|c| c.set(prev_in_instance)));
                // The instance's own types (`CONST_FN_LOCAL_TYPES`), installed
                // once its body typedefs are known below and kept for the rest
                // of this instance, so its declarations see them too.
                // Its type parameters are known now (defaults and overrides),
                // for header parameter defaults such as `H = T'(45)`.
                let header_types: HashMap<String, DataType> = sub_mod
                    .params_and_body_types()
                    .filter_map(|p| match &p.kind {
                        ParameterKind::Type { assignments } => Some(assignments),
                        _ => None,
                    })
                    .flatten()
                    .filter_map(|a| Some((a.name.name.clone(), a.init.clone()?)))
                    .chain(type_overrides.iter().cloned())
                    .collect();
                let mut prev_local_types =
                    Some(CONST_FN_LOCAL_TYPES.with(|c| c.replace(Some(header_types))));
                let _local_types = scopeguard_lite(move || {
                    if let Some(prev) = prev_local_types.take() {
                        CONST_FN_LOCAL_TYPES.with(|c| *c.borrow_mut() = prev);
                    }
                });
                // Its own functions, not the `$unit` ones injected into it.
                let local_funcs: HashSet<String> = UNIT_FUNCTION_SITES.with(|u| {
                    let u = u.borrow();
                    sub_mod
                        .items()
                        .iter()
                        .filter_map(|it| match it {
                            ModuleItem::FunctionDeclaration(fd)
                                if !u.contains(&(
                                    fd.name.name.name.clone(),
                                    fd.span.start,
                                    fd.span.end,
                                )) =>
                            {
                                Some(fd.name.name.name.clone())
                            }
                            _ => None,
                        })
                        .collect()
                });
                let mut prev_local_funcs =
                    Some(CONST_FN_LOCAL_FUNCS.with(|c| c.replace(Some(local_funcs))));
                let _local_funcs = scopeguard_lite(move || {
                    if let Some(prev) = prev_local_funcs.take() {
                        CONST_FN_LOCAL_FUNCS.with(|c| *c.borrow_mut() = prev);
                    }
                });
                let mut inst_types: HashMap<String, DataType> = HashMap::default();
                // §6.20.3 / §20.6.2: a header default `parameter int H =
                // $bits(T)` folds through TYPEDEFS_TLS, which was only synced
                // with this instance's type parameters at step 1b, after the
                // header. H read the PREVIOUS instance's T (0 for the first
                // one), and so did a module with no type parameters reading a
                // design typedef of the same name. Sync before the header, then
                // bind each type parameter as the header reaches it, so a
                // default that depends on an earlier value parameter
                // (`type T = logic [W-1:0]`) sizes with this instance's W; an
                // overridden one is already in the tables. The declared type
                // goes in too, so a header `parameter T P = '{..}` of a struct
                // T packs by its fields. Both restored before 1b.
                let mut header_type_saves: HashMap<String, (Option<u32>, Option<DataType>)> =
                    HashMap::default();
                sync_typedefs_tls(&elab.typedefs);
                for p_decl in sub_mod.params_and_body_types() {
                    if let ParameterKind::Type { assignments } = &p_decl.kind {
                        for a in assignments {
                            if let Some(def_dt) = &a.init {
                                if !type_overrides.iter().any(|(n, _)| *n == a.name.name) {
                                    inst_types.insert(a.name.name.clone(), def_dt.clone());
                                    let w = resolve_type_width(
                                        def_dt,
                                        Some(&sub_local_params),
                                        Some(&elab.typedefs),
                                    );
                                    let resolved_dt =
                                        resolve_typedef_chain(def_dt, &elab.typedef_types).clone();
                                    header_type_saves.entry(a.name.name.clone()).or_insert_with(
                                        || {
                                            (
                                                elab.typedefs.get(&a.name.name).copied(),
                                                elab.typedef_types.get(&a.name.name).cloned(),
                                            )
                                        },
                                    );
                                    elab.typedefs.insert_if_changed(a.name.name.clone(), w);
                                    elab.typedef_types.insert(a.name.name.clone(), resolved_dt);
                                }
                            }
                        }
                        sync_typedefs_tls(&elab.typedefs);
                    }
                    if let ParameterKind::Data {
                        data_type,
                        assignments,
                    } = &p_decl.kind
                    {
                        for assign in assignments {
                            // §6.20.2: the integral type this parameter's
                            // value converts to (scalar parameters only).
                            let target = if assign.dimensions.is_empty() {
                                param_integral_target(
                                    data_type,
                                    &inst_types,
                                    &sub_local_params,
                                    &elab.typedefs,
                                    &elab.typedef_types,
                                )
                            } else {
                                None
                            };
                            let no_range_signing = match data_type {
                                DataType::Implicit {
                                    signing: Some(s),
                                    dimensions,
                                    ..
                                } if dimensions.is_empty() => Some(matches!(s, Signing::Signed)),
                                _ => None,
                            };
                            // Element-select support for a multi-dim packed
                            // parameter of THIS instance (`inst.PARAM[i]`).
                            // Const-eval reads the TLS tables under the bare
                            // name; the simulator reads the prefixed key.
                            if let Some(elem_w) = packed_inner_elem_width(
                                data_type,
                                &sub_local_params,
                                &elab.typedefs,
                            ) {
                                tls_register_elem_w(&assign.name.name, elem_w);
                            }
                            // `fmt_logic_t` is `logic [0:N]`. The typedef carries
                            // the range, so `FpFmtMask[fmt]` keeps index 0 in
                            // the high bit.
                            if let Some((ew, msb0, low)) = packed_outer_elem(
                                data_type,
                                &sub_local_params,
                                &elab.typedef_types,
                            ) {
                                tls_register_elem_w(&assign.name.name, ew);
                                tls_register_elem_low(&assign.name.name, low);
                                if msb0 {
                                    tls_register_elem_msb0(&assign.name.name);
                                }
                            }
                            register_packed_param_index(
                                elab,
                                &cat2(&inst_prefix, &assign.name.name),
                                data_type,
                                Some(&sub_local_params),
                            );
                            // §6.20.2 unpacked-array parameter. This runs even when the
                            // parameter is OVERRIDDEN: the override arrives as a single
                            // packed value, so without slicing it here no element ever
                            // gets a value and `A[i]` reads 0.
                            if !assign.dimensions.is_empty() {
                                // The initializer of an override is evaluated in the
                                // parent; a default uses preceding header parameters.
                                let actual = ovr_exprs.get(&assign.name.name);
                                let init = actual.or(assign.init.as_ref());
                                let override_val = if actual.is_some() { None } else {
                                    sub_local_params.get(&assign.name.name)
                                };
                                let init_params = if actual.is_some() {
                                    scoped_eval_params
                                } else {
                                    &sub_local_params
                                };
                                if let Some(array) = array_params::compute(
                                    elab, &inst_prefix, &assign.name.name, &assign.dimensions,
                                    init, override_val, data_type, &sub_local_params, init_params,
                                ) {
                                    array.bind_local(&assign.name.name, &mut sub_local_params);
                                    array.apply(elab, &inst_prefix);
                                    continue;
                                }
                            }
                            if !sub_local_params.contains_key(&assign.name.name) {
                                if let Some(init) = &assign.init {
                                    // IEEE 1800-2023: associative-array
                                    // parameter literal `'{"k": v, ...}`.
                                    // Materialise as `<prefix><param>[key]`
                                    // signals and register the array.
                                    if let ExprKind::AssignmentPattern(items) =
                                        &peel_unpacked_typed_pattern(init).kind
                                    {
                                        let all_keyed = !items.is_empty()
                                            && items.iter().all(|it| {
                                                matches!(it, AssignmentPatternItem::Keyed(_, _))
                                            });
                                        // See the module-scope twin: an
                                        // index-keyed pattern on a multi-dim
                                        // packed vector packs by element and
                                        // must not become an assoc literal.
                                        if all_keyed
                                            && pack_packed_vector_pattern(
                                                data_type,
                                                init,
                                                &sub_local_params,
                                                &elab.typedef_types,
                                            )
                                            .is_none()
                                        {
                                            let elem_w = resolve_type_width(
                                                data_type,
                                                Some(&sub_local_params),
                                                Some(&elab.typedefs),
                                            );
                                            let arr_full = cat2(&inst_prefix, &assign.name.name);
                                            elab.associative_arrays.insert(arr_full.clone(), true);
                                            for it in items {
                                                if let AssignmentPatternItem::Keyed(k, v) = it {
                                                    let key_str = match &k.kind {
                                                        ExprKind::StringLiteral(s) => {
                                                            crate::value::encode_name_key(s)
                                                                .into_owned()
                                                        }
                                                        _ => eval_const_expr_val(
                                                            k,
                                                            &sub_local_params,
                                                        )
                                                        .to_dec_string(),
                                                    };
                                                    let val_v = eval_init_for_target(
                                                        v,
                                                        &sub_local_params,
                                                        elem_w,
                                                        is_type_real_resolved(
                                                            data_type,
                                                            &elab.typedef_types,
                                                        ),
                                                    );
                                                    let sname =
                                                        format!("{}[{}]", arr_full, key_str);
                                                    signals_insert_traced(
                                                        &mut elab.signals,
                                                        line!(),
                                                        sname.clone(),
                                                        Signal {
                                                            is_const: true,
                                                            name: sname.into(),
                                                            width: elem_w,
                                                            is_signed: is_type_signed(data_type),
                                                            is_real: false,
                                                            direction: None,
                                                            value: val_v.into(),
                                                            type_name: None,
                                                        },
                                                    );
                                                }
                                            }
                                            continue;
                                        }
                                    }
                                    // Register element-width / struct layout so a
                                    // header localparam like
                                    // `sc = all_cfgs_gp[SEL]` / `x = sc.field`
                                    // resolves through the const-eval index /
                                    // member-select arms (black-parrot config).
                                    register_packed_array_elem_w(
                                        &assign.name.name,
                                        data_type,
                                        &elab.typedefs,
                                        &sub_local_params,
                                    );
                                    if let Some(fields) = flatten_struct_fields(
                                        data_type,
                                        &sub_local_params,
                                        &elab.typedefs,
                                        &elab.typedef_types,
                                    ) {
                                        if !fields.is_empty() {
                                            tls_register_struct_layout(&assign.name.name, &fields);
                                            register_struct_member_elem_widths(
                                                &assign.name.name,
                                                data_type,
                                                &sub_local_params,
                                                &elab.typedef_types,
                                            );
                                        }
                                    }
                                    // §13.4.3 const-function calls in the
                                    // initializer: substitute before eval —
                                    // otherwise the call yields 0 and every
                                    // dependent width wraps.
                                    let subbed_init2;
                                    let init_eval: &Expression = if expr_has_call(init) {
                                        match substitute_const_fn_calls(
                                            init,Some(&sub_local_params),
                                            elab,
                                            0,
                                        )
                                        .filter(|e| !expr_has_call(e))
                                        {
                                            Some(e) => {
                                                subbed_init2 = e;
                                                &subbed_init2
                                            }
                                            None => init,
                                        }
                                    } else {
                                        init
                                    };
                                    let mut val = eval_const_expr_val(init_eval, &sub_local_params);
                                    if is_type_real_resolved(data_type, &elab.typedef_types) {
                                        val = Value::from_f64(val.to_f64());
                                    } else if matches!(data_type, DataType::Implicit { dimensions, .. } if dimensions.is_empty())
                                        && val.is_real
                                    {
                                        val = Value::from_f64(val.to_f64());
                                    } else if let Some(t) = target {
                                        // §6.20.2/§10.7: a header parameter with an
                                        // explicit type/range takes its DEFAULT as
                                        // an assignment to that type: evaluated in
                                        // the declared width, wrapped to it, with
                                        // the DECLARED signedness (`parameter [3:0]
                                        // P = -1` is 15, `parameter signed [3:0] P =
                                        // 15` is -1, `parameter int P = 2.6` is 3).
                                        // An untyped parameter keeps its
                                        // self-determined value, and an
                                        // UNPACKED-ARRAY one is sliced by
                                        // `register_array_param` above.
                                        val = convert_param_value(
                                            &val,
                                            Some(init_eval),
                                            &sub_local_params,
                                            t,
                                        );
                                    } else if let Some(s) = no_range_signing {
                                        // §6.20.2: `signed`/`unsigned` with no
                                        // range keeps the value's width but takes
                                        // the declared sign.
                                        if !val.is_real {
                                            val.is_signed = s;
                                        }
                                    }
                                    // Non-keyed assignment-pattern DEFAULT on a
                                    // multi-dim packed vector (`parameter bit
                                    // [1:0][7:0] M = '{8'h0F, 8'hF0}`) or a
                                    // struct pattern (`'{tag: ..}`): the plain
                                    // const-eval above yields 0; pack by
                                    // element like the override path does.
                                    // §7.4.5 / §10.9.1: a packed ARRAY of
                                    // structs (`s_t [1:0] P = '{'{..}, '{..}}`)
                                    // packs element by element first; the
                                    // struct packer alone laid the pattern
                                    // over ONE element (#817).
                                    if let Some(pv) = pack_packed_array_const_value(
                                        data_type,
                                        init_eval,
                                        &sub_local_params,
                                        &elab.typedefs,
                                        &elab.typedef_types,
                                    )
                                    .or_else(|| {
                                        pack_packed_vector_pattern(
                                            data_type,
                                            init_eval,
                                            &sub_local_params,
                                            &elab.typedef_types,
                                        )
                                    })
                                    .or_else(|| {
                                        pack_struct_const_value(
                                            data_type,
                                            init_eval,
                                            &sub_local_params,
                                            &elab.typedefs,
                                            &elab.typedef_types,
                                        )
                                    }) {
                                        val = pv;
                                    }
                                    sub_local_params.insert(assign.name.name.clone(), val);
                                }
                            } else if assign.dimensions.is_empty() {
                                // §7.2.1: an OVERRIDDEN parameter skips the
                                // default path above, which is where a
                                // struct-typed header parameter registers its
                                // field layout. Later header localparams
                                // (`localparam int unsigned WIDTH =
                                // Features.Width`) are folded in this same
                                // loop, so the layout has to be in place here;
                                // registered afterwards, the select reads a
                                // 32-bit 0 and `[WIDTH-1:0]` elaborates to 2
                                // bits.
                                if let Some(fields) = flatten_struct_fields(
                                    data_type,
                                    &sub_local_params,
                                    &elab.typedefs,
                                    &elab.typedef_types,
                                ) {
                                    if !fields.is_empty() {
                                        tls_register_struct_layout(&assign.name.name, &fields);
                                        register_struct_member_elem_widths(
                                            &assign.name.name,
                                            data_type,
                                            &sub_local_params,
                                            &elab.typedef_types,
                                        );
                                    }
                                }
                                // §23.10.2: an override (`#(…)` or defparam) is
                                // an assignment to the formal's declared type,
                                // just as the default is: evaluated in its width
                                // (in the instantiating scope), wrapped, and
                                // given its signedness. The width is resolved
                                // HERE, against this instance's own parameters
                                // and type bindings: `#(.W(16), .P(16'hABCD))` on
                                // `parameter [W-1:0] P` needs the child's W.
                                let cur = &sub_local_params[&assign.name.name];
                                let conv = if let Some(t) = target {
                                    Some(convert_param_value(
                                        cur,
                                        ovr_exprs.get(&assign.name.name),
                                        scoped_eval_params,
                                        t,
                                    ))
                                } else if let Some(s) = no_range_signing.filter(|_| !cur.is_real) {
                                    let mut v = cur.clone();
                                    v.is_signed = s;
                                    Some(v)
                                } else {
                                    None
                                };
                                if let Some(v) = conv {
                                    sub_local_params.insert(assign.name.name.clone(), v);
                                }
                            }
                        }
                    }
                }
                // §23.10.2: an override of a BODY `parameter` converts the same
                // way, when its type's range is already known (a range over a
                // body localparam is not bound yet; that override keeps its
                // value rather than wrap to a guessed width).
                for it in sub_mod.items() {
                    let ModuleItem::ParameterDeclaration(pd) = it else {
                        continue;
                    };
                    let ParameterKind::Data {
                        data_type,
                        assignments,
                    } = &pd.kind
                    else {
                        continue;
                    };
                    let dims: &[PackedDimension] = match data_type {
                        DataType::IntegerVector { dimensions, .. }
                        | DataType::Implicit { dimensions, .. } => dimensions,
                        _ => &[],
                    };
                    let known = dims.iter().all(|d| match d {
                        PackedDimension::Range { left, right, .. } => {
                            is_const_expr(left, &sub_local_params)
                                && is_const_expr(right, &sub_local_params)
                        }
                        PackedDimension::Unsized(_) => false,
                    });
                    if !known {
                        continue;
                    }
                    for a in assignments {
                        let Some(cur) = sub_local_params
                            .get(&a.name.name)
                            .filter(|_| a.dimensions.is_empty())
                        else {
                            continue;
                        };
                        if let Some(t) = param_integral_target(
                            data_type,
                            &inst_types,
                            &sub_local_params,
                            &elab.typedefs,
                            &elab.typedef_types,
                        ) {
                            let v = convert_param_value(
                                cur,
                                ovr_exprs.get(&a.name.name),
                                scoped_eval_params,
                                t,
                            );
                            sub_local_params.insert(a.name.name.clone(), v);
                        } else if let DataType::Implicit {
                            signing: Some(s),
                            dimensions,
                            ..
                        } = data_type
                            && dimensions.is_empty()
                            && !cur.is_real
                        {
                            // §6.20.2: `signed`/`unsigned` with no range keeps
                            // the value's width but takes the declared sign, as
                            // for a header parameter.
                            let mut v = cur.clone();
                            v.is_signed = matches!(s, Signing::Signed);
                            sub_local_params.insert(a.name.name.clone(), v);
                        }
                    }
                }

                // The header's type-parameter bindings: step 1b installs its
                // own per-round overlay and must see the design's table.
                for (name, (old_w, old_dt)) in header_type_saves {
                    match old_dt {
                        Some(dt) => {
                            elab.typedef_types.insert(name.clone(), dt);
                        }
                        None => {
                            elab.typedef_types.remove(&name);
                        }
                    }
                    match old_w {
                        Some(width) => {
                            elab.typedefs.insert_if_changed(name, width);
                        }
                        None => {
                            elab.typedefs.remove(&name);
                        }
                    }
                }

                // 1b. Pre-register the sub-module's LOCAL typedef widths using
                // THIS instance's (bare-named) parameters, then install them in
                // TYPEDEFS_TLS so the body localparams' `$bits(<local typedef>)`
                // resolve. black-parrot declares its types via macros
                // (`declare_bp_be_dcache_wbuf_entry_s(caddr_width_mp, ways_mp)`,
                // `bp_pte_leaf_s` …) parameterised by header params; without this
                // the body localparam `r_entry_high_bits_lp = $bits(bp_pte_leaf_s)
                // - …` saw $bits = 0 and the subtraction wrapped to ~u32::MAX,
                // producing a multi-GB phantom width. A few passes converge
                // typedefs whose width depends on an earlier-resolved typedef.
                // Header params + overrides are authoritative; body
                // localparams computed below may be revised as local typedef
                // widths converge.
                let frozen_params: HashSet<String> = sub_local_params.keys().cloned().collect();
                // 1b+2 fixed point: a local typedef's field widths can use
                // body LOCALPARAMS (LP1 = A*B; logic [LP1-1:0] f2;) and a
                // localparam can use $bits(<local typedef>) — registering the
                // typedefs once against header params only froze the wrong
                // width into everything downstream (a parameterized struct
                // read $bits = 15 instead of 53). Alternate the two passes
                // until neither changes.
                let __tb = iprof_now();
                // Names of `parameter type` formals overridden by this
                // instantiation — their widths were bound by the override
                // pass; the DEFAULTS are registered per-round below so a
                // body localparam `$bits(T)` sees the default too (it read 0
                // otherwise while an overridden T worked).
                let ovr_type_names: std::collections::HashSet<&str> =
                    type_overrides.iter().map(|(n, _)| n.as_str()).collect();
                // §25.5 J2e: parameters of a BOUND interface instance are
                // visible through the port formal in the child's CONSTANT
                // contexts (`localparam D = c.DEPTH;`, `[c.DEPTH-1:0]`).
                // Seed `<formal>.<param>` entries from the already-elaborated
                // instance's prefixed parameters, so the fixpoint below and
                // every width resolution see them instead of a silent 0.
                // (Requires the interface instance to appear before this
                // child in source order — the overwhelmingly common layout.)
                interface_arrays::register_views(
                    &mut sub_interface_map,
                    &elab.unpacked_decl_dims,
                    sub_mod.ports(),
                    &sub_local_params,
                );
                for (formal, bound) in &sub_interface_map {
                    elab.interface_port_aliases
                        .insert(cat2(&inst_prefix, formal), bound.clone());
                }
                // A range scan of the bound instance's keys, not a pass over
                // the design-wide table per interface-port formal.
                for (formal, bound) in sub_interface_map.iter() {
                    let bound_prefix = format!("{}.", bound);
                    elab.for_each_parameter_with_prefix(&bound_prefix, |rest, v| {
                        sub_local_params
                            .entry(format!("{}.{}", formal, rest))
                            .or_insert_with(|| v.clone());
                    });
                }
                // The fixpoint only reads body parameter, localparam and
                // typedef declarations. A body with none (at any generate
                // depth) leaves `sub_local_params` as it is after one round,
                // so skip expanding its generate constructs, twice per
                // instance, just to find that out; the round's typedef-width
                // scope is still installed below.
                let body_declares = items_declare_params_or_typedefs(sub_mod.items());
                // §6.20.2: the instance's LOCAL types — type-parameter
                // defaults and body typedefs — so a body localparam declared
                // with one (`typedef logic signed [1:0] T; localparam T C = …`)
                // takes its signedness. Widths come from the per-round table
                // installed in TYPEDEFS_TLS below.
                let mut local_types = inst_types;
                for _ in 0..4 {
                    let body_items = if body_declares {
                        collect_effective_items_ref(sub_mod.items(), &sub_local_params)
                    } else {
                        Vec::new()
                    };
                    // §6.18 / §23.9: install only this instance's width
                    // overlay. The logged table updates the TLS snapshot by
                    // replay, avoiding a design-wide copy per instance.
                    let mut saved_tds: HashMap<String, Option<u32>> = HashMap::default();
                    for p_decl in sub_mod.params_and_body_types() {
                        if let ParameterKind::Type { assignments } = &p_decl.kind {
                            for a in assignments {
                                if ovr_type_names.contains(a.name.name.as_str()) {
                                    continue;
                                }
                                if let Some(def_dt) = &a.init {
                                    let w =
                                        resolve_type_width(def_dt, Some(&sub_local_params), Some(&elab.typedefs));
                                    saved_tds
                                        .entry(a.name.name.clone())
                                        .or_insert_with(|| elab.typedefs.get(&a.name.name).copied());
                                    elab.typedefs.insert_if_changed(a.name.name.clone(), w);
                                    // §20.7: its full definition too (see
                                    // `saved_type_shapes`), kept for the
                                    // rest of this instance.
                                    let resolved_dt =
                                        resolve_typedef_chain(def_dt, &elab.typedef_types).clone();
                                    if !saved_type_shapes.iter().any(|(n, _)| *n == a.name.name) {
                                        saved_type_shapes.push((
                                            a.name.name.clone(),
                                            tls_typedef_shape(&a.name.name),
                                        ));
                                    }
                                    let (shape, dims) =
                                        type_param_shape(def_dt, resolved_dt, &sub_local_params);
                                    tls_register_typedef_shape(&a.name.name, &shape, &dims);
                                }
                            }
                        }
                    }
                    for _ in 0..3 {
                        for it in body_items.iter().map(|c| &**c) {
                            if let ModuleItem::TypedefDeclaration(td) = it {
                                let w = resolve_type_width(
                                    &td.data_type,
                                    Some(&sub_local_params),
                                    Some(&elab.typedefs),
                                );
                                saved_tds
                                    .entry(td.name.name.clone())
                                    .or_insert_with(|| elab.typedefs.get(&td.name.name).copied());
                                elab.typedefs.insert_if_changed(td.name.name.clone(), w);
                            }
                        }
                    }
                    type_trace_tls_refresh("submodule_local", &elab.typedefs);
                    sync_typedefs_tls(&elab.typedefs);
                    // Leave the snapshot's local widths active during folding,
                    // while restoring the design's table exactly as before.
                    // These undo writes are replayed by its next sync.
                    for (name, old) in saved_tds {
                        match old {
                            Some(width) => {
                                elab.typedefs.insert_if_changed(name, width);
                            }
                            None => {
                                elab.typedefs.remove(&name);
                            }
                        }
                    }
                    if !body_declares {
                        break;
                    }
                    for it in body_items.iter().map(|c| &**c) {
                        if let ModuleItem::TypedefDeclaration(td) = it {
                            local_types.insert(td.name.name.clone(), td.data_type.clone());
                        }
                    }
                    // 2. Parameters from module items
                    let snapshot = sub_local_params.clone();
                    // A constant function of this instance casts to its own
                    // typedefs and type parameters (`w_t'(x)`, `T'(x)`).
                    let mut fn_types = local_types.clone();
                    fn_types.extend(type_overrides.iter().cloned());
                    CONST_FN_LOCAL_TYPES.with(|c| *c.borrow_mut() = Some(fn_types));
                    add_params_from_items(
                        sub_mod.items(),
                        &mut sub_local_params,
                        elab,
                        &frozen_params,
                        &local_types,
                    );
                    if sub_local_params == snapshot {
                        break;
                    }
                }
                iprof_since("param_typedef_fixpoint", __tb);

                // §23.2.2.4: a port default is a constant expression of the
                // CHILD's scope (`input logic i = F` reads the child's own
                // parameter `F`, per instance). The port map holds PARENT-scope
                // actuals, so a default that names anything is folded to its
                // value here; a literal default is kept as written.
                for (name, def, is_string) in port_defaults {
                    let child_const = is_const_expr(&def, &sub_local_params);
                    if !child_const && !is_const_expr(&def, &elab.parameters) {
                        return Err(format!(
                            "Value assigned to default of port '{}' of module '{}' must be a constant expression (§23.2.2.4)",
                            name, sub_mod_name
                        ));
                    }
                    let mut names = Vec::new();
                    collect_ident_names(&def, &mut names);
                    let actual = if names.is_empty() || is_string || !child_const {
                        def
                    } else {
                        let v = eval_const_expr_val(&def, &sub_local_params);
                        const_value_literal(&v, def.span).unwrap_or(def)
                    };
                    port_map.insert(name, actual);
                }

                let __tp = iprof_now();
                cache.prepared.enter_instance(&inst_prefix);
                let prepared_sub = prepare_module_items(
                    sub_mod,
                    definitions,
                    &sub_local_params,
                    &elab.typedefs,
                    cache,
                    param_scope,
                );
                iprof_since("prepare_module_items", __tp);

                // §6.20.2 / §23.10 / §25: an unpacked-array BODY parameter or
                // localparam of this instance (`localparam int unsigned LA [3]
                // = '{7, 8, 9};` in the child module's — or interface's —
                // body). The header site above registered header params under
                // the instance prefix, but body declarations were only folded
                // to ONE scalar by add_params_from_items, so a hierarchical
                // `u.LA[1]` read a bit of the folded pattern and `$size(u.LA)`
                // saw no shape. Register each element under the
                // instance-prefixed key, mirroring the header site; the scalar
                // fold stays in sub_local_params for the child's own
                // const-eval. Runs for the top module too (prefix ""), where
                // it re-registers what the module-body pass already recorded.
                for it in sub_mod.items() {
                    let (ModuleItem::ParameterDeclaration(pd)
                    | ModuleItem::LocalparamDeclaration(pd)) = it
                    else {
                        continue;
                    };
                    let ParameterKind::Data {
                        data_type,
                        assignments,
                    } = &pd.kind
                    else {
                        continue;
                    };
                    for assign in assignments {
                        if assign.dimensions.is_empty() {
                            continue;
                        }
                        let snapshot = sub_local_params.clone();
                        let override_expr = ovr_exprs.get(&assign.name.name);
                        let init = override_expr.or(assign.init.as_ref());
                        let packed = if override_expr.is_some_and(|e| {
                            !matches!(
                                peel_unpacked_typed_pattern(e).kind,
                                ExprKind::AssignmentPattern(_) | ExprKind::Concatenation(_)
                            )
                        }) {
                            snapshot.get(&assign.name.name)
                        } else {
                            None
                        };
                        // §6.20.2: with this body's own types inlined, as
                        // the constant fold above evaluated the elements.
                        let inlined = inline_instance_typedefs(data_type);
                        if array_params::register(
                            elab,
                            &inst_prefix,
                            &assign.name.name,
                            &assign.dimensions,
                            init,
                            packed,
                            inlined.as_ref().unwrap_or(data_type),
                            &snapshot,
                            if override_expr.is_some() {
                                scoped_eval_params
                            } else {
                                &snapshot
                            },
                        ) && let Some(whole) =
                            elab.parameters.get(&cat2(&inst_prefix, &assign.name.name))
                        {
                            sub_local_params.insert(assign.name.name.clone(), whole.clone());
                        }
                    }
                }

                // Inline all resolved parameters into global map with prefix
                for (name, val) in &sub_local_params {
                    if name.contains('[') && elab.parameters.contains_key(&cat2(&inst_prefix, name)) {
                        continue;
                    }
                    let full_name = cat2(&inst_prefix, &name);
                    elab.set_param(line!(), full_name.clone(), val.clone());
                    // Also add as a signal for simulation access
                    signals_insert_traced(
                        &mut elab.signals,
                        line!(),
                        full_name.clone(),
                        Signal {
                            is_const: false,
                            name: full_name.into(),
                            width: val.width,
                            is_signed: val.is_signed,
                            is_real: val.is_real,
                            direction: None,
                            value: val.clone().into(),
                            type_name: None,
                        },
                    );
                }

                // Build the merged param map ONCE — used for both port-signal
                // declaration and the later sub-item processing. Skip the
                // parent clone when local_params is empty (top-level case).
                // §6.18/§23.10: this sub-module's own typedef names — used to
                // rename type references to their instance-scoped keys.
                let mut sub_typedef_names_all: std::collections::HashSet<String> = prepared_sub
                    .effective_items
                    .iter()
                    .filter_map(|it| match it {
                        ModuleItem::TypedefDeclaration(td) => Some(td.name.name.clone()),
                        ModuleItem::ClassDeclaration(cd) => Some(cd.name.name.clone()),
                        _ => None,
                    })
                    .collect();
                for parameter in sub_mod.params_and_body_types() {
                    if let ParameterKind::Type { assignments } = &parameter.kind {
                        sub_typedef_names_all
                            .extend(assignments.iter().map(|a| a.name.name.clone()));
                    }
                }
                record_param_decl_types(
                    elab,
                    sub_mod
                        .params()
                        .iter()
                        .chain(item_param_decls(&prepared_sub.effective_items)),
                    |n| cat2(&inst_prefix, n),
                    |dt| {
                        let folded = fold_packed_dims_with(dt, &sub_local_params, &|_, _| true);
                        instance_decl_type(
                            &mut cache.decl_types,
                            folded.as_ref().unwrap_or(dt),
                            &sub_typedef_names_all,
                            &inst_prefix,
                            sub_mod.name(),
                        )
                    },
                );
                // §23.4: only a lexically nested module inherits the
                // parent's array element names. Its other children can still
                // use them in their actual parameters above. Share the compact
                // inherited table among siblings of an array-bearing parent.
                let lexical_child = matches!(sub_mod, Definition::Module(m)
                    if m.lexical_parent.as_deref() == Some(source_def.name()));
                let inherited = if has_header_elements && !lexical_child {
                    nonlexical_params.get_or_init(|| local_params.iter()
                        .filter(|(key, _)| key.split_once('[').is_none_or(|(base, _)| base.contains("::") || base.contains('.')))
                        .map(|(k, v)| (k.clone(), v.clone())).collect())
                } else { local_params };
                let mut sub_merged_params: HashMap<String, Value> = if inherited.is_empty() {
                    sub_local_params.clone()
                } else if sub_local_params.is_empty() {
                    inherited.clone()
                } else {
                    let mut m = inherited.clone();
                    for (k, v) in &sub_local_params {
                        m.insert(k.clone(), v.clone());
                    }
                    m
                };
                // `local_params` holds the parent's scope and the table
                // entries it names; add those this child names (#740).
                param_scope.extend_scope(sub_mod, definitions, &mut sub_merged_params);

                // §7.2.1: struct-typed header and generated body parameters —
                // register the field layout under the SCOPED name so runtime
                // member selects (`C.a` inside the instance → "c0.C" + field
                // slice) resolve; without it they read x.
                let mut struct_member_entries: Vec<(String, Value, Vec<(String, u32, u32)>)> =
                    Vec::new();
                for p_decl in
                    sub_mod
                        .params()
                        .iter()
                        .chain(
                            prepared_sub
                                .effective_items
                                .iter()
                                .filter_map(|item| match item {
                                    ModuleItem::ParameterDeclaration(pd)
                                    | ModuleItem::LocalparamDeclaration(pd) => Some(pd),
                                    _ => None,
                                }),
                        )
                {
                    if let ParameterKind::Data {
                        data_type,
                        assignments,
                    } = &p_decl.kind
                    {
                        // The instance's own types first (#680): the table
                        // has the first instance's only once it settles.
                        let inlined = inline_body_typedefs(data_type, &local_types);
                        // §7.4.1 / §7.4.5: body constants need the same scoped
                        // packed-element geometry as header parameters. Resolve
                        // local typedefs and dimensions in this instance.
                        for assign in assignments {
                            if assign.dimensions.is_empty() {
                                register_packed_param_index(
                                    elab,
                                    &cat2(&inst_prefix, &assign.name.name),
                                    inlined.as_ref().unwrap_or(data_type),
                                    Some(&sub_merged_params),
                                );
                            }
                        }
                        if let Some(fields) = flatten_struct_fields(
                            inlined.as_ref().unwrap_or(data_type),
                            &sub_merged_params,
                            &elab.typedefs,
                            &elab.typedef_types,
                        ) {
                            if !fields.is_empty() {
                                for assign in assignments {
                                    let scoped = cat2(&inst_prefix, &assign.name.name);
                                    // §6.20.2: each member is a constant of
                                    // its own. Register it scoped for the
                                    // simulator's table and bare for this
                                    // instance's signature rewrite
                                    // (`param_expr_map` below), so a
                                    // function returning `logic
                                    // [Cfg.VLEN-1:0]` is sized by the member
                                    // and not left as `.VLEN` of a literal.
                                    if let Some(val) = elab.parameters.get(&scoped).cloned() {
                                        register_struct_param_members(
                                            |k, v| {
                                                elab.set_param(line!(), k, v);
                                            },
                                            &scoped,
                                            &val,
                                            &fields,
                                        );
                                        struct_member_entries.push((
                                            assign.name.name.clone(),
                                            val,
                                            fields.clone(),
                                        ));
                                    }
                                    elab.packed_struct_fields.insert(scoped, fields.clone());
                                    tls_register_struct_layout(&assign.name.name, &fields);
                                }
                            }
                        }
                    }
                }
                for (name, val, fields) in struct_member_entries {
                    register_struct_param_members(
                        |k, v| {
                            params_insert_traced(&mut sub_merged_params, line!(), k, v);
                        },
                        &name,
                        &val,
                        &fields,
                    );
                }

                // Bind NON-overridden `parameter type` DEFAULTS as scoped
                // typedefs, resolving their width against the sub-instance's
                // params. rr_arb_tree declares
                //   parameter type idx_t = logic [IdxWidth-1:0]
                // and never overrides it, so without this idx_t (used for
                // rr_q/idx_o/index_nodes) falls back to the 32-bit default —
                // the index-node concatenations then truncate and idx_o reads 0,
                // so the wormhole arbiter selects the wrong input and the router
                // drops the flit. Uses sub_merged_params (has IdxWidth), unlike
                // the override pass above which only sees parent params. Prior
                // typedef entries are saved to the same list for restore.
                let overridden_type_names: std::collections::HashSet<&str> =
                    type_overrides.iter().map(|(n, _)| n.as_str()).collect();
                for p_decl in sub_mod.params_and_body_types() {
                    if let ParameterKind::Type { assignments } = &p_decl.kind {
                        for a in assignments {
                            if overridden_type_names.contains(a.name.name.as_str()) {
                                continue;
                            }
                            let Some(def_dt) = &a.init else {
                                continue;
                            };
                            let resolved_dt =
                                resolve_typedef_chain(def_dt, &elab.typedef_types).clone();
                            let w = resolve_type_width(
                                &resolved_dt,
                                Some(&sub_merged_params),
                                Some(&elab.typedefs),
                            );
                            saved_type_binds.push((
                                a.name.name.clone(),
                                elab.typedefs.get(&a.name.name).copied(),
                                elab.typedef_types.get(&a.name.name).cloned(),
                            ));
                            typedefs_insert_traced(
                                &mut elab.typedefs,
                                "insert:submodule_type_param_default",
                                a.name.name.clone(),
                                w,
                            );
                            elab.typedef_types.insert(a.name.name.clone(), resolved_dt);
                        }
                    }
                }
                // String ports keep their dynamic type when their literal is
                // substituted. Their storage allocation is not a packed width.
                let mut string_ports = HashSet::default();
                let mut resolved_two_state_ports = HashSet::default();
                match sub_mod.ports() {
                    PortList::Ansi(ports) => {
                        for port in ports {
                            if prepared_sub.interface_ports.contains(&port.name.name) {
                                continue;
                            }
                            let width = port
                                .data_type
                                .as_ref()
                                .map(|dt| {
                                    resolve_type_width(
                                        dt,
                                        Some(&sub_merged_params),
                                        Some(&elab.typedefs),
                                    )
                                })
                                .unwrap_or(1);
                            let sig_name = cat2(&inst_prefix, &port.name.name);
                            // §6.6.7: resolve REALNESS through the typedef
                            // table — a nettype port formal (`inout rnet p`,
                            // rnet = `nettype real`) is a real signal. The
                            // bare is_type_real left it integral, so `%f` on
                            // the formal printed raw bits and a real consumer
                            // through it could read 0.0.
                            let is_real = port
                                .data_type
                                .as_ref()
                                .map(|dt| is_type_real_resolved(dt, &elab.typedef_types))
                                .unwrap_or(false);
                            // §6.18: the port's unpacked dimensions may come
                            // from its TYPEDEF (`typedef t_byte t_word [0:3];
                            // input t_word din;`), not the declarator. The
                            // TOP-module path consults typedef_unpacked_dims
                            // for exactly this; here only `port.dimensions`
                            // was used, so an INLINED child's typedef-array
                            // port registered as a plain scalar — the array
                            // never existed, its connection silently carried
                            // nothing, and (under `default_nettype none`) the
                            // actual was then reported as an implicit net
                            // (GitHub xezim#106).
                            let effective_port_dims: Vec<UnpackedDimension> =
                                if port.dimensions.is_empty() {
                                    match port.data_type.as_ref() {
                                        Some(DataType::TypeReference { name, .. }) => {
                                            lookup_scoped_type(name, &elab.typedef_unpacked_dims)
                                                .cloned()
                                                .unwrap_or_default()
                                        }
                                        _ => Vec::new(),
                                    }
                                } else {
                                    port.dimensions.clone()
                                };
                            let effective_port_dims = normalize_unpacked_dims(
                                &effective_port_dims,
                                &sub_merged_params,
                                &elab.typedef_types,
                            );
                            let port_shape =
                                fixed_unpacked_shape(&effective_port_dims, &sub_merged_params)
                                    .unwrap_or_default();
                            if let Some(dims) =
                                declared_unpacked_dims(&effective_port_dims, &sub_merged_params)
                            {
                                elab.unpacked_decl_dims
                                    .insert(sig_name.clone(), dims.clone());
                                if dims.first().is_some_and(|(l, r)| l > r) {
                                    elab.descending_arrays.insert(sig_name.clone());
                                }
                            }
                            // Register the packed-struct field layout for a
                            // struct-typed port so a member write to the port's
                            // internal signal (`dut.out.a` for an `output
                            // sample_t out`) resolves the field — otherwise the
                            // write was dropped and the output stayed X.
                            //
                            // §7.2: not for an UNPACKED struct, which is stored
                            // member-wise (see `register_unpacked_aggregate`
                            // below) like the root arm's ports. A layout there
                            // sent the child's own process writes (`o = '{..}`,
                            // `o.a = v`) into slices of the width-only
                            // container, which the parent never reads.
                            if let Some(dt) = &port.data_type {
                                let mut struct_w: u32 = 0;
                                let member_wise = inlined_port_member_wise(
                                    dt,
                                    &elab.typedef_types,
                                    &saved_type_binds,
                                );
                                let fields = if member_wise {
                                    None
                                } else {
                                    flatten_struct_fields(
                                        dt,
                                        &sub_merged_params,
                                        &elab.typedefs,
                                        &elab.typedef_types,
                                    )
                                };
                                if let Some(fields) = fields {
                                    if !fields.is_empty() {
                                        struct_w =
                                            fields.iter().map(|(_, o, w)| o + w).max().unwrap_or(0);
                                        tls_register_struct_layout(&sig_name, &fields);
                                        elab.packed_struct_fields.insert(sig_name.clone(), fields);
                                    }
                                }
                                // Per-MEMBER packed-array element widths, keyed
                                // `<signal>.<member>`, so `cnfg.SEC[0] <= v`
                                // slices a whole element instead of one bit
                                // when the member is itself a packed array
                                // (`u32_t [4:0] SEC`). The body-declaration
                                // paths register these; this PORT path recorded
                                // only the struct's field offsets, so a struct
                                // arriving through a port lost the metadata and
                                // every element write became a bit write.
                                {
                                    let member_dt =
                                        resolve_typedef_chain(dt, &elab.typedef_types).clone();
                                    if let DataType::Struct(su) = &member_dt {
                                        for m in &su.members {
                                            let (ew, fd) = packed_member_meta(
                                                &m.data_type,
                                                &sub_merged_params,
                                                &elab.typedefs,
                                                &elab.typedef_types,
                                            );
                                            for mdecl in &m.declarators {
                                                let key =
                                                    format!("{}.{}", sig_name, mdecl.name.name);
                                                if let Some(ew) = ew {
                                                    elab.packed_signal_elem_widths
                                                        .insert(key.clone(), ew);
                                                }
                                                if let Some(fd) = &fd {
                                                    elab.packed_full_dims.insert(key, fd.clone());
                                                }
                                            }
                                        }
                                    }
                                }
                                // Packed multi-D PORT (`output [3:0][7:0] opv`):
                                // record the element width and dimensions like a
                                // net/variable declaration would, so element and
                                // element-RANGE selects on the inlined signal
                                // (`u_s.opv[2:1] = …` from the submodule's own
                                // assigns) slice elements instead of bits.
                                // A port declared with a TYPEDEF'd packed multi-D
                                // type (`typedef logic [1:0][3:0] pair_t; input
                                // pair_t p`) carries no dimensions of its own, so
                                // both helpers bail on the `TypeReference` and the
                                // port registered nothing — `p[i]` then degraded to
                                // a one-BIT select exactly as an unregistered inline
                                // `logic [1:0][3:0]` port used to. Resolve the
                                // typedef and retry; the inline form already works,
                                // which is what made this look type-specific.
                                let resolved_dt =
                                    resolve_typedef_chain(dt, &elab.typedef_types).clone();
                                if matches!(
                                    resolved_dt,
                                    DataType::Simple { kind: SimpleType::String, .. }
                                ) {
                                    string_ports.insert(port.name.name.as_str());
                                }
                                if matches!(dt, DataType::TypeReference { .. })
                                    && is_type_two_state_resolved(&resolved_dt, &elab.typedef_types)
                                {
                                    resolved_two_state_ports.insert(port.name.name.as_str());
                                }
                                // §6.11.2, §23.3.3.2: a 2-state formal drops
                                // X and Z on every write, including the
                                // connection assign of a formal that keeps its
                                // own storage (`input var bit [3:0] b` bound to
                                // a 4-state net, a wider actual, an
                                // expression). Only body declarations were
                                // registered, so the formal kept the actual's
                                // X and Z bits.
                                if !is_real
                                    && is_type_two_state_resolved(&resolved_dt, &elab.typedef_types)
                                {
                                    elab.two_state_signals.insert(sig_name.clone());
                                }
                                if let Some(ew) =
                                    packed_inner_elem_width(dt, &sub_merged_params, &elab.typedefs)
                                        .or_else(|| {
                                            // §7.4.1: dimensions carried by a
                                            // typedef of a named element type
                                            // (`typedef lane_t [0:1] arr_t;`).
                                            let one = bare_typedef_step(dt, &elab.typedef_types)?;
                                            packed_inner_elem_width(
                                                &one,
                                                &sub_merged_params,
                                                &elab.typedefs,
                                            )
                                        })
                                        .or_else(|| {
                                            packed_inner_elem_width(
                                                &resolved_dt,
                                                &sub_merged_params,
                                                &elab.typedefs,
                                            )
                                        })
                                {
                                    elab.packed_signal_elem_widths.insert(sig_name.clone(), ew);
                                }
                                // A TYPEDEF'd element type with declared dims
                                // (`u7_t [4:0][1:0] a`): chain the declared dims
                                // with the typedef's like the top-level path does.
                                // Resolving the typedef first kept only ITS
                                // dimension, so `foreach (a[i, j])` on an inlined
                                // instance (every top under `__xezim_multi_top`)
                                // walked the 70 bits instead of the 10 elements.
                                if let Some(fdims) = packed_full_dims_of(dt, &sub_merged_params)
                                    .or_else(|| {
                                        packed_full_dims_chained(
                                            dt,
                                            &sub_merged_params,
                                            &elab.typedef_types,
                                        )
                                    })
                                    .or_else(|| {
                                        packed_full_dims_of(&resolved_dt, &sub_merged_params)
                                    })
                                {
                                    elab.packed_full_dims.insert(sig_name.clone(), fdims);
                                }
                                // Packed array of a STRUCT TYPEDEF as a PORT
                                // (`output some_t [1:0] o`). Both helpers above
                                // return None for a TypeReference base, so such a
                                // port registered no element metadata: the
                                // submodule's own `o[0].member = …` writes had no
                                // element width to slice by and every member of
                                // every element stayed X.
                                if let Some(fdims) =
                                    packed_typedef_array_dims(dt, struct_w, &sub_merged_params)
                                {
                                    let total: i64 =
                                        fdims.iter().map(|(l, r)| (l - r).abs() + 1).product();
                                    let (ol, orr) = fdims[0];
                                    let outer = (ol - orr).abs() + 1;
                                    if outer > 0 && total > 0 {
                                        elab.packed_signal_elem_widths
                                            .insert(sig_name.clone(), (total / outer) as u32);
                                    }
                                    elab.packed_full_dims.insert(sig_name.clone(), fdims);
                                }
                            }
                            if let Some(net_type) = ansi_port_net_type(port) {
                                register_net_type(
                                    elab,
                                    &sig_name,
                                    net_type,
                                    port.data_type.as_ref(),
                                );
                            }
                            if port_shape.is_empty() {
                                // §7.2: unpacked-struct port of an INLINED
                                // instance — register the member leaves too,
                                // so `<inst>.<port>.<member>` is a real signal
                                // (see the module-port arm for the symptom).
                                // A member-wise one also records its declared
                                // type, as the root arm does: the procedural
                                // struct copy and `%p` look it up there.
                                if let Some(dt) = &port.data_type {
                                    register_unpacked_aggregate(elab, &sig_name, dt);
                                    if inlined_port_member_wise(
                                        dt,
                                        &elab.typedef_types,
                                        &saved_type_binds,
                                    ) {
                                        elab.var_decl_types.insert_shared(
                                            sig_name.clone(),
                                            instance_decl_type(
                                                &mut cache.decl_types,
                                                dt,
                                                &sub_typedef_names_all,
                                                &inst_prefix,
                                                sub_mod.name(),
                                            ),
                                        );
                                    } else if names_packed_array_or_struct(dt, &elab.typedef_types)
                                    {
                                        // §7.4.1: a port that is a packed array
                                        // of a named type (`lane_t [0:8] p`)
                                        // keeps its declared type, as a variable
                                        // does: an element of a named signed
                                        // type is signed (aionhw/xezim#1107).
                                        if !elab.var_decl_types.contains_key(&sig_name) {
                                            elab.var_decl_types.insert_shared(
                                                sig_name.clone(),
                                                instance_decl_type(
                                                    &mut cache.decl_types,
                                                    dt,
                                                    &sub_typedef_names_all,
                                                    &inst_prefix,
                                                    sub_mod.name(),
                                                ),
                                            );
                                        };
                                    }
                                }
                                // §23.2.2.4: an output-variable default is its
                                // declaration initializer.  Inlined instances
                                // must preserve it just as the root module does.
                                let init_val = match (&port.direction, &port.default) {
                                    (Some(PortDirection::Output), Some(def)) => {
                                        let v = eval_const_expr(def, &sub_merged_params);
                                        Some(if is_real {
                                            Value::from_f64(v as f64)
                                        } else {
                                            Value::from_u64(v, width).resize(width)
                                        })
                                    }
                                    _ => None,
                                };
                                signals_insert_traced(
                                    &mut elab.signals,
                                    line!(),
                                    sig_name.clone(),
                                    Signal {
                                        is_const: false,
                                        name: sig_name.clone().into(),
                                        width,
                                        is_signed: port
                                            .data_type
                                            .as_ref()
                                            .map(|dt| is_type_signed_resolved(dt, &elab.typedef_types))
                                            .unwrap_or(false),
                                        is_real,
                                        direction: port.direction,
                                        value: init_val.unwrap_or_else(|| {
                                            default_port_value(
                                                port.direction,
                                                port.data_type.as_ref(),
                                                width,
                                                is_real,
                                                ansi_port_net_type(port),
                                            )
                                        }).into(),
                                        type_name: port
                                            .data_type
                                            .as_ref()
                                            .and_then(get_type_name)
                                            .map(SharedName::from),
                                    },
                                );
                            } else {
                                register_fixed_unpacked_array(
                                    elab,
                                    &sig_name,
                                    &port_shape,
                                    width,
                                    port.data_type
                                        .as_ref()
                                        .map(is_type_two_state)
                                        .unwrap_or(false),
                                );
                                if let Some(dt) = &port.data_type {
                                    if matches!(
                                        port.direction,
                                        Some(PortDirection::Input | PortDirection::Inout)
                                    ) {
                                        mark_array_z_init_if_4state(elab, &sig_name, dt);
                                    }
                                    elab.var_decl_types.insert_shared(
                                        sig_name,
                                        instance_decl_type(
                                            &mut cache.decl_types,
                                            &dt,
                                            &sub_typedef_names_all,
                                            &inst_prefix,
                                            sub_mod.name(),
                                        ),
                                    );
                                }
                            }
                        }
                    }
                    // Non-ANSI: registered after the local typedefs, below.
                    PortList::NonAnsi(_) | PortList::Empty => {}
                }

                iprof_since("ck3_after_hdrparams", __th);
                // sub_merged_params already built above for port declarations.
                iprof_since("ck4_before_loopB", __th);
                for sub_item in &prepared_sub.effective_items {
                    if let ModuleItem::TypedefDeclaration(td) = sub_item {
                        if let DataType::Enum(et) = &td.data_type {
                            let enum_signed =
                                is_type_signed_resolved(&td.data_type, &elab.typedef_types);
                            let base_width = et
                                .base_type
                                .as_ref()
                                .map(|bt| {
                                    resolve_type_width(
                                        bt,
                                        Some(&sub_merged_params),
                                        Some(&elab.typedefs),
                                    )
                                })
                                .unwrap_or(32);
                            // §6.19.6: the member LIST of this instance's enum,
                            // for `.name()/.first()/.num()` on its variables.
                            // Submodule enums never reach `process_typedef`, so
                            // `enum_members` had no entry for them at all —
                            // `.name()` then fell back to a design-wide
                            // by-value scan (a sibling's `PB` for our `SB`),
                            // and `.num()` read 0.
                            let mut inst_members: Vec<(String, u64)> = Vec::new();
                            for (nm, val, v) in enums::enum_members_values(
                                et,
                                base_width,
                                enum_signed,
                                &sub_merged_params,
                            ) {
                                inst_members.push((nm.clone(), val));
                                // Don't clobber an already-registered member
                                // with a DIFFERENT value: xezim's parameter
                                // namespace is flat, but per LRM §22.1.4 +
                                // §23.6 an enum member declared inside a
                                // submodule's typedef should NOT pollute the
                                // bare-name lookup used by sibling submodules.
                                // First-declared wins; a same-name same-value
                                // re-declaration is a no-op. Without this,
                                // testbench typedefs like
                                // `uvmt_cv32e40p_step_compare::state_e`
                                // (which has INIT=0, IDLE=1, …) overwrite
                                // `prefetch_state_e::IDLE`=0 / `rvvi_c_e::IDLE`=0,
                                // and every other module's `case` arm that
                                // references IDLE matches the wrong arm.
                                let prior = elab.parameters.get(&nm).cloned();
                                let should_insert = match &prior {
                                    None => true,
                                    Some(p) if v.has_xz() || p.has_xz() => {
                                        p.width == v.width && p.case_eq(&v).to_u64() == Some(1)
                                    }
                                    Some(p) => p.to_u64() == Some(val),
                                };
                                if should_insert {
                                    elab.set_param(line!(), nm.clone(), v.clone());
                                    signals_insert_traced(
                                        &mut elab.signals,
                                        line!(),
                                        nm.clone(),
                                        Signal {
                                            is_const: false,
                                            name: nm.clone().into(),
                                            width: base_width,
                                            is_signed: enum_signed,
                                            direction: None,
                                            value: v.clone().into(),
                                            type_name: None,
                                            is_real: false,
                                        },
                                    );
                                }
                                // INSTANCE-scoped key, unconditionally: a
                                // member whose value depends on this
                                // instance's parameters (`MAGIC = V`) loses
                                // the first-wins race above, and every later
                                // instance then read the FIRST instance's
                                // value. Statement identifiers already
                                // resolve through the instance prefix (that
                                // is how a plain parameter is per-instance),
                                // so the scoped entry wins where it matters
                                // and the bare slot stays the design-wide
                                // §23.6 fallback.
                                let sc = cat2(&inst_prefix, &nm);
                                elab.set_param(line!(), sc.clone(), v.clone());
                                signals_insert_traced(
                                    &mut elab.signals,
                                    line!(),
                                    sc.clone(),
                                    Signal {
                                        is_const: false,
                                        name: sc.into(),
                                        width: base_width,
                                        is_signed: enum_signed,
                                        direction: None,
                                        value: v.into(),
                                        type_name: None,
                                        is_real: false,
                                    },
                                );
                            }
                            // Keyed by the INSTANCE-scoped typedef name (the
                            // signal's `type_name` is scoped to match); the
                            // bare key is a first-wins fallback only.
                            elab.enum_members
                                .insert(cat2(&inst_prefix, &td.name.name), inst_members.clone());
                            elab.enum_members
                                .entry(td.name.name.clone())
                                .or_insert(inst_members);
                            // Prior-or-keep restore — see the non-enum twin below.
                            saved_type_binds.push((
                                td.name.name.clone(),
                                elab.typedefs.get(&td.name.name).copied(),
                                elab.typedef_types
                                    .get(&td.name.name)
                                    .cloned()
                                    .or_else(|| Some(td.data_type.clone())),
                            ));
                            typedefs_insert_traced(
                                &mut elab.typedefs,
                                "insert:submodule_typedef_enum",
                                td.name.name.clone(),
                                base_width,
                            );
                            elab.typedef_types
                                .insert(td.name.name.clone(), td.data_type.clone());
                            // §6.18/§23.10: the INSTANCE-scoped key. The bare
                            // key is last-writer-wins across differently
                            // parameterized instances of the same module, so a
                            // subroutine signature resolved later by name read
                            // the LAST instance's width — see below, where the
                            // signature's type references are renamed to this
                            // key.
                            typedefs_insert_traced(
                                &mut elab.typedefs,
                                "insert:submodule_typedef_enum_scoped",
                                cat2(&inst_prefix, &td.name.name),
                                base_width,
                            );
                            elab.typedef_types
                                .entry(cat2(&inst_prefix, &td.name.name))
                                .or_insert_with(|| {
                                    scope_local_typerefs(
                                        &td.data_type,
                                        &sub_typedef_names_all,
                                        &inst_prefix,
                                    )
                                });
                        } else {
                            let w = resolve_type_width(
                                &td.data_type,
                                Some(&sub_merged_params),
                                Some(&elab.typedefs),
                            );
                            // The BARE key must hold this module's local
                            // typedef only for the DURATION of this instance's
                            // inlining (its own body and children resolve it),
                            // then restore: leaving it permanently clobbered
                            // the $unit/global entry, so a LATER module with
                            // no local `t` sized its `t v;` from whichever
                            // instance inlined last (order-dependent 64 vs 16).
                            // Same save/restore rail the type-parameter
                            // overrides use.
                            // The TYPE slot is prior-or-KEEP: the saved value
                            // is what the slot held before this instance — or,
                            // for the FIRST instance, this instance's own type
                            // — so the restore hands post-inlining consumers
                            // (the struct-member machinery reads the bare slot
                            // AFTER inlining; removing it broke every
                            // struct-typed member) the same first-declared
                            // fallback as before, while the overwrite below
                            // makes the slot context-correct DURING inlining.
                            // With first-wins (`entry().or_insert`) here, a
                            // second differently-parameterized instance
                            // resolved its `#(.T(rec_t))` overrides and its
                            // own member writes through the FIRST instance's
                            // baked layout — 39-bit field offsets in a 68-bit
                            // struct, order-dependent on instance order.
                            saved_type_binds.push((
                                td.name.name.clone(),
                                elab.typedefs.get(&td.name.name).copied(),
                                elab.typedef_types
                                    .get(&td.name.name)
                                    .cloned()
                                    .or_else(|| Some(td.data_type.clone())),
                            ));
                            typedefs_insert_traced(
                                &mut elab.typedefs,
                                "insert:submodule_typedef",
                                td.name.name.clone(),
                                w,
                            );
                            // Instance-scoped key — see the enum branch above.
                            typedefs_insert_traced(
                                &mut elab.typedefs,
                                "insert:submodule_typedef_scoped",
                                cat2(&inst_prefix, &td.name.name),
                                w,
                            );
                            // Packed ELEMENT width, both keys, mirroring the
                            // width entries: the bytecode compiler's packed
                            // element splice/extract on typedef'd locals
                            // resolves through this table, and a submodule
                            // typedef recorded only its total width, so a
                            // `y[i] = …` on a packed-of-packed local bailed
                            // to the 1-bit select path.
                            if let Some(ew) = packed_inner_elem_width(
                                &td.data_type,
                                &sub_merged_params,
                                &elab.typedefs,
                            ) {
                                elab.typedef_elem_widths.insert(td.name.name.clone(), ew);
                                elab.typedef_elem_widths
                                    .insert(cat2(&inst_prefix, &td.name.name), ew);
                            }
                            // Register the TYPE too (not just its width) so a
                            // struct/union member access (`s.m0`) on a submodule
                            // variable of this typedef can resolve to its bit
                            // layout. Only the width was recorded before, so
                            // `flatten_struct_fields` below found nothing and the
                            // member cont-assign was silently dropped (struct
                            // stayed X). Plain insert: THIS instance's type,
                            // for the duration of its inlining (see the rail
                            // comment above); first-declared still wins the
                            // post-inlining fallback via the restore.
                            elab.typedef_types
                                .insert(td.name.name.clone(), td.data_type.clone());
                            elab.typedef_types
                                .entry(cat2(&inst_prefix, &td.name.name))
                                .or_insert_with(|| {
                                    scope_local_typerefs(
                                        &td.data_type,
                                        &sub_typedef_names_all,
                                        &inst_prefix,
                                    )
                                });
                            // §6.18/§7.4: its UNPACKED dimensions under the
                            // instance-scoped key as well, which is what this
                            // instance's subroutine signatures name. Missing,
                            // a function returning `typedef u8_t u8a_t [0:7]`
                            // returned one element and `f = mk(v)` read x.
                            let scoped = cat2(&inst_prefix, &td.name.name);
                            let mut udims = td.dimensions.clone();
                            if let DataType::TypeReference {
                                name, dimensions, ..
                            } = &td.data_type
                                && dimensions.is_empty()
                            {
                                let base = name
                                    .scopes
                                    .is_empty()
                                    .then(|| {
                                        elab.typedef_unpacked_dims
                                            .get(&cat2(&inst_prefix, &name.name.name))
                                    })
                                    .flatten()
                                    .or_else(|| {
                                        lookup_scoped_type(name, &elab.typedef_unpacked_dims)
                                    });
                                if let Some(bd) = base {
                                    udims.extend(bd.iter().cloned());
                                }
                            }
                            // The BARE key holds them for the duration of the
                            // inlining too, like the width and type slots
                            // above: the body's declarations (`u8a_t g;`) look
                            // the bare name up, and another module's same-named
                            // typedef must not shape them.
                            saved_unpacked_dims.push((
                                td.name.name.clone(),
                                elab.typedef_unpacked_dims.get(&td.name.name).cloned(),
                            ));
                            if udims.is_empty() {
                                elab.typedef_unpacked_dims.remove(&td.name.name);
                            } else {
                                elab.typedef_unpacked_dims
                                    .insert(td.name.name.clone(), udims.clone());
                                elab.typedef_unpacked_dims.insert(scoped, udims);
                            }
                        }
                    }
                }
                // §23.2.2.1/§6.18: a non-ANSI port declaration lives in the
                // BODY, so it may name a typedef declared there (`typedef
                // logic [7:0] u8_t; output u8_t [0:7] o;`). Register the
                // ports after this instance's typedefs (loop B above): sized
                // before them, the local type fell back to 32 bits per element.
                if let PortList::NonAnsi(_) = sub_mod.ports() {
                    for sub_item in &prepared_sub.effective_items {
                        if let ModuleItem::PortDeclaration(pd) = sub_item {
                            if is_interface_type(&pd.data_type, definitions) {
                                continue;
                            }
                            if matches!(
                                resolve_typedef_chain(&pd.data_type, &elab.typedef_types),
                                DataType::Simple { kind: SimpleType::String, .. }
                            ) {
                                string_ports.extend(
                                    pd.declarators.iter().map(|d| d.name.name.as_str()),
                                );
                            }
                            if matches!(pd.data_type, DataType::TypeReference { .. })
                                && is_type_two_state_resolved(&pd.data_type, &elab.typedef_types)
                            {
                                resolved_two_state_ports.extend(
                                    pd.declarators.iter().map(|d| d.name.name.as_str()),
                                );
                            }
                            let width = resolve_type_width(
                                &pd.data_type,
                                Some(&sub_local_params),
                                Some(&elab.typedefs),
                            );
                            let is_signed = is_type_signed_resolved(&pd.data_type, &elab.typedef_types);
                            for decl in &pd.declarators {
                                let sig_name = cat2(&inst_prefix, &decl.name.name);
                                let dims = if decl.dimensions.is_empty() {
                                    match &pd.data_type {
                                        DataType::TypeReference { name, .. } => {
                                            lookup_scoped_type(name, &elab.typedef_unpacked_dims)
                                                .cloned()
                                                .unwrap_or_default()
                                        }
                                        _ => Vec::new(),
                                    }
                                } else {
                                    decl.dimensions.clone()
                                };
                                let dims = normalize_unpacked_dims(
                                    &dims,
                                    &sub_local_params,
                                    &elab.typedef_types,
                                );
                                if let Some(shape) = fixed_unpacked_shape(&dims, &sub_local_params)
                                    .filter(|d| !d.is_empty())
                                {
                                    register_fixed_unpacked_array(
                                        elab,
                                        &sig_name,
                                        &shape,
                                        width,
                                        is_type_two_state_resolved(
                                            &pd.data_type,
                                            &elab.typedef_types,
                                        ),
                                    );
                                    if let Some(declared) =
                                        declared_unpacked_dims(&dims, &sub_local_params)
                                    {
                                        if declared.first().is_some_and(|(l, r)| l > r) {
                                            elab.descending_arrays.insert(sig_name.clone());
                                        }
                                        elab.unpacked_decl_dims.insert(sig_name.clone(), declared);
                                    }
                                    elab.var_decl_types.insert_shared(
                                        sig_name.clone(),
                                        instance_decl_type(
                                            &mut cache.decl_types,
                                            &pd.data_type,
                                            &sub_typedef_names_all,
                                            &inst_prefix,
                                            sub_mod.name(),
                                        ),
                                    );
                                } else if names_packed_array_or_struct(
                                    &pd.data_type,
                                    &elab.typedef_types,
                                ) && !elab.var_decl_types.contains_key(&sig_name)
                                {
                                    // §7.4.1: a port of a named type keeps
                                    // its declaration, so an element of
                                    // `input lane_t [0:1] p;` has the signing
                                    // of `lane_t`.
                                    elab.var_decl_types.insert_shared(
                                        sig_name.clone(),
                                        instance_decl_type(
                                            &mut cache.decl_types,
                                            &pd.data_type,
                                            &sub_typedef_names_all,
                                            &inst_prefix,
                                            sub_mod.name(),
                                        ),
                                    );
                                }
                                // §7.4.1: a non-ANSI PORT of a packed
                                // multi-D / packed-struct type needs the
                                // same shape registrations a variable
                                // declaration gets. Without them
                                // `assign o[1] = v;` on a
                                // `output logic [3:0][9:0] o;` inlined
                                // port degraded to a bit-window write, and
                                // struct-port member assigns lost the
                                // layout.
                                if let Some(ew) = packed_inner_elem_width(
                                    &pd.data_type,
                                    &sub_local_params,
                                    &elab.typedefs,
                                )
                                .or_else(|| {
                                    // Dims on the TYPEDEF (`output w_t o;`).
                                    let one =
                                        bare_typedef_step(&pd.data_type, &elab.typedef_types)?;
                                    packed_inner_elem_width(&one, &sub_local_params, &elab.typedefs)
                                }) {
                                    elab.packed_signal_elem_widths
                                        .entry(sig_name.clone())
                                        .or_insert(ew);
                                }
                                // §7.4.1: a TYPEDEF'd element with
                                // declared dims (`output u8_t [0:7] o;`)
                                // chains them with the typedef's, as the
                                // ANSI arm does; unrecorded, ascending
                                // `[0:7]` fell back to [7:0] order.
                                if let Some(fd) =
                                    packed_full_dims_of(&pd.data_type, &sub_local_params).or_else(
                                        || {
                                            packed_full_dims_chained(
                                                &pd.data_type,
                                                &sub_local_params,
                                                &elab.typedef_types,
                                            )
                                        },
                                    )
                                {
                                    elab.packed_full_dims
                                        .insert_if_absent(sig_name.clone(), || fd);
                                }
                                if let Some(fields) = packed_struct_field_layout(
                                    &pd.data_type,
                                    &sub_local_params,
                                    &elab.typedefs,
                                    &elab.typedef_types,
                                ) {
                                    if !fields.is_empty() {
                                        // §7.4.1: a packed ARRAY of the struct
                                        // (`output s_t [0:3] o;`), as the ANSI
                                        // arm records it.
                                        let struct_w =
                                            fields.iter().map(|(_, o, w)| o + w).max().unwrap_or(0);
                                        if let Some(fd) = packed_typedef_array_dims(
                                            &pd.data_type,
                                            struct_w,
                                            &sub_local_params,
                                        ) {
                                            elab.packed_full_dims
                                                .entry(sig_name.clone())
                                                .or_insert(fd);
                                        }
                                        tls_register_struct_layout(&sig_name, &fields);
                                        elab.packed_struct_fields
                                            .entry(sig_name.clone())
                                            .or_insert(fields);
                                        // §7.2, §7.4.1: its members' shapes,
                                        // as the top-level port arm records.
                                        register_member_packed_meta(
                                            elab,
                                            &sig_name,
                                            &pd.data_type,
                                            Some(&sub_local_params),
                                        );
                                    }
                                }
                                // §6.6.7: resolve REALNESS through the
                                // typedef table — a nettype port formal
                                // (`inout rnet p`, rnet = `nettype real`)
                                // is a real signal. The bare is_type_real
                                // left it integral, so `%f` on the formal
                                // printed raw bits and any true real
                                // consumer read 0.0 (reads only worked
                                // when both sides were bit-identical).
                                let port_is_real =
                                    is_type_real_resolved(&pd.data_type, &elab.typedef_types);
                                signals_insert_traced(
                                    &mut elab.signals,
                                    line!(),
                                    sig_name.clone(),
                                    Signal {
                                        is_const: false,
                                        name: sig_name.clone().into(),
                                        width,
                                        is_signed,
                                        direction: Some(pd.direction),
                                        value: default_port_value(
                                            Some(pd.direction),
                                            Some(&pd.data_type),
                                            width,
                                            port_is_real,
                                            port_decl_net_type(pd),
                                        ).into(),
                                        is_real: port_is_real,
                                        type_name: scope_local_type_name(
                                            get_type_name(&pd.data_type),
                                            &sub_typedef_names_all,
                                            &inst_prefix,
                                        ),
                                    },
                                );
                                if let Some(net_type) = port_decl_net_type(pd) {
                                    register_net_type(
                                        elab,
                                        &sig_name,
                                        net_type,
                                        Some(&pd.data_type),
                                    );
                                }
                                // §6.11.2: as for an ANSI port, a 2-state
                                // formal drops X and Z on every write.
                                if !port_is_real
                                    && is_type_two_state_resolved(
                                        &pd.data_type,
                                        &elab.typedef_types,
                                    )
                                {
                                    elab.two_state_signals.insert(sig_name.clone());
                                }
                            }
                        }
                    }
                }
                iprof_since("ck5_before_loopC", __th);
                for sub_item in &prepared_sub.effective_items {
                    match sub_item {
                        ModuleItem::NetDeclaration(nd) => {
                            let width = resolve_type_width(
                                &nd.data_type,
                                Some(&sub_merged_params),
                                Some(&elab.typedefs),
                            );
                            for decl in &nd.declarators {
                                let sig_name = cat2(&inst_prefix, &decl.name.name);
                                if let Some(mut d) = net_delay_of(decl, nd, &sub_merged_params) {
                                    if let Some(exprs) = &mut d.3 {
                                        for operand in exprs.iter_mut().flatten() {
                                            *operand = rewrite_expr(operand, &inst_prefix, &port_map,
                                                &prepared_sub.local_names, &sub_interface_map);
                                        }
                                    }
                                    elab.net_delays.insert(sig_name.clone(), d);
                                }
                                let effective_dims = normalize_unpacked_dims(
                                    &decl.dimensions,
                                    &sub_merged_params,
                                    &elab.typedef_types,
                                );
                                if let Some(dims) =
                                    declared_unpacked_dims(&effective_dims, &sub_merged_params)
                                {
                                    if dims.first().is_some_and(|(l, r)| l > r) {
                                        elab.descending_arrays.insert(sig_name.clone());
                                    }
                                    elab.unpacked_decl_dims.insert(sig_name.clone(), dims);
                                }
                                // An UNPACKED array net inside a submodule
                                // (`wire [15:0] pipe [0:2];`) must register its
                                // range like the variable arm below, otherwise it
                                // collapses to a single scalar signal and every
                                // element select degrades to a 1-BIT select —
                                // `$bits(pipe[0])` came back 1 instead of 16 and a
                                // port fed from `pipe[i]` carried one bit. The same
                                // declaration at TOP level always worked, which is
                                // what made this look like a generate/genvar bug.
                                // Packed multi-D net (`wire [1:0][15:0] a;`):
                                // record the element width / full dimensions so
                                // `a[i]` slices instead of bit-selecting.
                                // §7.4.1: packed dims that live on the TYPEDEF
                                // (`typedef k_lane [4:0] k_plane; wire k_plane a;`)
                                // — one step of a BARE reference, as the inlined
                                // variable arm does; a reference carrying its own
                                // dims keeps them for the chained walk below. The
                                // raw reference had no element stride, so `a` was
                                // one flat vector and `assign a[1][0] = 1'b1`
                                // wrote bit 0 (same hole issue #92 reports for
                                // variables).
                                let nd_resolved: DataType = match &nd.data_type {
                                    DataType::TypeReference {
                                        name, dimensions, ..
                                    } if dimensions.is_empty() => {
                                        lookup_scoped_type(name, &elab.typedef_types)
                                            .cloned()
                                            .unwrap_or_else(|| nd.data_type.clone())
                                    }
                                    _ => nd.data_type.clone(),
                                };
                                if let Some(elem_w) = packed_inner_elem_width(
                                    &nd.data_type,
                                    &sub_merged_params,
                                    &elab.typedefs,
                                )
                                .or_else(|| {
                                    packed_inner_elem_width(
                                        &nd_resolved,
                                        &sub_merged_params,
                                        &elab.typedefs,
                                    )
                                }) {
                                    elab.packed_signal_elem_widths
                                        .insert(sig_name.clone(), elem_w);
                                }
                                if let Some(fdims) =
                                    packed_full_dims_of(&nd.data_type, &sub_merged_params)
                                        .or_else(|| {
                                            packed_full_dims_of(&nd_resolved, &sub_merged_params)
                                        })
                                        .or_else(|| {
                                            packed_full_dims_chained(
                                                &nd.data_type,
                                                &sub_merged_params,
                                                &elab.typedef_types,
                                            )
                                        })
                                {
                                    elab.packed_full_dims.insert(sig_name.clone(), fdims);
                                }
                                // UNPACKED array net of any rank
                                // (`wire [15:0] pipe [0:2];`, `… [0:1][0:1];`).
                                if let Some(shape) =
                                    fixed_unpacked_shape(&effective_dims, &sub_merged_params)
                                        .filter(|shape| !shape.is_empty())
                                {
                                    register_fixed_unpacked_array(
                                        elab,
                                        &sig_name,
                                        &shape,
                                        width,
                                        is_type_two_state(&nd.data_type),
                                    );
                                    mark_array_z_init_if_4state(elab, &sig_name, &nd.data_type);
                                    elab.var_decl_types.insert_shared(
                                        sig_name.clone(),
                                        instance_decl_type(
                                            &mut cache.decl_types,
                                            &nd.data_type,
                                            &sub_typedef_names_all,
                                            &inst_prefix,
                                            sub_mod.name(),
                                        ),
                                    );
                                    if let Some(UnpackedDimension::Range { left, right, .. }) =
                                        effective_dims.first()
                                    {
                                        let l = const_eval_i64_with_params(
                                            left,
                                            Some(&sub_merged_params),
                                        )
                                        .unwrap_or(0);
                                        let r = const_eval_i64_with_params(
                                            right,
                                            Some(&sub_merged_params),
                                        )
                                        .unwrap_or(0);
                                        if l > r {
                                            elab.descending_arrays.insert(sig_name.clone());
                                        }
                                    }
                                    // Per-element Signals are synthesized by
                                    // Simulator::new from the array metadata.
                                    continue;
                                }
                                // §6.18 / §7.2.1: a net keeps its typedef's
                                // member layout, just like a variable or port.
                                elab.var_decl_types.insert_shared(
                                    sig_name.clone(),
                                    instance_decl_type(
                                        &mut cache.decl_types,
                                        &nd.data_type,
                                        &sub_typedef_names_all,
                                        &inst_prefix,
                                        sub_mod.name(),
                                    ),
                                );
                                if matches!(resolve_typedef_chain(&nd.data_type, &elab.typedef_types),
                                    DataType::Struct(su) if su.packed)
                                    && let Some(fields) = flatten_struct_fields(
                                    &nd.data_type, &sub_merged_params,
                                    &elab.typedefs, &elab.typedef_types,
                                ) {
                                    if !fields.is_empty() {
                                        let element_width = fields.iter().map(|(_, o, w)| o + w).max().unwrap_or(0);
                                        if element_width > 0 && width > element_width && width % element_width == 0 {
                                            elab.packed_signal_elem_widths.insert(sig_name.clone(), element_width);
                                        }
                                        tls_register_struct_layout(&sig_name, &fields);
                                        elab.packed_struct_fields.insert(sig_name.clone(), fields);
                                    }
                                }
                                let net_is_real =
                                    is_type_real_resolved(&nd.data_type, &elab.typedef_types);
                                register_net_type(
                                    elab,
                                    &sig_name,
                                    nd.net_type,
                                    Some(&nd.data_type),
                                );
                                // §7.2.1, §6.7.1: a packed-struct NET's declared
                                // type and field layout, as the top-level net
                                // arm and this instance's variable and port arms
                                // register them. Without the layout a member
                                // read (`n.a`) did not resolve to the net's
                                // bits, so a reader was never woken by the net
                                // and kept a stale value; the same declaration
                                // in the top module worked.
                                if let DataType::Struct(su) =
                                    resolve_typedef_chain(&nd.data_type, &elab.typedef_types)
                                    && su.packed
                                    && let Some(fields) = flatten_struct_fields(
                                        &nd.data_type,
                                        &sub_merged_params,
                                        &elab.typedefs,
                                        &elab.typedef_types,
                                    )
                                    && !fields.is_empty()
                                {
                                    elab.var_decl_types.insert(
                                        sig_name.clone(),
                                        scope_local_typerefs(
                                            &nd.data_type,
                                            &sub_typedef_names_all,
                                            &inst_prefix,
                                        ),
                                    );
                                    tls_register_struct_layout(&sig_name, &fields);
                                    elab.packed_struct_fields.insert(sig_name.clone(), fields);
                                    register_member_packed_meta(
                                        elab,
                                        &sig_name,
                                        &nd.data_type,
                                        Some(&sub_merged_params),
                                    );
                                }
                                let init_value = default_net_value(nd.net_type, width, net_is_real);
                                signals_insert_traced(
                                    &mut elab.signals,
                                    line!(),
                                    sig_name.clone(),
                                    Signal {
                                        is_const: false,
                                        name: sig_name.into(),
                                        width,
                                        is_signed: is_type_signed_resolved(&nd.data_type, &elab.typedef_types),
                                        // Resolved through the typedef table so a
                                        // NETTYPE net declared in a submodule
                                        // (`rnet n;`) is real like its top-level
                                        // twin (§6.6.7).
                                        is_real: net_is_real,
                                        direction: None,
                                        value: init_value.into(),
                                        type_name: scope_local_type_name(
                                            get_type_name(&nd.data_type),
                                            &sub_typedef_names_all,
                                            &inst_prefix,
                                        ),
                                    },
                                );
                            }
                        }
                        ModuleItem::DataDeclaration(dd) => {
                            // §8.25: a class variable declared in an
                            // INSTANTIATED module (`C #(int, P) o;`) keeps its
                            // specialization under its instance-scoped name,
                            // value arguments folded with THIS instance's
                            // parameters. Only the top module's declarations
                            // were recorded, so `o = new` in any sub-module
                            // built the class at its defaults.
                            if let DataType::TypeReference { type_args, .. } = &dd.data_type {
                                if !type_args.is_empty() {
                                    let args: Vec<Expression> = type_args
                                        .iter()
                                        .map(|a| fold_class_param_arg(a, &sub_merged_params))
                                        .collect();
                                    for decl in &dd.declarators {
                                        elab.class_type_args.insert(
                                            cat2(&inst_prefix, &decl.name.name),
                                            args.clone(),
                                        );
                                    }
                                }
                            }
                            // Anonymous enum on a variable decl in a
                            // submodule's items (e.g. cv32e40p_obi_interface's
                            // state_q FSM): mirror the top-level DataDecl
                            // arm so enum members resolve as constants in
                            // submodule scopes too.
                            register_anonymous_enum_members(&dd.data_type, elab);
                            // ALSO register the members under the fully-
                            // scoped instance name (e.g.
                            // `dut_wrap...alu_div_i.FINISH`) so a local
                            // anon-enum value can win over a same-named
                            // pkg-imported member via scope-first lookup
                            // in `get_signal_value_by_name` at sim time
                            // (LRM §22.4 local declaration shadows
                            // wildcard-imported).
                            if let DataType::Enum(et) = &dd.data_type {
                                let base_width = et
                                    .base_type
                                    .as_ref()
                                    .map(|bt| {
                                        resolve_type_width(
                                            bt,
                                            Some(&sub_merged_params),
                                            Some(&elab.typedefs),
                                        )
                                    })
                                    .unwrap_or(32);
                                let mut next_val: u64 = 0;
                                let inst_prefix_no_dot = inst_prefix
                                    .strip_suffix('.')
                                    .unwrap_or(&inst_prefix)
                                    .to_string();
                                for member in &et.members {
                                    let val = if let Some(init) = &member.init {
                                        eval_const_expr(init, &sub_merged_params)
                                    } else {
                                        next_val
                                    };
                                    next_val = val.wrapping_add(1);
                                    let v = Value::from_u64(val, base_width);
                                    let scoped =
                                        format!("{}.{}", inst_prefix_no_dot, member.name.name);
                                    elab.set_param(line!(), scoped.clone(), v.clone());
                                    signals_insert_traced(
                                        &mut elab.signals,
                                        line!(),
                                        scoped.clone(),
                                        Signal {
                                            is_const: false,
                                            name: scoped.into(),
                                            width: base_width,
                                            is_signed: false,
                                            is_real: false,
                                            direction: None,
                                            value: v.into(),
                                            type_name: None,
                                        },
                                    );
                                }
                            }
                            // Packed multi-D (`logic [N-1:0][W-1:0] x`) — register
                            // the per-element width under BOTH the bare name and
                            // the fully-scoped name. Without this hook a
                            // `mem[i] = data` write inside a parameterised
                            // submodule like cv32e40p_fifo silently degrades to
                            // a single-bit write at bit `i`, corrupting all
                            // prefetch data.
                            // §6.16: a `string` declared in an INSTANTIATED
                            // module. Only the top module's walk recorded
                            // these, so a submodule string was width-fit to
                            // the 1024-bit placeholder on every write —
                            // silently dropping the FRONT of any text past 128
                            // characters (string bytes pack LSB-first, so the
                            // tail is what survived). Registered under both the
                            // bare and instance-scoped names, like the packed
                            // widths below.
                            if matches!(
                                &dd.data_type,
                                DataType::Simple {
                                    kind: SimpleType::String,
                                    ..
                                }
                            ) {
                                for decl in &dd.declarators {
                                    let bare = decl.name.name.clone();
                                    let scoped = cat2(&inst_prefix, &bare);
                                    if elab.string_signals.insert(bare.clone()) {
                                        inst_bare_keys.push((2, bare));
                                    }
                                    elab.string_signals.insert(scoped);
                                }
                            }
                            // The BARE key is FIRST-WINS: these tables are
                            // global bare-name maps, and an instance variable
                            // that happens to share a name with an OUTER-scope
                            // signal of a different shape must not stomp the
                            // outer entry — a 128-bit `[1:0][63:0] x` inside
                            // an instance redefined the TB's 292-bit struct-
                            // array `x`'s element geometry, so every
                            // `x[i][j]` read in the TB sliced with the
                            // submodule's dims (the §5g bare-name family).
                            // The scoped key is always this instance's own.
                            if let Some(elem_w) = packed_inner_elem_width(
                                &dd.data_type,
                                &sub_merged_params,
                                &elab.typedefs,
                            ) {
                                for decl in &dd.declarators {
                                    let bare = decl.name.name.clone();
                                    let scoped = cat2(&inst_prefix, &bare);
                                    if !elab.packed_signal_elem_widths.contains_key(&bare) {
                                        elab.packed_signal_elem_widths.insert(bare.clone(), elem_w);
                                        inst_bare_keys.push((0, bare));
                                    }
                                    elab.packed_signal_elem_widths.insert(scoped, elem_w);
                                }
                            }
                            // A TYPEDEF'd element type with declared dims
                            // (`u7_t [4:0][1:0] a`) has no dims of its own for
                            // `packed_full_dims_of`: chain the declared dims with
                            // the typedef's, as the top-level declaration path
                            // does. Without this the inlined signal had NO dims
                            // entry, and `foreach (a[i, j])` in an instance —
                            // every top under `__xezim_multi_top` — walked the
                            // 70 bits instead of the 10 elements.
                            if let Some(fdims) =
                                packed_full_dims_of(&dd.data_type, &sub_merged_params).or_else(
                                    || {
                                        packed_full_dims_chained(
                                            &dd.data_type,
                                            &sub_merged_params,
                                            &elab.typedef_types,
                                        )
                                    },
                                )
                            {
                                for decl in &dd.declarators {
                                    let bare = decl.name.name.clone();
                                    let scoped = cat2(&inst_prefix, &bare);
                                    if !elab.packed_full_dims.contains_key(&bare) {
                                        elab.packed_full_dims.insert(bare.clone(), fdims.clone());
                                        inst_bare_keys.push((1, bare));
                                    }
                                    elab.packed_full_dims.insert(scoped, fdims.clone());
                                }
                            }
                            // PACKED-STRUCT member layout for a submodule variable
                            // (`typedef struct packed {...} t; t s;`). The top-
                            // level DataDeclaration arm registers this; the
                            // submodule arm did NOT, so `s.m0 = v` had no bit
                            // offset to resolve and was DROPPED (struct read back
                            // X). Register under BOTH the bare name and the
                            // instance-scoped name, mirroring the packed-dim
                            // blocks above. Only PACKED structs (contiguous bit
                            // layout); unpacked structs keep per-member signals.
                            if let DataType::Struct(su) =
                                &resolve_typedef_chain(&dd.data_type, &elab.typedef_types)
                            {
                                if su.packed {
                                    if let Some(fields) = flatten_struct_fields(
                                        &dd.data_type,
                                        &sub_merged_params,
                                        &elab.typedefs,
                                        &elab.typedef_types,
                                    ) {
                                        if !fields.is_empty() {
                                            let struct_w = fields
                                                .iter()
                                                .map(|(_, o, w)| o + w)
                                                .max()
                                                .unwrap_or(0);
                                            for decl in &dd.declarators {
                                                if !decl.dimensions.is_empty() {
                                                    continue;
                                                }
                                                let bare = decl.name.name.clone();
                                                let scoped = cat2(&inst_prefix, &bare);
                                                tls_register_struct_layout(&bare, &fields);
                                                tls_register_struct_layout(&scoped, &fields);
                                                // First-wins on the bare key
                                                // (see the packed-dim blocks
                                                // above).
                                                if !elab.packed_struct_fields.contains_key(&bare) {
                                                    elab.packed_struct_fields
                                                        .insert(bare.clone(), fields.clone());
                                                    inst_bare_keys.push((3, bare.clone()));
                                                }
                                                elab.packed_struct_fields
                                                    .insert(scoped.clone(), fields.clone());
                                                // Per-MEMBER packed-array element
                                                // widths, keyed `<signal>.<member>`
                                                // — a member that is itself a
                                                // packed array (`u32_t [4:0] SEC`)
                                                // needs them or `mcp.SEC[0] <= v`
                                                // writes ONE BIT. The top-level and
                                                // PORT paths register these; this
                                                // SUB-MODULE BODY path did not, so
                                                // the identical declaration worked
                                                // at top level and silently lost
                                                // every element inside an instance.
                                                {
                                                    let mdt = resolve_typedef_chain(
                                                        &dd.data_type,
                                                        &elab.typedef_types,
                                                    )
                                                    .clone();
                                                    if let DataType::Struct(su) = &mdt {
                                                        for m in &su.members {
                                                            let (ew, fd) = packed_member_meta(
                                                                &m.data_type,
                                                                &sub_merged_params,
                                                                &elab.typedefs,
                                                                &elab.typedef_types,
                                                            );
                                                            for mdecl in &m.declarators {
                                                                for base in [&bare, &scoped] {
                                                                    let key = format!(
                                                                        "{}.{}",
                                                                        base, mdecl.name.name
                                                                    );
                                                                    if let Some(ew) = ew {
                                                                        elab
                                                                          .packed_signal_elem_widths
                                                                          .insert(key.clone(), ew);
                                                                    }
                                                                    if let Some(fd) = &fd {
                                                                        elab.packed_full_dims
                                                                            .insert(
                                                                                key,
                                                                                fd.clone(),
                                                                            );
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                                // Packed dims written on the
                                                // typedef itself (`some_t [1:0] g;`)
                                                // — register the element metadata
                                                // under the SCOPED name, like the
                                                // top-level and port paths already
                                                // do. Without it `g[0]` inside the
                                                // submodule was a 1-BIT select:
                                                // `$bits(g[0])` read 1 and an
                                                // element assign wrote one bit.
                                                if let Some(fdims) = packed_typedef_array_dims(
                                                    &dd.data_type,
                                                    struct_w,
                                                    &sub_merged_params,
                                                ) {
                                                    let total: i64 = fdims
                                                        .iter()
                                                        .map(|(l, r)| (l - r).abs() + 1)
                                                        .product();
                                                    let (ol, orr) = fdims[0];
                                                    let outer = (ol - orr).abs() + 1;
                                                    if outer > 0 && total > 0 {
                                                        elab.packed_signal_elem_widths.insert(
                                                            scoped.clone(),
                                                            (total / outer) as u32,
                                                        );
                                                    }
                                                    elab.packed_full_dims.insert(scoped, fdims);
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            // §7.2, §7.4.1: the packed geometry of each member
                            // of a submodule struct variable, packed or
                            // unpacked, as the top-level declaration path
                            // registers it: a packed array of packed structs
                            // (`pair_t [0:1] pairs`) needs its element layout
                            // and dimensions, and a packed-array member of an
                            // unpacked struct (`lane_t [0:3] lanes`) its
                            // dimensions. Without them `s.pairs[0].pair[0]`
                            // and `us.lanes[0]` in an instance — every top of
                            // a multi-top design — took the wrong element or
                            // a single bit.
                            if let DataType::Struct(su) =
                                &resolve_typedef_chain(&dd.data_type, &elab.typedef_types)
                            {
                                for decl in &dd.declarators {
                                    let scoped = cat2(&inst_prefix, &decl.name.name);
                                    for m in &su.members {
                                        let (ew, fd) = packed_member_meta(
                                            &m.data_type,
                                            &sub_merged_params,
                                            &elab.typedefs,
                                            &elab.typedef_types,
                                        );
                                        let elem = packed_struct_array_info(
                                            &m.data_type,
                                            &sub_merged_params,
                                            &elab.typedef_types,
                                        )
                                        .and_then(|(dims, elem_dt)| {
                                            let fields = flatten_struct_fields(
                                                &elem_dt,
                                                &sub_merged_params,
                                                &elab.typedefs,
                                                &elab.typedef_types,
                                            )?;
                                            let w = fields
                                                .iter()
                                                .map(|(_, o, w)| o + w)
                                                .max()
                                                .filter(|&w| w > 0)?;
                                            let mut fdims = dims;
                                            fdims.push((w as i64 - 1, 0));
                                            Some((w, fdims, fields))
                                        });
                                        for mdecl in &m.declarators {
                                            let key = format!("{}.{}", scoped, mdecl.name.name);
                                            if let Some((w, fdims, fields)) = &elem {
                                                elab.packed_signal_elem_widths
                                                    .insert(key.clone(), *w);
                                                elab.packed_full_dims
                                                    .insert(key.clone(), fdims.clone());
                                                elab.packed_struct_fields
                                                    .entry(key)
                                                    .or_insert_with(|| fields.clone());
                                                continue;
                                            }
                                            if let Some(ew) = ew {
                                                elab.packed_signal_elem_widths
                                                    .entry(key.clone())
                                                    .or_insert(ew);
                                            }
                                            if let Some(fd) = &fd {
                                                elab.packed_full_dims
                                                    .entry(key)
                                                    .or_insert_with(|| fd.clone());
                                            }
                                        }
                                    }
                                }
                            }
                            let width = match &dd.data_type {
                                // Packed dims on the reference (`some_t [1:0] g`)
                                // multiply the typedef's width — the bare-typedef
                                // shortcut is only valid without them. Taking it
                                // anyway sized a two-element struct array at ONE
                                // element, so the second element's writes were
                                // clamped away and it read X (the top-level arms
                                // already carry this exact guard).
                                DataType::TypeReference {
                                    name, dimensions, ..
                                } if dimensions.is_empty() => {
                                    elab.typedefs.get(&name.name.name).copied().unwrap_or(
                                        resolve_type_width(
                                            &dd.data_type,
                                            Some(&sub_merged_params),
                                            Some(&elab.typedefs),
                                        ),
                                    )
                                }
                                _ => resolve_type_width(
                                    &dd.data_type,
                                    Some(&sub_merged_params),
                                    Some(&elab.typedefs),
                                ),
                            };
                            let is_signed =
                                is_type_signed_resolved(&dd.data_type, &elab.typedef_types);
                            // §7.4.1: packed dims that live on the TYPEDEF
                            // (`typedef k_lane [4:0] k_plane; k_plane a;`) are
                            // recorded for a top-level variable and for an
                            // inlined port or net. This inlined VARIABLE arm
                            // never did, so `a` was one 320-bit scalar with no
                            // element stride. A continuous `a[1][0] = 1'b1`
                            // then compiled as a bit-select of bit 0, and
                            // `a[lane] = 64'h..` wrote that lane's LSB.
                            // Procedural assigns stayed on the interpreter,
                            // which still walked the typedef. One step of the
                            // typedef, same as the top-level DataDecl arm —
                            // `resolve_typedef_chain` would drop the
                            // intermediate `[4:0]`.
                            // Only a BARE reference resolves one step: with dims
                            // written on the reference itself (`pair_t [3:0] a;`)
                            // the typedef's own type would drop that outer
                            // `[3:0]` and `packed_full_dims_of` would record
                            // the typedef's dims as the whole shape. Such a
                            // declaration takes the chained walk below.
                            let dd_resolved: DataType = match &dd.data_type {
                                DataType::TypeReference {
                                    name, dimensions, ..
                                } if dimensions.is_empty() => {
                                    lookup_scoped_type(name, &elab.typedef_types)
                                        .cloned()
                                        .unwrap_or_else(|| dd.data_type.clone())
                                }
                                _ => dd.data_type.clone(),
                            };
                            for decl in &dd.declarators {
                                let base_name = decl.name.name.clone();
                                let sig_name = cat2(&inst_prefix, &base_name);
                                if !elab.packed_signal_elem_widths.contains_key(&sig_name) {
                                    if let Some(elem_w) = packed_inner_elem_width(
                                        &dd.data_type,
                                        &sub_merged_params,
                                        &elab.typedefs,
                                    )
                                    .or_else(|| {
                                        packed_inner_elem_width(
                                            &dd_resolved,
                                            &sub_merged_params,
                                            &elab.typedefs,
                                        )
                                    }) {
                                        elab.packed_signal_elem_widths
                                            .insert(sig_name.clone(), elem_w);
                                    }
                                }
                                if !elab.packed_full_dims.contains_key(&sig_name) {
                                    if let Some(fdims) =
                                        packed_full_dims_of(&dd.data_type, &sub_merged_params)
                                            .or_else(|| {
                                                packed_full_dims_of(
                                                    &dd_resolved,
                                                    &sub_merged_params,
                                                )
                                            })
                                            .or_else(|| {
                                                packed_full_dims_chained(
                                                    &dd.data_type,
                                                    &sub_merged_params,
                                                    &elab.typedef_types,
                                                )
                                            })
                                    {
                                        elab.packed_full_dims.insert(sig_name.clone(), fdims);
                                    }
                                }
                                // §6.18: unpacked dims may come from the
                                // TYPEDEF (`typedef t_byte t_word [0:3];
                                // t_word s;`), not the declarator — same gap
                                // just fixed for inlined PORTS (xezim#106).
                                // Without this the child-local variable
                                // registered as a scalar and the whole-array
                                // assigns through it carried nothing.
                                // §7.4.5: declarator dimensions come before
                                // the typedef's.
                                let effective_decl_dims: Vec<UnpackedDimension> = match &dd
                                    .data_type
                                {
                                    DataType::TypeReference {
                                        name, dimensions, ..
                                    } if dimensions.is_empty() => {
                                        let mut d = decl.dimensions.clone();
                                        if let Some(td) =
                                            lookup_scoped_type(name, &elab.typedef_unpacked_dims)
                                        {
                                            d.extend(td.iter().cloned());
                                        }
                                        d
                                    }
                                    _ => decl.dimensions.clone(),
                                };
                                let effective_decl_dims = normalize_unpacked_dims(
                                    &effective_decl_dims,
                                    &sub_merged_params,
                                    &elab.typedef_types,
                                );
                                record_coll_shape(
                                    elab,
                                    &sig_name,
                                    &effective_decl_dims,
                                    Some(&sub_merged_params),
                                );
                                let array_range =
                                    extract_array_range(&effective_decl_dims, &sub_merged_params);
                                if elab
                                    .signals
                                    .get(&sig_name)
                                    .is_some_and(|s| s.direction.is_some())
                                    && !elab.parameters.contains_key(&sig_name)
                                {
                                    let explicit_type =
                                        !matches!(dd.data_type, DataType::Implicit { .. });
                                    let decl_is_real =
                                        is_type_real_resolved(&dd.data_type, &elab.typedef_types);
                                    let existing = elab.signals.get_mut(&sig_name).unwrap();
                                    if explicit_type {
                                        if let Some(pats) = signal_trace_patterns() {
                                            if pats
                                                .iter()
                                                .any(|p| existing.name.contains(p.as_str()))
                                            {
                                                eprintln!(
                                                    "[xezim][trace-signal] width_mut@elaborate.rs:{} key={} width={} prev_width=Some({})",
                                                    line!(),
                                                    existing.name,
                                                    width,
                                                    existing.width
                                                );
                                            }
                                        }
                                        existing.width = width;
                                        existing.is_signed = is_signed;
                                        existing.is_real = decl_is_real;
                                        existing.type_name = scope_local_type_name(
                                            get_type_name(&dd.data_type),
                                            &sub_typedef_names_all,
                                            &inst_prefix,
                                        );
                                        existing.value = default_port_value(
                                            existing.direction,
                                            Some(&dd.data_type),
                                            width,
                                            decl_is_real,
                                            None,
                                        ).into();
                                    }
                                    if is_type_two_state_resolved(
                                        &dd.data_type,
                                        &elab.typedef_types,
                                    ) {
                                        elab.two_state_signals.insert(sig_name.clone());
                                    }
                                    unregister_net_type(elab, &sig_name);
                                    elab.var_decl_types.insert_shared(
                                        sig_name.clone(),
                                        instance_decl_type(
                                            &mut cache.decl_types,
                                            &dd.data_type,
                                            &sub_typedef_names_all,
                                            &inst_prefix,
                                            sub_mod.name(),
                                        ),
                                    );
                                    continue;
                                }
                                if sig_name.contains("ram0.mem")
                                    && std::env::var("XEZIM_DBG_ARR").is_ok()
                                {
                                    let mut p: Vec<_> = sub_merged_params.iter().collect();
                                    p.sort_by_key(|(k, _)| k.as_str());
                                    eprintln!(
                                        "[DBG_ARR] {} width={} array_range={:?} prefix='{}' sub_merged_params(len={}): {:?}",
                                        sig_name,
                                        width,
                                        array_range,
                                        inst_prefix,
                                        sub_merged_params.len(),
                                        p.iter()
                                            .map(|(k, v)| format!(
                                                "{}={}",
                                                k,
                                                v.to_u64().unwrap_or(0)
                                            ))
                                            .collect::<Vec<_>>()
                                    );
                                }
                                // A queue / dynamic / associative dim on a
                                // SUBMODULE or interface decl must register
                                // like a top-level one — `tif.q.push_back(x)`
                                // read a phantom 64-slot fixed array before.
                                // An instance variable with unpacked dims (queue, dynamic,
                                // associative, fixed) whose ELEMENT is a packed struct: the
                                // module path registers the element layout under the container
                                // name so `q[i].field` resolves; the inlined copy never did, so
                                // every element field read 0 and writes were lost inside an
                                // instance while the same code worked at the top level.
                                if !effective_decl_dims.is_empty()
                                    && !elab.packed_struct_fields.contains_key(&sig_name)
                                {
                                    if let Some(fields) = packed_struct_field_layout(
                                        &dd.data_type,
                                        &sub_merged_params,
                                        &elab.typedefs,
                                        &elab.typedef_types,
                                    ) {
                                        if !fields.is_empty() {
                                            elab.packed_struct_fields
                                                .insert(sig_name.clone(), fields);
                                        }
                                    }
                                }
                                match effective_decl_dims.first() {
                                    Some(UnpackedDimension::Unsized(_))
                                    | Some(UnpackedDimension::Queue { .. }) => {
                                        elab.dynamic_arrays.insert(sig_name.clone());
                                        // The ELEMENT type, under the scoped
                                        // name — without it a queue of unpacked
                                        // structs inside an instance evaluated
                                        // `push_back(item)` as one packed value
                                        // (always x) instead of copying member
                                        // signals, so the queue filled with x.
                                        elab.var_decl_types.insert_shared(
                                            sig_name.clone(),
                                            instance_decl_type(
                                                &mut cache.decl_types,
                                                &dd.data_type,
                                                &sub_typedef_names_all,
                                                &inst_prefix,
                                                sub_mod.name(),
                                            ),
                                        );
                                    }
                                    Some(UnpackedDimension::Associative {
                                        data_type: kdt, ..
                                    }) => {
                                        let is_str = kdt.as_ref().is_some_and(|dt| {
                                            matches!(
                                                dt.as_ref(),
                                                DataType::Simple {
                                                    kind: SimpleType::String,
                                                    ..
                                                }
                                            )
                                        });
                                        elab.associative_arrays.insert(sig_name.clone(), is_str);
                                        // §10.7: the element width, under the SCOPED name — the runtime
                                        // looks it up by resolved signal name, and a bare leaf would
                                        // collide with a same-named array in another module.
                                        if width > 0 {
                                            elab.assoc_elem_widths.insert(sig_name.clone(), width);
                                        }
                                        // §7.8.2: the KEY type, in this instance's parameter
                                        // scope, exactly as the module-scope arm records it.
                                        // Without it a `foreach` key variable over
                                        // `mem[logic [KW-1:0]]` in a child was 32 bits wide.
                                        let (kiw, ktn) = assoc_key_type_info(
                                            kdt.as_deref(),
                                            &sub_merged_params,
                                            &elab.typedefs,
                                            &elab.typedef_types,
                                        );
                                        if let Some(iw) = kiw {
                                            elab.assoc_index_widths.insert(sig_name.clone(), iw);
                                        }
                                        if let Some(tn) = ktn {
                                            elab.assoc_key_type_names.insert(sig_name.clone(), tn);
                                        }
                                    }
                                    _ => {}
                                }
                                // IEEE 1800-2017 §7.4.5 / §7.8: unpacked array
                                // whose ELEMENT is itself a dynamic collection
                                // (`int q[3][$]`, `int d[3][]`, `int a[2][k_t]`)
                                // declared in a SUBMODULE. Mirrors the
                                // module-scope DataDecl arm, under the scoped
                                // name — without this the trailing dimension
                                // was dropped, `q[i]` registered as a plain
                                // fixed array element, and `q[i].push_back(x)`
                                // inside an instance was a silent no-op
                                // (`q[i].size()` read 0 forever).
                                if let Some(split) = coll_elem_split(&effective_decl_dims) {
                                    if let Some(qd) = effective_decl_dims.get(split) {
                                        if matches!(
                                            qd,
                                            UnpackedDimension::Unsized(_)
                                                | UnpackedDimension::Queue { .. }
                                                | UnpackedDimension::Associative { .. }
                                        ) {
                                            let outer = &effective_decl_dims[..split];
                                            let shape: Option<Vec<(i64, i64)>> = outer
                                                .iter()
                                                .map(|d| {
                                                    extract_array_range(
                                                        std::slice::from_ref(d),
                                                        &sub_merged_params,
                                                    )
                                                })
                                                .collect();
                                            if let Some(shape) = shape.filter(|sh| {
                                                sh.iter()
                                                    .all(|&(lo, hi)| hi >= lo && hi - lo < 4096)
                                            }) {
                                                if let Some(declared) = declared_unpacked_dims(
                                                    outer,
                                                    &sub_merged_params,
                                                ) {
                                                    elab.unpacked_decl_dims
                                                        .insert(sig_name.clone(), declared);
                                                }
                                                match shape.len() {
                                                    1 => {
                                                        elab.arrays.insert(
                                                            sig_name.clone(),
                                                            (shape[0].0, shape[0].1, width),
                                                        );
                                                    }
                                                    2 => {
                                                        elab.arrays_2d.insert(
                                                            sig_name.clone(),
                                                            (shape[0], shape[1], width),
                                                        );
                                                    }
                                                    _ => {
                                                        elab.arrays_nd.insert(
                                                            sig_name.clone(),
                                                            (shape.clone(), width),
                                                        );
                                                    }
                                                }
                                                let qmax = if let UnpackedDimension::Queue {
                                                    max_size: Some(ms),
                                                    ..
                                                } = qd
                                                {
                                                    const_eval_i64_with_params(
                                                        ms,
                                                        Some(&sub_merged_params),
                                                    )
                                                    .filter(|n| *n >= 0)
                                                    .map(|n| (n + 1) as u32)
                                                } else {
                                                    None
                                                };
                                                let assoc_key = match qd {
                                                    UnpackedDimension::Associative {
                                                        data_type: kdt,
                                                        ..
                                                    } => Some(kdt.as_ref().is_some_and(|dt| {
                                                        matches!(
                                                            dt.as_ref(),
                                                            DataType::Simple {
                                                                kind: SimpleType::String,
                                                                ..
                                                            }
                                                        )
                                                    })),
                                                    _ => None,
                                                };
                                                let assoc_key_info = match qd {
                                                    UnpackedDimension::Associative {
                                                        data_type,
                                                        ..
                                                    } => assoc_key_type_info(
                                                        data_type.as_deref(),
                                                        &sub_merged_params,
                                                        &elab.typedefs,
                                                        &elab.typedef_types,
                                                    ),
                                                    _ => (None, None),
                                                };
                                                for suffix in index_tuples(&shape) {
                                                    let en = format!("{}{}", sig_name, suffix);
                                                    if let Some(is_str) = assoc_key {
                                                        // Associative elements are sparse: no
                                                        // backing buffer, no `.size` shadow.
                                                        register_assoc_element_key_type(
                                                            elab,
                                                            en,
                                                            is_str,
                                                            width,
                                                            &assoc_key_info,
                                                        );
                                                        continue;
                                                    }
                                                    elab.dynamic_arrays.insert(en.clone());
                                                    if let Some(m) = qmax {
                                                        elab.queue_max_sizes.insert(en.clone(), m);
                                                    }
                                                    elab.arrays.insert(en, (0, 63, width));
                                                }
                                                elab.var_decl_types.insert_shared(
                                                    sig_name.clone(),
                                                    instance_decl_type(
                                                        &mut cache.decl_types,
                                                        &dd.data_type,
                                                        &sub_typedef_names_all,
                                                        &inst_prefix,
                                                        sub_mod.name(),
                                                    ),
                                                );
                                                continue;
                                            }
                                        }
                                    }
                                }
                                // A MULTI-dimensional unpacked variable in a
                                // submodule (`logic [15:0] grid [0:1][0:1];`).
                                // `extract_array_range` only understands ONE
                                // dimension, so a 2-D/N-D declarator fell through
                                // to the scalar branch below and no element
                                // storage existed at all — writes to `grid[i][j]`
                                // went nowhere and reads came back X. The same
                                // declaration at top level registers via
                                // `fixed_unpacked_shape`; mirror that here.
                                {
                                    // Checked BEFORE `array_range`, which reports
                                    // only the FIRST dimension and so claims a 2-D
                                    // declarator as 1-D (storage came out as
                                    // `grid[0]`/`grid[1]` instead of
                                    // `grid[i][j]`).
                                    if let Some(shape) = fixed_unpacked_shape(
                                        &effective_decl_dims,
                                        &sub_merged_params,
                                    )
                                    .filter(|sh| sh.len() > 1)
                                    {
                                        register_fixed_unpacked_array(
                                            elab,
                                            &sig_name,
                                            &shape,
                                            width,
                                            is_type_two_state(&dd.data_type),
                                        );
                                        // Same §7.6 order as the 1-D instance path.
                                        // `register_fixed_unpacked_array` records the
                                        // normalized (lo, hi) shape; overwrite it with
                                        // the declared bounds so a descending range
                                        // still pairs left to right.
                                        if let Some(declared) = declared_unpacked_dims(
                                            &effective_decl_dims,
                                            &sub_merged_params,
                                        ) {
                                            if declared.first().is_some_and(|(l, r)| l > r) {
                                                elab.descending_arrays.insert(sig_name.clone());
                                            }
                                            elab.unpacked_decl_dims
                                                .insert(sig_name.clone(), declared);
                                        }
                                        elab.var_decl_types.insert_shared(
                                            sig_name.clone(),
                                            instance_decl_type(
                                                &mut cache.decl_types,
                                                &dd.data_type,
                                                &sub_typedef_names_all,
                                                &inst_prefix,
                                                sub_mod.name(),
                                            ),
                                        );
                                        // §6.8: its initializer is deferred like every
                                        // other instance declaration's (one whole-pattern
                                        // assignment, rewritten into the instance scope).
                                        if let Some(init_expr) = &decl.init {
                                            deferred_decl_inits.push((
                                                sig_name.clone(),
                                                init_expr.as_ref().clone(),
                                            ));
                                        }
                                        continue;
                                    }
                                }
                                if let Some((lo, hi)) = array_range {
                                    if matches!(
                                        &dd.data_type,
                                        DataType::Simple {
                                            kind: SimpleType::Event,
                                            ..
                                        }
                                    ) {
                                        elab.events.insert(sig_name.clone());
                                        if hi >= lo && (hi - lo) < 4096 {
                                            for i in lo..=hi {
                                                elab.events.insert(format!("{}[{}]", sig_name, i));
                                            }
                                        }
                                    }
                                    elab.arrays.insert(sig_name.clone(), (lo, hi, width));
                                    // §7.6: a 1-D variable in an INSTANCE keeps its
                                    // declared left-to-right order, same as the
                                    // top-level path. `arrays` stores (lo, hi);
                                    // without `unpacked_decl_dims` /
                                    // `descending_arrays` a `[N-1:0]` actual was
                                    // paired with a descending port as if it were
                                    // `[0:N-1]`, so element 0 of the port received
                                    // the parent's highest index (and the output
                                    // port reversed it back, hiding the swap from
                                    // the parent).
                                    if let Some(declared) = declared_unpacked_dims(
                                        &effective_decl_dims,
                                        &sub_merged_params,
                                    ) {
                                        if declared.first().is_some_and(|(l, r)| l > r) {
                                            elab.descending_arrays.insert(sig_name.clone());
                                        }
                                        elab.unpacked_decl_dims.insert(sig_name.clone(), declared);
                                    }
                                    // §6.8: a fixed array's declaration initializer is
                                    // deferred like every other instance declaration's
                                    // (one whole-pattern assignment, rewritten into the
                                    // instance scope); it used to be dropped here.
                                    if let Some(init_expr) = &decl.init {
                                        deferred_decl_inits
                                            .push((sig_name.clone(), init_expr.as_ref().clone()));
                                    }
                                    // The ELEMENT type of a child array — the
                                    // top-level path records one and every
                                    // type-directed operation needs it
                                    // (`arr[i] = '{...}` resolves the element
                                    // struct through it).
                                    if !elab.var_decl_types.contains_key(&sig_name) {
                                        elab.var_decl_types.insert_shared(
                                            sig_name.clone(),
                                            instance_decl_type(
                                                &mut cache.decl_types,
                                                &dd.data_type,
                                                &sub_typedef_names_all,
                                                &inst_prefix,
                                                sub_mod.name(),
                                            ),
                                        );
                                    };
                                    // §7.2: an array of UNPACKED structs stores
                                    // each element member-wise, exactly as the
                                    // top-level path registers it. Without this
                                    // the child's elements were packed vectors
                                    // with no member leaves, so `arr[i].m = v`
                                    // wrote somewhere the read never looked
                                    // (`arr[i].m` came back x) — while the same
                                    // declaration at top level was correct.
                                    if let DataType::Struct(su) =
                                        resolve_typedef_chain(&dd.data_type, &elab.typedef_types)
                                            .clone()
                                    {
                                        if !su.packed
                                            && !(matches!(su.kind, StructUnionKind::Union)
                                                && !su.tagged)
                                            && hi >= lo
                                            && (hi - lo) < 4096
                                        {
                                            for i in lo..=hi {
                                                let ebase = format!("{}[{}]", sig_name, i);
                                                register_unpacked_aggregate(
                                                    elab,
                                                    &ebase,
                                                    &dd.data_type,
                                                );
                                            }
                                        }
                                    }
                                    if is_type_two_state_resolved(
                                        &dd.data_type,
                                        &elab.typedef_types,
                                    ) {
                                        elab.two_state_signals.insert(sig_name.clone());
                                    }
                                    // Per-element Signals synthesized by
                                    // Simulator::new from arrays metadata.
                                    let _ = is_signed;
                                } else {
                                    // §6.8: 2-state types (bit/int/…) default to
                                    // 0, not X — same as the top-level decl path.
                                    // `Value::new` left a submodule's `bit` counter
                                    // at X, so `cnt++` stayed X forever (issue #22).
                                    // §6.16: a string has no declared width, so
                                    // its initializer must NOT be fit to the
                                    // 1024-bit placeholder — the same exemption
                                    // the top-level decl path carries. Fitting
                                    // it kept only the low 128 characters, i.e.
                                    // dropped the FRONT of the text (issue #76:
                                    // a 142-character string in an
                                    // INSTANTIATED module lost its "HEAD_"
                                    // prefix, while the identical declaration
                                    // in the top module was correct).
                                    // §6.6.7, §10.3.1: the initializer of a
                                    // user-defined nettype net is one of its
                                    // continuous drivers, as at top level; it
                                    // joins the instance's net declaration
                                    // assignments once the rewrite context
                                    // exists.
                                    let nettype_net = get_type_name(&dd.data_type)
                                        .is_some_and(|t| elab.nettype_resolvers.contains_key(&t));
                                    if nettype_net && let Some(init_expr) = &decl.init {
                                        nettype_decl_inits.push((
                                            decl.name.name.clone(),
                                            init_expr.as_ref().clone(),
                                        ));
                                    }
                                    let init_val = if let Some(init_expr) = &decl.init {
                                        // An initializer that is NOT a constant
                                        // expression reads a sibling VARIABLE
                                        // (`string cmd = $sformatf("%s", dir);`,
                                        // `int m = n + 1;`). The parameter map
                                        // holds no variables, so const-folding it
                                        // here silently produced 0 / "" — while
                                        // the identical declaration at top level
                                        // was correct. Defer it to an
                                        // initial-block assignment exactly as the
                                        // top-level declaration path does.
                                        if !is_const_expr(init_expr, &sub_merged_params) {
                                            if !nettype_net {
                                                deferred_decl_inits.push((
                                                    sig_name.clone(),
                                                    init_expr.as_ref().clone(),
                                                ));
                                            }
                                            default_value_for_type_resolved(
                                                &dd.data_type,
                                                width,
                                                &elab.typedef_types,
                                            )
                                        } else if matches!(
                                            &dd.data_type,
                                            DataType::Simple {
                                                kind: SimpleType::String,
                                                ..
                                            }
                                        ) {
                                            eval_const_expr_val(init_expr, &sub_merged_params)
                                        } else {
                                            eval_init_for_target(
                                                init_expr,
                                                &sub_merged_params,
                                                width,
                                                is_type_real_resolved(
                                                    &dd.data_type,
                                                    &elab.typedef_types,
                                                ),
                                            )
                                        }
                                    } else {
                                        default_value_for_type_resolved(
                                            &dd.data_type,
                                            width,
                                            &elab.typedef_types,
                                        )
                                    };
                                    // §7.2: an UNPACKED struct is per-member
                                    // storage, not one packed vector. The child
                                    // path registered a single packed signal, so
                                    // no member leaves existed: a member write
                                    // created an ad-hoc runtime entry and a
                                    // member read of an unwritten struct fell
                                    // through the suffix scan into ANOTHER
                                    // struct's member — two distinct variables
                                    // silently shared storage. Register the
                                    // member signals the way the top-level path
                                    // does, and skip the packed signal.
                                    let unpacked_struct_decl = match resolve_typedef_chain(
                                        &dd.data_type,
                                        &elab.typedef_types,
                                    ) {
                                        DataType::Struct(su) => {
                                            !su.packed
                                                && !(matches!(su.kind, StructUnionKind::Union)
                                                    && !su.tagged)
                                        }
                                        _ => false,
                                    };
                                    // §6.19.6: an ANONYMOUS enum variable keys
                                    // its member list by the variable's own
                                    // (scoped) name; the top-level path did
                                    // this, the instance path did not, so
                                    // `anon.name()` in a submodule fell to the
                                    // by-value scan.
                                    if matches!(dd.data_type, DataType::Enum(_)) {
                                        if let Some(m) = anon_enum_members_ordered(
                                            &dd.data_type,
                                            &sub_merged_params,
                                        ) {
                                            elab.enum_members.insert(sig_name.clone(), m);
                                        }
                                    }
                                    if unpacked_struct_decl {
                                        register_unpacked_aggregate(elab, &sig_name, &dd.data_type);
                                        elab.var_decl_types.insert_shared(
                                            sig_name.clone(),
                                            instance_decl_type(
                                                &mut cache.decl_types,
                                                &dd.data_type,
                                                &sub_typedef_names_all,
                                                &inst_prefix,
                                                sub_mod.name(),
                                            ),
                                        );
                                        continue;
                                    }
                                    // The declared type of a SCALAR child
                                    // declaration. Only the array/collection
                                    // branches above recorded one, so an
                                    // unpacked STRUCT in an instance had no
                                    // type on file and every type-directed
                                    // path missed it — `s = '{a:1, b:2}` found
                                    // no aggregate to spread into and left the
                                    // members x, while the same declaration at
                                    // top level worked.
                                    if matches!(
                                        &dd.data_type,
                                        DataType::Simple {
                                            kind: SimpleType::Event,
                                            ..
                                        }
                                    ) {
                                        elab.events.insert(sig_name.clone());
                                    }
                                    if !elab.var_decl_types.contains_key(&sig_name) {
                                        elab.var_decl_types.insert_shared(
                                            sig_name.clone(),
                                            instance_decl_type(
                                                &mut cache.decl_types,
                                                &dd.data_type,
                                                &sub_typedef_names_all,
                                                &inst_prefix,
                                                sub_mod.name(),
                                            ),
                                        );
                                    };
                                    // §6.11.1: a 2-state scalar drops x/z on
                                    // every write, as at top level.
                                    if is_type_two_state_resolved(
                                        &dd.data_type,
                                        &elab.typedef_types,
                                    ) {
                                        elab.two_state_signals.insert(sig_name.clone());
                                    }
                                    signals_insert_traced(
                                        &mut elab.signals,
                                        line!(),
                                        sig_name.clone(),
                                        Signal {
                                            is_const: dd.const_kw,
                                            name: sig_name.into(),
                                            width,
                                            is_signed,
                                            direction: None,
                                            // §6.8: the declared signedness,
                                            // not the initializer literal's
                                            // (`logic q = 1;` read back -1).
                                            value: {
                                                let mut v = init_val;
                                                if !v.is_real {
                                                    v.is_signed = is_signed;
                                                }
                                                v
.into()                                            },
                                            is_real: is_type_real_resolved(
                                                &dd.data_type,
                                                &elab.typedef_types,
                                            ),
                                            type_name: scope_local_type_name(
                                                get_type_name(&dd.data_type),
                                                &sub_typedef_names_all,
                                                &inst_prefix,
                                            ),
                                        },
                                    );
                                }
                            }
                        }
                        _ => {}
                    }
                }

                // §10.11: an `alias` statement in the child's body names ONE
                // physical net. The operands are the child's OWN port and net
                // names, so they carry the instance prefix (`u.p`, `u.q`);
                // the unification pass decides which of them is the net the
                // group stands for.

                // §6.6.8: an `interconnect` port has NO data type of its own --
                // it takes whatever the things connected to it agree on. Every
                // other port kind knows its type from its own declaration, so
                // this is the one case that has to be resolved HERE, where the
                // actual is finally visible. Left untyped it lands as a 1-bit
                // net and silently truncates: a UVM-MS wrapper carrying an
                // analog value saw 1.0 where the parent net held 1.25.
                let interconnect_ports: HashSet<String> = match sub_mod.ports() {
                    PortList::Ansi(ps) => ps
                        .iter()
                        .filter(|q| matches!(q.net_type, Some(NetType::Interconnect)))
                        .map(|q| q.name.name.clone())
                        .collect(),
                    _ => Default::default(),
                };
                // Connection assigns of plain INPUT ports, by port name, for
                // the unobserved-port elision below.
                let mut input_connects: Vec<(String, usize)> = Vec::new();
                for (port_name, parent_expr) in &port_map {
                    if prepared_sub.interface_ports.contains(port_name) {
                        continue;
                    }
                    let sub_sig_name = cat2(&inst_prefix, &port_name);
                    // §6.6.8: a declared `interconnect` net is TYPELESS — it
                    // adopts the type of the port it connects. The declaration
                    // registered a 1-bit z placeholder; the first
                    // definitely-typed formal shapes it (width, realness, and
                    // the nettype name the §6.6.7 resolver machinery keys on).
                    // A dimensioned interconnect (width > 1) keeps its
                    // declared width, per the declaration's own constraint.
                    // An ARRAY element actual (`iBus[1]`) is a select, not a
                    // whole-net ident, so `whole_net_ident_name` returns None;
                    // fall back to its base so the typeless interconnect
                    // array adopts the width/realness of the element it is
                    // bound to (§6.6.8).
                    if let Some(an) = whole_net_ident_name(parent_expr)
                        .or_else(|| interconnect_array_base_name(parent_expr))
                    {
                        if elab.interconnect_nets.contains(&an) {
                            let formal = elab
                                .signals
                                .get(&sub_sig_name)
                                .map(|f| (f.width, f.is_real, f.type_name.clone()));
                            if let Some((fw, freal, ftn)) = formal {
                                // §6.6.7, §7.2: a nettype over an unpacked
                                // struct is stored per member.
                                let struct_dt = ftn
                                    .as_deref()
                                    .and_then(|tn| elab.typedef_types.get(tn))
                                    .map(|sdt| {
                                        resolve_typedef_chain(sdt, &elab.typedef_types).clone()
                                    })
                                    .filter(|r| {
                                        matches!(
                                            r,
                                            DataType::Struct(su)
                                                if !su.packed && !su.members.is_empty()
                                        )
                                    });
                                // §6.6.8: an ELEMENT bound to a struct nettype
                                // makes a still typeless array an array of
                                // that struct, each element with its member
                                // leaves (`sa[0].V`) as a declared
                                // `vinet sa[0:1]` has. Giving the BASE net
                                // the members and every element the
                                // container's width truncated the `real`
                                // elements of an array shaped before, which
                                // keeps its shape here.
                                let element = whole_net_ident_name(parent_expr).is_none();
                                if element && let Some(dt) = &struct_dt {
                                    let typeless = elab
                                        .signals
                                        .get(&an)
                                        .is_some_and(|a| a.width <= 1 && !a.is_real);
                                    let range = elab
                                        .arrays
                                        .get(&an)
                                        .map(|&(l, r, _)| (l.min(r), l.max(r)))
                                        .filter(|&(lo, hi)| typeless && hi - lo < 4096);
                                    if let Some((lo, hi)) = range {
                                        if let Some((_, _, ew)) = elab.arrays.get_mut(&an) {
                                            *ew = fw;
                                        }
                                        if let Some(asig) = elab.signals.get_mut(&an) {
                                            asig.width = fw;
                                            asig.type_name = ftn;
                                            asig.value = Value::all_z(fw).into();
                                        }
                                        elab.var_decl_types.insert(an.clone(), dt.clone());
                                        for i in lo..=hi {
                                            register_unpacked_aggregate(
                                                elab,
                                                &format!("{an}[{i}]"),
                                                dt,
                                            );
                                        }
                                    }
                                } else if fw > 1 || freal {
                                    if let Some(asig) = elab.signals.get_mut(&an) {
                                        if asig.width <= 1 && !asig.is_real {
                                            asig.width = fw;
                                            asig.is_real = freal;
                                            if asig.type_name.is_none() {
                                                asig.type_name = ftn;
                                            }
                                            asig.value = if freal {
                                                Value::from_f64(0.0)
.into()                                            } else {
                                                Value::all_z(fw)
.into()                                            };
                                        }
                                    }
                                    // §6.6.8: the interconnect ARRAY's
                                    // per-element storage must match the
                                    // shaped element width/realness too —
                                    // `arrays[an]` still says elem_w=1 for a
                                    // typeless interconnect array, so a real
                                    // element (`iBus[1] = r1.out`) truncated to
                                    // one bit even after the base was shaped
                                    // (#1039). Bump the element width/realness
                                    // to the formal's, mirroring a
                                    // nettype-typed array (`realNet a[0:1]`
                                    // registers elem_w=64).
                                    if let Some((_, _, ew)) = elab.arrays.get_mut(&an) {
                                        if *ew < fw {
                                            *ew = fw;
                                        }
                                    }
                                    if freal {
                                        // The declaration recorded the
                                        // interconnect's implicit type;
                                        // readers that go by the declared
                                        // type took the element's bits for
                                        // an integer.
                                        elab.var_decl_types.insert(
                                            an.clone(),
                                            DataType::Real {
                                                kind: RealType::Real,
                                                span: Span::new(0, 0),
                                            },
                                        );
                                    }
                                    // §6.6.7, §7.2: the sub-module
                                    // declaration path creates member leaves
                                    // (`d.o.V`, `d.o.I`) for the formal. A
                                    // typeless interconnect bound to it
                                    // adopted the packed whole signal but got
                                    // no member leaves, so the member-wise
                                    // connect assigns (`w.V = d.o.V`) wrote
                                    // into bit-selects of the packed storage
                                    // and read back nan (#1040). Give the
                                    // interconnect the same member leaves.
                                    if let Some(dt) = &struct_dt {
                                        register_unpacked_aggregate(elab, &an, dt);
                                    }
                                }
                            }
                        }
                    }
                    // §6.6.8, the other direction: an `interconnect` PORT is
                    // typeless and adopts the shape of the actual it is
                    // connected to. The block above shapes a typeless ACTUAL
                    // from a typed formal; this one shapes a typeless FORMAL
                    // from a typed actual. Both are needed — either side of a
                    // port connection may be the typeless one.
                    if interconnect_ports.contains(port_name) {
                        // Adopt the actual's shape. Only the attributes that
                        // decide how the value is STORED are copied -- width,
                        // real-ness, signedness, and the nettype name so a
                        // resolved net stays resolved; direction stays the
                        // port's own.
                        if let Some(src) = whole_net_ident_name(parent_expr)
                            .and_then(|n| elab.signals.get(&n).cloned())
                        {
                            if let Some(dst) = elab.signals.get_mut(&sub_sig_name) {
                                dst.width = src.width;
                                dst.is_real = src.is_real;
                                dst.is_signed = src.is_signed;
                                dst.type_name = src.type_name.clone();
                                if dst.is_real {
                                    dst.value = Value::from_f64(0.0).into();
                                } else {
                                    dst.value = Value::zero(src.width.max(1)).into();
                                }
                            }
                        }
                    }
                    let port_shape = elab
                        .unpacked_decl_dims
                        .get(&sub_sig_name)
                        .map(|dims| {
                            dims.iter()
                                .map(|&(l, r)| (l.min(r), l.max(r)))
                                .collect::<Vec<_>>()
                        })
                        .unwrap_or_default();
                    if !port_shape.is_empty() {
                        // §7.6: use each side's declared order, independently of
                        // numeric index labels. A slice supplies its own bounds.
                        let formal_elems = unpacked_connection_elements(
                            &make_ident_expr(&sub_sig_name),
                            elab,
                            &sub_merged_params,
                        );
                        let actual_elems =
                            unpacked_connection_elements(parent_expr, elab, local_params);
                        let pairs = match (formal_elems, actual_elems) {
                            (Some(f), Some(a)) if f.len() == a.len() => {
                                f.into_iter().zip(a).collect::<Vec<_>>()
                            }
                            _ => shape_index_tuples(&port_shape)
                                .into_iter()
                                .map(|indices| {
                                    (
                                        ai_append_indices(make_ident_expr(&sub_sig_name), &indices),
                                        ai_append_indices(parent_expr.clone(), &indices),
                                    )
                                })
                                .collect(),
                        };
                        for (sub_expr, parent_elem) in pairs {
                            match prepared_sub.port_directions.get(port_name) {
                                Some(PortDirection::Input) | Some(PortDirection::Inout) => {
                                    elab.continuous_assigns.push(
                                        ContinuousAssignment::plain_scoped(
                                            sub_expr,
                                            parent_elem,
                                            true,
                                        ),
                                    );
                                }
                                Some(PortDirection::Output) => {
                                    elab.continuous_assigns.push(ContinuousAssignment::plain(
                                        parent_elem,
                                        sub_expr,
                                    ));
                                }
                                _ => {}
                            }
                        }
                        continue;
                    }
                    // Dump-only net collapsing: the formal and a whole-net actual
                    // are ONE physical net (see `ElaboratedModule::port_aliases`).
                    // Anything that is not a plain hierarchical identifier — a
                    // bit/part-select, a concat, an expression, a literal — is a
                    // separate object and gets no alias. A net reached through
                    // an indexed SCOPE (`g[1].w`, §27.6) names a whole net, so
                    // it does get one.
                    if let Some(actual) = whole_net_ident_name_scoped(parent_expr, elab).or_else(|| {
                        if prepared_sub.port_directions.get(port_name) != Some(&PortDirection::Inout) {
                            return None;
                        }
                        let (cell, base) = fixed_net_cell(elab, parent_expr)?;
                        elab.nets.insert(cell.clone());
                        if let Some(k) = elab.resolved_net_kinds.get(base.as_str()).cloned() {
                            elab.resolved_net_kinds.insert(cell.clone(), k);
                        }
                        Some(cell)
                    }) {
                        // §23.3.3.2: only a formal that is a NET is merged with
                        // its actual. A formal that declares a VARIABLE
                        // (`input var`) is connected by an implied continuous
                        // assignment — a COPY — so the formal keeps its own
                        // storage and a force on it does not reach the actual.
                        let formal_is_net = is_net_name(elab, &sub_sig_name);
                        let actual_is_net = is_net_name(elab, &actual);
                        if formal_is_net || !actual_is_net {
                            elab.port_aliases
                                .insert(sub_sig_name.clone(), actual.as_str().into());
                            // §23.3.3.3: an INOUT port and the net it is
                            // connected to are ONE physical net. An input
                            // port copies the actual into the formal and an
                            // output port copies the formal onto the actual,
                            // so neither merges the two nets.
                            if formal_is_net
                                && actual_is_net
                                && matches!(
                                    prepared_sub.port_directions.get(port_name),
                                    Some(PortDirection::Inout)
                                )
                            {
                                elab.net_port_merges
                                    .insert(sub_sig_name.clone(), actual.clone());
                            }
                            // §23.3.3.7, Table 23-1: the formal and the
                            // actual become ONE net, and an internal tri0,
                            // tri1 or supply net dominates an external
                            // `wire`: the merged net is tri0/tri1/supply.
                            // After port substitution the sub-module's writes
                            // land on the ACTUAL (`w`/`p`), so the implicit
                            // pull has to be there, not only on the leftover
                            // port signal (`u_diff.p`) — otherwise the
                            // outside wire reads z while the port reads 1
                            // (#1060). An actual with a net type of its own
                            // other than `wire` keeps it (the table's
                            // "external" cells).
                            if elab.nets.contains(&actual) {
                                let formal_kind =
                                    elab.resolved_net_kinds.get(&sub_sig_name).cloned();
                                let formal_supply = elab.supply_nets.contains(&sub_sig_name);
                                let have_own = elab.resolved_net_kinds.contains_key(&actual)
                                    || elab.supply_nets.contains(&actual);
                                if !have_own {
                                    // §6.6.5, §6.6.6: with no driver at all
                                    // the merged net rests at the dominating
                                    // net's value (1 for tri1), which no fold
                                    // computes.
                                    let rest = matches!(
                                        formal_kind,
                                        Some(ResolvedNetKind::Tri0 | ResolvedNetKind::Tri1)
                                    ) || formal_supply;
                                    if let Some(k) = formal_kind {
                                        elab.resolved_net_kinds.insert(actual.clone(), k);
                                    }
                                    if formal_supply {
                                        elab.supply_nets.insert(actual.clone());
                                    }
                                    if rest
                                        && let Some(v) = elab
                                            .signals
                                            .get(&sub_sig_name)
                                            .filter(|f| !f.is_real)
                                            .map(|f| (f.width, f.value.clone()))
                                        && let Some(asig) = elab.signals.get_mut(&actual)
                                        && !asig.is_real
                                        && asig.width == v.0
                                    {
                                        asig.value = v.1;
                                    }
                                }
                            }
                        }
                    } else if let Some(pull) =
                        tri_port_select_pull(parent_expr, &sub_sig_name, elab)
                    {
                        elab.continuous_assigns.push(pull);
                    }
                    // §23.3.3.7 port collapsing: a port bound to a NET (whole,
                    // a select, or a concatenation of them) merges with that
                    // net into one, and the merged net carries the EXTERNAL
                    // net's delay — the reference drops the port's own net
                    // delay (`output o; wire #4 o;` on `.o(w)` follows `w`).
                    // A port on a variable or an expression, or left open,
                    // stays a net of its own and keeps its delay.
                    if elab.net_delays.contains_key(&sub_sig_name)
                        && elab.nets.contains(&sub_sig_name)
                        && is_net_lvalue(parent_expr, &|n| elab.nets.contains(n))
                    {
                        elab.net_delays.remove(&sub_sig_name);
                    }
                    let plain_parent = ContinuousAssignment::plain_ident_name(parent_expr);
                    match prepared_sub.port_directions.get(port_name) {
                        Some(PortDirection::Input) | Some(PortDirection::Inout) => {
                            // §23.3.3.6: a port connection is an implicit
                            // continuous assignment, so a NARROWER actual on
                            // an INPUT extends to the formal width like any
                            // assignment (`.p(1'b0)` on a 4-bit port reads
                            // 0000). One reference simulator instead leaves
                            // the unconnected high bits z ("zzzz1010"
                            // measured) and this code used to copy that; the
                            // LRM reading — which the other reference
                            // implements — was chosen after the z bits walked
                            // through a production DUT's CDC and stalled its
                            // write path as X.
                            //
                            // An INOUT keeps the z-fill: it is bidirectional,
                            // and driving the unconnected high bits would
                            // fight the sub-module's own driver.
                            let is_inout = matches!(
                                prepared_sub.port_directions.get(port_name),
                                Some(PortDirection::Inout)
                            );
                            let mut zfill_width: Option<u32> = None;
                            if is_inout {
                                let fw = elab
                                    .signals
                                    .get(&sub_sig_name)
                                    .map(|s| s.width)
                                    .unwrap_or(0);
                                let is_real_port = elab
                                    .signals
                                    .get(&sub_sig_name)
                                    .map(|s| s.is_real)
                                    .unwrap_or(false);
                                if !is_real_port && fw > 0 {
                                    if let Some(aw) = port_conn_width(parent_expr, elab) {
                                        if aw > 0 && aw < fw {
                                            zfill_width = Some(fw - aw);
                                        }
                                    }
                                }
                            }
                            if !is_inout {
                                input_connects
                                    .push((port_name.clone(), elab.continuous_assigns.len()));
                            }
                            if zfill_width.is_none()
                                && let Some(parent_name) = plain_parent
                            {
                                elab.continuous_assigns.push(ContinuousAssignment::plain_link(
                                    sub_sig_name.as_str(),
                                    parent_name,
                                    true,
                                ));
                            } else {
                                let sub_expr = make_ident_expr(&sub_sig_name);
                                let mut rhs = parent_expr.clone();
                                if let Some(zw) = zfill_width {
                                    let span = parent_expr.span;
                                    let zfill = Expression::new(
                                        ExprKind::Number(
                                            crate::ast::expr::NumberLiteral::Integer {
                                                size: Some(zw),
                                                signed: false,
                                                base: crate::ast::expr::NumberBase::Binary,
                                                value: "z".to_string(),
                                                cached_val: crate::ast::cache::LiteralCache::new(
                                                    None,
                                                ),
                                            },
                                        ),
                                        span,
                                    );
                                    rhs = Expression::new(
                                        ExprKind::Concatenation(vec![zfill, rhs]),
                                        span,
                                    );
                                }
                                elab.continuous_assigns.push(ContinuousAssignment::plain_scoped(
                                    sub_expr, rhs, true,
                                ));
                            }
                        }
                        Some(PortDirection::Output) => {
                            if let Some(parent_name) = plain_parent {
                                elab.continuous_assigns.push(ContinuousAssignment::plain_link(
                                    parent_name,
                                    sub_sig_name.as_str(),
                                    false,
                                ));
                            } else {
                                elab.continuous_assigns.push(ContinuousAssignment::plain(
                                    parent_expr.clone(),
                                    make_ident_expr(&sub_sig_name),
                                ));
                            }
                        }
                        _ => {
                            if let Some(parent_name) = plain_parent {
                                elab.continuous_assigns.push(ContinuousAssignment::plain_link(
                                    sub_sig_name.as_str(),
                                    parent_name,
                                    true,
                                ));
                            } else {
                                elab.continuous_assigns.push(ContinuousAssignment::plain_scoped(
                                    make_ident_expr(&sub_sig_name),
                                    parent_expr.clone(),
                                    true,
                                ));
                            }
                        }
                    }
                }

                // Pre-simulation connectivity lint: every bound port's own
                // signal (registered above for both ANSI and non-ANSI styles)
                // carries the FORMAL width under this instance's parameters;
                // compare with each actual's self-determined width and warn on
                // mismatch, naming the instance and port.
                //
                // The same walk decides which INPUT ports must keep their own
                // signal instead of being substituted away — see
                // `no_subst_ports` and the `rewrite_port_map` filter below.
                let mut no_subst_ports: std::collections::HashSet<String> =
                    std::collections::HashSet::default();
                for (pname, actual) in port_map.iter() {
                    // §23.3.3: an unpacked formal keeps its own index range.
                    let array_formal = cat2(&inst_prefix, pname);
                    if elab.arrays.contains_key(&array_formal)
                        || elab.arrays_2d.contains_key(&array_formal)
                        || elab.arrays_nd.contains_key(&array_formal)
                    {
                        no_subst_ports.insert(pname.clone());
                    }
                    // §23.3.3: "If only one of the two connections is of a
                    // user-defined nettype then ... the connection shall be
                    // treated as a continuous assignment from source to
                    // sink"; only connections of the same nettype merge into
                    // one simulated net. An input formal of a user-defined
                    // nettype therefore keeps its own net, driven by the
                    // connection assign and resolved by the nettype's
                    // resolution function (§6.6.7), unless the actual is a
                    // whole net of that nettype. Substituting a variable, a
                    // literal or a member select renames the formal onto it,
                    // and every read of the formal then skips the resolution
                    // function. Checked before the signal lookup below: a
                    // nettype over an unpacked struct has no signal of its
                    // own, only member leaves.
                    if matches!(
                        prepared_sub.port_directions.get(pname.as_str()),
                        Some(PortDirection::Input)
                    ) && let Some(formal_nettype) =
                        user_nettype_of(elab, &cat2(&inst_prefix, pname))
                        && whole_net_ident_name_scoped(actual, elab)
                            .and_then(|n| user_nettype_of(elab, &n))
                            .is_none_or(|t| t != formal_nettype)
                    {
                        no_subst_ports.insert(pname.clone());
                    }
                    let Some(formal) = elab
                        .signals
                        .get(&cat2(&inst_prefix, &pname))
                        .map(|s| (s.width, s.is_signed))
                    else {
                        continue;
                    };
                    let (formal, formal_signed) = formal;
                    // Only a pure INPUT — one the body never drives — can be
                    // safely de-substituted. A driven port (illegal for an
                    // input, but xezim allows it) must keep reaching the
                    // parent net through substitution; see
                    // `PreparedModuleItems::body_driven_ports`.
                    let is_input = matches!(
                        prepared_sub.port_directions.get(pname.as_str()),
                        Some(PortDirection::Input)
                    ) && !prepared_sub.body_driven_ports.contains(pname.as_str());
                    // §23.3.3.2: a formal that declares a VARIABLE
                    // (`input var`) is connected by an implied continuous
                    // assignment — a COPY of the actual, not a merge with
                    // it. The body reads the formal's own storage, which
                    // the connection drives; substituting the actual would
                    // rename the formal onto the actual and make the two
                    // one object, so a force on the formal would reach the
                    // actual as well (§10.6.2).
                    let formal_is_net = is_net_name(elab, &cat2(&inst_prefix, &pname));
                    let actual_is_net = whole_net_ident_name_scoped(actual, elab)
                        .is_some_and(|n| is_net_name(elab, &n));
                    if is_input && !formal_is_net && actual_is_net {
                        no_subst_ports.insert(pname.clone());
                    }
                    // §6.7.1: an input port whose net keeps a net delay (see
                    // the port-collapsing note above) is read THROUGH that
                    // delay; substituting the actual would read around it.
                    if is_input && elab.net_delays.contains_key(&cat2(&inst_prefix, &pname)) {
                        no_subst_ports.insert(pname.clone());
                    }
                    // §23.3.3: a port connection is a continuous assignment.
                    // Substituting an actual that COMPUTES something pastes
                    // the computation into every read of the port — a decoder
                    // term `(addr % 1024) / 128 == m` fed to 128 rows was
                    // evaluated 128 times per address change instead of once.
                    // Such an input reads its own net, driven once by the
                    // connection assign; only a rename (a net, a constant
                    // select of one, a literal, a concatenation of those) is
                    // substituted.
                    if is_input && !port_actual_is_simple(actual, local_params, &elab.parameters) {
                        no_subst_ports.insert(pname.clone());
                    }
                    let mut literal_actual: &Expression = actual;
                    while let ExprKind::Paren(inner) = &literal_actual.kind {
                        literal_actual = inner;
                    }
                    // §6.11.2, §23.3.3.8: a 2-state formal reads its actual
                    // through an assignment that maps X and Z to 0.
                    // Substituting a 4-state net, variable or X-bearing
                    // parameter renamed the formal onto it, so the body read
                    // the X and Z bits (`input var bit [3:0] b` bound to a
                    // `logic` holding 4'b1x01 printed 1x01). Keep the formal,
                    // whose connection assign converts. A literal actual is
                    // converted in place instead (`port_literal_for_formal`).
                    if is_input
                        && !matches!(
                            literal_actual.kind,
                            ExprKind::Number(_) | ExprKind::StringLiteral(_)
                        )
                        && elab.two_state_signals.contains(&array_formal)
                        && port_actual_may_carry_xz(actual, elab, local_params)
                    {
                        no_subst_ports.insert(pname.clone());
                    }
                    // §23.3.3.8, §6.12.1: a real net, variable or parameter
                    // on an integral formal, or an integral one on a real
                    // formal, converts through the connection assign. A
                    // literal is converted in place (`port_literal_for_formal`).
                    if is_input
                        && let ExprKind::Ident(h) = &literal_actual.kind
                        && let Some(n) = whole_net_ident_name(literal_actual)
                        && let Some(actual_real) = match elab.signals.get(&n) {
                            Some(s) => Some(s.is_real),
                            None => port_actual_param(h, local_params, elab).map(|v| v.is_real),
                        }
                        && elab.signals.get(&array_formal).is_some_and(|f| {
                            f.is_real != actual_real
                                // §6.12, §23.3.3.8: a shortreal formal rounds a
                                // real actual to binary32, so it keeps its own
                                // storage too (and a real formal a shortreal one).
                                || (f.is_real
                                    && signal_is_shortreal(elab, &array_formal)
                                        != signal_is_shortreal(elab, &n))
                        })
                    {
                        no_subst_ports.insert(pname.clone());
                    }
                    // §23.3.3.8: "The sign attribute shall not cross hierarchy".
                    // Substituting a signed formal `input int p` by an unsigned
                    // whole-net or concatenation/replication actual renames the
                    // formal onto the actual, so a pure SIGN flip silently stops
                    // happening: `input int` bound to `{1{x}}` read 4294967291
                    // instead of -5. §11.8.1 always leaves a concatenation or
                    // replication unsigned; keep the formal so its own sign
                    // governs the body and the connection assign converts.
                    // An element of a signed unpacked array or a signed member
                    // is no bit-select: it keeps its declared sign (§7.4.1).
                    if is_input
                        && formal_signed
                        && port_actual_is_unsigned_concat(actual)
                        && declared_select_signedness(actual, elab, formal) != Some(true)
                    {
                        no_subst_ports.insert(pname.clone());
                    }
                    // §23.3.3.8 (generalized): "The sign attribute shall not
                    // cross hierarchy." The concat rule above is one instance;
                    // an equal-width WHOLE-NET actual of the opposite sign
                    // breaks substitution the same way. A signed `input int p`
                    // bound to an UNSIGNED `logic [31:0] u` — or an unsigned
                    // `input [31:0] p` bound to a SIGNED `int s` — must keep
                    // its own storage so the connection assign converts the
                    // bits through the FORMAL's sign; renaming the formal onto
                    // the actual reads the actual's bits with the actual's sign
                    // and the sign flip silently stops (`q = p` then zero- vs
                    // sign-extended the wrong way).
                    if is_input
                        && let Some(n) = whole_net_ident_name(actual)
                        && let Some(asig) = elab.signals.get(&n)
                        && asig.is_signed != formal_signed
                    {
                        no_subst_ports.insert(pname.clone());
                    }
                    // §7.4.1: a packed multi-D formal indexes by its OWN
                    // element stride. Substituting the actual makes `p[i]`
                    // index the actual instead, so the stride silently becomes
                    // whatever the parent net happens to be declared as — 1 bit
                    // for a flat vector / concat / part-select, or the parent's
                    // own element width for a differently-shaped packed array.
                    if is_input
                        && elab
                            .packed_signal_elem_widths
                            .get(&cat2(&inst_prefix, &pname))
                            .is_some_and(|&w| w > 1)
                    {
                        no_subst_ports.insert(pname.clone());
                    }
                    // §7.4.1: a formal whose packed range is not `[N:0]`
                    // indexes by its own labels (`input [11:2] p`,
                    // `input [0:7] p`). Substituting a zero-based actual — a
                    // part-select `addr[2+:10]`, a constant range, a concat,
                    // a `[N:0]` net — makes `p[k]` index THAT value. The
                    // labels then land on the wrong physical bits, and a
                    // label past the actual's MSB is X. The connection
                    // assign keeps the formal, stored LSB-aligned and
                    // selected with its declared bounds.
                    if is_input
                        && elab
                            .packed_full_dims
                            .get(&cat2(&inst_prefix, &pname))
                            .is_some_and(|d| d.iter().any(|&(l, r)| r != 0 || l < 0))
                    {
                        no_subst_ports.insert(pname.clone());
                    }
                    // The mirror case: a `[N:0]` formal bound to a WHOLE net
                    // whose own range is not `[N:0]` (`logic [0:7] a` to
                    // `input [7:0] p`). Substituting renames `p[0]` to `a[0]`,
                    // the actual's MSB, where §23.3.3 pairs the formal's bit
                    // 0 with the actual's LSB `a[7]`. Keep the formal then too.
                    if is_input
                        && !elab.packed_full_dims.contains_key(&cat2(&inst_prefix, &pname))
                        && whole_net_ident_name(actual)
                            .is_some_and(|n| elab.packed_full_dims.contains_key(&n))
                    {
                        no_subst_ports.insert(pname.clone());
                    }
                    // §5.7.1/§23.3.3: a fill literal (`'0`, `'1`, `'x`, `'z`)
                    // has no width of its own; it takes the FORMAL's width
                    // through the connection assign. Substituting it hands
                    // the body a one-bit literal, so `$bits(p)` read 1 and
                    // `%b` printed one digit while selects still worked.
                    let mut fill_actual: &Expression = actual;
                    while let ExprKind::Paren(inner) = &fill_actual.kind {
                        fill_actual = inner;
                    }
                    if is_input
                        && formal != 0
                        && matches!(
                            &fill_actual.kind,
                            ExprKind::Number(NumberLiteral::UnbasedUnsized(_))
                        )
                    {
                        no_subst_ports.insert(pname.clone());
                    }
                    // §6.6.5: a high-impedance driver lets the pull value win.
                    // §6.6.4: a trireg holds its charge on the bits no driver
                    // drives. Either needs the formal's own net when the
                    // actual can carry Z: a Z-bearing literal, a 4-state
                    // variable, a parameter or a concatenation. A whole net
                    // collapses with the formal into the dominating net type
                    // instead (§23.3.3.7, see `port_aliases`).
                    if is_input
                        && port_actual_may_carry_xz(fill_actual, elab, local_params)
                        && !whole_net_ident_name_scoped(actual, elab)
                            .is_some_and(|n| is_net_name(elab, &n))
                        && matches!(
                            elab.resolved_net_kinds.get(&array_formal),
                            Some(
                                ResolvedNetKind::Tri0
                                    | ResolvedNetKind::Tri1
                                    | ResolvedNetKind::ChargeStorage
                            )
                        )
                    {
                        no_subst_ports.insert(pname.clone());
                    }
                    // §7.2.1/§23.3.3: a PACKED-STRUCT formal read member-wise
                    // (`din.f0`) needs its own member layout. Substituting a
                    // FLAT actual (a plain vector net, a concat, a select)
                    // hands the body a name with no layout, so every member
                    // read went x while the whole-port read stayed right —
                    // the same conversion block worked when the parent net
                    // happened to be struct-typed. Keep the formal's signal
                    // unless the actual carries the same member layout.
                    // A selected struct array element keeps its parent's field
                    // layout. A selected packed vector has element widths
                    // but no field names (#1645).
                    let formal_key = cat2(&inst_prefix, &pname);
                    if is_input
                        && elab.packed_struct_fields.contains_key(&formal_key)
                        && !elab.packed_signal_elem_widths.contains_key(&formal_key)
                    {
                        let mut root: &Expression = actual;
                        loop {
                            match &root.kind {
                                ExprKind::Index { expr, .. }
                                | ExprKind::RangeSelect { expr, .. } => root = expr,
                                ExprKind::Paren(inner) => root = inner,
                                _ => break,
                            }
                        }
                        let actual_layout = whole_net_ident_name(root)
                            .and_then(|n| elab.packed_struct_fields.get(&n));
                        if actual_layout != elab.packed_struct_fields.get(&formal_key) {
                            no_subst_ports.insert(pname.clone());
                        }
                    }
                    // §23.3.3.7, §11.8.1: the formal's own declaration decides
                    // whether the body reads the port as signed, and the
                    // connection converts the actual to it. A select or a
                    // concatenation is unsigned, so substituting
                    // `{c[11], c}` for `input logic signed [12:0] e_i` made
                    // `e_i < 0` false and `a_i - e_i` unsigned in the body.
                    // Keep the formal unless the actual is known to have the
                    // formal's signedness: an element of a signed unpacked
                    // array or a signed struct member renamed into an unsigned
                    // port made `p < 0` true there.
                    // A literal is exempt: `port_literal_for_formal` converts it
                    // to the formal's type in place (`.en(1)`, an unsized and so
                    // signed decimal, into `input logic en`), and a real literal
                    // into a real formal needs no conversion.
                    if is_input
                        && !matches!(
                            literal_actual.kind,
                            ExprKind::Number(_) | ExprKind::StringLiteral(_)
                        )
                    {
                        let formal_signed =
                            elab.signals.get(&formal_key).is_some_and(|s| s.is_signed);
                        if simple_actual_signedness(actual, elab, local_params)
                            .or_else(|| declared_select_signedness(actual, elab, formal))
                            != Some(formal_signed)
                        {
                            no_subst_ports.insert(pname.clone());
                        }
                    }
                    let Some(actual_w) = port_conn_width(actual, elab) else {
                        continue;
                    };
                    if actual_w != formal && actual_w != 0 && formal != 0 {
                        // §23.3.3: the formal keeps its declared size and the
                        // CONNECTION truncates/extends. Substitution would hand
                        // the body the actual's width instead, so `$bits(p)`
                        // reported the parent net's size.
                        if is_input {
                            no_subst_ports.insert(pname.clone());
                        }
                        warn_port_width_mismatch(
                            sub_mod_name,
                            pname,
                            formal,
                            actual_w,
                            &inst_prefix,
                            actual,
                            elab,
                            source_def.name(),
                        );
                    }
                }

                // Build a rewrite_port_map that excludes output ports.
                // Output ports should use the local prefixed name (inst_prefix + port_name)
                // rather than the parent expression, because:
                //   - Input ports: the sub-module reads from the parent → use parent expr
                //   - Output ports: the sub-module writes to its local reg → use prefixed local name
                //     (a continuous assign parent = local handles the connection)
                //
                // Substituting the actual for an input port is a rename, and a
                // rename is only sound when formal and actual have the same
                // shape: the formal's declared type is what governs `$bits` and
                // every select inside the body (§23.3.3). `no_subst_ports`
                // (built with the width lint above) carries the inputs where
                // the two disagree — those resolve to `<inst>.<port>` instead,
                // which is registered with the FORMAL's width and element
                // stride and is driven by the connection assign pushed above.
                for port in &prepared_sub.sampled_ports {
                    elab.sampled_input_ports.insert(cat2(&inst_prefix, port));
                }
                let mut rewrite_port_map: HashMap<String, Expression> = port_map
                    .iter()
                    .filter(|(name, _)| {
                        !matches!(
                            prepared_sub.port_directions.get(name.as_str()),
                            Some(PortDirection::Output)
                        ) && !no_subst_ports.contains(name.as_str())
                            && !prepared_sub.sampled_ports.contains(name.as_str())
                    })
                    .map(|(name, actual)| {
                        let converted = if matches!(
                            prepared_sub.port_directions.get(name.as_str()),
                            Some(PortDirection::Input)
                        ) && !prepared_sub.body_driven_ports.contains(name.as_str())
                            && !string_ports.contains(name.as_str())
                        {
                            port_literal_for_formal(
                                actual,
                                &inst_prefix,
                                name,
                                elab,
                                &resolved_two_state_ports,
                            )
                        } else {
                            None
                        };
                        (name.clone(), converted.unwrap_or_else(|| actual.clone()))
                    })
                    .collect();
                // §8.3 / §23.6: a module-instance class cannot replace a
                // same-named compilation-unit or sibling-instance class.
                let class_bindings: HashMap<String, Expression> = prepared_sub
                    .effective_items
                    .iter()
                    .filter_map(|item| {
                        let name = match item {
                            ModuleItem::ClassDeclaration(cd) => &cd.name.name,
                            ModuleItem::TypedefDeclaration(td) => &td.name.name,
                            _ => return None,
                        };
                        Some((name.clone(), make_ident_expr(&cat2(&inst_prefix, name))))
                    })
                    .collect();
                rewrite_port_map.extend(class_bindings.clone());
                // The actuals themselves are read from the finished table
                // below (`InputPortActual`), not copied out of it here.
                let mut input_actuals: Vec<(String, usize, bool)> = Vec::new();
                for pname in rewrite_port_map.keys() {
                    if matches!(
                        prepared_sub.port_directions.get(pname.as_str()),
                        Some(PortDirection::Input)
                    ) {
                        // §6.8: the formal starts at its own initial value,
                        // 0 for a 2-state type and z for a 4-state one
                        // (`default_port_value`); a scalar ANSI port is not
                        // in `two_state_signals`.
                        let formal = cat2(&inst_prefix, pname);
                        let two_state = elab.two_state_signals.contains(&formal)
                            || elab
                                .signals
                                .get(&formal)
                                .is_some_and(|s| !s.is_real && !s.value.has_xz());
                        let name_start = formal.len() - pname.len();
                        input_actuals.push((formal, name_start, two_state));
                    }
                }

                // Unobserved-port elision (see `set_port_elision`): a plain
                // input whose every read in the body was just substituted by
                // its actual keeps its net only for name observers. With none
                // possible — none at run time (the driver's switch), none in
                // the sources (no dotted reference ends in or passes through
                // this port's name, no by-name system task, no DPI) and none
                // in the child itself (`port_elision_blocked_by_items`) — the
                // connection assign and the net are left out altogether.
                if !input_connects.is_empty() && matches!(sub_mod, Definition::Module(_)) {
                    let dotted = PORT_ELISION_DOTTED.with(|d| d.borrow().clone());
                    if let Some(dotted) = dotted {
                        // A module, interface or program instance inlines
                        // through the substitution; a UDP or checker
                        // instance does not.
                        let plain_inst = |name: &str| {
                            matches!(
                                definitions.get(name),
                                Some(
                                    Definition::Module(_)
                                        | Definition::Interface(_)
                                        | Definition::Program(_)
                                )
                            ) && !elab.checker_decls.contains_key(name)
                        };
                        let bind_blocks_elision = cache.unit_module_binds.contains_key(sub_mod_name)
                            || match bind_state.as_deref_mut() {
                                Some(bs)
                                    if bs.filter.has_non_plain_bind
                                        && bs.filter.matches(
                                            inst_prefix.trim_end_matches('.'),
                                            sub_mod_name,
                                        ) =>
                                {
                                    bs.kept_bound_ports = true;
                                    true
                                }
                                _ => false,
                            };
                        if !bind_blocks_elision
                            && !port_elision_blocked_by_items(
                                &prepared_sub.effective_items,
                                &plain_inst,
                            )
                        {
                            let mut drop_idx: Vec<usize> = Vec::new();
                            for (pname, idx) in &input_connects {
                                let formal = cat2(&inst_prefix, pname);
                                let elidable = rewrite_port_map.contains_key(pname.as_str())
                                    && !dotted.contains(pname.as_str())
                                    && !prepared_sub.body_driven_ports.contains(pname.as_str())
                                    && !interconnect_ports.contains(pname.as_str())
                                    && elab.signals.contains_key(&formal)
                                    && !elab.packed_struct_fields.contains_key(&formal)
                                    && !elab.packed_signal_elem_widths.contains_key(&formal)
                                    // A `[0:7]` or `[8:1]` formal indexes by
                                    // its own range, which lookups of the
                                    // substituted actual can still consult
                                    // under the instance scope.
                                    && !elab.ascending_packed.contains_key(&formal)
                                    && elab.packed_full_dims.get(&formal).is_none_or(|d| {
                                        d.iter().all(|&(l, r)| r == 0 && l >= 0)
                                    })
                                    && !elab.net_delays.contains_key(&formal)
                                    && !elab.events.contains(&formal)
                                    && port_decl_is_plain(
                                        &sub_mod,
                                        &prepared_sub.effective_items,
                                        pname,
                                    )
                                    && elab.continuous_assigns.get(*idx).is_some_and(|ca| {
                                        ca.delay() == 0
                                            && ca.delay_fall().is_none()
                                            && ca.delay_off().is_none()
                                            && ca.lhs_ident_name().as_deref()
                                                == Some(formal.as_str())
                                    });
                                if elidable {
                                    // `.clk(clk)` from the top substitutes the
                                    // bare `clk`, which a lookup under this
                                    // instance's scope tries as `<inst>.clk`
                                    // first — the net being left out — before
                                    // the top-level `clk` it stood for. Such a
                                    // probe is harmless, so it is not tracked.
                                    let bare_same_name = rewrite_port_map
                                        .get(pname.as_str())
                                        .is_some_and(|m| match &m.kind {
                                            ExprKind::Ident(h) => {
                                                h.root.is_none()
                                                    && h.path.len() == 1
                                                    && h.path[0].selects.is_empty()
                                                    && h.path[0].name.name == *pname
                                            }
                                            _ => false,
                                        });
                                    forget_elided_port(elab, &formal, pname, !bare_same_name);
                                    drop_idx.push(*idx);
                                }
                            }
                            // Indices ascend (pushed in order); remove from the
                            // back so earlier ones stay valid.
                            for idx in drop_idx.into_iter().rev() {
                                elab.continuous_assigns.remove(idx);
                            }
                        }
                    }
                }

                // Build ONE RewriteCtx for this instance, shared (via Rc) across
                // every pending always/initial/cont-assign it produces. The
                // prefix, port_map and interface_map are instance-constant, so
                // cloning them once here instead of per pending item collapses
                // the duplicated port-map entries (on c910: ~10.8M -> ~1.2M),
                // the dominant elaboration memory cost. `local_names` was already
                // Rc-shared across sibling instances.
                // Per-instance type-parameter bindings for statement
                // substitution — see `RewriteCtx::type_binds`.
                let mut pend_type_binds: HashMap<String, DataType> = HashMap::default();
                // An input actual whose table entry a type parameter's class
                // receiver of the same name replaces below.
                let mut displaced_actuals: HashMap<String, Expression> = HashMap::default();
                for p_decl in sub_mod.params_and_body_types() {
                    if let ParameterKind::Type { assignments } = &p_decl.kind {
                        for a in assignments {
                            let resolved = type_overrides
                                .iter()
                                .find(|(n, _)| n == &a.name.name)
                                .map(|(_, dt)| dt.clone())
                                .or_else(|| {
                                    a.init.as_ref().map(|dt| {
                                        resolve_typedef_chain(dt, &elab.typedef_types).clone()
                                    })
                                });
                            if let Some(mut resolved) = resolved {
                                // Same fold as the scoped alias below. Statement
                                // substitution (`word_t'(imm)`) bakes this
                                // binding in, and a later eval of `Cfg.W`
                                // against the flat table reads 0.
                                lsdd_data_type(&mut resolved, &sub_merged_params);
                                pend_type_binds.insert(a.name.name.clone(), resolved);
                            }
                        }
                    }
                }
                // §6.20.3 / §8.23: temporary elaboration bindings do not
                // survive inlining. Bake class-valued type parameters into
                // expression receivers as well as declaration data types.
                for (name, dt) in &pend_type_binds {
                    // §6.20.3: variables declared with a module type parameter
                    // need its binding after the temporary bare typedef is
                    // restored. Keep an instance-qualified alias for `new`,
                    // reflection and member access through those variables.
                    let key = cat2(&inst_prefix, name);
                    let mut scoped =
                        scope_local_typerefs(dt, &sub_typedef_names_all, &inst_prefix);
                    // §6.20.3: `localparam type word_t = logic [Cfg.W-1:0]`
                    // still names the member. The formal is renamed to this
                    // scoped key and its geometry is read from the flat
                    // parameter table. That table holds the struct value;
                    // the dotted member is only in this instance's map, so
                    // the bound evaluates as 0 and the formal is
                    // `logic [-1:0]` while its value keeps the real width.
                    // A part-select of it is then x. Fold the bounds with
                    // this instance's map before the alias is stored.
                    lsdd_data_type(&mut scoped, &sub_merged_params);
                    let width =
                        resolve_type_width(&scoped, Some(&sub_merged_params), Some(&elab.typedefs));
                    typedefs_insert_traced(
                        &mut elab.typedefs,
                        "insert:instance_type_parameter",
                        key.clone(),
                        width,
                    );
                    elab.typedef_types.insert(key, scoped);
                    if let Some(receiver) = module_class_scope::receiver(dt) {
                        if let Some(actual) = rewrite_port_map.insert(name.clone(), receiver) {
                            displaced_actuals.insert(name.clone(), actual);
                        }
                    }
                }
                // §23.3.3 (#721): the table is complete. The deferred bodies
                // of this instance and its input-port actuals read this one
                // copy; each used to retain a deep copy of every actual.
                let rewrite_port_map = Rc::new(rewrite_port_map);
                for (formal, name_start, two_state) in input_actuals {
                    let actual = match displaced_actuals.remove(&formal[name_start..]) {
                        Some(actual) => InputPortActual::owned(formal, actual, two_state),
                        None => InputPortActual::shared(
                            formal,
                            name_start,
                            Rc::clone(&rewrite_port_map),
                            two_state,
                        ),
                    };
                    elab.input_port_actuals.push(actual);
                }
                let pend_type_bind_widths: HashMap<String, u32> = pend_type_binds
                    .iter()
                    .map(|(n, dt)| {
                        (
                            n.clone(),
                            resolve_type_width(dt, Some(&sub_merged_params), Some(&elab.typedefs)),
                        )
                    })
                    .collect();
                // §20.7: the same answers the constant queries give, from the
                // shapes registered for this instance (`saved_type_shapes`).
                let pend_type_bind_queries: HashMap<String, TypeQueryDims> = TYPEDEF_SHAPES_TLS
                    .with(|sh| {
                        let sh = sh.borrow();
                        pend_type_binds
                            .keys()
                            .filter_map(|n| {
                                let q = type_query_dims_by_name(
                                    n,
                                    Some(&sub_merged_params),
                                    Some(&elab.typedefs),
                                    Some(&sh.0),
                                    Some(&sh.1),
                                )?;
                                Some((n.clone(), q))
                            })
                            .collect()
                    });
                let pend_ctx = std::rc::Rc::new(RewriteCtx {
                    prefix: inst_prefix.clone(),
                    origin_scope: inst_prefix.trim_end_matches('.').into(),
                    port_map: Rc::clone(&rewrite_port_map),
                    local_names: std::rc::Rc::clone(&prepared_sub.local_names),
                    interface_map: sub_interface_map.clone(),
                    type_binds: cache.type_binds.intern(pend_type_binds),
                    type_bind_widths: cache.type_widths.intern(pend_type_bind_widths),
                    type_bind_queries: cache.type_queries.intern(pend_type_bind_queries),
                    owner: sub_mod.name().to_string(),
                    upward: Rc::clone(&elab.upward_scopes),
                });
                // §6.6.7, §10.3.1: a nettype net's initializer drives the net
                // like a net declaration assignment, in the instance's scope.
                for (name, init_expr) in nettype_decl_inits.drain(..) {
                    let span = init_expr.span;
                    elab.pending_cont_assign.push(PendingContAssign::new(
                        std::rc::Rc::new(make_ident_expr(&name)),
                        true,
                        std::rc::Rc::new(init_expr),
                        std::rc::Rc::clone(&pend_ctx),
                        None,
                        None,
                        None,
                        None,
                        Some(span),
                    ));
                }

                crate::oom_trace::checkpoint(
                    "retain instance context",
                    &[
                        ("signals", elab.signals.len()),
                        ("type_bindings", pend_ctx.type_binds.len()),
                        ("type_widths", pend_ctx.type_bind_widths.len()),
                        ("type_queries", pend_ctx.type_bind_queries.len()),
                        ("port_bindings", pend_ctx.port_map.len()),
                        ("interface_bindings", pend_ctx.interface_map.len()),
                        ("local_names", pend_ctx.local_names.len()),
                        ("prepared_bodies", cache.prepared.len()),
                    ],
                );

                // §6.8: the deferred (non-constant) declaration initializers of
                // this instance, in DECLARATION ORDER and ahead of the
                // instance's own initial blocks (pushed further below). One
                // SeqBlock keeps the order; the LHS is already the
                // instance-qualified signal, the RHS is rewritten into the
                // instance scope so sibling references resolve.
                if !deferred_decl_inits.is_empty() {
                    let stmts: Vec<Statement> = deferred_decl_inits
                        .drain(..)
                        .map(|(target, init_expr)| {
                            let rhs = rewrite_expr(
                                &init_expr,
                                &inst_prefix,
                                &rewrite_port_map,
                                &prepared_sub.local_names,
                                &sub_interface_map,
                            );
                            Statement::new(
                                StatementKind::BlockingAssign {
                                    lvalue: make_ident_expr(&target),
                                    rvalue: rhs,
                                },
                                Span::dummy(),
                            )
                        })
                        .collect();
                    // §6.8: "variable declaration assignments ... shall occur
                    // before any initial or always block is started", so this
                    // goes on the STATIC-init list, which the simulator
                    // schedules ahead of every initial block. Using
                    // `initial_blocks` was not enough: an inlined child's own
                    // blocks travel via `pending_initial`, which is chained
                    // FIRST, so the initializer landed after the code reading it.
                    // Both sides are already instance-qualified (LHS is
                    // `sig_name`, RHS went through `rewrite_expr`), so the block
                    // carries NO scope — a scope would look for
                    // `<inst>.<inst>.name`. However, a `%m` in the RHS (e.g. a
                    // class `A a = new($sformatf("%m.xxx"))`) MUST see this
                    // instance's scope or it degrades to the top module name.
                    // The block IS instance-scoped, so carry the instance
                    // prefix; name resolution tolerates the wrap (a scoped
                    // lookup that misses falls back to the bare name). Covered
                    // by the hierarchy group's percent_m_module_init_scope self-test.
                    elab.static_init_blocks.push(InitialBlock {
                        stmt: Statement::new(
                            StatementKind::SeqBlock { name: None, stmts: stmts.into() },
                            Span::dummy(),
                        ),
                        scope: inst_prefix.trim_end_matches('.').to_string(),
                    });
                }

                // A task/function formal whose width uses a MODULE PARAMETER
                // (`input [word_width-1:0] d`) must have that parameter baked in
                // NOW — the sub-module is being inlined, so its params won't be
                // in the flat param map when the formal's width is resolved at
                // call time, and the formal would collapse to 1 bit. Substitute
                // the sub-instance's resolved params into the formals' data
                // types + unpacked dims.
                // §13.3/#721: only callable signatures need these literal
                // expressions. Empty instances must not copy every ancestor's
                // parameters into another retained map at each hierarchy level.
                let mut param_expr_map: HashMap<String, Expression> = if prepared_sub.has_subroutines {
                    sub_merged_params
                        .iter()
                        .filter_map(|(k, v)| {
                            v.to_i64()?;
                            // §6.20.2: a substituted parameter keeps its type.
                            // A signed 32-bit genvar literal widened narrow
                            // arithmetic in a signature's $rtoi argument.
                            let literal = if v.is_real {
                                NumberLiteral::Real(v.to_f64())
                            } else if v.is_fill {
                                NumberLiteral::UnbasedUnsized(v.to_bin_string().chars().last()?)
                            } else {
                                NumberLiteral::Integer {
                                    size: Some(v.width),
                                    signed: v.is_signed,
                                    base: NumberBase::Binary,
                                    value: v.to_bin_string(),
                                    cached_val: crate::ast::cache::LiteralCache::new(None),
                                }
                            };
                            Some((
                                k.clone(),
                                Expression::new(ExprKind::Number(literal), Span::dummy()),
                            ))
                        })
                        .collect()
                } else {
                    HashMap::default()
                };
                let member_replacements: Vec<_> = param_expr_map
                    .iter()
                    .filter(|(name, _)| name.contains('.'))
                    .map(|(name, expr)| {
                        (format!("{}{name}", expr_rewrite::PARAM_MEMBER_KEY_PREFIX), expr.clone())
                    })
                    .collect();
                param_expr_map.extend(member_replacements);
                let no_local: std::collections::HashSet<String> =
                    std::collections::HashSet::default();
                let no_iface: HashMap<String, String> = HashMap::default();
                // §6.18/§23.10: the sub-module's OWN typedef names. A signature
                // type naming one must resolve against THIS instance's widths —
                // the bare typedef key is last-writer-wins across differently
                // parameterized instances, so `function word_t f();` in a W=4
                // instance returned the W=20 instance's width once that one
                // elaborated later. The references are renamed to the
                // instance-scoped key registered above.
                let sub_typedef_names: &std::collections::HashSet<String> = &sub_typedef_names_all;
                let scope_local_typeref = |dt: &DataType| -> DataType {
                    if let DataType::TypeReference {
                        name,
                        dimensions,
                        type_args,
                        span,
                    } = dt
                    {
                        if name.scopes.is_empty() && sub_typedef_names.contains(&name.name.name) {
                            let mut nn = name.clone();
                            nn.name.name = cat2(&inst_prefix, &name.name.name);
                            return DataType::TypeReference {
                                name: nn,
                                dimensions: dimensions.clone(),
                                type_args: type_args.clone(),
                                span: *span,
                            };
                        }
                    }
                    dt.clone()
                };
                // §6.18/§23.9: a subroutine-local declaration typed by this
                // instance's own unpacked-array typedef (`u8a_t r;` with
                // `typedef u8_t u8a_t [0:7]`) names the instance-scoped key,
                // as the signature does; the bare key is not this instance's.
                // Capture the set once per instance in `callable_ctx` so deferred
                // function/task bodies apply it on demand (#193).
                let callable_ctx: Option<Rc<CallableRewriteCtx>> = if prepared_sub.has_subroutines {
                    let lat: std::collections::HashSet<String> = sub_typedef_names
                        .iter()
                        .filter(|n| {
                            elab.typedef_unpacked_dims
                                .contains_key(&cat2(&inst_prefix, n))
                        })
                        .cloned()
                        .collect();
                    Some(Rc::new(CallableRewriteCtx {
                        ctx: Rc::clone(&pend_ctx),
                        local_array_typedefs: (!lat.is_empty()).then(|| Rc::new(lat)),
                    }))
                } else {
                    None
                };
                let bake_formal_type = |p: &mut FunctionPort| {
                    p.data_type = scope_local_typeref(&rewrite_data_type_genvar(
                        &p.data_type,
                        &param_expr_map,
                        &no_local,
                        &no_iface,
                    ));
                    p.data_type =
                        module_class_scope::data_type(&p.data_type, &inst_prefix, &class_bindings);
                    p.dimensions = rewrite_unpacked_dims_genvar(
                        &p.dimensions,
                        &param_expr_map,
                        &no_local,
                        &no_iface,
                    );
                };
                // Inline the sub-module's continuous assigns
                iprof_since("ck6_before_fntask", __th);
                let __td = iprof_now();
                // Function/task bodies retain their shared definition syntax
                // and materialize on demand via `callable_ctx`; keep this
                // instance's type-parameter TLS active for eager items in the loop.
                set_type_bind_tls(&pend_ctx);
                let body_classes: Vec<&ClassDeclaration> = prepared_sub
                    .effective_items
                    .iter()
                    .filter_map(|item| match item {
                        ModuleItem::ClassDeclaration(c) => Some(c.as_ref()),
                        _ => None,
                    })
                    .collect();
                for (sub_item, body_src) in prepared_sub
                    .effective_items
                    .iter()
                    .zip(prepared_sub.body_sources.iter())
                {
                    if let ModuleItem::FunctionDeclaration(fd) = sub_item {
                        let mut new_fd = fd.as_ref().clone();
                        new_fd.name.name.name = cat2(&inst_prefix, &fd.name.name.name);
                        // Return-type width can also use a module parameter.
                        new_fd.return_type = scope_local_typeref(&rewrite_data_type_genvar(
                            &new_fd.return_type,
                            &param_expr_map,
                            &no_local,
                            &no_iface,
                        ));
                        new_fd.return_type = module_class_scope::data_type(
                            &new_fd.return_type,
                            &inst_prefix,
                            &class_bindings,
                        );
                        for p in &mut new_fd.ports {
                            bake_formal_type(p);
                        }
                        if new_fd.ports.iter().any(|p| p.default.is_some()) {
                            // A formal or top-level local shadows any same-named
                            // module-scope object inside default expressions (§13.4).
                            let mut fn_locals = (*prepared_sub.local_names).clone();
                            for p in &fd.ports {
                                fn_locals.remove(&p.name.name);
                            }
                            for n in stmt_list_declared_names(&fd.items) {
                                fn_locals.remove(n);
                            }
                            for p in &mut new_fd.ports {
                                if let Some(def) = &p.default {
                                    p.default = Some(Box::new(rewrite_expr(
                                        def,
                                        &inst_prefix,
                                        &rewrite_port_map,
                                        &fn_locals,
                                        &sub_interface_map,
                                    )));
                                }
                            }
                        }
                        let key = new_fd.name.name.name.clone();
                        match &callable_ctx {
                            Some(cctx) if callable_body_names_scopes(&fd.items) => {
                                new_fd.items = cache.callable_bodies.intern(
                                    cctx.rewrite_body_now(&fd.ports, &fd.items).into(),
                                );
                                elab.functions.insert(key, new_fd);
                            }
                            _ => {
                                new_fd.items = cache.share_callable_source(&fd.items);
                                elab.functions.insert(key.clone(), new_fd);
                                if let Some(cctx) = &callable_ctx {
                                    elab.deferred_function_bodies.insert(key, Rc::clone(cctx));
                                }
                            }
                        }
                    }
                    // §16.6/§16.8: a named property or sequence of an INLINED
                    // instance was never registered, so `assert property
                    // (p(a))` in a sub-module or interface found no body and
                    // degraded to an unclocked probe that never ran its
                    // action. Register it under the instance-prefixed name
                    // the rewritten references use, with the body rewritten
                    // into this instance's scope (formals shadow ports and
                    // locals and stay bare for the call-site substitution).
                    let named_sva = match sub_item {
                        ModuleItem::PropertyDeclaration(pd) => {
                            Some((&pd.name.name, &pd.ports, &pd.body, &pd.port_defaults))
                        }
                        ModuleItem::SequenceDeclaration(sd) => {
                            Some((&sd.name.name, &sd.ports, &sd.body, &sd.port_defaults))
                        }
                        _ => None,
                    };
                    if let Some((name, ports, body, defaults)) = named_sva {
                        let key = cat2(&inst_prefix, &name);
                        if let Some(body) = body {
                            let formals: Vec<&str> =
                                ports.iter().map(|p| p.name.as_str()).collect();
                            with_shadowed(
                                &formals,
                                &rewrite_port_map,
                                &prepared_sub.local_names,
                                |ports, locals| {
                                    let rewrite = |expr: &Expression| {
                                        rewrite_expr(
                                            expr,
                                            &inst_prefix,
                                            ports,
                                            locals,
                                            &sub_interface_map,
                                        )
                                    };
                                    // §16.6, §16.8: only complete, rewritten bodies can
                                    // share. Their formal widths and lookups depend on the call.
                                    let body =
                                        crate::ast::cache::without_scope_caches(|| rewrite(body));
                                    elab.property_decls.insert(
                                        key.clone(),
                                        cache.named_sva_bodies.intern(Rc::new(body)),
                                    );
                                    if defaults.iter().any(Option::is_some) {
                                        let defaults = defaults
                                            .iter()
                                            .map(|d| d.as_ref().map(&rewrite))
                                            .collect();
                                        elab.property_param_defaults.insert(key.clone(), defaults);
                                    }
                                },
                            );
                            if !ports.is_empty() {
                                let names: Vec<String> =
                                    ports.iter().map(|p| p.name.clone()).collect();
                                elab.property_params.insert(key, names);
                            }
                        } else {
                            elab.sequences.insert(key);
                        }
                    }
                    // §35.4: a DPI import declared inside a CHILD module was
                    // never registered — only the top module's and packages'
                    // items reach register_dpi_import — so every call in an
                    // instantiated module silently resolved to nothing and
                    // "returned" 0/null with no diagnostic (GitHub xezim#108;
                    // the parameterized case in the report is just the common
                    // spelling of "child"). The import's SV name is global by
                    // symbol (§35.5.2 allows consistent re-imports, and
                    // register_dpi_import treats them as no-ops), so no
                    // instance prefix applies.
                    if let ModuleItem::DPIImport(di) = sub_item {
                        register_dpi_import(di, elab, None)?;
                    }
                    // §35.5.3, §35.11: an export declared in an INSTANTIATED
                    // module names THIS instance's copy of the subroutine.
                    // Every instance shares the one C symbol; a call from C
                    // runs the copy whose instance is the current DPI scope
                    // (the calling context import's, or svSetScope's).
                    if let ModuleItem::DPIExport(e) = sub_item {
                        register_instance_dpi_export(e, &inst_prefix, elab);
                    }
                    if let ModuleItem::TaskDeclaration(td) = sub_item {
                        let mut new_td = td.as_ref().clone();
                        new_td.name.name.name = cat2(&inst_prefix, &td.name.name.name);
                        for p in &mut new_td.ports {
                            bake_formal_type(p);
                        }
                        if new_td.ports.iter().any(|p| p.default.is_some()) {
                            // Same formal-shadowing rule as functions above.
                            let mut task_locals = (*prepared_sub.local_names).clone();
                            for p in &td.ports {
                                task_locals.remove(&p.name.name);
                            }
                            for n in stmt_list_declared_names(&td.items) {
                                task_locals.remove(n);
                            }
                            for p in &mut new_td.ports {
                                if let Some(def) = &p.default {
                                    p.default = Some(Box::new(rewrite_expr(
                                        def,
                                        &inst_prefix,
                                        &rewrite_port_map,
                                        &task_locals,
                                        &sub_interface_map,
                                    )));
                                }
                            }
                        }
                        let key = new_td.name.name.name.clone();
                        match &callable_ctx {
                            Some(cctx) if callable_body_names_scopes(&td.items) => {
                                new_td.items = cache.callable_bodies.intern(
                                    cctx.rewrite_body_now(&td.ports, &td.items).into(),
                                );
                                elab.tasks.insert(key, new_td);
                            }
                            _ => {
                                new_td.items = cache.share_callable_source(&td.items);
                                elab.tasks.insert(key.clone(), new_td);
                                if let Some(cctx) = &callable_ctx {
                                    elab.deferred_task_bodies.insert(key, Rc::clone(cctx));
                                }
                            }
                        }
                    }
                    if let ModuleItem::ClassDeclaration(cd) = sub_item {
                        validate_class_constraints_in_body(
                            cd,
                            Some(definitions),
                            &body_classes,
                            Some(&elab.enum_members),
                            Some(&elab),
                            Some(&inst_prefix),
                        )?;
                        // §8.3, §23.9: a class of a generate block reads the
                        // block's data by its key, this instance's (`u.a.k`).
                        let mut bindings = class_bindings.clone();
                        visit_renamed_decls(&prepared_sub.effective_items, &mut |n, _, kind| {
                            if n.contains('.')
                                && !matches!(kind, DeclKind::Function | DeclKind::Task)
                            {
                                let key = make_ident_expr(&cat2(&inst_prefix, n));
                                bindings.entry(n.to_string()).or_insert(key);
                            }
                        });
                        let mut scoped = module_class_scope::class(cd, &inst_prefix, &bindings);
                        for item in &mut scoped.items {
                            if let ClassItem::Method(method) = item {
                                let body = match &mut method.kind {
                                    ClassMethodKind::Function(f)
                                    | ClassMethodKind::Extern(f)
                                    | ClassMethodKind::PureVirtual(f) => &mut f.items,
                                    ClassMethodKind::Task(t) => &mut t.items,
                                };
                                *body = cache.callable_bodies.intern(std::mem::take(body));
                            }
                        }
                        register_class_enum_members(&scoped, elab);
                        register_class_covergroups(&scoped, elab);
                        register_class_scoped_typedef_aliases(&scoped, None, elab);
                        let mut ec = elaborate_class_with_params(&scoped, Some(&elab.parameters));
                        ec.declaring_module = Some(sub_mod_name.clone());
                        let ec = std::sync::Arc::new(ec);
                        elab.classes.insert(scoped.name.name.clone(), ec.clone());
                        elab.classes.entry(cd.name.name.clone()).or_insert(ec);
                        register_nested_classes(&scoped, &scoped.name.name, elab);
                    }
                    // §19.3: a covergroup declared in an instantiated module or
                    // interface is a type of THAT instance, registered as
                    // `<inst>.cg` with its expressions rewritten into the
                    // instance scope. The formals stay bare.
                    if let ModuleItem::CovergroupDeclaration(cg) = sub_item {
                        let mut cg_locals = (*prepared_sub.local_names).clone();
                        let mut cg_ports = (*rewrite_port_map).clone();
                        for p in cg.ports.iter().chain(cg.sample_ports.iter()) {
                            cg_locals.remove(&p.name.name);
                            cg_ports.remove(&p.name.name);
                        }
                        let mut new_cg = cg.as_ref().clone();
                        new_cg.for_each_expr_mut(&mut |e| {
                            *e = rewrite_expr(
                                e,
                                &inst_prefix,
                                &cg_ports,
                                &cg_locals,
                                &sub_interface_map,
                            );
                        });
                        if let Some(EventControl::Identifier(id)) = &mut new_cg.event {
                            if cg_locals.contains(&id.name) {
                                id.name = cat2(&inst_prefix, &id.name);
                            }
                        }
                        new_cg.name.name = cat2(&inst_prefix, &cg.name.name);
                        elab.covergroups.insert(new_cg.name.name.clone(), new_cg);
                    }
                    if let ModuleItem::ClockingDeclaration(cd) = sub_item {
                        // §14.7: one clocking block per instance, registered as
                        // `inst.cb`; the clock and clocking signals resolve in the
                        // instance scope.
                        let resolve = |name: &str| -> String {
                            let e = make_ident_expr(name);
                            let re = rewrite_expr(
                                &e,
                                &inst_prefix,
                                &rewrite_port_map,
                                &prepared_sub.local_names,
                                &sub_interface_map,
                            );
                            match &re.kind {
                                ExprKind::Ident(h) => h
                                    .path
                                    .iter()
                                    .map(|s| s.name.name.as_str())
                                    .collect::<Vec<_>>()
                                    .join("."),
                                _ => cat2(&inst_prefix, &name),
                            }
                        };
                        let mut new_cd = cd.as_ref().clone();
                        new_cd.name.name = cat2(&inst_prefix, &cd.name.name);
                        if let Some(clk) = &cd.clock_signal {
                            new_cd.clock_signal = Some(crate::ast::Identifier {
                                name: resolve(&clk.name),
                                span: clk.span,
                            });
                        }
                        // §14.3: with `= expression` the clockvar name is local to
                        // the block and the expression is the clocking signal.
                        for s in &mut new_cd.signals {
                            match &mut s.bound_to {
                                Some(e) => {
                                    *e = rewrite_expr(
                                        e,
                                        &inst_prefix,
                                        &rewrite_port_map,
                                        &prepared_sub.local_names,
                                        &sub_interface_map,
                                    )
                                }
                                None => s.name.name = resolve(&s.name.name),
                            }
                        }
                        let mut dirs = HashMap::default();
                        for s in &new_cd.signals {
                            dirs.insert(s.name.name.clone(), s.direction);
                        }
                        // §14.12: a standalone `default clocking <name>;` is an
                        // empty, clock-less marker. Both module paths fold it
                        // into the real same-named block; this instance path did
                        // not, so the marker OVERWROTE the real block and every
                        // clocking access through the interface became x — one
                        // innocuous line disabling the whole block.
                        let is_designation = new_cd.clock_signal.is_none()
                            && new_cd.signals.is_empty()
                            && new_cd.is_default;
                        if is_designation {
                            if let Some(existing) = elab.clocking_blocks.get_mut(&new_cd.name.name)
                            {
                                existing.is_default = true;
                            } else {
                                elab.clocking_blocks
                                    .insert(new_cd.name.name.clone(), new_cd);
                            }
                        } else {
                            elab.clocking_signal_dirs
                                .insert(new_cd.name.name.clone(), dirs);
                            elab.clocking_blocks
                                .insert(new_cd.name.name.clone(), new_cd);
                        }
                    }
                    if let ModuleItem::ContinuousAssign(ca_item) = sub_item {
                        // #7: Rc-share source ASTs across sibling instances.
                        let delay_rc = ca_item
                            .delay
                            .as_deref()
                            .map(|d| std::rc::Rc::new(d.clone()));
                        let delay_fall_rc = ca_item
                            .delay_fall
                            .as_deref()
                            .map(|d| std::rc::Rc::new(d.clone()));
                        let delay_off_rc = ca_item
                            .delay_off
                            .as_deref()
                            .map(|d| std::rc::Rc::new(d.clone()));
                        if let BodySource::ContAssign(pairs) = body_src {
                            for (lhs_rc, rhs_rc) in pairs {
                                elab.pending_cont_assign.push(PendingContAssign::new(
                                    std::rc::Rc::clone(lhs_rc),
                                    false,
                                    std::rc::Rc::clone(rhs_rc),
                                    std::rc::Rc::clone(&pend_ctx),
                                    ca_item.strength.clone(),
                                    delay_rc.clone(),
                                    delay_fall_rc.clone(),
                                    delay_off_rc.clone(),
                                    Some(ca_item.span),
                                ));
                            }
                        }
                    }
                    if let ModuleItem::GateInstantiation(gi) = sub_item {
                        // §28.8 switches produce no assign pairs; record them
                        // with terminals rewritten into this instance's scope.
                        record_tran_switches(gi, elab, sub_mod.default_net_type(), |e| {
                            rewrite_expr(
                                e,
                                &pend_ctx.prefix,
                                &pend_ctx.port_map,
                                &pend_ctx.local_names,
                                &pend_ctx.interface_map,
                            )
                        });
                        if let BodySource::GateInst(pairs) = body_src {
                            // §28.9/§28.11: the gate's `#d` / `#(rise, fall)`
                            // delays travel unevaluated like an `assign #d`
                            // delay, so a parameter they name (`and #(D)`)
                            // resolves per instance at materialize time.
                            // Passing None ran every inlined gate undelayed.
                            let delay_rc = gi.delay.as_deref().map(|d| std::rc::Rc::new(d.clone()));
                            let delay_fall_rc =
                                gi.delay_fall.as_deref().map(|d| std::rc::Rc::new(d.clone()));
                            let delay_off_rc = gi.delay_off.as_deref().cloned().map(std::rc::Rc::new);
                            for (lhs_rc, rhs_rc) in pairs {
                                // §28.4: mark the driven net gate-driven, as
                                // `gate_inst_to_assigns` does at the top level,
                                // so a `buf` fed z drives x here too.
                                let lhs = rewrite_expr(
                                    lhs_rc,
                                    &pend_ctx.prefix,
                                    &pend_ctx.port_map,
                                    &pend_ctx.local_names,
                                    &pend_ctx.interface_map,
                                );
                                if let Some(n) = ident_flat_name(&lhs) {
                                    elab.gate_driven_nets.insert(n);
                                }
                                elab.pending_cont_assign.push(PendingContAssign::new(
                                    std::rc::Rc::clone(lhs_rc),
                                    false,
                                    std::rc::Rc::clone(rhs_rc),
                                    std::rc::Rc::clone(&pend_ctx),
                                    None,
                                    delay_rc.clone(),
                                    delay_fall_rc.clone(),
                                    delay_off_rc.clone(),
                                    None,
                                ));
                            }
                        }
                    }
                    if let ModuleItem::NetDeclaration(nd) = sub_item {
                        if let BodySource::NetInits(inits) = body_src {
                            // §10.3.1 `wire #d w = expr;` drives through the
                            // declaration's delay, resolved per instance like
                            // the `assign #d` form above. With an assignment
                            // the delay is the ASSIGNMENT's (§10.3.3), not a
                            // net delay; see `net_delay_of`.
                            let rc =
                                |d: Option<&Expression>| d.map(|d| std::rc::Rc::new(d.clone()));
                            let (delay_rc, delay_fall_rc, delay_off_rc) = (
                                rc(nd.delay()),
                                rc(nd.delay_fall()),
                                rc(nd.delay_off()),
                            );
                            for (lhs_rc, rhs_rc) in inits {
                                elab.pending_cont_assign.push(PendingContAssign::new(
                                    std::rc::Rc::clone(lhs_rc),
                                    true,
                                    std::rc::Rc::clone(rhs_rc),
                                    std::rc::Rc::clone(&pend_ctx),
                                    // §6.7: `wire (weak0, weak1) w = v;`
                                    // drives with the declaration's strength.
                                    nd.strength().map(str::to_string),
                                    delay_rc.clone(),
                                    delay_fall_rc.clone(),
                                    delay_off_rc.clone(),
                                    Some(rhs_rc.span),
                                ));
                            }
                        }
                    }
                    if let ModuleItem::SpecifyBlock(sb) = sub_item {
                        // Delays evaluate in the INSTANCE's parameter scope:
                        // a specparam-valued delay (`(a => y) = tpd;`) read
                        // the flat map, missed its bare name and became 0.
                        let delay_vals: Vec<Vec<u64>> = sb
                            .paths
                            .iter()
                            .map(|p| {
                                p.delays
                                    .iter()
                                    .map(|d| eval_const_expr(d, &sub_merged_params))
                                    .collect()
                            })
                            .collect();
                        elaborate_module_paths(elab, &sb.paths, &delay_vals, &|e| {
                            rewrite_expr(
                                e,
                                &inst_prefix,
                                &rewrite_port_map,
                                &prepared_sub.local_names,
                                &sub_interface_map,
                            )
                        });
                        // §15.6 delayed nets: drive `delayed_net = source` as a
                        // zero-delay continuous assign in the instance scope so
                        // the cell's functional clock/data path (which reads
                        // these nets) works even though the timing check itself
                        // is not modeled.
                        for (delayed, source) in &sb.delayed_nets {
                            let lhs = rewrite_expr(
                                &make_ident_expr(delayed),
                                &inst_prefix,
                                &rewrite_port_map,
                                &prepared_sub.local_names,
                                &sub_interface_map,
                            );
                            let rhs = rewrite_expr(
                                &make_ident_expr(source),
                                &inst_prefix,
                                &rewrite_port_map,
                                &prepared_sub.local_names,
                                &sub_interface_map,
                            );
                            elab.continuous_assigns
                                .push(ContinuousAssignment::plain(lhs, rhs));
                        }
                        if !sb.timing_checks.is_empty() {
                            let scope = inst_prefix.strip_suffix('.').unwrap_or(&inst_prefix);
                            let timing_consts: Vec<Vec<Option<i64>>> = sb
                                .timing_checks
                                .iter()
                                .map(|tc| {
                                    let limits = timing_check_limit_args(&tc.name);
                                    let flags = timing_check_flag_args(&tc.name);
                                    tc.args
                                        .iter()
                                        .enumerate()
                                        .map(|(i, a)| {
                                            let a = a.as_ref()?;
                                            if !limits.contains(&i) && !flags.contains(&i) {
                                                return None;
                                            }
                                            let v = eval_const_expr_val(
                                                &a.expr,
                                                &sub_merged_params,
                                            );
                                            if v.is_real {
                                                let f = v.to_f64();
                                                f.is_finite().then(|| f.round() as i64)
                                            } else if v.has_xz() {
                                                None
                                            } else {
                                                v.to_i64()
                                            }
                                        })
                                        .collect()
                                })
                                .collect();
                            elaborate_timing_checks(
                                elab,
                                &sb.timing_checks,
                                scope,
                                sub_mod_name,
                                &timing_consts,
                                &|e| {
                                    rewrite_expr(
                                        e,
                                        &inst_prefix,
                                        &rewrite_port_map,
                                        &prepared_sub.local_names,
                                        &sub_interface_map,
                                    )
                                },
                            );
                        }
                    }
                    if matches!(sub_item, ModuleItem::AlwaysConstruct(_)) {
                        if let BodySource::Always(kind, stmt_rc, gen_scope) = body_src {
                            elab.pending_always.push(PendingAlways {
                                kind: *kind,
                                source: std::rc::Rc::clone(stmt_rc),
                                ctx: std::rc::Rc::clone(&pend_ctx),
                                gen_scope: gen_scope.clone(),
                            });
                        }
                    }
                    if matches!(
                        sub_item,
                        ModuleItem::InitialConstruct(_) | ModuleItem::AssertionItem(_)
                    ) {
                        if let BodySource::Initial(stmt_rc, gen_scope) = body_src {
                            if std::env::var("XEZIM_TRACE_INIT").ok().as_deref() == Some("1") {
                                eprintln!(
                                    "[xezim][elab] inline_module: pushing initial from {}",
                                    inst_prefix
                                );
                            }
                            let pending = PendingInitial {
                                source: std::rc::Rc::clone(stmt_rc),
                                ctx: std::rc::Rc::clone(&pend_ctx),
                                gen_scope: gen_scope.clone(),
                            };
                            // §24.3: the initial blocks of an instantiated
                            // program run in the reactive region, like those
                            // of a top-level program.
                            if matches!(sub_mod, Definition::Program(_))
                                && matches!(sub_item, ModuleItem::InitialConstruct(_))
                            {
                                elab.program_initial_blocks.push(pending.materialize());
                            } else {
                                elab.pending_initial.push(pending);
                            }
                        }
                    }
                    if let ModuleItem::FinalConstruct(fc) = sub_item {
                        // §9.2.3: a submodule's `final` blocks run at
                        // simulation end just like the top module's, but
                        // inlining dropped them — only top-level finals ever
                        // executed (issue #22). They are few and run once, so
                        // rewrite eagerly instead of adding a pending lane.
                        let stmt = rewrite_stmt(
                            &fc.stmt,
                            &pend_ctx.prefix,
                            &pend_ctx.port_map,
                            &pend_ctx.local_names,
                            &pend_ctx.interface_map,
                        );
                        elab.final_blocks.push(InitialBlock {
                            stmt,
                            scope: pend_ctx.prefix.trim_end_matches('.').to_string(),
                        });
                    }
                }
                clear_type_bind_tls();
                // Signature rewriting is complete; do not retain this map
                // through recursive child elaboration (§13.3, #721).
                drop(param_expr_map);

                // Record the instance before descending. Inlining is about to
                // dissolve this module into the parent, so this is the only
                // place the (path, definition) pair still exists.
                let default_net_type = sub_mod.default_net_type();
                if default_net_type != Some(NetType::Wire)
                    && !elab.default_net_types.contains_key(sub_mod_name)
                {
                    elab.default_net_types
                        .insert(sub_mod_name.clone(), default_net_type);
                }
                elab.instances.push(ElabInstance {
                    path: inst_path_shared,
                    def_name: sub_mod_name.as_str().into(),
                    parent: prefix.trim_end_matches('.').into(),
                    src_pos: (hi.span.start as usize).max(item_floor),
                });
                elab.upward_scopes.borrow_mut().add_instance(
                    prefix.trim_end_matches('.'),
                    inst_prefix.trim_end_matches('.'),
                    &sub_mod_name,
                );
                // Keep later items strictly after this one: bound
                // instantiations carry spans from elsewhere.
                *items_end = (*items_end).max((hi.span.start as usize).max(item_floor) + 1);

                // Recurse into sub-module instantiations
                iprof_since("subitem_loop", __td);
                iprof_since("per_hi_prelude", __th);
                let __te = iprof_now();
                // §23.10/§27: a recursive instantiation whose terminating
                // generate branch never fires expands the hierarchy forever —
                // ivtest pr2728812b reached 37 GB RSS before the kernel killed
                // the process. Commercial tools cap the depth and error (the
                // originating test expects failure "after 100 loops"). Depth =
                // instance-path segments; real hierarchies sit far below the
                // cap. XEZIM_MAX_INST_DEPTH overrides.
                {
                    static MAX_DEPTH: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
                    let cap = *MAX_DEPTH.get_or_init(|| {
                        std::env::var("XEZIM_MAX_INST_DEPTH")
                            .ok()
                            .and_then(|v| v.parse().ok())
                            .unwrap_or(200)
                    });
                    let depth = inst_prefix.matches('.').count();
                    if depth > cap {
                        // A 200-segment path is unreadable; head + tail is
                        // enough to recognise the repeating cycle.
                        let path = inst_prefix.trim_end_matches('.');
                        let segs: Vec<&str> = path.split('.').collect();
                        let shown = if segs.len() > 8 {
                            format!(
                                "{} ... {}",
                                segs[..4].join("."),
                                segs[segs.len() - 4..].join(".")
                            )
                        } else {
                            path.to_string()
                        };
                        return Err(format!(
                            "instantiation depth exceeds {} at instance '{}' (module '{}') — \
                             unbounded recursive instantiation? A generate-based recursion \
                             needs a terminating branch (IEEE 1800-2017 §27.3); raise the \
                             limit with XEZIM_MAX_INST_DEPTH if the hierarchy is genuinely \
                             this deep",
                            cap, shown, sub_mod_name
                        ));
                    }
                }
                let child_meta = inline_module_items(
                    elab,
                    sub_mod,
                    &inst_prefix,
                    definitions,
                    &mut sub_interface_map,
                    &sub_merged_params,
                    cache,
                    &rewrite_port_map,
                    &sub_defparams,
                    param_scope,
                    bind_state.as_deref_mut(),
                )?;
                crate::oom_trace::model("instance complete", elab, Some(cache.prepared.len()));
                iprof_since("recursion", __te);

                if let Some(bs) = bind_state.as_deref_mut() {
                    let inst_path = inst_prefix.trim_end_matches('.');
                    if bs.filter.matches(inst_path, sub_mod_name) {
                        let type_overlay = capture_type_overlay(
                            elab,
                            &saved_type_binds,
                            &saved_type_shapes,
                            &saved_unpacked_dims,
                        );
                        let local_names = Some(
                            child_meta
                                .local_names
                                .unwrap_or_else(|| Rc::clone(&prepared_sub.local_names)),
                        );
                        let local_typedefs = child_meta.local_typedefs.or_else(|| {
                            (!prepared_sub.local_typedefs.is_empty())
                                .then(|| Box::new(prepared_sub.local_typedefs.clone()))
                        });
                        let saved_defparams = if !child_meta.was_flat_leaf {
                            child_meta.defparams
                        } else {
                            std::mem::take(&mut sub_defparams)
                        };
                        bs.scopes.insert(
                            inst_path.to_string(),
                            TargetScope {
                                def_name: sub_mod_name.clone(),
                                local_names,
                                local_typedefs,
                                interface_map: std::mem::take(&mut sub_interface_map),
                                port_map: Rc::clone(&rewrite_port_map),
                                local_params: std::mem::take(&mut sub_merged_params),
                                defparams: saved_defparams,
                                type_overlay,
                                items_end: child_meta.items_end,
                                was_flat_leaf: child_meta.was_flat_leaf,
                            },
                        );
                    }
                }

                for (tp_name, saved) in saved_type_shapes.into_iter().rev() {
                    tls_restore_typedef_shape(&tp_name, saved);
                }
                for (name, prev) in saved_unpacked_dims.into_iter().rev() {
                    match prev {
                        Some(d) => {
                            elab.typedef_unpacked_dims.insert(name, d);
                        }
                        None => {
                            elab.typedef_unpacked_dims.remove(&name);
                        }
                    }
                }
                // Restore typedef entries shadowed by this instance's TYPE
                // parameter overrides.
                for (tp_name, prev_w, prev_dt) in saved_type_binds {
                    match prev_w {
                        Some(w) => {
                            typedefs_insert_traced(
                                &mut elab.typedefs,
                                "restore:type_param",
                                tp_name.clone(),
                                w,
                            );
                        }
                        None => {
                            let removed = elab.typedefs.remove(&tp_name);
                            if type_trace_on(&tp_name) {
                                let prev_s = removed
                                    .map(|p| p.to_string())
                                    .unwrap_or_else(|| "<none>".into());
                                type_trace(
                                    "remove:type_param",
                                    &tp_name,
                                    &format!("prev={prev_s}"),
                                );
                            }
                        }
                    }
                    match prev_dt {
                        Some(dt) => {
                            elab.typedef_types.insert(tp_name, dt);
                        }
                        None => {
                            elab.typedef_types.remove(&tp_name);
                        }
                    }
                }
                // The instance is fully inlined: every name in its body now
                // carries the instance prefix, so the bare geometry keys it
                // registered are no longer needed — and leaving them made
                // `inp.sram_renA[2]` on a struct member in another instance
                // resolve against this instance's `[3:0][1:0] sram_renA`.
                for (table, key) in inst_bare_keys.drain(..) {
                    match table {
                        0 => {
                            elab.packed_signal_elem_widths.remove(&key);
                        }
                        1 => {
                            elab.packed_full_dims.remove(&key);
                        }
                        2 => {
                            elab.string_signals.remove(&key);
                        }
                        _ => {
                            elab.packed_struct_fields.remove(&key);
                        }
                    }
                }
            }
        }
    }
    Ok(())
}
