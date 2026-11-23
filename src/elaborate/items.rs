use super::*;

/// Helper: process a slice of module items into the elaborated module.
/// This is extracted so it can be called recursively for generate regions.
pub(super) fn elaborate_items(
    items: &[ModuleItem],
    elab: &mut ElaboratedModule,
    all_defs: Option<&HashMap<String, Definition>>,
) -> Result<(), String> {
    // Classes declared in THIS body must be visible to each other's `extends`.
    let local_defs = defs_with_local_classes(items, all_defs);
    let cls_defs = local_defs.as_ref().or(all_defs);
    for item in items {
        match item {
            ModuleItem::PortDeclaration(pd) => {
                let port_modport_view = match &pd.data_type {
                    DataType::Interface {
                        name,
                        modport: Some(mp),
                        ..
                    } => resolve_interface_modport_view(&name.name, &mp.name, all_defs),
                    _ => None,
                };
                let width =
                    resolve_type_width(&pd.data_type, Some(&elab.parameters), Some(&elab.typedefs));
                let is_signed = is_type_signed_resolved(&pd.data_type, &elab.typedef_types);
                let is_real = is_type_real_resolved(&pd.data_type, &elab.typedef_types);
                for decl in &pd.declarators {
                    if elab.parameters.contains_key(&decl.name.name) {
                        if elab.claim_local_decl_displacement(
                            &decl.name.name,
                            decl.name.span,
                            "variable/net",
                        ) {
                            elab.remove_param(&decl.name.name);
                            elab.signals.remove(&decl.name.name);
                        } else {
                            return Err(duplicate_decl_error(
                                &elab,
                                &decl.name.name,
                                decl.name.span,
                                "net",
                            ));
                        }
                    }
                    // §23.2.2.1 non-ANSI split type/direction — merge (see the
                    // matching comment in the top-module elaboration path).
                    if let Some(existing) = elab.signals.get_mut(&decl.name.name) {
                        if existing.direction.is_none() {
                            let explicit_type = !matches!(pd.data_type, DataType::Implicit { .. });
                            existing.direction = Some(pd.direction);
                            if explicit_type {
                                if let Some(pats) = signal_trace_patterns() {
                                    if pats.iter().any(|p| existing.name.contains(p.as_str())) {
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
                                existing.is_real = is_real;
                                existing.type_name = get_type_name(&pd.data_type);
                                existing.value = default_port_value(
                                    Some(pd.direction),
                                    Some(&pd.data_type),
                                    width,
                                    is_real,
                                    pd.net_type,
                                );
                            }
                            if !elab.port_order.contains(&decl.name.name) {
                                elab.port_order.push(decl.name.name.clone());
                            }
                            if let Some(view) = &port_modport_view {
                                elab.modport_views
                                    .insert(decl.name.name.clone(), view.clone());
                            }
                            if let Some(net_type) = pd.net_type {
                                register_net_type(
                                    elab,
                                    &decl.name.name,
                                    net_type,
                                    Some(&pd.data_type),
                                );
                            }
                            continue;
                        }
                        return Err(duplicate_decl_error(
                            &elab,
                            &decl.name.name,
                            decl.name.span,
                            "net",
                        ));
                    }
                    let sig = Signal {
                        is_const: false,
                        name: decl.name.name.clone().into(),
                        width,
                        is_signed,
                        direction: Some(pd.direction),
                        value: default_port_value(
                            Some(pd.direction),
                            Some(&pd.data_type),
                            width,
                            is_real,
                            port_decl_net_type(pd),
                        ),
                        is_real,
                        type_name: get_type_name(&pd.data_type),
                    };
                    signals_insert_traced(&mut elab.signals, line!(), decl.name.name.clone(), sig);
                    if let Some(net_type) = port_decl_net_type(pd) {
                        register_net_type(elab, &decl.name.name, net_type, Some(&pd.data_type));
                    }
                    elab.port_order.push(decl.name.name.clone());
                    if let Some(view) = &port_modport_view {
                        elab.modport_views
                            .insert(decl.name.name.clone(), view.clone());
                    }
                }
            }
            ModuleItem::NetDeclaration(nd) => {
                check_net_data_type(nd, elab)?;
                let width =
                    resolve_type_width(&nd.data_type, Some(&elab.parameters), Some(&elab.typedefs));
                let is_signed = is_type_signed_resolved(&nd.data_type, &elab.typedef_types);
                let is_real = is_type_real_resolved(&nd.data_type, &elab.typedef_types);
                for decl in &nd.declarators {
                    // §7.6: net arrays retain left-to-right declaration order too.
                    if let Some(dims) = declared_unpacked_dims(&decl.dimensions, &elab.parameters) {
                        if dims.first().is_some_and(|(l, r)| l > r) {
                            elab.descending_arrays.insert(decl.name.name.clone());
                        }
                        elab.unpacked_decl_dims.insert(decl.name.name.clone(), dims);
                    }
                    if let Some(d) = net_delay_of(decl, nd, &elab.parameters) {
                        elab.net_delays.insert(decl.name.name.clone(), d);
                    }
                    register_net_type(elab, &decl.name.name, nd.net_type, Some(&nd.data_type));
                    let init_value = default_net_value(nd.net_type, width, is_real);
                    let sig = Signal {
                        is_const: false,
                        name: decl.name.name.clone().into(),
                        width,
                        is_signed,
                        direction: None,
                        value: init_value,
                        is_real,
                        type_name: get_type_name(&nd.data_type),
                    };
                    signals_insert_traced(&mut elab.signals, line!(), decl.name.name.clone(), sig);
                    if let Some(init_expr) = &decl.init {
                        let decl_dly = net_decl_assign_delay(nd, &elab.parameters);
                        let decl_rhs = net_declaration_driver(nd, &decl.name.name, init_expr, elab);
                        elab.continuous_assigns.push(ContinuousAssignment {
                            gate_delay_fall: None,
                            delay_exprs: decl_dly.3,
                            delay_select: None,
                            origin: Some((init_expr.span, top_origin_scope())),
                            lhs: make_ident_expr(&decl.name.name),
                            rhs: decl_rhs,
                            delay: decl_dly.0,
                            rhs_parent_scoped: false,
                            delay_fall: decl_dly.1,
                            delay_off: decl_dly.2,
                        });
                    }
                }
            }
            ModuleItem::DataDeclaration(dd) => {
                // See the main-path arm: beyond-cap dead declarations elide.
                let dd_filtered;
                let dd = match filter_dead_giant_declarators(dd, elab, all_defs) {
                    Some(f) => {
                        dd_filtered = f;
                        &dd_filtered
                    }
                    None => dd,
                };
                if dd.declarators.is_empty() {
                    continue;
                }
                register_anonymous_enum_members(&dd.data_type, elab);
                // Packed multi-D (`logic [N-1:0][W-1:0] mem;`) — record the
                // per-element width under the bare declarator name so
                // `mem[i] = v` writes a W-bit slice. Mirrors the same
                // registration in the top-level module DataDecl arm. Without
                // this hook the submodule path leaves packed_signal_elem_widths
                // empty, and the bytecode emitter falls back to a single-bit
                // write at `mem[i]` — silent data corruption in any packed-2D
                // FIFO (e.g. cv32e40p_fifo's mem_n).
                // §7.4.1: the packed dims may live in the TYPEDEF rather than on
                // the declaration (`typedef T1 [3:0] T2; T2 val;`). Resolving the
                // chain first is what makes those visible — declared bare, the
                // element width was never recorded and `val[i]` degraded to a
                // BIT select (val[0] happened to read right, val[1] read 0).
                // ONE step, not the full chain: `resolve_typedef_chain` walks to
                // the end and would discard the intermediate `[3:0]` (T2 -> T1
                // -> logic[7:0]). The immediate definition is what carries the
                // packed dims.
                let dd_resolved: DataType = match &dd.data_type {
                    DataType::TypeReference { name, .. } => elab
                        .typedef_types
                        .get(&name.name.name)
                        .cloned()
                        .unwrap_or_else(|| dd.data_type.clone()),
                    _ => dd.data_type.clone(),
                };
                if let Some(elem_w) =
                    packed_inner_elem_width(&dd.data_type, &elab.parameters, &elab.typedefs)
                        .or_else(|| {
                            packed_inner_elem_width(&dd_resolved, &elab.parameters, &elab.typedefs)
                        })
                {
                    for decl in &dd.declarators {
                        elab.packed_signal_elem_widths
                            .insert(decl.name.name.clone(), elem_w);
                    }
                }
                if let Some(fdims) = packed_full_dims_of(&dd.data_type, &elab.parameters)
                    // Ranges on the declaration precede those supplied by its typedef.
                    .or_else(|| {
                        packed_full_dims_chained(
                            &dd.data_type,
                            &elab.parameters,
                            &elab.typedef_types,
                        )
                    })
                    .or_else(|| packed_full_dims_of(&dd_resolved, &elab.parameters))
                {
                    for decl in &dd.declarators {
                        elab.packed_full_dims
                            .insert(decl.name.name.clone(), fdims.clone());
                    }
                }
                let data_modport_view = match &dd.data_type {
                    DataType::Interface {
                        name,
                        modport: Some(mp),
                        ..
                    } => resolve_interface_modport_view(&name.name, &mp.name, all_defs),
                    _ => None,
                };
                let width = match &dd.data_type {
                    // A bare typedef reference takes the registered typedef
                    // width, but packed dimensions on the DECLARATION
                    // (`foo_s [1:0][3:0] x`) multiply it — resolve_type_width
                    // applies both, so only take the shortcut when there are
                    // no such dims.
                    DataType::TypeReference {
                        name, dimensions, ..
                    } if dimensions.is_empty() => {
                        {
                            // §26.3: a SCOPED `P::T` prefers the qualified key so
                            // a module-local `typedef ... T` cannot capture it.
                            let scoped_w = specialized_class_scope_width(name, &elab)
                                .or_else(|| lookup_scoped_type(name, &elab.typedefs).copied());
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
                if let DataType::TypeReference { type_args, .. } = &dd.data_type {
                    if !type_args.is_empty() {
                        for decl in &dd.declarators {
                            elab.class_type_args
                                .insert(decl.name.name.clone(), type_args.clone());
                        }
                    }
                }
                let is_signed = is_type_signed_resolved(&dd.data_type, &elab.typedef_types);
                let is_real = is_type_real_resolved(&dd.data_type, &elab.typedef_types);
                for decl in &dd.declarators {
                    // §6.18, §7.4.5: a variable of a dimensioned typedef takes
                    // the typedef's unpacked dimensions after its own, as the
                    // module-scope path does; this (generate-region) path used
                    // the declarator's alone, so `aa_t m;` was a scalar.
                    let typed_decl;
                    let decl = match &dd.data_type {
                        DataType::TypeReference {
                            name, dimensions, ..
                        } if dimensions.is_empty() => {
                            match lookup_scoped_type(name, &elab.typedef_unpacked_dims) {
                                Some(td) => {
                                    let mut d = decl.clone();
                                    d.dimensions.extend(td.iter().cloned());
                                    typed_decl = d;
                                    &typed_decl
                                }
                                None => decl,
                            }
                        }
                        _ => decl,
                    };
                    if elab.signals.contains_key(&decl.name.name)
                        || elab.parameters.contains_key(&decl.name.name)
                    {
                        return Err(duplicate_decl_error(
                            &elab,
                            &decl.name.name,
                            decl.name.span,
                            "net",
                        ));
                    }
                    // §6.6.7, §27.2: a generate block declares a nettype net
                    // like a module does; its resolution function admits
                    // several continuous drivers (§6.5).
                    let nettype_net = declared_user_nettype(elab, &dd.data_type).is_some();
                    if nettype_net {
                        elab.nets.insert(decl.name.name.clone());
                        if let Some(d) = nettype_net_delay(dd, decl, &elab.parameters) {
                            elab.net_delays.insert(decl.name.name.clone(), d);
                        }
                    }
                    let shape_dims = normalize_unpacked_dims(
                        &decl.dimensions,
                        &elab.parameters,
                        &elab.typedef_types,
                    );
                    record_coll_shape(elab, &decl.name.name, &shape_dims, None);
                    // §7.4.2 / §7.8: `r [N]` parses as an associative dimension
                    // keyed by "type N"; the normalized dims know whether `N` is
                    // a parameter (fixed size) or a type (associative). Decided
                    // from the raw dimension, a block's `[N]` sized by a
                    // module or package parameter was registered associative
                    // as well as fixed (the module-body path reads the
                    // normalized dims).
                    if let Some(UnpackedDimension::Associative {
                        data_type: key_dt, ..
                    }) = shape_dims.first()
                    {
                        let is_string_key = key_dt.as_ref().is_some_and(|dt| {
                            matches!(
                                dt.as_ref(),
                                DataType::Simple {
                                    kind: SimpleType::String,
                                    ..
                                }
                            )
                        });
                        elab.associative_arrays
                            .insert(decl.name.name.clone(), is_string_key);
                        if width > 0 {
                            elab.assoc_elem_widths.insert(decl.name.name.clone(), width);
                        }
                        let (kiw, ktn) = assoc_key_type_info(
                            key_dt.as_deref(),
                            &elab.parameters,
                            &elab.typedefs,
                            &elab.typedef_types,
                        );
                        if let Some(iw) = kiw {
                            elab.assoc_index_widths.insert(decl.name.name.clone(), iw);
                        }
                        if let Some(tn) = ktn {
                            elab.assoc_key_type_names.insert(decl.name.name.clone(), tn);
                        }
                    }
                    let is_dynamic_dim = decl.dimensions.first().is_some_and(|d| {
                        matches!(
                            d,
                            UnpackedDimension::Unsized(_) | UnpackedDimension::Queue { .. }
                        )
                    });
                    if is_dynamic_dim {
                        elab.dynamic_arrays.insert(decl.name.name.clone());
                    }
                    // IEEE 1800-2017 §7.4.5 / §7.8: unpacked array whose
                    // ELEMENT is itself a dynamic collection (`int q[3][$]`,
                    // `int d[3][]`, `int a[2][u8_t]`) declared in a generate /
                    // submodule-routed scope. Mirrors the module-scope
                    // DataDecl arm — without this the trailing dimension was
                    // dropped, `q[i]` registered as a plain scalar, and
                    // `q[i].push_back(x)` inside an instance was a silent
                    // no-op (`q[i].size()` read 0 forever).
                    if decl.dimensions.len() >= 2 {
                        let eff_dims = normalize_unpacked_dims(
                            &decl.dimensions,
                            &elab.parameters,
                            &elab.typedef_types,
                        );
                        let split = coll_elem_split(&eff_dims).unwrap_or(eff_dims.len());
                        if let Some(qd) = eff_dims.get(split) {
                            if matches!(
                                qd,
                                UnpackedDimension::Unsized(_)
                                    | UnpackedDimension::Queue { .. }
                                    | UnpackedDimension::Associative { .. }
                            ) {
                                let outer = &eff_dims[..split];
                                let shape: Option<Vec<(i64, i64)>> = outer
                                    .iter()
                                    .map(|d| {
                                        extract_array_range(
                                            std::slice::from_ref(d),
                                            &elab.parameters,
                                        )
                                    })
                                    .collect();
                                if let Some(shape) = shape.filter(|sh| {
                                    sh.iter().all(|&(lo, hi)| hi >= lo && hi - lo < 4096)
                                }) {
                                    let name = decl.name.name.clone();
                                    match shape.len() {
                                        1 => {
                                            elab.arrays.insert(
                                                name.clone(),
                                                (shape[0].0, shape[0].1, width),
                                            );
                                        }
                                        2 => {
                                            elab.arrays_2d
                                                .insert(name.clone(), (shape[0], shape[1], width));
                                        }
                                        _ => {
                                            elab.arrays_nd
                                                .insert(name.clone(), (shape.clone(), width));
                                        }
                                    }
                                    let qmax = if let UnpackedDimension::Queue {
                                        max_size: Some(ms),
                                        ..
                                    } = qd
                                    {
                                        const_eval_i64_with_params(ms, Some(&elab.parameters))
                                            .filter(|n| *n >= 0)
                                            .map(|n| (n + 1) as u32)
                                    } else {
                                        None
                                    };
                                    // Each element gets exactly the registration a
                                    // standalone `int q[$]` / `int a[key_t]` gets.
                                    let assoc_key = match qd {
                                        UnpackedDimension::Associative {
                                            data_type: kdt, ..
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
                                    // A packed-struct ELEMENT type: every element
                                    // collection carries the field layout, so
                                    // `q3[i][j].f` and a locator's `item.f` slice
                                    // the element like a standalone `T q[$]`.
                                    let elem_fields = packed_struct_field_layout(
                                        &dd.data_type,
                                        &elab.parameters,
                                        &elab.typedefs,
                                        &elab.typedef_types,
                                    )
                                    .filter(|f| !f.is_empty());
                                    if let Some(f) = &elem_fields {
                                        elab.packed_struct_fields
                                            .entry(name.clone())
                                            .or_insert_with(|| f.clone());
                                    }
                                    let assoc_key_info = match qd {
                                        UnpackedDimension::Associative { data_type, .. } => {
                                            assoc_key_type_info(
                                                data_type.as_deref(),
                                                &elab.parameters,
                                                &elab.typedefs,
                                                &elab.typedef_types,
                                            )
                                        }
                                        _ => (None, None),
                                    };
                                    for suffix in index_tuples(&shape) {
                                        let en = format!("{}{}", name, suffix);
                                        if let Some(f) = &elem_fields {
                                            elab.packed_struct_fields
                                                .entry(en.clone())
                                                .or_insert_with(|| f.clone());
                                        }
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
                                    elab.var_decl_types.insert(name, dd.data_type.clone());
                                    continue;
                                }
                            }
                        }
                    }
                    // A fixed MULTI-dimensional array declared in a generate
                    // block (or any other elaborate_items-routed scope): register
                    // its real shape — the 1-D path below kept only the first
                    // dimension — and apply its initializer as one whole-pattern
                    // assignment.
                    if let Some(shape) = fixed_unpacked_shape(&decl.dimensions, &elab.parameters)
                        .filter(|sh| sh.len() > 1)
                    {
                        let two_state =
                            is_type_two_state_resolved(&dd.data_type, &elab.typedef_types);
                        register_fixed_unpacked_array(
                            elab,
                            &decl.name.name,
                            &shape,
                            width,
                            two_state,
                        );
                        elab.var_decl_types
                            .entry(decl.name.name.clone())
                            .or_insert_with(|| dd.data_type.clone());
                        if let Some(init_expr) = &decl.init {
                            elab.initial_blocks.push(InitialBlock {
                                stmt: Statement::new(
                                    StatementKind::BlockingAssign {
                                        lvalue: make_ident_expr(&decl.name.name),
                                        rvalue: init_expr.as_ref().clone(),
                                    },
                                    Span::dummy(),
                                ),
                                scope: String::new(),
                            });
                        }
                        continue;
                    }
                    let array_range = extract_array_range(&decl.dimensions, &elab.parameters);
                    if let Some((lo, hi)) = array_range {
                        elab.arrays.insert(decl.name.name.clone(), (lo, hi, width));
                        // §6.8: a 2-state ELEMENT type means the array's
                        // slots default to 0 (the simulator consults this
                        // when it builds the element storage).
                        if is_type_two_state_resolved(&dd.data_type, &elab.typedef_types) {
                            elab.two_state_signals.insert(decl.name.name.clone());
                        }
                        // §7.2, §27: an array of UNPACKED structs in a generate
                        // block stores each element member-wise, as the
                        // top-level path registers it; the element type drives
                        // `%p` and `arr[i] = '{...}`. Without either,
                        // `g.q[2].f` read x and `q[2] = '{5, 6}` stored a vector.
                        elab.var_decl_types
                            .entry(decl.name.name.clone())
                            .or_insert_with(|| dd.data_type.clone());
                        if let DataType::Struct(su) =
                            resolve_typedef_chain(&dd.data_type, &elab.typedef_types)
                            && !su.packed
                            && !(matches!(su.kind, StructUnionKind::Union) && !su.tagged)
                            && hi >= lo
                            && (hi - lo) < 4096
                        {
                            for i in lo..=hi {
                                let ebase = format!("{}[{}]", decl.name.name, i);
                                register_unpacked_aggregate(elab, &ebase, &dd.data_type);
                            }
                        }
                        if let Some(UnpackedDimension::Range { left, right, .. }) =
                            decl.dimensions.first()
                        {
                            let l = const_eval_i64_with_params(left, Some(&elab.parameters))
                                .unwrap_or(0);
                            let r = const_eval_i64_with_params(right, Some(&elab.parameters))
                                .unwrap_or(0);
                            if l > r {
                                elab.descending_arrays.insert(decl.name.name.clone());
                            }
                        }
                        // Per-element Signals synthesized by Simulator::new
                        // from the `arrays` metadata — skip per-element
                        // HashMap inserts.
                        let _ = (is_signed, width, is_real);
                        if let Some(init_expr) = &decl.init {
                            let init_items: Vec<&Expression> =
                                match &peel_unpacked_typed_pattern(init_expr).kind {
                                    ExprKind::AssignmentPattern(items) => {
                                        items.iter().map(|i| i.expr()).collect()
                                    }
                                    ExprKind::Concatenation(exprs) => exprs.iter().collect(),
                                    _ => vec![],
                                };
                            // §7.5/§7.10/§10.10: a dynamic array / queue initialized
                            // by an unpacked array CONCATENATION (`{a, b, 9}`) or any
                            // other non-pattern expression (`= other_q`) is one
                            // whole-collection assignment: an operand that is itself
                            // a collection contributes all of its elements. Spread
                            // item-per-element, each collection operand became ONE
                            // (zero) element, and a bare collection initializer was
                            // dropped.
                            // §10.9.1: retain fixed-array patterns as whole assignments,
                            // including keyed/default entries and declared direction, and
                            // fixed-array concatenations, whose array operands (`{w, 5}`, a row
                            // `m[1]`) contribute every element in the target's declared order.
                            if (!is_dynamic_dim
                                && matches!(
                                    peel_unpacked_typed_pattern(init_expr).kind,
                                    ExprKind::AssignmentPattern(_) | ExprKind::Concatenation(_)
                                ))
                                || (is_dynamic_dim
                                    && !matches!(
                                        peel_unpacked_typed_pattern(init_expr).kind,
                                        ExprKind::AssignmentPattern(_)
                                    ))
                            {
                                elab.initial_blocks.push(InitialBlock {
                                    stmt: Statement::new(
                                        StatementKind::BlockingAssign {
                                            lvalue: make_ident_expr(&decl.name.name),
                                            rvalue: init_expr.as_ref().clone(),
                                        },
                                        Span::dummy(),
                                    ),
                                    scope: String::new(),
                                });
                            } else if !init_items.is_empty() {
                                let mut stmts: Vec<Statement> = Vec::new();
                                for (i, item_expr) in init_items.iter().enumerate() {
                                    let idx_i = lo + i as i64;
                                    let lval = Expression::new(
                                        ExprKind::Index {
                                            expr: Box::new(make_ident_expr(&decl.name.name)),
                                            index: Box::new(Expression::new(
                                                ExprKind::Number(
                                                    crate::ast::expr::NumberLiteral::Integer {
                                                        size: None,
                                                        signed: false,
                                                        base: crate::ast::expr::NumberBase::Decimal,
                                                        value: idx_i.to_string(),
                                                        cached_val: crate::ast::cache::LiteralCache::new(None),
                                                    },
                                                ),
                                                Span::dummy(),
                                            )),
                                        },
                                        Span::dummy(),
                                    );
                                    stmts.push(Statement::new(
                                        StatementKind::BlockingAssign {
                                            lvalue: lval,
                                            rvalue: (*item_expr).clone(),
                                        },
                                        Span::dummy(),
                                    ));
                                }
                                if is_dynamic_dim {
                                    let size_name = format!("{}.size", decl.name.name);
                                    let size_sig = Signal {
                                        is_const: false,
                                        name: size_name.clone().into(),
                                        width: 32,
                                        is_signed: false,
                                        is_real: false,
                                        direction: None,
                                        value: Value::from_u64(init_items.len() as u64, 32),
                                        type_name: None,
                                    };
                                    signals_insert_traced(
                                        &mut elab.signals,
                                        line!(),
                                        size_name,
                                        size_sig,
                                    );
                                }
                                elab.initial_blocks.push(InitialBlock {
                                    stmt: Statement::new(
                                        StatementKind::SeqBlock { name: None, stmts: stmts.into() },
                                        Span::dummy(),
                                    ),
                                    scope: String::new(),
                                });
                            }
                        }
                    } else {
                        // §10.3.1: a nettype net's declaration assignment is a
                        // continuous driver, not an initial value.
                        let decl_driver =
                            decl.init.as_deref().filter(|_| nettype_net).map(|init| {
                                nettype_declaration_driver(
                                    dd,
                                    &decl.name.name,
                                    init,
                                    false,
                                    &elab.parameters,
                                )
                            });
                        let procedural_init = decl.init.as_deref().filter(|init| {
                            decl_driver.is_none() && !is_const_expr(init, &elab.parameters)
                        });
                        let init_val = if let Some(init_expr) = decl
                            .init
                            .as_deref()
                            .filter(|_| decl_driver.is_none() && procedural_init.is_none())
                        {
                            let mut rv =
                                eval_init_for_target(init_expr, &elab.parameters, width, is_real);
                            if !is_real {
                                rv.is_signed = is_signed;
                            }
                            if is_real {
                                rv = Value::from_f64(rv.to_f64());
                            }
                            rv
                        } else {
                            default_value_for_type_resolved(
                                &dd.data_type,
                                width,
                                &elab.typedef_types,
                            )
                        };
                        let sig = Signal {
                            is_const: dd.const_kw,
                            name: decl.name.name.clone().into(),
                            width,
                            is_signed,
                            is_real,
                            direction: None,
                            value: init_val,
                            type_name: get_type_name(&dd.data_type),
                        };
                        signals_insert_traced(
                            &mut elab.signals,
                            line!(),
                            decl.name.name.clone(),
                            sig,
                        );
                        if let Some(ca) = decl_driver {
                            elab.continuous_assigns.push(ca);
                        }
                        if let Some(view) = &data_modport_view {
                            elab.modport_views
                                .insert(decl.name.name.clone(), view.clone());
                        }
                        // §6.8/§27: a generate-body initializer also executes
                        // before initial processes. Constant folding cannot
                        // construct an object or call a runtime function.
                        if let Some(init) = procedural_init {
                            if dd.const_kw {
                                elab.const_decl_inits.insert(decl.name.name.clone());
                            }
                            elab.static_init_blocks.push(InitialBlock {
                                stmt: Statement::new(
                                    StatementKind::BlockingAssign {
                                        lvalue: make_ident_expr(&decl.name.name),
                                        rvalue: init.clone(),
                                    },
                                    decl.name.span,
                                ),
                                scope: String::new(),
                            });
                        }
                        // Packed-struct metadata for a GENERATE-scope (or other
                        // elaborate_items-routed) declaration, mirroring the
                        // top-level DataDeclaration arm. This arm registered
                        // widths and generic dims but never the struct layout,
                        // the typedef-array shape, or the declared type — so a
                        // `burst_t [0:0][1:0] sig;` inside `if (1) begin : g`
                        // read $bits(g.sig[0][0]) = 1 and every member select
                        // returned garbage, while the identical module-scope
                        // declaration worked.
                        elab.var_decl_types
                            .entry(decl.name.name.clone())
                            .or_insert_with(|| dd.data_type.clone());
                        let chain2 =
                            resolve_typedef_chain(&dd.data_type, &elab.typedef_types).clone();
                        if let DataType::Struct(su) = &chain2 {
                            // §7.2 / §27.3: each generated aggregate owns its
                            // member cells and collection/type metadata, just
                            // like a module-scope aggregate.
                            if !su.packed
                                && !(matches!(su.kind, StructUnionKind::Union) && !su.tagged)
                            {
                                register_unpacked_aggregate(
                                    elab,
                                    &decl.name.name,
                                    &dd.data_type,
                                );
                            } else if su.packed {
                                if let Some(fields) = flatten_struct_fields(
                                    &dd.data_type,
                                    &elab.parameters,
                                    &elab.typedefs,
                                    &elab.typedef_types,
                                ) {
                                    if !fields.is_empty() {
                                        let struct_w =
                                            fields.iter().map(|(_, o, w)| o + w).max().unwrap_or(0);
                                        tls_register_struct_layout(&decl.name.name, &fields);
                                        elab.packed_struct_fields
                                            .insert(decl.name.name.clone(), fields);
                                        // Dims on the typedef reference itself
                                        // (`burst_t [0:0][1:0] sig;`): the
                                        // precise registration OVERRIDES the
                                        // generic chain that ran above — full
                                        // dims carry the struct width as the
                                        // innermost entry.
                                        if let Some(fdims) = packed_typedef_array_dims(
                                            &dd.data_type,
                                            struct_w,
                                            &elab.parameters,
                                        ) {
                                            let total: i64 = fdims
                                                .iter()
                                                .map(|(l, r)| (l - r).abs() + 1)
                                                .product();
                                            let (ol, orr) = fdims[0];
                                            let outer = (ol - orr).abs() + 1;
                                            if outer > 0 && total > 0 {
                                                elab.packed_signal_elem_widths.insert(
                                                    decl.name.name.clone(),
                                                    (total / outer) as u32,
                                                );
                                            }
                                            elab.packed_full_dims
                                                .insert(decl.name.name.clone(), fdims);
                                        }
                                    }
                                }
                            } else {
                                // §7.2, §27: an unpacked struct declared in
                                // a generate block is stored member by
                                // member, as the module-scope arm stores
                                // one. Left as a single vector, a 4-state
                                // or handle member kept x through every
                                // write (aionhw/xezim#1161).
                                register_unpacked_aggregate(elab, &decl.name.name, &dd.data_type);
                            }
                        }
                    }
                }
            }
            ModuleItem::ParameterDeclaration(pd) | ModuleItem::LocalparamDeclaration(pd) => {
                if let ParameterKind::Data {
                    data_type,
                    assignments,
                } = &pd.kind
                {
                    let base_width =
                        resolve_type_width(data_type, Some(&elab.parameters), Some(&elab.typedefs));
                    // §6.20.2: resolve through typedefs (see the module-scope
                    // pre-pass above) — a typedef'd SIGNED declared type must
                    // read the typedef's sign.
                    let base_signed = is_type_signed_resolved(data_type, &elab.typedef_types);
                    let base_is_real = is_type_real_resolved(data_type, &elab.typedef_types);
                    if matches!(
                        data_type,
                        DataType::Simple {
                            kind: SimpleType::String,
                            ..
                        }
                    ) {
                        for a in assignments {
                            elab.string_signals.insert(a.name.name.clone());
                        }
                    }
                    let implicit = matches!(data_type, DataType::Implicit { dimensions, .. } if dimensions.is_empty());
                    for assign in assignments {
                        if elab.signals.contains_key(&assign.name.name)
                            || elab.parameters.contains_key(&assign.name.name)
                        {
                            if elab.claim_local_decl_displacement(
                                &assign.name.name,
                                assign.name.span,
                                "parameter/localparam",
                            ) {
                                elab.remove_param(&assign.name.name);
                                elab.signals.remove(&assign.name.name);
                            } else {
                                return Err(duplicate_decl_error(
                                    &elab,
                                    &assign.name.name,
                                    assign.name.span,
                                    "parameter",
                                ));
                            }
                        }
                        elab.note_decl_site(
                            &assign.name.name,
                            assign.name.span,
                            "parameter/localparam",
                            true,
                        );
                        // §27, §6.20.2: a generate scope holds the same shapes
                        // as a module body. Without this an unpacked array got
                        // no elements, so every `A[i]` read 0, and an index of
                        // a packed array bit-selected.
                        if !assign.dimensions.is_empty() {
                            if register_array_param(
                                elab,
                                "",
                                &assign.name.name,
                                &assign.dimensions,
                                assign.init.as_ref(),
                                None,
                                data_type,
                                None,
                            ) {
                                continue;
                            }
                        }
                        register_packed_param_shape(elab, &assign.name.name, data_type);
                        if !elab.parameters.contains_key(&assign.name.name) {
                            if implicit
                                && let Some(init) = &assign.init
                                && let ExprKind::Number(NumberLiteral::UnbasedUnsized(c)) =
                                    &init.kind
                            {
                                // §6.20.2 self-determined: 1-bit, unsigned, plain.
                                let mut pv = Value::fill_of(*c);
                                pv.is_fill = false;
                                elab.set_param(line!(), assign.name.name.clone(), pv.clone());
                                signals_insert_traced(
                                    &mut elab.signals,
                                    line!(),
                                    assign.name.name.clone(),
                                    Signal {
                                        is_const: false,
                                        name: assign.name.name.clone().into(),
                                        width: 1,
                                        is_signed: false,
                                        direction: None,
                                        value: pv,
                                        is_real: false,
                                        type_name: get_type_name(data_type),
                                    },
                                );
                                continue;
                            }
                            let prebound: Option<Expression> = assign
                                .init
                                .as_ref()
                                .filter(|init| expr_mentions_bits(init))
                                .map(|init| {
                                    prebind_bits_of_signals(
                                        init,
                                        &elab.signals,
                                        &elab.parameters,
                                        "",
                                        &elab.typedefs,
                                        &elab.typedef_types,
                                        &elab.packed_struct_fields,
                                        &elab.arrays,
                                    )
                                });
                            let res = resolve_param_decl_value(
                                elab,
                                data_type,
                                prebound.as_ref().or(assign.init.as_ref()),
                                None,
                                None,
                                base_width,
                                base_signed,
                                base_is_real,
                                ParamDeclPolicy {
                                    unresolved_call: UnresolvedCallPolicy::ContinueOriginal,
                                    promote_implicit_real: false,
                                    narrow_implicit_string_lit: false,
                                    force_signed_on_override: false,
                                    eval_packed_aggregate: false,
                                    require_known_idents: false,
                                    signed_from_pkg_helper: false,
                                },
                            );
                            let val = res.val;
                            let width = res.width;
                            let signed = res.signed;
                            let is_real = res.is_real;
                            elab.set_param(line!(), assign.name.name.clone(), val.clone());
                            signals_insert_traced(
                                &mut elab.signals,
                                line!(),
                                assign.name.name.clone(),
                                Signal {
                                    is_const: false,
                                    name: assign.name.name.clone().into(),
                                    width,
                                    is_signed: signed,
                                    direction: None,
                                    value: val,
                                    is_real,
                                    type_name: get_type_name(data_type),
                                },
                            );
                        }
                    }
                }
            }
            ModuleItem::ContinuousAssign(ca) => {
                let (delay, delay_fall, delay_off, delay_exprs) = cont_assign_delays(
                    [ca.delay.as_deref(), ca.delay_fall.as_deref(), ca.delay_off.as_deref()], &elab.parameters);
                for (lhs, rhs) in &ca.assignments {
                    // §10.3.1 / §21.2.1.5: record the drive strength pair on
                    // the target net so `%v` can report it (e.g. "Pu0").
                    if let Some(s) = &ca.strength {
                        if let ExprKind::Ident(h) = &lhs.kind {
                            if h.path.len() == 1 {
                                let mut s1 = String::new();
                                let mut s0 = String::new();
                                for tok in s.split(',') {
                                    if tok.ends_with('1') {
                                        s1 = tok.to_string();
                                    } else if tok.ends_with('0') {
                                        s0 = tok.to_string();
                                    }
                                }
                                if !s1.is_empty() || !s0.is_empty() {
                                    elab.net_strengths
                                        .insert(h.path[0].name.name.clone(), (s1, s0));
                                }
                            }
                        }
                    }
                    let mut rhs_final = match ca.strength.as_deref().and_then(strength_marker) {
                        Some((marker, code)) => make_syscall(
                            marker,
                            vec![rhs.clone(), strength_code_literal(code, rhs.span)],
                            rhs.span,
                        ),
                        None => rhs.clone(),
                    };
                    root_mark_hier_ca_rhs(
                        lhs,
                        &mut rhs_final,
                        &|n| elab.struct_members.contains_key(n),
                        &|n| elab.packages.contains(n),
                    );
                    if !expand_whole_array_assign(lhs, &rhs_final, delay, &delay_exprs, elab) {
                        elab.continuous_assigns.push(ContinuousAssignment {
                            gate_delay_fall: None,
                            delay_exprs: delay_exprs.clone(),
                            delay_select: None,
                            origin: Some((ca.span, top_origin_scope())),
                            lhs: lhs.clone(),
                            rhs: rhs_final,
                            delay,
                            rhs_parent_scoped: false,
                            delay_fall,
                            delay_off,
                        });
                    }
                }
            }
            ModuleItem::GateInstantiation(gi) => {
                gate_inst_to_assigns(gi, elab);
            }
            ModuleItem::AlwaysConstruct(ac) => {
                // §21.2.1.7: include generate block scope in the instance path for %m.
                if pend_dbg_enabled() {
                    eprintln!("[PEND-DIRECT] scope={:?}", ac.gen_scope);
                }
                elab.always_blocks.push(AlwaysBlock {
                    kind: ac.kind,
                    stmt: ac.stmt.clone(),
                    scope: ac.gen_scope.clone(),
                });
            }
            ModuleItem::InitialConstruct(ic) => {
                if std::env::var("XEZIM_TRACE_INIT").ok().as_deref() == Some("1") {
                    eprintln!("[xezim][elab] @2453 pushing initial (other path)");
                }
                // §21.2.1.7: include generate block scope in the instance path for %m.
                elab.initial_blocks.push(InitialBlock {
                    stmt: ic.stmt.clone(),
                    scope: ic.gen_scope.clone(),
                });
            }
            // Mirror the AssertionItem hoist in elaborate_module_with_defs
            // so module-level `assert/assume/cover property (…)` inside
            // generate blocks or checker bodies fires too.
            ModuleItem::AssertionItem(a) => {
                elab.initial_blocks.push(InitialBlock {
                    stmt: crate::ast::stmt::Statement::new(
                        crate::ast::stmt::StatementKind::Assertion(a.clone()),
                        a.span,
                    ),
                    scope: String::new(),
                });
            }
            ModuleItem::FinalConstruct(fc) => {
                // §24.9 — nonblocking assignments are illegal in a final block.
                if stmt_contains_nonblocking(&fc.stmt) {
                    return Err(
                        "final procedures cannot contain nonblocking assignments (LRM §24.9)"
                            .to_string(),
                    );
                }
                elab.final_blocks.push(InitialBlock {
                    stmt: fc.stmt.clone(),
                    scope: String::new(),
                });
            }
            ModuleItem::ModuleInstantiation(inst) => {
                for hi in &inst.instances {
                    if !elab.signals.contains_key(&hi.name.name) {
                        signals_insert_traced(
                            &mut elab.signals,
                            line!(),
                            hi.name.name.clone(),
                            Signal {
                                is_const: false,
                                name: hi.name.name.clone().into(),
                                width: 1,
                                is_signed: false,
                                direction: None,
                                value: Value::new(1),
                                type_name: Some(inst.module_name.name.clone()),
                                is_real: false,
                            },
                        );
                    }
                    for c in &hi.connections {
                        if let PortConnection::Named { expr: Some(e), .. }
                        | PortConnection::Ordered(Some(e)) = c
                        {
                            declare_block_port_implicit_nets(e, elab)?;
                        }
                    }
                }
            }
            ModuleItem::TypedefDeclaration(td) => {
                process_typedef(td, elab);
            }
            ModuleItem::AliasDecl(terms) => {
                // §10.11: an alias statement in a generate block names ONE
                // physical net. The block's OWN declarations carry the scope
                // prefix (`g.x`), a name from OUTSIDE the block keeps its own
                // name, so the group is recorded with both forms and the
                // unification pass picks the one that exists.
                let Ok(names) = alias_term_names(terms) else {
                    return Err(
                        "alias operands must be plain nets (IEEE 1800-2017 \u{00a7}10.11)"
                            .to_string(),
                    );
                };
                let group: Vec<String> = names
                    .iter()
                    .map(|n| {
                        if elab.nets.contains(n) || elab.signals.contains_key(n) {
                            n.clone()
                        } else {
                            // A block-local name: the scope prefix is added by
                            // the generate rename, so the flat name carries it.
                            n.clone()
                        }
                    })
                    .collect();
                elab.alias_groups.push(group);
            }
            ModuleItem::GenerateRegion(gr) => {
                elaborate_items(&gr.items, elab, cls_defs)?;
            }
            ModuleItem::GenerateIf(gi) => {
                elaborate_generate_if(gi, elab, cls_defs)?;
            }
            ModuleItem::GenerateCase(gc) => {
                elaborate_generate_case(gc, elab, cls_defs)?;
            }
            ModuleItem::GenerateFor(gf) => {
                elaborate_generate_for(gf, elab, cls_defs)?;
            }

            ModuleItem::ClassDeclaration(cd) => {
                validate_class_constraints(
                    cd,
                    cls_defs,
                    Some(&elab.enum_members),
                    Some(&elab),
                    None,
                )?;
                // Class-body enum typedef members are class constants; without
                // this, `CB` in a method and `box::CB` both read x for classes
                // declared in a MODULE body (package/$unit classes already
                // registered).
                register_class_enum_members(cd, elab);
                register_class_scoped_typedef_aliases(cd, None, elab);
                let cls =
                    std::sync::Arc::new(elaborate_class_with_params(cd, Some(&elab.parameters)));
                elab.classes.insert(cd.name.name.clone(), cls);
                register_nested_classes(cd, &cd.name.name, elab);
            }
            ModuleItem::ClockingDeclaration(cd) => {
                // §14.12 standalone designation `default clocking <name>;`
                // arrives as an empty, clock-less marker — fold it into the
                // real same-named block instead of overwriting it (either
                // declaration order). A real block keeps a designation that
                // arrived first.
                let is_designation =
                    cd.clock_signal.is_none() && cd.signals.is_empty() && cd.is_default;
                if is_designation {
                    if let Some(existing) = elab.clocking_blocks.get_mut(&cd.name.name) {
                        existing.is_default = true;
                    } else {
                        elab.clocking_blocks
                            .insert(cd.name.name.clone(), cd.clone());
                    }
                    continue;
                }
                let mut dirs = HashMap::default();
                for s in &cd.signals {
                    dirs.insert(s.name.name.clone(), s.direction);
                }
                let was_default = elab
                    .clocking_blocks
                    .get(&cd.name.name)
                    .is_some_and(|p| p.is_default && p.clock_signal.is_none());
                let mut cd_owned = cd.clone();
                if was_default {
                    cd_owned.is_default = true;
                }
                elab.clocking_signal_dirs.insert(cd.name.name.clone(), dirs);
                elab.clocking_blocks.insert(cd.name.name.clone(), cd_owned);
            }
            ModuleItem::LetDeclaration(ld) => {
                elab.lets.insert(ld.name.name.clone(), ld.clone());
            }
            ModuleItem::SequenceDeclaration(sd) => {
                elab.sequences.insert(sd.name.name.clone());
                if let Some(body) = &sd.body {
                    // Sequences share the property_decls map for
                    // `assert property (s)` style references.
                    elab.property_decls
                        .insert(sd.name.name.clone(), Rc::new(body.clone()));
                    elab.property_params.insert(
                        sd.name.name.clone(),
                        sd.ports.iter().map(|p| p.name.clone()).collect(),
                    );
                    register_sva_port_defaults(elab, &sd.name.name, &sd.port_defaults);
                }
            }
            ModuleItem::PropertyDeclaration(pd) => {
                elab.sequences.insert(pd.name.name.clone());
                if let Some(body) = &pd.body {
                    elab.property_decls
                        .insert(pd.name.name.clone(), Rc::new(body.clone()));
                    elab.property_params.insert(
                        pd.name.name.clone(),
                        pd.ports.iter().map(|p| p.name.clone()).collect(),
                    );
                    register_sva_port_defaults(elab, &pd.name.name, &pd.port_defaults);
                }
            }
            // LRM §17 — register the checker name AND inline its body
            // items into the current module. This is the minimum-viable
            // shape: the checker has no formal-arg binding (single
            // "always-on" instance at the declaration site), but
            // assertions / always-blocks / let-decls inside the body
            // fire as if they were written directly in the parent
            // module. Multiple instantiations and port binding remain
            // future work.
            ModuleItem::CheckerDeclaration(cd) => {
                elab.sequences.insert(cd.name.name.clone());
                let body = cd.items.clone();
                elaborate_items(&body, elab, all_defs)?;
            }
            ModuleItem::SpecifyBlock(sb) => {
                // Evaluate delays against `&elab.parameters` (read-only)
                // before the `&mut` borrow, so no whole-table clone is needed.
                let delay_vals: Vec<Vec<u64>> = {
                    let params = &elab.parameters;
                    sb.paths
                        .iter()
                        .map(|p| {
                            p.delays.iter().map(|d| eval_const_expr(d, params)).collect()
                        })
                        .collect()
                };
                elaborate_module_paths(elab, &sb.paths, &delay_vals, &|e| e.clone());
                // §15.6 delayed nets: `assign delayed_net = source` (zero delay)
                // so a top-level cell's functional path through them works.
                for (delayed, source) in &sb.delayed_nets {
                    elab.continuous_assigns.push(ContinuousAssignment {
                        gate_delay_fall: None,
                        delay_exprs: None,
                        delay_select: None,
                        origin: None,
                        lhs: make_ident_expr(delayed),
                        rhs: make_ident_expr(source),
                        delay: 0,
                        rhs_parent_scoped: false,
                        delay_fall: None,
                        delay_off: None,
                    });
                }
                if !sb.timing_checks.is_empty() {
                    let timing_consts: Vec<Vec<Option<i64>>> = {
                        let params = &elab.parameters;
                        sb.timing_checks
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
                                        let v = eval_const_expr_val(&a.expr, params);
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
                            .collect()
                    };
                    let def_name = elab.name.clone();
                    elaborate_timing_checks(
                        elab,
                        &sb.timing_checks,
                        "",
                        &def_name,
                        &timing_consts,
                        &|e| e.clone(),
                    );
                }
            }
            ModuleItem::FunctionDeclaration(fd) => {
                if matches!(fd.return_type, DataType::Void(_)) {
                    fn check_void_return(s: &crate::ast::stmt::Statement) -> Result<(), String> {
                        use crate::ast::stmt::StatementKind as SK;
                        match &s.kind {
                            SK::Return(Some(_)) => {
                                Err("void function must not return a value".into())
                            }
                            SK::SeqBlock { stmts, .. } | SK::ParBlock { stmts, .. } => {
                                for st in stmts {
                                    check_void_return(st)?;
                                }
                                Ok(())
                            }
                            SK::If {
                                then_stmt,
                                else_stmt,
                                ..
                            } => {
                                check_void_return(then_stmt)?;
                                if let Some(eb) = else_stmt {
                                    check_void_return(eb)?;
                                }
                                Ok(())
                            }
                            SK::For { body, .. }
                            | SK::While { body, .. }
                            | SK::DoWhile { body, .. }
                            | SK::Repeat { body, .. }
                            | SK::Forever { body }
                            | SK::Foreach { body, .. } => check_void_return(body),
                            SK::TimingControl { stmt, .. } | SK::Wait { stmt, .. } => {
                                check_void_return(stmt)
                            }
                            SK::Case { items, .. } => {
                                for it in items {
                                    check_void_return(&it.stmt)?;
                                }
                                Ok(())
                            }
                            _ => Ok(()),
                        }
                    }
                    for it in &fd.items {
                        check_void_return(it)?;
                    }
                }
                fn check_fn_fork(s: &crate::ast::stmt::Statement) -> Result<(), String> {
                    use crate::ast::stmt::StatementKind as SK;
                    match &s.kind {
                        SK::ParBlock {
                            join_type, stmts, ..
                        } => {
                            if !matches!(join_type, crate::ast::stmt::JoinType::JoinNone) {
                                return Err(
                                    "only fork-join_none is permitted inside a function".into()
                                );
                            }
                            for st in stmts {
                                check_fn_fork(st)?;
                            }
                            Ok(())
                        }
                        SK::SeqBlock { stmts, .. } => {
                            for st in stmts {
                                check_fn_fork(st)?;
                            }
                            Ok(())
                        }
                        SK::If {
                            then_stmt,
                            else_stmt,
                            ..
                        } => {
                            check_fn_fork(then_stmt)?;
                            if let Some(eb) = else_stmt {
                                check_fn_fork(eb)?;
                            }
                            Ok(())
                        }
                        SK::For { body, .. }
                        | SK::While { body, .. }
                        | SK::DoWhile { body, .. }
                        | SK::Repeat { body, .. }
                        | SK::Forever { body }
                        | SK::Foreach { body, .. } => check_fn_fork(body),
                        SK::TimingControl { stmt, .. } | SK::Wait { stmt, .. } => {
                            check_fn_fork(stmt)
                        }
                        SK::Case { items, .. } => {
                            for it in items {
                                check_fn_fork(&it.stmt)?;
                            }
                            Ok(())
                        }
                        _ => Ok(()),
                    }
                }
                for it in &fd.items {
                    check_fn_fork(it)?;
                }
                // Same scope filter as above: out-of-class method definitions
                // must not override free functions.
                if fd.name.scopes.is_empty() {
                    elab.functions.insert(fd.name.name.name.clone(), fd.clone());
                }
            }
            ModuleItem::TaskDeclaration(td) => {
                fn check_no_return_in_fork(
                    s: &crate::ast::stmt::Statement,
                    in_fork: bool,
                ) -> Result<(), String> {
                    use crate::ast::stmt::StatementKind as SK;
                    match &s.kind {
                        SK::Return(_) if in_fork => Err("illegal return from fork".into()),
                        SK::ParBlock { stmts, .. } => {
                            for st in stmts {
                                check_no_return_in_fork(st, true)?;
                            }
                            Ok(())
                        }
                        SK::SeqBlock { stmts, .. } => {
                            for st in stmts {
                                check_no_return_in_fork(st, in_fork)?;
                            }
                            Ok(())
                        }
                        SK::If {
                            then_stmt,
                            else_stmt,
                            ..
                        } => {
                            check_no_return_in_fork(then_stmt, in_fork)?;
                            if let Some(eb) = else_stmt {
                                check_no_return_in_fork(eb, in_fork)?;
                            }
                            Ok(())
                        }
                        SK::For { body, .. }
                        | SK::While { body, .. }
                        | SK::DoWhile { body, .. }
                        | SK::Repeat { body, .. }
                        | SK::Forever { body }
                        | SK::Foreach { body, .. } => check_no_return_in_fork(body, in_fork),
                        SK::TimingControl { stmt, .. } | SK::Wait { stmt, .. } => {
                            check_no_return_in_fork(stmt, in_fork)
                        }
                        SK::Case { items, .. } => {
                            for it in items {
                                check_no_return_in_fork(&it.stmt, in_fork)?;
                            }
                            Ok(())
                        }
                        _ => Ok(()),
                    }
                }
                for it in &td.items {
                    check_no_return_in_fork(it, false)?;
                }
                // Same scope filter: don't let out-of-class method definitions
                // override free tasks in the module namespace.
                if td.name.scopes.is_empty() {
                    elab.tasks.insert(td.name.name.name.clone(), td.clone());
                }
            }
            ModuleItem::ImportDeclaration(imp) => {
                if let Some(defs) = all_defs {
                    process_import(imp, elab, defs, false)?;
                }
            }
            ModuleItem::DPIImport(di) => {
                register_dpi_import(di, elab, None)?;
            }
            _ => {}
        }
    }
    Ok(())
}
