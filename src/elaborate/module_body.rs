use super::*;

pub fn elaborate_module_with_defs(
    module: Definition,
    param_overrides: &HashMap<String, Value>,
    all_defs: Option<&HashMap<String, Definition>>,
    top_level_imports: &[ImportDeclaration],
    top_level_lets: &[LetDeclaration],
    seed_ooc_constraints: &[(String, String, Vec<crate::ast::decl::ConstraintItem>)],
) -> Result<ElaboratedModule, String> {
    PACKED_WIDTH_ERROR.with(|slot| slot.take());
    let _oom_trace = crate::oom_trace::session();
    let _oom_definition = crate::oom_trace::definition(module, "elaborate module", module.name());
    let mut elab = ElaboratedModule::new(module.name().to_string());
    // §6.5/§10: within a scope a net/variable must be DECLARED before it is
    // referenced (implicit nets §6.10 are the only exception, and they do not
    // apply to a name declared LATER). Check every data expression, including
    // call arguments and event/assertion expressions.
    validate_module_data_declarations(Some(module), all_defs, top_level_imports)?;
    // §20.6.2/§20.7: the module's declarations answer `$bits` and the array
    // queries in its constant expressions for the whole elaboration.
    DECL_SHAPES_CACHE.with(|c| c.borrow_mut().clear());
    crate::oom_trace::checkpoint(
        "elaborate.decl_shapes.begin",
        &[
            ("module_items", module.items().len()),
            ("shape_inline_bytes", std::mem::size_of::<StoredDeclShape>()),
            ("shape_query_inline_bytes", std::mem::size_of::<DeclShape>()),
        ],
    );
    let _decl_shapes = install_decl_shapes(module);
    crate::oom_trace::checkpoint("elaborate.decl_shapes.ready", &[]);

    // §24.3: a program block shall not contain module declarations —
    // reject before elaboration runs the nested module's items (ivtest
    // program5a; the reference errors at parse).
    if matches!(module, Definition::Program(_)) {
        for item in module.items() {
            if let ModuleItem::NestedModule(nm) = item {
                return Err(format!(
                    "module '{}' declared inside program '{}'; programs cannot contain module declarations (§24.3)",
                    nm.name.name,
                    module.name()
                ));
            }
        }
    }

    // §18.5.1: seed $unit-scope out-of-class constraint definitions so a class's
    // `extern constraint c;` is satisfied regardless of whether the design has a
    // module (the definition is parsed at compilation-unit scope, outside any).
    for (c, n, _items) in seed_ooc_constraints {
        elab.out_of_class_constraints.insert((c.clone(), n.clone()));
    }
    // The class table is populated just below (from `all_defs`); the bodies of
    // $unit-scope definitions are installed after that, see `seed_ooc_bodies`.

    // Process top-level typedefs and other global definitions from all_defs
    // Set below once the `$unit` typedefs are known; never another design's.
    CONST_FN_UNIT_TYPES.with(|c| *c.borrow_mut() = None);
    if let Some(defs) = all_defs {
        // §6.18: typedefs must be processed in DEPENDENCY order. A struct
        // typedef's width is resolved from the width map built by the
        // typedefs processed BEFORE it, and an unresolved member type falls
        // back to 32 bits. `defs` is a HashMap, so the order was whatever
        // hashing produced — `typedef struct packed { sp_t inner; logic [15:0]
        // tail; } via_t;` came out 48 bits instead of 32 whenever `via_t`
        // hashed ahead of `sp_t`. Adding an unrelated module to the file
        // changed the map's contents and so its iteration order, which silently
        // changed `$bits` of a nested struct typedef and every signal declared
        // with it.
        // Package PARAMETERS first, to a fixpoint, so that (a) a package
        // typedef sized by its own or another package's parameter
        // (`logic [LOG-1:0]`, `LOG = $clog2(cfg::DEPTH) - 6`) resolves during
        // the hoist below, and (b) a $unit typedef referencing `pkg::param`
        // resolves in the pass that follows. Previously package parameters
        // only materialized on IMPORT, so any width computed before the first
        // import of the owning package saw 0 — the classic symptom being a
        // parameter "resolved to -6" and five 7-bit fields clamping to 1 bit,
        // narrowing a struct port's testbench side by exactly 30 bits while
        // the DUT side (healed by the child fixpoint) stayed correct.
        hoist_package_params(defs, &mut elab);
        // §8.23: class constants next, so a `cls::N` dimension sizes before
        // any class or module declaration is elaborated.
        hoist_class_consts(defs, &mut elab);
        // §26.3: a package typedef can reference ANOTHER package's scoped
        // typedef (`q::inner_t` inside p's struct). The per-package
        // processing below runs in map order, so p's struct width fell back
        // to 32 per unresolved member whenever p hashed ahead of q.
        // Pre-register every package's typedefs to a fixpoint (two passes,
        // re-processing is idempotent) so cross-package members resolve
        // regardless of iteration order.
        for _pass in 0..2 {
            for def in defs.values() {
                let Definition::Package(pkg) = def else {
                    continue;
                };
                let ov = overlay_pkg_params(pkg, &mut elab);
                for item in &pkg.items {
                    if let crate::ast::decl::PackageItem::Typedef(td) = item {
                        process_typedef(td, &mut elab);
                        register_scoped_typedef_alias(&pkg.name.name, td, &mut elab);
                    }
                }
                restore_overlay(&mut elab, ov);
            }
        }
        for td in ordered_typedefs(defs) {
            check_enum_member_duplicates(td, &elab)?;
            process_typedef(td, &mut elab);
        }
        // §6.20.2: aggregate array values need their element typedef layout.
        // Scalar sizing parameters still hoist first; only designs with typed
        // package arrays need the second fixpoint after typedef registration.
        if defs.values().any(|d| {
            matches!(d, Definition::Package(p)
            if p.items.iter().any(|i| matches!(i, PackageItem::Parameter(pd)
                if matches!(&pd.kind, ParameterKind::Data { data_type, assignments }
                    if matches!(data_type, DataType::TypeReference { .. } | DataType::Struct(_))
                    && assignments.iter().any(|a| !a.dimensions.is_empty())))))
        }) {
            hoist_package_params(defs, &mut elab);
        }
        for def in defs.values() {
            match def {
                Definition::Typedef(_) => {}
                Definition::Class(c) => {
                    validate_class_constraints(
                        c,
                        Some(defs),
                        Some(&elab.enum_members),
                        Some(&elab),
                        None,
                    )?;
                    register_class_enum_members(c, &mut elab);
                    register_class_covergroups(c, &mut elab);
                    register_class_scoped_typedef_aliases(c, None, &mut elab);
                    elab.classes.insert(
                        c.name.name.clone(),
                        std::sync::Arc::new(elaborate_class_with_params(c, Some(&elab.parameters))),
                    );
                    // §18.5.1: a `constraint Class::name {...}` written at
                    // $unit scope fills this class's extern prototype.
                    for (cn, nn, items) in seed_ooc_constraints {
                        if cn == &c.name.name {
                            install_ooc_constraint_body(&mut elab, cn, nn, items);
                        }
                    }
                }
                Definition::Covergroup(cg) => {
                    elab.covergroups.insert(cg.name.name.clone(), (*cg).clone());
                }
                Definition::Package(p) => {
                    elab.packages.insert(p.name.name.clone());
                    // Bounded bare view of this package's own parameters while
                    // ITS items are hoisted (see overlay_pkg_params).
                    let __pkg_overlay = overlay_pkg_params(p, &mut elab);
                    // Hoist package-scope functions/tasks for `pkg::f(...)`
                    // and bare-name resolution after `import pkg::*`. A
                    // scoped name (`ClassName::m`) is an out-of-class method
                    // body — `link_extern_methods` handles those.
                    for item in &p.items {
                        match item {
                            crate::ast::decl::PackageItem::Function(f)
                                if f.name.scopes.is_empty() =>
                            {
                                elab.functions
                                    .insert_if_absent_with(f.name.name.name.clone(), || f.clone());
                                // §26.3: the qualified key — `pkg::f(...)` must
                                // reach THIS package's declaration even when a
                                // later package hoists the same bare name.
                                elab.functions.insert(
                                    format!("{}::{}", p.name.name, f.name.name.name),
                                    f.clone(),
                                );
                                elab.pkg_subr_owner
                                    .entry(f.name.name.name.clone())
                                    .or_insert_with(|| p.name.name.clone());
                            }
                            crate::ast::decl::PackageItem::Task(t) if t.name.scopes.is_empty() => {
                                elab.tasks
                                    .entry(t.name.name.name.clone())
                                    .or_insert_with(|| t.clone());
                                elab.tasks.insert(
                                    format!("{}::{}", p.name.name, t.name.name.name),
                                    t.clone(),
                                );
                                elab.pkg_subr_owner
                                    .entry(t.name.name.name.clone())
                                    .or_insert_with(|| p.name.name.clone());
                            }
                            // §26.3: register package classes by name so an
                            // (imported or scoped) reference like
                            // `uvm_config_db#(T)::set` resolves instead of being
                            // flagged "Undeclared identifier". Class bodies are
                            // also reachable through their package for
                            // `pkg::Class::method`.
                            crate::ast::decl::PackageItem::Covergroup(cg) => {
                                register_package_covergroup(&p.name.name, cg, &mut elab);
                            }
                            crate::ast::decl::PackageItem::Class(c) => {
                                register_class_enum_members(c, &mut elab);
                                register_class_covergroups(c, &mut elab);
                                register_class_scoped_typedef_aliases(
                                    c,
                                    Some(&p.name.name),
                                    &mut elab,
                                );
                                // Compute the elaborated class before taking
                                // `&mut elab.classes`, so no parameter-snapshot
                                // clone is needed.
                                if !elab.classes.contains_key(&c.name.name) {
                                    let cls = std::sync::Arc::new(elaborate_class_with_params(
                                        c,
                                        Some(&elab.parameters),
                                    ));
                                    elab.classes.insert(c.name.name.clone(), cls);
                                }
                            }
                            // Hoist package typedefs (loads enum members + typedef
                            // widths) so an explicit scoped reference `pkg::CONST`
                            // — which does NOT require an import — resolves during
                            // top-module elaboration, e.g. a generate-if
                            // `CVA6Cfg.DCacheType == config_pkg::WT` (ariane).
                            // Package types are otherwise only processed later in
                            // inline_instantiations, after the top body.
                            crate::ast::decl::PackageItem::Typedef(td) => {
                                process_typedef(td, &mut elab);
                                register_scoped_typedef_alias(&p.name.name, td, &mut elab);
                            }
                            // Hoist package DPI imports so calls to
                            // `uvm_re_compexecfree` etc. resolve via
                            // `exec_dpi_import_call`.
                            crate::ast::decl::PackageItem::DPIImport(di) => {
                                register_dpi_import(di, &mut elab, Some(p.name.name.as_str()))?;
                            }
                            _ => {}
                        }
                    }
                    restore_overlay(&mut elab, __pkg_overlay);
                }
                _ => {}
            }
        }
        // Second pass over $unit typedefs, now that every package typedef has
        // its scoped `pkg::name` alias. A compilation-unit typedef whose member
        // names a package type (`typedef struct packed { CHIP::t w; ... }`)
        // was processed BEFORE any package existed, fell back to 32 bits for
        // that member, and was never revisited. `process_typedef` recomputes
        // and overwrites, so correct entries are unchanged and stale ones heal.
        for td in ordered_typedefs(defs) {
            process_typedef(td, &mut elab);
        }
        let unit_types: HashMap<String, DataType> = ordered_typedefs(defs)
            .into_iter()
            .filter_map(|td| {
                let dt = elab.typedef_types.get(&td.name.name)?;
                Some((td.name.name.clone(), dt.clone()))
            })
            .collect();
        CONST_FN_UNIT_TYPES.with(|c| *c.borrow_mut() = Some(unit_types));
        // Package parameters again, now that typedefs and enum members exist:
        // the first hoist ran before either, so an enum-valued parameter
        // (`localparam cache_type_t T = config_pkg::WT`) folded to 0 — and a
        // struct parameter built from it (CVA6's `DCacheType`) picked the
        // wrong generate branch. Then the struct parameters themselves.
        hoist_package_params(defs, &mut elab);
        hoist_package_struct_params(defs, &mut elab);
        // §6.19, §26.3: a `$unit` enum member initialized from a package
        // parameter that this hoist has just settled (`A = p::K`, with
        // `localparam int K = E;` and `E` a member of `p`'s enum) read the
        // parameter's first-pass value, 0. Register the `$unit` enums once
        // more, then record the entries of their members that a package also
        // declares, which `reassert_unit_enum_members` puts back once
        // instances are inlined.
        for td in ordered_typedefs(defs) {
            if matches!(td.data_type, DataType::Enum(_)) {
                process_typedef(td, &mut elab);
            }
        }
        elab.unit_member_slots = contested_unit_member_slots(defs, &elab);
    }

    crate::oom_trace::checkpoint("elaborate.global_definitions.ready", &[("functions", elab.functions.len())]);

    // Process top-level imports
    for imp in top_level_imports {
        if let Some(defs) = all_defs {
            process_import(imp, &mut elab, defs, false)?;
        }
    }

    for l in top_level_lets {
        elab.lets.insert(l.name.name.clone(), l.clone());
    }

    // §26.3: names a wildcard import brings in that are ALSO declared locally
    // — the local declaration shadows the imported one (no duplicate error).
    if let Some(defs) = all_defs {
        elab.wildcard_shadowed = compute_wildcard_shadowed(module.items(), module.params(), defs)
            .into_iter()
            .collect();
        elab.foreign_package_names = compute_foreign_package_names(module.items(), defs)
            .into_iter()
            .collect();
    }
    // §26.3: an explicit import conflicts with a header declaration;
    // unlike a wildcard import, it cannot be displaced by that declaration.
    let header_names: HashSet<&str> = module
        .params()
        .iter()
        .flat_map(|pd| match &pd.kind {
            ParameterKind::Data { assignments, .. } => assignments
                .iter()
                .map(|a| a.name.name.as_str())
                .collect::<Vec<_>>(),
            ParameterKind::Type { assignments } => {
                assignments.iter().map(|a| a.name.name.as_str()).collect()
            }
        })
        .collect();
    for item in module.items() {
        if let ModuleItem::ImportDeclaration(imp) = item {
            for ii in &imp.items {
                if let Some(name) = &ii.item
                    && header_names.contains(name.name.as_str())
                {
                    return Err(format!(
                        "'{}' is already declared as a module parameter (IEEE 1800-2023 §26.3)",
                        name.name
                    ));
                }
            }
        }
    }

    // §13.4.3: register module-body function declarations before the
    // parameter pass so a header `parameter LOG_X = log2(X)` const-evaluates.
    for it in module.items() {
        if let ModuleItem::FunctionDeclaration(fd) = it
            && fd.name.scopes.is_empty()
        {
            elab.functions
                .insert_if_absent_with(fd.name.name.name.clone(), || fd.clone());
        }
    }
    crate::oom_trace::checkpoint("elaborate.functions.registered", &[("functions", elab.functions.len())]);
    set_funcs_tls(&elab.functions);
    crate::oom_trace::checkpoint("elaborate.functions.published", &[("functions", elab.functions.len())]);
    // §23.2.2 / A.1.2: module-HEADER imports (`module m import P::*;
    // #(parameter X = FOO) (...)`) precede the parameter list in the grammar
    // and are usable in it. The items walk processes imports in source order
    // — long after this header-parameter pass had evaluated defaults, so
    // `parameter X = FOO` read 0. Process every module import first; later
    // re-processing is idempotent (inserts).
    for item in module.items() {
        if let ModuleItem::ImportDeclaration(imp) = item {
            if let Some(defs) = all_defs {
                process_import(imp, &mut elab, defs, false)?;
            }
        }
    }
    record_param_decl_types(
        &mut elab,
        module
            .params()
            .iter()
            .chain(item_param_decls(module.items())),
        str::to_string,
        |dt| Rc::new(dt.clone()),
    );
    if let Some(defs) = all_defs {
        for def in defs.values() {
            if let Definition::Package(p) = def {
                let pds = p.items.iter().filter_map(|i| match i {
                    PackageItem::Parameter(pd) => Some(pd),
                    _ => None,
                });
                record_param_decl_types(
                    &mut elab,
                    pds,
                    |n| format!("{}::{n}", p.name.name),
                    |dt| Rc::new(dt.clone()),
                );
            }
        }
    }
    // Process parameters
    for param in module.params_and_body_types() {
        if let ParameterKind::Data {
            data_type,
            assignments,
        } = &param.kind
        {
            for assign in assignments {
                elab.declared_parameters.insert(assign.name.name.clone());
                // IEEE 1800-2023: keyed assignment-pattern parameter
                // (associative array literal). Materialize the entries
                // as `<param>["key"]` signals before falling into the
                // scalar parameter path.
                if let Some(init) = &assign.init {
                    if let ExprKind::AssignmentPattern(items) =
                        &peel_unpacked_typed_pattern(init).kind
                    {
                        // A struct/union-typed parameter is NOT an associative
                        // array even if its `'{ident: v}` items parse as Keyed —
                        // its keys are field names, handled by the struct path.
                        let is_struct_dt = flatten_struct_fields(
                            data_type,
                            &elab.parameters,
                            &elab.typedefs,
                            &elab.typedef_types,
                        )
                        .is_some_and(|f| !f.is_empty());
                        let all_keyed = !is_struct_dt
                            && !items.is_empty()
                            && items
                                .iter()
                                .all(|it| matches!(it, AssignmentPatternItem::Keyed(_, _)))
                            && pack_packed_vector_pattern(
                                data_type,
                                init,
                                &elab.parameters,
                                &elab.typedef_types,
                            )
                            .is_none();
                        if all_keyed {
                            let elem_w = resolve_type_width(
                                data_type,
                                Some(&elab.parameters),
                                Some(&elab.typedefs),
                            );
                            elab.associative_arrays
                                .insert(assign.name.name.clone(), true);
                            for it in items {
                                if let AssignmentPatternItem::Keyed(k, v) = it {
                                    let key_str = match &k.kind {
                                        ExprKind::StringLiteral(s) => {
                                            crate::value::encode_name_key(s).into_owned()
                                        }
                                        _ => {
                                            eval_const_expr_val(k, &elab.parameters).to_dec_string()
                                        }
                                    };
                                    let val_v = eval_init_for_width(v, &elab.parameters, elem_w);
                                    let signal_name = format!("{}[{}]", assign.name.name, key_str);
                                    signals_insert_traced(
                                        &mut elab.signals,
                                        line!(),
                                        signal_name.clone(),
                                        Signal {
                                            is_const: true,
                                            name: signal_name.into(),
                                            width: elem_w,
                                            is_signed: is_type_signed(data_type),
                                            is_real: false,
                                            direction: None,
                                            value: val_v,
                                            type_name: None,
                                        },
                                    );
                                }
                            }
                            continue;
                        }
                    }
                }
                // §6.20.2 unpacked-array parameter: `u32_t A[N] = {a, b}`.
                if !assign.dimensions.is_empty() {
                    let ov = param_overrides.get(&assign.name.name).cloned();
                    if register_array_param(
                        &mut elab,
                        "",
                        &assign.name.name,
                        &assign.dimensions,
                        assign.init.as_ref(),
                        ov.as_ref(),
                        data_type,
                        None,
                    ) {
                        continue;
                    }
                }
                let base_width =
                    resolve_type_width(data_type, Some(&elab.parameters), Some(&elab.typedefs));
                let base_signed = is_type_signed_resolved(data_type, &elab.typedef_types);
                let base_is_real = is_type_real_resolved(data_type, &elab.typedef_types);

                // IEEE 1800-2017 §6.20: a struct/union-typed parameter whose
                // value is an assignment pattern (`parameter cfg_t C = '{f:v}`)
                // must be packed by field offset at elaboration, and its field
                // layout registered so later `C.f` selects resolve.
                let struct_fields = flatten_struct_fields(
                    data_type,
                    &elab.parameters,
                    &elab.typedefs,
                    &elab.typedef_types,
                );
                let ov = param_overrides.get(&assign.name.name).cloned();
                let res = resolve_param_decl_value(
                    &mut elab,
                    data_type,
                    assign.init.as_ref(),
                    None,
                    ov.as_ref(),
                    base_width,
                    base_signed,
                    base_is_real,
                    ParamDeclPolicy {
                        unresolved_call: UnresolvedCallPolicy::ContinueOriginal,
                        promote_implicit_real: true,
                        narrow_implicit_string_lit: true,
                        force_signed_on_override: false,
                        eval_packed_aggregate: true,
                        require_known_idents: false,
                        signed_from_pkg_helper: false,
                    },
                );
                let mut val = res.val;

                // §6.20.2 + §5.7.1: an IMPLICIT-type parameter initialized with
                // an unbased-unsized literal keeps its fill-ness, so
                // `parameter P = '1; wire [3:0] w = P;` yields 4'b1111 and
                // `w !== P` compares equal at the consumer's width.
                if matches!(data_type, DataType::Implicit { dimensions, .. } if dimensions.is_empty())
                    && param_overrides.get(&assign.name.name).is_none()
                {
                    if let Some(init) = &assign.init {
                        if let ExprKind::Number(NumberLiteral::UnbasedUnsized(c)) = &init.kind {
                            // §6.20.2 self-determined: 1-bit, unsigned, plain.
                            val = Value::fill_of(*c);
                            val.is_fill = false;
                        }
                    }
                }

                if let Some(fields) = struct_fields {
                    tls_register_struct_layout(&assign.name.name, &fields);
                    register_struct_member_elem_widths(
                        &assign.name.name,
                        data_type,
                        &elab.parameters,
                        &elab.typedef_types,
                    );
                    // §6.20.2 / §7.2.1: `P.member` of a packed-struct
                    // parameter is itself a constant. Register each member
                    // under its dotted name so a declared range such as
                    // `logic [Cfg.VLEN-1:0]` on a function's return type or
                    // formal (sized by name through the parameter table, not
                    // by the struct-aware elaborator) resolves, and so a
                    // function reading `Cfg.VLEN` is still a constant
                    // function.
                    register_struct_param_members(
                        |k, v| {
                            elab.set_param(line!(), k, v);
                        },
                        &assign.name.name,
                        &val,
                        &fields,
                    );
                    elab.packed_struct_fields
                        .entry(assign.name.name.clone())
                        .or_insert(fields);
                }
                elab.set_param(line!(), assign.name.name.clone(), val);
            }
        } else if let ParameterKind::Type { assignments } = &param.kind {
            // §6.20.3 type parameter (`parameter type T1 = integer`): register
            // the (default) type as a typedef so `T1 x;` and `$bits(T1)` resolve.
            // The type may reference earlier value params (`logic [A-1:0]`), which
            // are already in elab.parameters by this point (params elaborate in
            // source order). Instance type-overrides aren't threaded here yet.
            for a in assignments {
                if let Some(dt) = &a.init {
                    let w = resolve_type_width(dt, Some(&elab.parameters), Some(&elab.typedefs));
                    typedefs_insert_traced(
                        &mut elab.typedefs,
                        "insert:type_param_hdr",
                        a.name.name.clone(),
                        w,
                    );
                    elab.typedef_types.insert(a.name.name.clone(), dt.clone());
                    // §6.24.1: a cast to the type parameter in a constant
                    // expression (`T'(45)`) reads its declared type from the
                    // shape table, like a typedef.
                    tls_register_typedef_shape(&a.name.name, dt, &[]);
                    register_anonymous_enum_members(dt, &mut elab);
                    sync_typedefs_tls(&elab.typedefs);
                }
            }
        }
    }

    // Process ports
    match module.ports() {
        PortList::Ansi(ports) => {
            for port in ports {
                // §23.2.2: ANSI port names are unique, and the declaration is
                // COMPLETE — a later variable of the same name is a clash too
                // (the reference simulator rejects both). Registering the
                // port as an incompatible typed decl routes both cases
                // through the standard duplicate machinery.
                if elab.typed_decls.contains_key(&port.name.name) {
                    return Err(duplicate_decl_error(
                        &elab,
                        &port.name.name,
                        port.name.span,
                        "port",
                    ));
                }
                elab.note_decl_site(&port.name.name, port.name.span, "ANSI port", true);
                elab.typed_decls.insert(port.name.name.clone(), true);
                let modport_view = match port.data_type.as_ref() {
                    Some(DataType::Interface {
                        name,
                        modport: Some(mp),
                        ..
                    }) => resolve_interface_modport_view(&name.name, &mp.name, all_defs),
                    _ => None,
                };
                let width = port
                    .data_type
                    .as_ref()
                    .map(|dt| resolve_type_width(dt, Some(&elab.parameters), Some(&elab.typedefs)))
                    .unwrap_or(1);
                let is_signed = port.data_type.as_ref().map(|dt| is_type_signed_resolved(dt, &elab.typedef_types)).unwrap_or(false);
                let is_real = port.data_type.as_ref().map(is_type_real).unwrap_or(false);
                // §6.18/§7.4: a port declared with an ARRAY typedef
                // (`typedef logic [A-1:0] T[B]; input T x;`) inherits the
                // typedef's UNPACKED dims — mirroring the variable path's
                // `effective_dims`. Without this the port registered as a
                // scalar of the ELEMENT width, so `$size(x,1)` was the packed
                // width and element indexing was wrong.
                let effective_port_dims: Vec<UnpackedDimension> = if port.dimensions.is_empty() {
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
                    &elab.parameters,
                    &elab.typedef_types,
                );
                let port_shape = fixed_unpacked_shape(&effective_port_dims, &elab.parameters)
                    .unwrap_or_default();
                if let Some(dims) = declared_unpacked_dims(&effective_port_dims, &elab.parameters) {
                    elab.unpacked_decl_dims
                        .insert(port.name.name.clone(), dims.clone());
                    if dims.first().is_some_and(|(l, r)| l > r) {
                        elab.descending_arrays.insert(port.name.name.clone());
                    }
                }
                // §7.4.1: a port that is a packed array of a named type, or a
                // packed structure, keeps its declared type like a variable.
                if let Some(dt) = &port.data_type
                    && names_packed_array_or_struct(dt, &elab.typedef_types)
                    && !elab.var_decl_types.contains_key(&port.name.name)
                {
                    elab.var_decl_types
                        .insert(port.name.name.clone(), dt.clone());
                }
                // §23.2.2.4: a port default must be a CONSTANT expression —
                // a reference to a runtime variable is rejected (ivtest
                // sv_default_port_value3; the reference errors identically).
                if let Some(def) = &port.default {
                    if !is_const_expr(def, &elab.parameters) {
                        return Err(format!(
                            "Value assigned to default of port '{}' must be a constant expression (§23.2.2.4)",
                            port.name.name
                        ));
                    }
                }
                // §23.2.2.4: `output logic clk = 0` — the default on an
                // OUTPUT (variable) port is the variable's initializer.
                // (Input-port defaults are unconnected-port fallbacks,
                // handled at instantiation time.)
                let init_val = match (&port.direction, &port.default) {
                    (Some(PortDirection::Output), Some(def)) => {
                        let v = eval_const_expr(def, &elab.parameters);
                        Some(if is_real {
                            Value::from_f64(v as f64)
                        } else {
                            Value::from_u64(v, width).resize(width)
                        })
                    }
                    _ => None,
                };
                let sig = Signal {
                    is_const: false,
                    name: port.name.name.clone().into(),
                    width,
                    is_signed,
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
                    }),
                    type_name: port.data_type.as_ref().and_then(get_type_name),
                };
                elab.port_order.push(port.name.name.clone());
                if let Some(net_type) = ansi_port_net_type(port) {
                    register_net_type(
                        &mut elab,
                        &port.name.name,
                        net_type,
                        port.data_type.as_ref(),
                    );
                }
                if port_shape.is_empty() {
                    signals_insert_traced(&mut elab.signals, line!(), port.name.name.clone(), sig);
                    // §7.4.1, §7.2: a packed multi-D or packed-struct port keeps its
                    // shape like a variable. Unrecorded, `o[1]` of an `output logic
                    // [5:0][7:0] o` on the top module was a one-bit select.
                    if let Some(dt) = &port.data_type {
                        register_port_packed_shape(&mut elab, &port.name.name, dt);
                    }
                    // §7.2/§23.2.2: a port whose type is an UNPACKED STRUCT is
                    // stored member-wise, exactly like a variable of the same
                    // type — the flat container above only carries the width.
                    // Without the leaves the submodule's own `assign o.a = …`
                    // had nowhere to land and a member read through the port
                    // fell back to a raw slice of the container, losing
                    // `is_real` (a `real` member read back as its f64 BIT
                    // PATTERN: 9.25 as 4621396905123905536).
                    if let Some(dt) = &port.data_type {
                        register_unpacked_aggregate(&mut elab, &port.name.name, dt);
                        elab.var_decl_types
                            .insert(port.name.name.clone(), dt.clone());
                    }
                } else {
                    register_fixed_unpacked_array(
                        &mut elab,
                        &port.name.name,
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
                            mark_array_z_init_if_4state(&mut elab, &port.name.name, dt);
                        }
                        elab.var_decl_types
                            .insert(port.name.name.clone(), dt.clone());
                    }
                }
                if let Some(view) = modport_view {
                    elab.modport_views.insert(port.name.name.clone(), view);
                }
            }
        }
        PortList::NonAnsi(names) => {
            for name in names {
                elab.port_order.push(name.name.clone());
                // Direction/type will be declared in module body
            }
        }
        PortList::Empty => {}
    }

    crate::oom_trace::checkpoint("elaborate.header.ready", &[("signals", elab.signals.len())]);

    // Process items
    if let Definition::Package(p) = module {
        // §13.4.3: package functions first, so a package parameter whose
        // initializer calls a sizing helper const-evaluates. §8.24: scoped
        // definitions are class methods, not free package functions; their
        // signatures must not enter the bare-name function table.
        for item in &p.items {
            if let crate::ast::decl::PackageItem::Function(fd) = item
                && fd.name.scopes.is_empty()
            {
                elab.functions
                    .insert_if_absent_with(fd.name.name.name.clone(), || fd.clone());
            }
        }
        set_funcs_tls(&elab.functions);
        let __pkg_imp_overlay = overlay_pkg_imports(p, &mut elab);
        for item in &p.items {
            match item {
                crate::ast::decl::PackageItem::Typedef(td) => {
                    process_typedef(td, &mut elab);
                }
                crate::ast::decl::PackageItem::Parameter(pd) => {
                    if let ParameterKind::Data {
                        data_type,
                        assignments,
                    } = &pd.kind
                    {
                        let mut width = resolve_type_width(
                            data_type,
                            Some(&elab.parameters),
                            Some(&elab.typedefs),
                        );
                        let is_implicit_no_dims = matches!(
                            data_type,
                            DataType::Implicit { dimensions, .. } if dimensions.is_empty()
                        );
                        for assign in assignments {
                            if register_visible_array_param(
                                &mut elab,
                                &p.name.name,
                                assign,
                                data_type,
                            ) {
                                continue;
                            }
                            register_packed_array_elem_w(
                                &assign.name.name,
                                data_type,
                                &elab.typedefs,
                                &elab.parameters,
                            );
                            register_packed_param_index(
                                &mut elab,
                                &assign.name.name,
                                data_type,
                                None,
                            );
                            if matches!(
                                data_type,
                                DataType::Simple {
                                    kind: SimpleType::String,
                                    ..
                                }
                            ) {
                                tls_register_string_param(&assign.name.name);
                            }
                            if let Some(init) = &assign.init {
                                // For implicit-typed parameters, infer width
                                // from a sized literal initializer so
                                // `parameter X = 7'h13;` stores Value{width=7}
                                // instead of being padded to 32. Otherwise
                                // refs inside concats place the param at the
                                // wrong bit position, shifting other operands
                                // off-end. (Surfaced by cv32e40p's
                                // compressed_decoder: `instr_o = { ...,
                                // pkg::OPCODE_OPIMM };` was emitting NOP
                                // because OPCODE_OPIMM took 32 bits.)
                                let eff_width = if is_implicit_no_dims {
                                    untyped_param_width(init, &elab.parameters).unwrap_or(32)
                                } else {
                                    width
                                };
                                width = eff_width;
                                // §13.4.3 const-function calls in package
                                // parameter initializers.
                                let subbed_init5;
                                let init_eval: &Expression = if expr_has_call(init) {
                                    match substitute_const_fn_calls(
                                        init,Some(&elab.parameters),
                                        &elab,
                                        0,
                                    )
                                    .filter(|e| !expr_has_call(e))
                                    {
                                        Some(e) => {
                                            subbed_init5 = e;
                                            &subbed_init5
                                        }
                                        None => init,
                                    }
                                } else {
                                    init
                                };
                                let mut v = if is_string_data_type(data_type) {
                                    string_param_value(init_eval, &elab.parameters)
                                } else {
                                    eval_param_init(
                                        data_type,
                                        init_eval,
                                        &elab.parameters,
                                        &elab.typedef_types,
                                        eff_width,
                                    )
                                };
                                if !v.is_real {
                                    v.is_signed = pkg_param_is_signed(
                                        data_type,
                                        Some(init_eval),
                                        &elab.typedef_types,
                                        &elab.parameters,
                                    );
                                }
                                alias_pkg_param(&mut elab, &p.name.name, &assign.name.name, &v);
                                let scoped = format!("{}.{}", p.name.name, assign.name.name);
                                register_pkg_param_elem(&mut elab, "", &scoped, data_type);
                                elab.set_param(line!(), assign.name.name.clone(), v);
                                // §7.2.1: a STRUCT-typed package parameter needs
                                // its field layout registered, or member selects
                                // (`pkg::CDEF.a`) read x at runtime and 0 in
                                // const context (module-scope params already do
                                // this; packages didn't).
                                if let Some(fields) = flatten_struct_fields(
                                    data_type,
                                    &elab.parameters,
                                    &elab.typedefs,
                                    &elab.typedef_types,
                                ) {
                                    if !fields.is_empty() {
                                        tls_register_struct_layout(&assign.name.name, &fields);
                                        elab.packed_struct_fields
                                            .insert(assign.name.name.clone(), fields);
                                    }
                                }
                            }
                        }
                    }
                }
                crate::ast::decl::PackageItem::Class(c) => {
                    validate_class_constraints(
                        c,
                        all_defs,
                        Some(&elab.enum_members),
                        Some(&elab),
                        None,
                    )?;
                    register_class_enum_members(c, &mut elab);
                    register_class_covergroups(c, &mut elab);
                    register_class_scoped_typedef_aliases(c, Some(&p.name.name), &mut elab);
                    elab.classes.insert(
                        c.name.name.clone(),
                        std::sync::Arc::new(elaborate_class_with_params(c, Some(&elab.parameters))),
                    );
                }
                crate::ast::decl::PackageItem::Let(l) => {
                    elab.lets.insert(l.name.name.clone(), l.clone());
                }
                crate::ast::decl::PackageItem::DPIImport(di) => {
                    register_dpi_import(di, &mut elab, Some(p.name.name.as_str()))?;
                }
                crate::ast::decl::PackageItem::DPIExport(e) => {
                    register_dpi_export(e, &mut elab);
                }
                _ => {}
            }
        }
        restore_overlay(&mut elab, __pkg_imp_overlay);
    }

    // Pre-pass: collect user-defined nettype names so variables declared with
    // those types can be classified as nets (§6.6.7 — nettype resolution permits
    // multiple continuous drivers). Also register each nettype's width as a
    // typedef so TypeReference lookups resolve correctly.
    let mut user_nettypes: HashSet<String> = HashSet::default();
    // §6.6.7 nettype registry: name -> (data type, resolution function).
    // The DATA TYPE registration into `typedef_types` is what lets every
    // existing type-resolving helper (real/signed/two-state detection, struct
    // field layout, member access) see THROUGH a nettype name to the type it
    // wraps — without it a `nettype real rn;` net lost `is_real` and read back
    // as the raw f64 bit pattern.
    let mut nettype_info: HashMap<String, (DataType, Option<String>)> = HashMap::default();
    let register_nettype = |elab: &mut ElaboratedModule,
                            info: &mut HashMap<String, (DataType, Option<String>)>,
                            seen: &mut HashSet<String>,
                            nd: &crate::ast::decl::NettypeDeclaration,
                            key: String,
                            package: Option<&str>| {
        seen.insert(key.clone());
        let w = resolve_type_width(&nd.data_type, Some(&elab.parameters), Some(&elab.typedefs));
        typedefs_insert_traced(&mut elab.typedefs, "insert:nettype", key.clone(), w);
        elab.typedef_types.insert(key.clone(), nd.data_type.clone());
        info.insert(
            key,
            (
                nd.data_type.clone(),
                // §26.3: an import exposes the original declaration; its
                // resolver stays in the declaring package, even if the
                // importing module has a function with the same name.
                nd.resolver.as_ref().map(|r| match package {
                    Some(pkg) => {
                        let qualified = format!("{}::{}", pkg, r.name);
                        if elab.functions.contains_key(&qualified) {
                            qualified
                        } else {
                            // Keep imported resolvers on the existing lookup path.
                            r.name.clone()
                        }
                    }
                    None => r.name.clone(),
                }),
            ),
        );
    };

    // §6.6.7 + §26.2: a nettype may be declared in a PACKAGE — which is the
    // natural place for one, since a nettype crossing a port boundary has to be
    // named identically on both sides. Only `$unit`-scope declarations reached
    // here (`lib.rs` copies those into every module's item list), so a
    // package-declared nettype was never registered: its nets were not even
    // classified as nets, and a second driver failed with the generic
    // "Variable 'n' has multiple continuous drivers" rather than resolving.
    //
    // Registered under the bare name and the qualified `Pkg::name` (§26.3), so
    // both `import P::*; pnet n;` and `P::pnet n;` resolve. Packages are walked
    // in sorted order: `all_defs` is a hash map and a module-local declaration
    // below must be the last writer, so registration order is observable.
    if let Some(defs) = all_defs {
        let mut pkg_names: Vec<&String> = defs
            .iter()
            .filter(|(_, d)| matches!(d, Definition::Package(_)))
            .map(|(n, _)| n)
            .collect();
        pkg_names.sort();
        for pname in pkg_names {
            let Some(Definition::Package(pkg)) = defs.get(pname) else {
                continue;
            };
            for item in &pkg.items {
                if let crate::ast::decl::PackageItem::Nettype(nd) = item {
                    let bare = nd.name.name.clone();
                    // A package nettype whose name collides with another
                    // package's type already carries its package key.
                    if !bare.contains("::") {
                        register_nettype(
                            &mut elab,
                            &mut nettype_info,
                            &mut user_nettypes,
                            nd,
                            format!("{}::{}", pkg.name.name, bare),
                            Some(&pkg.name.name),
                        );
                    }
                    register_nettype(
                        &mut elab,
                        &mut nettype_info,
                        &mut user_nettypes,
                        nd,
                        bare,
                        Some(&pkg.name.name),
                    );
                }
            }
        }
    }

    // A module-local declaration shadows an imported one, so it registers last.
    for item in module.items() {
        if let ModuleItem::NettypeDeclaration(nd) = item {
            let key = nd.name.name.clone();
            register_nettype(
                &mut elab,
                &mut nettype_info,
                &mut user_nettypes,
                nd,
                key,
                None,
            );
        }
    }
    // §6.6.7 nettype ALIAS: `nettype T wT; nettype wT wT2;` — a nettype may be
    // declared from another nettype name, inheriting its data type AND its
    // resolution function. Resolve transitively (bounded, so a malformed cycle
    // diagnoses instead of hanging).
    for _ in 0..64 {
        let mut changed = false;
        let aliases: Vec<(String, String)> = nettype_info
            .iter()
            .filter_map(|(n, (dt, res))| match dt {
                DataType::TypeReference { name, .. }
                    if res.is_none() && nettype_info.contains_key(&name.name.name) =>
                {
                    Some((n.clone(), name.name.name.clone()))
                }
                _ => None,
            })
            .collect();
        for (alias, target) in aliases {
            if alias == target {
                continue;
            }
            if let Some((tdt, tres)) = nettype_info.get(&target).cloned() {
                if tres.is_some() || !matches!(tdt, DataType::TypeReference { .. }) {
                    nettype_info.insert(alias.clone(), (tdt.clone(), tres));
                    elab.typedef_types.insert(alias, tdt);
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    // §6.6.7: publish the nettype registry NOW, before the items are walked.
    // A declaration inside a GENERATE scope has to tell a nettype from a
    // plain typedef to store the net's members per member (the way the
    // module-scope path does), and the registry is the only place that
    // knows. Publishing it later left the generate-scope nettype net without
    // member storage: the resolution function's write landed nowhere and the
    // formal on the other side of the port read the default.
    for (nt, (_, resolver)) in &nettype_info {
        if let Some(r) = resolver {
            elab.nettype_resolvers.insert(nt.clone(), r.clone());
        } else {
            // Declared without a resolution function: recorded with an empty
            // name so the post-inline pass can still enforce the one-driver
            // limit across the flattened design.
            elab.nettype_resolvers.entry(nt.clone()).or_default();
        }
    }
    // §6.18, §26.3, §26.5: a module's own typedef, class or type parameter
    // hides a compilation-unit or package nettype of the same name, so a
    // declaration spelled with that name declares a variable. (A module-local
    // nettype and typedef of one name would be a redeclaration.)
    let mut hidden: HashSet<String> = HashSet::default();
    let type_params = |pd: &ParameterDeclaration, hidden: &mut HashSet<String>| {
        if let ParameterKind::Type { assignments } = &pd.kind {
            hidden.extend(assignments.iter().map(|a| a.name.name.clone()));
        }
    };
    for pd in module.params() {
        type_params(pd, &mut hidden);
    }
    for item in module.items() {
        match item {
            ModuleItem::TypedefDeclaration(td) if !td.forward => {
                hidden.insert(td.name.name.clone());
            }
            ModuleItem::ClassDeclaration(cd) => {
                hidden.insert(cd.name.name.clone());
            }
            ModuleItem::ParameterDeclaration(pd) | ModuleItem::LocalparamDeclaration(pd) => {
                type_params(pd, &mut hidden);
            }
            _ => {}
        }
    }
    hidden.retain(|n| nettype_info.contains_key(n));
    for n in &hidden {
        user_nettypes.remove(n);
    }
    elab.shadowed_nettypes = hidden;

    // §6.20 — resolve the module's own parameters to a FIXPOINT before walking
    // the items, so a declaration whose width depends on one of them is sized
    // correctly no matter what ORDER the parameters appear in.
    //
    // The walk below evaluates each parameter where it appears, so
    // `localparam A = $clog2(B) - 6;` ahead of `localparam B = 4096;` saw
    // nothing for B, fell back to 0, and produced -6. Read back unsigned that
    // is 4294967290, which becomes a `[4294967289:0]` packed range and
    // collapses the whole bus to ONE BIT — the design then simulates wrongly
    // with only a width warning to show for it. A reference simulator resolves
    // the declarations order-independently.
    //
    // Names seeded here are exempted from the duplicate-declaration check the
    // first time the walk reaches them (and only the first time, so a genuine
    // duplicate is still an error). Instantiation overrides are already bound
    // and are never overwritten.
    let mut preseeded_params: std::collections::HashSet<String> = std::collections::HashSet::new();
    // Consumed on first encounter so a GENUINE duplicate declaration still errors.
    let mut preseed_dup_exempt: std::collections::HashSet<String> =
        std::collections::HashSet::new();
    {
        let mut decls: Vec<(&str, &DataType, &Expression)> = Vec::new();
        for item in module.items() {
            let (ModuleItem::ParameterDeclaration(pd) | ModuleItem::LocalparamDeclaration(pd)) =
                item
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
                let name = assign.name.name.as_str();
                // Already bound => instantiation override; leave it alone.
                if elab.parameters.contains_key(name) {
                    continue;
                }
                if let Some(init) = &assign.init {
                    // Only pre-seed initializers built from plain module-local
                    // names. A package- or class-scoped reference
                    // (`pkg::SIZE`) is not bound until the walk reaches the
                    // import, so seeding it here would store a wrong value
                    // that any declaration sized from it would then pick up.
                    if expr_refs_are_all_local(init) {
                        decls.push((name, data_type, init));
                    }
                }
            }
        }
        for _ in 0..8 {
            let mut changed = false;
            for (name, data_type, init) in &decls {
                let base_width =
                    resolve_type_width(data_type, Some(&elab.parameters), Some(&elab.typedefs));
                let base_is_real = is_type_real_resolved(data_type, &elab.typedef_types);
                let res = resolve_param_decl_value(
                    &mut elab,
                    data_type,
                    Some(init),
                    None,
                    None,
                    base_width,
                    is_type_signed(data_type),
                    base_is_real,
                    ParamDeclPolicy {
                        unresolved_call: UnresolvedCallPolicy::ContinueOriginal,
                        promote_implicit_real: false,
                        narrow_implicit_string_lit: false,
                        force_signed_on_override: false,
                        eval_packed_aggregate: false,
                        require_known_idents: true,
                        signed_from_pkg_helper: false,
                    },
                );
                if res.skipped || res.val.is_real {
                    continue; // unresolved ident or real param keeps the walk's handling
                }
                let v = res.val;
                if elab.parameters.get(*name) != Some(&v) {
                    elab.set_param(line!(), (*name).to_string(), v);
                    preseeded_params.insert((*name).to_string());
                    preseed_dup_exempt.insert((*name).to_string());
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
    }

    // §6.18: a FORWARD typedef (`typedef T;`) may be completed LATER in the
    // module, with declarations using the name in between (`typedef T; T x;
    // typedef int T;`). The main walk below processes items in source order,
    // so `T x` sized against the Void placeholder (width 0). Pre-register
    // every REAL module typedef here — after the parameter pre-seed, so their
    // dims resolve — exactly as packages pre-register theirs; the main walk's
    // re-processing is idempotent.
    for item in module.items() {
        if let ModuleItem::TypedefDeclaration(td) = item {
            if !td.forward
                && struct_typedef_self_reference(&td.name.name, &td.data_type, &elab.typedef_types)
                    .is_none()
            {
                check_enum_member_duplicates(td, &elab)?;
                process_local_typedef(td, &mut elab);
            }
        }
    }

    // §6.21: subroutines default to the enclosing scope's lifetime.
    use crate::ast::types::Lifetime;
    let sub_default_static =
        !matches!(module, Definition::Module(m) if m.lifetime == Some(Lifetime::Automatic));
    if let Some(defs) = all_defs {
        for def in defs.values() {
            let Definition::Package(pkg) = def else {
                continue;
            };
            if pkg.lifetime == Some(Lifetime::Automatic) {
                continue;
            }
            for it in &pkg.items {
                match it {
                    // Out-of-class method bodies (`function C::m`) are class
                    // methods — automatic lifetime (§8.6) — not package subs.
                    crate::ast::decl::PackageItem::Function(fd)
                        if fd.lifetime != Some(Lifetime::Automatic)
                            && fd.name.scopes.is_empty() =>
                    {
                        check_implicit_static_inits(
                            &fd.items,
                            &elab,
                            StaticInitScope {
                                kind: "function",
                                name: &fd.name.name.name,
                                owner_kind: "package",
                                owner: &pkg.name.name,
                            },
                        )?
                    }
                    crate::ast::decl::PackageItem::Task(td)
                        if td.lifetime != Some(Lifetime::Automatic)
                            && td.name.scopes.is_empty() =>
                    {
                        check_implicit_static_inits(
                            &td.items,
                            &elab,
                            StaticInitScope {
                                kind: "task",
                                name: &td.name.name.name,
                                owner_kind: "package",
                                owner: &pkg.name.name,
                            },
                        )?
                    }
                    _ => {}
                }
            }
        }
    }

    // Classes declared in THIS module body must be visible to each other's
    // `extends` when their constraints are validated.
    let local_defs = defs_with_local_classes(module.items(), all_defs);
    let cls_defs = local_defs.as_ref().or(all_defs);
    for (item_index, item) in module.items().iter().enumerate() {
        if item_index + 4096 >= module.items().len() && crate::oom_trace::enabled() {
            crate::oom_trace::checkpoint("elaborate.last_item", &[
                ("item_index", item_index), ("signals", elab.signals.len()),
                ("var_decl_types", elab.var_decl_types.len()),
                ("initial", matches!(item, ModuleItem::InitialConstruct(_)) as usize),
                ("always", matches!(item, ModuleItem::AlwaysConstruct(_)) as usize),
                ("signal_inline_bytes", std::mem::size_of::<Signal>()),
                ("type_inline_bytes", std::mem::size_of::<DataType>()),
            ]);
        }
        if item_index % 4096 == 0 && crate::oom_trace::enabled() {
            crate::oom_trace::checkpoint("elaborate.items", &[
                ("item_index", item_index), ("module_items", module.items().len()),
                ("signals", elab.signals.len()), ("var_decl_types", elab.var_decl_types.len()),
                ("functions", elab.functions.len()),
            ]);
        }
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
                let ranged = matches!(&pd.data_type,
                    DataType::Implicit { dimensions, .. } | DataType::IntegerVector { dimensions, .. }
                        if !dimensions.is_empty());
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
                    if ranged {
                        elab.ranged_port_widths
                            .insert(decl.name.name.clone(), width);
                    }
                    // §7.4.1: a non-ANSI PORT of a packed multi-D (or packed
                    // struct) type needs the same element/field registrations
                    // a variable declaration gets — the DataDeclaration arm
                    // has always done this, the port arm never did, so
                    // `output logic [3:0][9:0] o; assign o[1] = v;` degraded
                    // to a bit-window write (only the low bits landed) and
                    // struct-port member writes missed the layout.
                    register_port_packed_shape(&mut elab, &decl.name.name, &pd.data_type);
                    // §6.18/§7.4: a PORT declared with an ARRAY typedef
                    // (`typedef logic [A-1:0] T[B]; input T x;`) inherits the
                    // typedef's UNPACKED dimensions — the Data path has always
                    // done this via `effective_dims`; the port path registered
                    // a scalar of the ELEMENT width, so `$size(x,1)` reported
                    // the packed width and element indexing was wrong.
                    {
                        let tdims: Vec<UnpackedDimension> = match &pd.data_type {
                            DataType::TypeReference { name, .. } if decl.dimensions.is_empty() => {
                                lookup_scoped_type(name, &elab.typedef_unpacked_dims)
                                    .cloned()
                                    .unwrap_or_default()
                            }
                            _ => Vec::new(),
                        };
                        if !tdims.is_empty() {
                            let tdims = normalize_unpacked_dims(
                                &tdims,
                                &elab.parameters,
                                &elab.typedef_types,
                            );
                            if let Some(shape) = fixed_unpacked_shape(&tdims, &elab.parameters)
                                .filter(|sh| !sh.is_empty())
                            {
                                register_fixed_unpacked_array(
                                    &mut elab,
                                    &decl.name.name,
                                    &shape,
                                    width,
                                    false,
                                );
                                elab.var_decl_types
                                    .entry(decl.name.name.clone())
                                    .or_insert_with(|| pd.data_type.clone());
                            }
                        }
                    }
                    // §7.4.1, §23.2.2.1: a non-ANSI port of a named type keeps
                    // its declaration like an ANSI port or a variable of the
                    // type: an element of `input lane_t [0:1] p;` has the
                    // signing of `lane_t`, and so does a packed-array member
                    // of a structure port.
                    if names_packed_array_or_struct(&pd.data_type, &elab.typedef_types) {
                        elab.var_decl_types
                            .entry(decl.name.name.clone())
                            .or_insert_with(|| pd.data_type.clone());
                    }
                    elab.note_explicit_type(&decl.name.name, &pd.data_type, decl.name.span)?;
                    // §23.2.2.1 non-ANSI ports: the data type and the direction
                    // may be declared in separate statements (`byte x; output x;`).
                    // If `x` was already registered (by a prior data/net decl)
                    // and carries no direction yet, this is the direction half of
                    // the same port — merge instead of erroring. A port-only
                    // direction line carries an Implicit type, so keep the
                    // existing width/type; if this line DOES carry an explicit
                    // type, adopt it.
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
                                    &mut elab,
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
                        is_real,
                        direction: Some(pd.direction),
                        value: default_port_value(
                            Some(pd.direction),
                            Some(&pd.data_type),
                            width,
                            is_real,
                            port_decl_net_type(pd),
                        ),
                        type_name: get_type_name(&pd.data_type),
                    };
                    if !elab.port_order.contains(&decl.name.name) {
                        elab.port_order.push(decl.name.name.clone());
                    }
                    signals_insert_traced(&mut elab.signals, line!(), decl.name.name.clone(), sig);
                    if let Some(net_type) = port_decl_net_type(pd) {
                        register_net_type(
                            &mut elab,
                            &decl.name.name,
                            net_type,
                            Some(&pd.data_type),
                        );
                    }
                    if let Some(view) = &port_modport_view {
                        elab.modport_views
                            .insert(decl.name.name.clone(), view.clone());
                    }
                }
            }
            ModuleItem::NetDeclaration(nd) => {
                check_net_data_type(nd, &elab)?;
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
                    elab.note_explicit_type(&decl.name.name, &nd.data_type, decl.name.span)?;
                    // A `wire X;` (or other NetDeclaration) following an
                    // `input X;` / `output X;` port declaration is the
                    // legal SystemVerilog idiom that explicitly attaches a
                    // net-type to an already-declared port. Keep the
                    // existing port entry (direction, width, type_name)
                    // and just record the leaf in `nets`. Only treat it
                    // as an error if the existing entry is not a port
                    // (i.e. a true duplicate user declaration).
                    if elab
                        .signals
                        .get(&decl.name.name)
                        .is_some_and(|s| s.direction.is_some())
                    {
                        elab.complete_port(&decl.name.name, decl.name.span, &nd.data_type, width)?;
                    }
                    if let Some(existing) = elab.signals.get_mut(&decl.name.name) {
                        if existing.direction.is_some() {
                            existing.value =
                                default_net_value(nd.net_type, existing.width, existing.is_real);
                            // §6.8: port and net signing MERGE — signed if
                            // EITHER declaration says signed (an explicit
                            // `unsigned` on one side does not downgrade the
                            // other's `signed`; ivtest br_gh540).
                            if is_signed {
                                existing.is_signed = true;
                            }
                            register_net_type(
                                &mut elab,
                                &decl.name.name,
                                nd.net_type,
                                Some(&nd.data_type),
                            );
                            // §10.3.1: the net declaration's initializer is a
                            // continuous assignment — it was dropped when the
                            // name was already declared as a port, leaving
                            // `output p; wire p = 1'b1;` undriven (z).
                            if let Some(init_expr) = &decl.init {
                                let decl_dly = net_decl_assign_delay(nd, &elab.parameters);
                                let decl_rhs = net_declaration_driver(
                                    nd,
                                    &decl.name.name,
                                    init_expr,
                                    &mut elab,
                                );
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
                            continue;
                        }
                        return Err(duplicate_decl_error(
                            &elab,
                            &decl.name.name,
                            decl.name.span,
                            "net",
                        ));
                    }
                    // §7.4.2: an unpacked NET array (`wire [3:0] outs [0:1];`) is
                    // an ARRAY OF NETS, exactly like the variable form
                    // (`logic [3:0] outs [0:1];`) — not one `width * n` wide net.
                    // Flattening it made `outs[0]` a plain bit-select of that wide
                    // vector (so `assign outs[0] = 4'd5;` drove a single bit) and
                    // dumped the whole array as one wide VCD vector instead of
                    // element-wise `outs[0]`/`outs[1]` vars. Register the same
                    // `arrays` metadata the variable path does; `Simulator::new`
                    // synthesizes the per-element signals from it.
                    let effective_dims = normalize_unpacked_dims(
                        &decl.dimensions,
                        &elab.parameters,
                        &elab.typedef_types,
                    );
                    let net_array_range = extract_array_range(&effective_dims, &elab.parameters);
                    let w = if net_array_range.is_some() {
                        width
                    } else {
                        width_with_unpacked_dims(&effective_dims, width)
                    };
                    // supply0 → constant 0, supply1 → constant 1.
                    // §6.6.1: an undriven wire reads high-impedance — nets
                    // default to Z, not X (bits with drivers are overwritten
                    // at the first settle; bits nothing drives stay z).
                    register_net_type(&mut elab, &decl.name.name, nd.net_type, Some(&nd.data_type));
                    let init_value = default_net_value(nd.net_type, w, is_real);
                    let sig = Signal {
                        is_const: false,
                        name: decl.name.name.clone().into(),
                        width: w,
                        is_signed,
                        is_real,
                        direction: None,
                        value: init_value,
                        type_name: get_type_name(&nd.data_type),
                    };
                    signals_insert_traced(&mut elab.signals, line!(), decl.name.name.clone(), sig);
                    // The declared type, same as the variable arm: the
                    // simulator's `register_struct_member_packed_dims` walks
                    // `packed_struct_fields` and needs the declaring type to
                    // derive per-MEMBER element strides (`x.lanes` -> 64).
                    // The net arm only recorded it on the unpacked-array
                    // branch, so `x[0][0].lanes[0]` on a typedef'd wire read
                    // one bit of the wrong field while the identical variable
                    // declaration worked.
                    elab.var_decl_types
                        .entry(decl.name.name.clone())
                        .or_insert_with(|| nd.data_type.clone());
                    // §7.2.1: a packed-struct-typed NET needs its field layout
                    // registered in `packed_struct_fields` so member reads/writes
                    // (`word2.high`, `assign word2.high = ...`) slice into the
                    // parent net — mirroring the variable (line ~2793) and port
                    // (line ~9002) paths, which the net arm previously omitted
                    // (member access read x).
                    if net_array_range.is_none() && effective_dims.is_empty() {
                        let chain =
                            resolve_typedef_chain(&nd.data_type, &elab.typedef_types).clone();
                        if let DataType::Struct(su) = &chain {
                            if su.packed {
                                if let Some(fields) = flatten_struct_fields(
                                    &nd.data_type,
                                    &elab.parameters,
                                    &elab.typedefs,
                                    &elab.typedef_types,
                                ) {
                                    if !fields.is_empty() {
                                        let struct_w =
                                            fields.iter().map(|(_, o, w)| o + w).max().unwrap_or(0);
                                        // §7.4.2: a packed ARRAY of packed struct
                                        // net (`wire dword foo;`) is one vector of
                                        // N structs; register the element width so
                                        // `foo[i].field` addresses `i*elem_w+off`.
                                        if struct_w > 0 && w > struct_w && w % struct_w == 0 {
                                            elab.packed_signal_elem_widths
                                                .insert(decl.name.name.clone(), struct_w);
                                        }
                                        tls_register_struct_layout(&decl.name.name, &fields);
                                        elab.packed_struct_fields
                                            .insert(decl.name.name.clone(), fields);
                                    }
                                }
                            }
                        }
                    }
                    // Packed multi-D NET: `wire logic [3:0][7:0] foo;` —
                    // record the per-element width so `foo[i]` resolves to
                    // an 8-bit slice instead of a 1-bit select (LRM §7.4.1).
                    // Registered even when the declarator ALSO has unpacked
                    // dimensions (`wire [1:0][7:0] w [0:1];`): the packed dims
                    // of the ELEMENT type still govern `w[i][j]`. The variable
                    // (DataDeclaration) arm has always registered
                    // unconditionally; the net arm gated it behind
                    // "no unpacked dims", so element selects into an unpacked
                    // array of packed vectors lost their width.
                    // Typedef'd element type (`wire burst_t [0:0][1:0] x;`,
                    // scoped or bare): the direct calls see only a
                    // TypeReference and return None, so element selects lost
                    // their width — `$bits(x[0][0])` read 1. Chase the typedef
                    // exactly like the variable (DataDeclaration) arm does.
                    let nd_resolved: DataType = match &nd.data_type {
                        DataType::TypeReference { name, .. } => {
                            lookup_scoped_type(name, &elab.typedef_types)
                                .cloned()
                                .unwrap_or_else(|| nd.data_type.clone())
                        }
                        _ => nd.data_type.clone(),
                    };
                    // Packed dims written on the typedef itself
                    // (`wire burst_t [0:0][1:0] x;` over a packed struct):
                    // the SAME registration the variable arm performs — the
                    // full-dims vector carries the element type's own width as
                    // its innermost entry, and the element width is the
                    // product of the inner dims. Without it `x[0][0]` was a
                    // 1-bit select on a net where the identical variable
                    // declaration worked.
                    {
                        let chain2 =
                            resolve_typedef_chain(&nd.data_type, &elab.typedef_types).clone();
                        let base_w = match &chain2 {
                            DataType::Struct(su) if su.packed => flatten_struct_fields(
                                &chain2,
                                &elab.parameters,
                                &elab.typedefs,
                                &elab.typedef_types,
                            )
                            .map(|f| f.iter().map(|(_, o, w)| o + w).max().unwrap_or(0))
                            .unwrap_or(0),
                            _ => 0,
                        };
                        if base_w > 0 {
                            if let Some(fdims) =
                                packed_typedef_array_dims(&nd.data_type, base_w, &elab.parameters)
                            {
                                let total: i64 =
                                    fdims.iter().map(|(l, r)| (l - r).abs() + 1).product();
                                let (ol, orr) = fdims[0];
                                let outer = (ol - orr).abs() + 1;
                                if outer > 0 && total > 0 {
                                    elab.packed_signal_elem_widths
                                        .insert(decl.name.name.clone(), (total / outer) as u32);
                                }
                                elab.packed_full_dims.insert(decl.name.name.clone(), fdims);
                            }
                        }
                    }
                    if let Some(elem_w) =
                        packed_inner_elem_width(&nd.data_type, &elab.parameters, &elab.typedefs)
                            .or_else(|| {
                                packed_inner_elem_width(
                                    &nd_resolved,
                                    &elab.parameters,
                                    &elab.typedefs,
                                )
                            })
                    {
                        elab.packed_signal_elem_widths
                            .entry(decl.name.name.clone())
                            .or_insert(elem_w);
                    }
                    if let Some(fdims) = packed_full_dims_of(&nd.data_type, &elab.parameters)
                        .or_else(|| packed_full_dims_of(&nd_resolved, &elab.parameters))
                        .or_else(|| {
                            packed_full_dims_chained(
                                &nd.data_type,
                                &elab.parameters,
                                &elab.typedef_types,
                            )
                        })
                    {
                        elab.packed_full_dims
                            .entry(decl.name.name.clone())
                            .or_insert(fdims);
                    }
                    if let Some(shape) = fixed_unpacked_shape(&effective_dims, &elab.parameters)
                        .filter(|shape| !shape.is_empty())
                    {
                        register_fixed_unpacked_array(
                            &mut elab,
                            &decl.name.name,
                            &shape,
                            width,
                            false,
                        );
                        mark_array_z_init_if_4state(&mut elab, &decl.name.name, &nd.data_type);
                        elab.var_decl_types
                            .insert(decl.name.name.clone(), nd.data_type.clone());
                        if let Some(UnpackedDimension::Range { left, right, .. }) =
                            effective_dims.first()
                        {
                            let l = const_eval_i64_with_params(left, Some(&elab.parameters))
                                .unwrap_or(0);
                            let r = const_eval_i64_with_params(right, Some(&elab.parameters))
                                .unwrap_or(0);
                            if l > r {
                                elab.descending_arrays.insert(decl.name.name.clone());
                            }
                        }
                    }
                    // Wire with initializer → continuous assign (not constant eval)
                    if let Some(init_expr) = &decl.init {
                        let decl_dly = net_decl_assign_delay(nd, &elab.parameters);
                        let decl_rhs =
                            net_declaration_driver(nd, &decl.name.name, init_expr, &mut elab);
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
                // Beyond-cap declarations referenced nowhere are elided (see
                // filter_dead_giant_declarators): no phantom allocation, no
                // width-cap warning — matching the reference's silent DCE.
                let dd_filtered;
                let dd = match filter_dead_giant_declarators(dd, &elab, all_defs) {
                    Some(f) => {
                        dd_filtered = f;
                        &dd_filtered
                    }
                    None => dd,
                };
                if dd.declarators.is_empty() {
                    continue;
                }
                // Anonymous enum on a variable decl
                // (`enum logic { A, B } var_name;`): the typedef path
                // registers member constants, but the bare variable form
                // does not, so the names A/B resolve to implicit nets at
                // simulation time. Surfaced by cv32e40p_obi_interface.sv's
                // `state_q FSM`. Helper is also called from the other
                // DataDeclaration arms (submodule items, generate items).
                register_anonymous_enum_members(&dd.data_type, &mut elab);
                // §6.19.6: an anonymous `enum {...} v;` variable needs its
                // ordered member list so `v.num/first/last/next/prev` resolve.
                // Key enum_members by the variable name (there is no typedef
                // name) and stamp the signal's type_name to that key.
                if let Some(members) = anon_enum_members_ordered(&dd.data_type, &elab.parameters) {
                    for decl in &dd.declarators {
                        elab.enum_members
                            .insert(decl.name.name.clone(), members.clone());
                        if let Some(sig) = elab.signals.get_mut(&decl.name.name) {
                            sig.type_name = Some(decl.name.name.clone());
                        }
                    }
                }
                // String-typed declarations (LRM §6.16). Recorded for the
                // bytecode compiler so concatenations involving string
                // operands bail to the AST interpreter (which has byte-
                // level concat semantics; bit-level concat truncates).
                if matches!(
                    &dd.data_type,
                    DataType::Simple {
                        kind: SimpleType::String,
                        ..
                    }
                ) {
                    for decl in &dd.declarators {
                        elab.string_signals.insert(decl.name.name.clone());
                    }
                }
                // Packed multi-D: `logic [3:0][7:0] words;` — record the
                // per-element width so `words[i]` resolves to an 8-bit slice
                // instead of a 1-bit select (LRM §7.4.1).
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
                // Ascending packed vector (`logic [0:7] pa;`): bit/part selects
                // index from the MSB end (label 0 = MSB), so the interpreter
                // remaps `pa[i]` → internal bit (W-1)-i (LRM §7.4.1, §11.5.1).
                if let Some(bounds) = packed_ascending_bounds(&dd.data_type, &elab.parameters) {
                    for decl in &dd.declarators {
                        if decl.dimensions.is_empty() {
                            elab.ascending_packed.insert(decl.name.name.clone(), bounds);
                        }
                    }
                }
                // User-defined nettype → classify as net (allow multiple continuous drivers).
                if let DataType::TypeReference { name, .. } = &dd.data_type {
                    if user_nettypes.contains(&name.name.name) {
                        for decl in &dd.declarators {
                            elab.nets.insert(decl.name.name.clone());
                        }
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
                for decl in &dd.declarators {
                    elab.note_explicit_type(&decl.name.name, &dd.data_type, decl.name.span)?;
                    // §23.2.2.1 non-ANSI port completion: a variable declaration
                    // may supply the data type of an already-declared port —
                    //   output [W-1:0] Q_out;   // direction (implicit net type)
                    //   reg    [W-1:0] Q_out;   // completes it as a variable
                    // The port line registered Q_out (direction = Some), so this
                    // `reg`/`logic` line is the legal type-completing half, NOT
                    // an illegal redeclaration (mirrors the `wire`-completes-port
                    // handling in NetDeclaration and the direction-completes-var
                    // handling in PortDeclaration). Merge the data type onto the
                    // existing port entry and mark it a variable.
                    if elab
                        .signals
                        .get(&decl.name.name)
                        .is_some_and(|s| s.direction.is_some())
                        && !elab.parameters.contains_key(&decl.name.name)
                    {
                        elab.complete_port(&decl.name.name, decl.name.span, &dd.data_type, width)?;
                        let explicit_type = !matches!(dd.data_type, DataType::Implicit { .. });
                        let decl_is_real =
                            is_type_real_resolved(&dd.data_type, &elab.typedef_types);
                        let existing = elab.signals.get_mut(&decl.name.name).unwrap();
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
                            existing.is_real = decl_is_real;
                            existing.type_name = get_type_name(&dd.data_type);
                            existing.value = if decl_is_real {
                                Value::from_f64(0.0)
                            } else {
                                default_port_value(
                                    existing.direction,
                                    Some(&dd.data_type),
                                    width,
                                    decl_is_real,
                                    None,
                                )
                            };
                        }
                        if is_type_two_state_resolved(&dd.data_type, &elab.typedef_types) {
                            elab.two_state_signals.insert(decl.name.name.clone());
                        }
                        // A reg/logic completion makes the port a variable, not a net.
                        unregister_net_type(&mut elab, &decl.name.name);
                        elab.var_decl_types
                            .insert(decl.name.name.clone(), dd.data_type.clone());
                        continue;
                    }
                    if (elab.signals.contains_key(&decl.name.name)
                        || elab.parameters.contains_key(&decl.name.name))
                        && elab.claim_local_decl_displacement(
                            &decl.name.name,
                            decl.name.span,
                            "variable/net",
                        )
                    {
                        // §26.3: local decl shadows the wildcard-imported name,
                        // so an imported package net's kind goes too (#610).
                        elab.signals.remove(&decl.name.name);
                        elab.remove_param(&decl.name.name);
                        unregister_net_type(&mut elab, &decl.name.name);
                    } else if elab.signals.contains_key(&decl.name.name)
                        || elab.parameters.contains_key(&decl.name.name)
                    {
                        // LRM §6.x: re-declaring a name already declared in the
                        // same scope is illegal. In strict mode (the default)
                        // this is a hard error. It stays a warning under
                        // --no-strict because xezim sometimes merges class-
                        // function locals into module scope (e.g. cv32e40p UVM
                        // TB's `bit tp;` colliding with a same-named function
                        // local), which would otherwise be a false-positive
                        // collision; --no-strict keeps those designs elaborating
                        // until that scope-merge is fixed.
                        if sv_parser::strict_checks() {
                            return Err(duplicate_decl_error(
                                &elab,
                                &decl.name.name,
                                decl.name.span,
                                "data",
                            ));
                        }
                        eprintln!(
                            "[xezim][warning] duplicate declaration of '{}' (data); keeping first definition",
                            decl.name.name
                        );
                        continue;
                    }
                    // A variable typed by an unpacked-array typedef
                    // (`typedef T A[0:3]; A v;`) inherits the typedef's unpacked
                    // dimensions when it declares none of its own (LRM §6.18,
                    // §7.4). For every other declaration this is exactly
                    // `decl.dimensions`, so behavior is unchanged.
                    // §7.4.5: declarator dimensions come before the typedef's.
                    let effective_dims: Vec<UnpackedDimension> = match &dd.data_type {
                        DataType::TypeReference {
                            name, dimensions, ..
                        } if dimensions.is_empty() => {
                            let mut d = decl.dimensions.clone();
                            if let Some(td) = lookup_scoped_type(name, &elab.typedef_unpacked_dims)
                            {
                                d.extend(td.iter().cloned());
                            }
                            d
                        }
                        _ => decl.dimensions.clone(),
                    };
                    // `a[N]` (N a parameter) parses as an associative dim keyed by
                    // "type" N; rewrite it back to a fixed size.
                    let effective_dims = normalize_unpacked_dims(
                        &effective_dims,
                        &elab.parameters,
                        &elab.typedef_types,
                    );
                    record_coll_shape(&mut elab, &decl.name.name, &effective_dims, None);
                    if let Some(UnpackedDimension::Associative {
                        data_type: key_dt, ..
                    }) = effective_dims.first()
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
                        // Record the element DataType keyed by the array's base
                        // name so an inline `arr[k] = new` can resolve the
                        // element CLASS from its declared type (module- OR
                        // package-scope associative arrays; the runtime maps
                        // `array_elem_class` / `var_class_types` only cover
                        // local/fixed arrays). Without this the constructor
                        // falls through to an OPAQUE unknown-LHS instance and
                        // the stored handle deref's null — e.g. UVM's
                        // `uvm_seed_map uvm_random_seed_table_lookup [string]`
                        // then `uvm_create_random_seed` reads
                        // `seed_map.seed_table` through null at t=0.
                        elab.var_decl_types
                            .insert(decl.name.name.clone(), dd.data_type.clone());
                        // §7.8.2: an AA index is narrowed to the declared key
                        // type. Record the key width + signedness so the runtime
                        // can narrow a wider index expression before keying
                        // (`int k; aa[k]` on `shortint aa[shortint]`).
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
                        if let Some(init_expr) = &decl.init {
                            if let ExprKind::AssignmentPattern(items) =
                                &peel_unpacked_typed_pattern(init_expr).kind
                            {
                                for item in items {
                                    if let crate::ast::expr::AssignmentPatternItem::Default(
                                        def_expr,
                                    ) = item
                                    {
                                        elab.assoc_defaults
                                            .insert(decl.name.name.clone(), def_expr.clone());
                                    }
                                }
                            }
                        }
                    }
                    let is_dynamic_dim = effective_dims.first().is_some_and(|d| {
                        matches!(
                            d,
                            UnpackedDimension::Unsized(_) | UnpackedDimension::Queue { .. }
                        )
                    });
                    if is_dynamic_dim {
                        elab.dynamic_arrays.insert(decl.name.name.clone());
                    }
                    if matches!(
                        effective_dims.first(),
                        Some(UnpackedDimension::Queue { .. })
                    ) {
                        elab.queue_vars.insert(decl.name.name.clone());
                    }
                    // §7.8 / §8.4: record the ELEMENT CLASS for associative,
                    // queue and dynamic collections, exactly as the fixed-size
                    // array branches above do. Without it the simulator's
                    // `coll[key] = new` route cannot resolve which class to
                    // construct, so it stored X — `q.push_back(new)` and
                    // `pool[k] = new` silently produced a null/X element while
                    // `arr[i] = new` on a FIXED array worked. UVM hits this on
                    // every `uvm_create_random_seed` call.
                    if matches!(
                        effective_dims.first(),
                        Some(
                            UnpackedDimension::Associative { .. }
                                | UnpackedDimension::Queue { .. }
                                | UnpackedDimension::Unsized(_)
                        )
                    ) {
                        if let DataType::TypeReference { name: tn, .. } = &dd.data_type {
                            elab.array_elem_class
                                .insert(decl.name.name.clone(), tn.name.name.clone());
                        }
                    }
                    if let Some(UnpackedDimension::Queue {
                        max_size: Some(ms), ..
                    }) = effective_dims.first()
                    {
                        let n = const_eval_i64_with_params(ms, Some(&elab.parameters)).unwrap_or(0);
                        if n >= 0 {
                            elab.queue_max_sizes
                                .insert(decl.name.name.clone(), (n + 1) as u32);
                        }
                    }
                    // IEEE 1800-2017 §7.4.5 / §7.8: an unpacked array whose
                    // ELEMENT is itself a dynamic collection —
                    //   `int q[3][$]`      array of queues
                    //   `int d[3][]`       array of dynamic arrays
                    //   `int a[2][u8_t]`   array of associative arrays
                    // The leading dimensions give the (fixed) shape; the
                    // trailing one makes every element its own collection.
                    // Without this the trailing dimension was simply dropped and
                    // `q[i]` was a plain scalar.
                    // A leading dynamic dim is fine too (`int qq[$][$]`): its
                    // backing buffer gives the outer shape.
                    if let Some(split) = coll_elem_split(&effective_dims) {
                        if let Some(qd) = effective_dims.get(split) {
                            if matches!(
                                qd,
                                UnpackedDimension::Unsized(_)
                                    | UnpackedDimension::Queue { .. }
                                    | UnpackedDimension::Associative { .. }
                            ) {
                                let outer = &effective_dims[..split];
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
                                    if let Some(declared) =
                                        declared_unpacked_dims(outer, &elab.parameters)
                                    {
                                        elab.unpacked_decl_dims
                                            .insert(decl.name.name.clone(), declared);
                                    }
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
                                                &mut elab,
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
                    // Helper: if the element type resolves to a packed struct,
                    // register the FLATTENED field layout (including nested
                    // dotted paths like `outer.inner.leaf`) under the array
                    // name so `arr[i][j]...[k].outer.inner.leaf` read/write
                    // paths can splice it. Mirrors the 1-D-array packed-
                    // struct registration below, but uses the shared
                    // `flatten_array_elem_fields` helper that produces the
                    // same dotted-keys layout `flatten_struct_fields` does for
                    // standalone struct vars.
                    let register_packed_for_array = |elab: &mut ElaboratedModule| {
                        fn flatten_elem(
                            dt: &DataType,
                            params: &dyn ParamLookup,
                            typedefs: &HashMap<String, u32>,
                            typedef_types: &HashMap<String, DataType>,
                        ) -> Option<Vec<(String, u32, u32)>> {
                            // Scoped element types (`p::r_t arr[4]`): member
                            // dims bind the OWNING package's params bare —
                            // re-derive per level (see scoped_type_owner).
                            let owner_own;
                            let stacked;
                            let params: &dyn ParamLookup =
                                match scoped_type_owner(dt, typedef_types) {
                                    Some(pkg) => {
                                        owner_own = owner_param_overrides(&pkg, params);
                                        stacked = StackedParamEnv {
                                            base: params,
                                            top: &owner_own,
                                        };
                                        &stacked
                                    }
                                    None => params,
                                };
                            let resolved = resolve_typedef_chain(dt, typedef_types);
                            if let DataType::Struct(su) = resolved {
                                let is_union = matches!(su.kind, StructUnionKind::Union);
                                let mut raw: Vec<(String, u32, DataType)> = Vec::new();
                                for member in &su.members {
                                    let mw = resolve_type_width_env(
                                        &member.data_type,
                                        Some(&params),
                                        Some(typedefs),
                                    );
                                    for mdecl in &member.declarators {
                                        raw.push((
                                            mdecl.name.name.clone(),
                                            mw,
                                            member.data_type.clone(),
                                        ));
                                    }
                                }
                                let mut out: Vec<(String, u32, u32)> = Vec::new();
                                if is_union {
                                    for (mn, mw, mdt) in &raw {
                                        out.push((mn.clone(), 0, *mw));
                                        if let Some(subs) =
                                            flatten_elem(mdt, params, typedefs, typedef_types)
                                        {
                                            for (sn, so, sw) in subs {
                                                out.push((format!("{}.{}", mn, sn), so, sw));
                                            }
                                        }
                                    }
                                } else {
                                    let mut offset: u32 = 0;
                                    for (mn, mw, mdt) in raw.iter().rev() {
                                        out.push((mn.clone(), offset, *mw));
                                        if let Some(subs) =
                                            flatten_elem(mdt, params, typedefs, typedef_types)
                                        {
                                            for (sn, so, sw) in subs {
                                                out.push((
                                                    format!("{}.{}", mn, sn),
                                                    offset + so,
                                                    sw,
                                                ));
                                            }
                                        }
                                        offset += mw;
                                    }
                                }
                                Some(out)
                            } else {
                                None
                            }
                        }
                        let elem_resolved: &DataType =
                            if let DataType::TypeReference { name, .. } = &dd.data_type {
                                // §26.3: scoped element type — qualified key
                                // first so a same-named local can't capture.
                                lookup_scoped_type(name, &elab.typedef_types)
                                    .unwrap_or(&dd.data_type)
                            } else {
                                &dd.data_type
                            };
                        // Only a PACKED struct element has a contiguous bit layout that
                        // `arr[i].member` can slice. An UNPACKED struct element stores each
                        // member as its own signal (`arr[i].member`); bit-slicing it drops
                        // `real` members' is_real (they read back as raw bits) and shifts the
                        // offsets of any member following a string / nested aggregate.
                        let elem_is_packed = matches!(
                            resolve_typedef_chain(elem_resolved, &elab.typedef_types),
                            DataType::Struct(su) if su.packed
                        );
                        if elem_is_packed {
                            if let Some(fields) = flatten_elem(
                                &dd.data_type,
                                &elab.parameters,
                                &elab.typedefs,
                                &elab.typedef_types,
                            ) {
                                if !fields.is_empty() {
                                    tls_register_struct_layout(&decl.name.name, &fields);
                                    elab.packed_struct_fields
                                        .insert(decl.name.name.clone(), fields);
                                }
                            }
                        }
                        // A member that is itself a multi-dimensional PACKED
                        // array (`logic [1:0][63:0] wdata;`) needs its element
                        // width recorded so `arr[i].wdata[j]` selects a whole
                        // lane. The non-array declarator path does this, but an
                        // ARRAY of structs reaches `continue` before it, so the
                        // select silently degraded to a 1-BIT read — a 64-bit
                        // lane compared against one bit. Registered under the
                        // DECLARATION name; the runtime aliases each element to
                        // it. Applies whether or not the element is packed:
                        // an unpacked struct still stores `wdata` as one signal.
                        {
                            let mut pending: Vec<(String, u32)> = Vec::new();
                            let mut pending_dims: Vec<(String, Vec<(i64, i64)>)> = Vec::new();
                            if let DataType::Struct(su) =
                                resolve_typedef_chain(elem_resolved, &elab.typedef_types)
                            {
                                for m in &su.members {
                                    let (ew, fd) = packed_member_meta(
                                        &m.data_type,
                                        &elab.parameters,
                                        &elab.typedefs,
                                        &elab.typedef_types,
                                    );
                                    for mdecl in &m.declarators {
                                        let key = format!("{}.{}", decl.name.name, mdecl.name.name);
                                        if let Some(ew) = ew {
                                            pending.push((key.clone(), ew));
                                        }
                                        if let Some(fd) = &fd {
                                            pending_dims.push((key, fd.clone()));
                                        }
                                    }
                                }
                            }
                            for (k, ew) in pending {
                                elab.packed_signal_elem_widths.insert(k, ew);
                            }
                            for (k, fd) in pending_dims {
                                elab.packed_full_dims.insert(k, fd);
                            }
                        }
                    };
                    // IEEE 1800-2017 §7.4.5: a DYNAMIC outer dimension with
                    // FIXED trailing dimensions — `mailbox mbx[][16]`,
                    // `int a[$][2][3]`. The trailing dims were dropped, so the
                    // variable elaborated as a plain 1-D dynamic array and
                    // `a[i][j]` was a bit-select of element `a[i]`. Register a
                    // 2-D/N-D backing buffer whose outer dim is the standard
                    // 64-slot dynamic buffer (same buffer `extract_array_range`
                    // gives a 1-D dynamic array); the runtime size still lives
                    // in the `.size` shadow, and foreach clamps the outer dim
                    // to it. Elements resolve at `a[i][j]` like any fixed
                    // multi-D array's.
                    if effective_dims.len() >= 2
                        && effective_dims.first().is_some_and(|d| {
                            matches!(
                                d,
                                UnpackedDimension::Unsized(_) | UnpackedDimension::Queue { .. }
                            )
                        })
                        && effective_dims[1..].iter().all(|d| {
                            matches!(
                                d,
                                UnpackedDimension::Range { .. }
                                    | UnpackedDimension::Expression { .. }
                            )
                        })
                    {
                        let inner: Option<Vec<(i64, i64)>> = effective_dims[1..]
                            .iter()
                            .map(|d| extract_array_range(std::slice::from_ref(d), &elab.parameters))
                            .collect();
                        if let Some(inner) =
                            inner.filter(|sh| sh.iter().all(|&(lo, hi)| hi >= lo && hi - lo < 4096))
                        {
                            let name = decl.name.name.clone();
                            // §21.2.1.7: the fixed dimensions' declared bounds,
                            // behind the same placeholder outer dimension as the
                            // shape, so `%p` prints a `[1:0]` row from 1 (#597).
                            if let Some(dd) =
                                declared_unpacked_dims(&effective_dims[1..], &elab.parameters)
                            {
                                let mut all = vec![(0i64, 63i64)];
                                all.extend(dd);
                                elab.unpacked_decl_dims.insert(name.clone(), all);
                            }
                            if inner.len() == 1 {
                                elab.arrays_2d
                                    .insert(name.clone(), ((0, 63), inner[0], width));
                            } else {
                                let mut shape = vec![(0i64, 63i64)];
                                shape.extend(inner.iter().cloned());
                                elab.arrays_nd.insert(name.clone(), (shape, width));
                            }
                            elab.var_decl_types
                                .insert(name.clone(), dd.data_type.clone());
                            if let DataType::TypeReference { name: tn, .. } = &dd.data_type {
                                elab.array_elem_class
                                    .insert(name.clone(), tn.name.name.clone());
                            }
                            register_packed_for_array(&mut elab);
                            continue;
                        }
                    }
                    // Check for 2D unpacked array (e.g., mem [0:1023][0:3])
                    if effective_dims.len() == 2 {
                        // Both `[0:1][0:2]` (range) and `[2][3]` (size) spell the
                        // same 2-D array. Only the range form was recognised, so
                        // `int m[2][3]` fell through to the 1-D path and every
                        // `m[i][j]` was a bit-select that read X. The N-D branch
                        // below already accepted both forms.
                        let dim_range = |d: &UnpackedDimension, params: &HashMap<String, Value>| {
                            extract_array_range(std::slice::from_ref(d), params)
                        };
                        let r1 = match &effective_dims[0] {
                            d @ (UnpackedDimension::Range { .. }
                            | UnpackedDimension::Expression { .. }) => {
                                dim_range(d, &elab.parameters)
                            }
                            _ => None,
                        };
                        let r2 = match &effective_dims[1] {
                            d @ (UnpackedDimension::Range { .. }
                            | UnpackedDimension::Expression { .. }) => {
                                dim_range(d, &elab.parameters)
                            }
                            _ => None,
                        };
                        if let (Some((lo1, hi1)), Some((lo2, hi2))) = (r1, r2) {
                            elab.arrays_2d
                                .insert(decl.name.name.clone(), ((lo1, hi1), (lo2, hi2), width));
                            if let Some(dd) =
                                declared_unpacked_dims(&effective_dims, &elab.parameters)
                            {
                                elab.unpacked_decl_dims.insert(decl.name.name.clone(), dd);
                            }
                            // §6.8: a 2-state ELEMENT type means the array's
                            // slots default to 0 (the simulator consults this
                            // when it builds the element storage).
                            if is_type_two_state_resolved(&dd.data_type, &elab.typedef_types) {
                                elab.two_state_signals.insert(decl.name.name.clone());
                            }
                            // Element type, for the type-directed `%p` renderer.
                            elab.var_decl_types
                                .insert(decl.name.name.clone(), dd.data_type.clone());
                            // LRM §8.4 (2D class arrays). Same as the 1D
                            // path: record the element class so the
                            // simulator's `arr[i][j] = new(...)` route
                            // constructs the right instance.
                            if let DataType::TypeReference { name, .. } = &dd.data_type {
                                elab.array_elem_class
                                    .insert(decl.name.name.clone(), name.name.name.clone());
                            }
                            register_packed_for_array(&mut elab);
                            // Per-element Signal entries are synthesized lazily
                            // by Simulator::new from the arrays_2d metadata —
                            // avoids the per-element HashMap entries at
                            // elaborate time (major memory win on designs
                            // with large memories). The width/signed/real
                            // attributes are uniform across elements so we
                            // don't need a per-element Signal struct.
                            // §6.8/§10.9: apply the declaration initializer as one
                            // whole-pattern assignment (the per-element lowering of the
                            // 1-D path walks a single dimension; this shape's initializer
                            // was silently dropped).
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
                            let _ = (is_signed, width);
                            continue;
                        }
                    }
                    // Check for N-dimensional unpacked array (N >= 3)
                    if effective_dims.len() >= 3
                        && effective_dims.iter().all(|d| {
                            matches!(
                                d,
                                UnpackedDimension::Range { .. }
                                    | UnpackedDimension::Expression { .. }
                            )
                        })
                    {
                        let mut shape: Vec<(i64, i64)> = Vec::new();
                        for d in &effective_dims {
                            match d {
                                UnpackedDimension::Range { left, right, .. } => {
                                    let l =
                                        const_eval_i64_with_params(left, Some(&elab.parameters))
                                            .unwrap_or(0);
                                    let r =
                                        const_eval_i64_with_params(right, Some(&elab.parameters))
                                            .unwrap_or(0);
                                    shape.push((l.min(r), l.max(r)));
                                }
                                UnpackedDimension::Expression { expr, .. } => {
                                    let n =
                                        const_eval_i64_with_params(expr, Some(&elab.parameters))
                                            .unwrap_or(0);
                                    shape.push((0, (n - 1).max(0)));
                                }
                                _ => {}
                            }
                        }
                        elab.arrays_nd
                            .insert(decl.name.name.clone(), (shape.clone(), width));
                        if let Some(dd2) = declared_unpacked_dims(&effective_dims, &elab.parameters)
                        {
                            elab.unpacked_decl_dims.insert(decl.name.name.clone(), dd2);
                        }
                        // §6.8: a 2-state ELEMENT type means the array's
                        // slots default to 0 (the simulator consults this
                        // when it builds the element storage).
                        if is_type_two_state_resolved(&dd.data_type, &elab.typedef_types) {
                            elab.two_state_signals.insert(decl.name.name.clone());
                        }
                        elab.var_decl_types
                            .insert(decl.name.name.clone(), dd.data_type.clone());
                        if let DataType::TypeReference { name, .. } = &dd.data_type {
                            elab.array_elem_class
                                .insert(decl.name.name.clone(), name.name.name.clone());
                        }
                        register_packed_for_array(&mut elab);
                        // Per-element Signals synthesized by Simulator::new
                        // from arrays_nd — skip the per-element HashMap
                        // inserts here.
                        // §6.8/§10.9: apply the declaration initializer as one
                        // whole-pattern assignment (the per-element lowering of the
                        // 1-D path walks a single dimension; this shape's initializer
                        // was silently dropped).
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
                        let _ = is_signed;
                        continue;
                    }
                    // Check for unpacked array dimensions (e.g., memory [0:255])
                    let array_range = extract_array_range(&effective_dims, &elab.parameters);
                    if let Some((lo, hi)) = array_range {
                        // Register this as an array for the simulator
                        elab.arrays.insert(decl.name.name.clone(), (lo, hi, width));
                        if let Some(dd) = declared_unpacked_dims(&effective_dims, &elab.parameters)
                        {
                            elab.unpacked_decl_dims.insert(decl.name.name.clone(), dd);
                        }
                        // §6.8: a 2-state ELEMENT type means the array's
                        // slots default to 0 (the simulator consults this
                        // when it builds the element storage).
                        if is_type_two_state_resolved(&dd.data_type, &elab.typedef_types) {
                            elab.two_state_signals.insert(decl.name.name.clone());
                        }
                        // §15.5 an ARRAY of named events. Only the scalar
                        // declarator path registers `events` + a 1-bit backing
                        // signal, so an element had neither: `-> ev[1]` found
                        // no signal to toggle, and `@ev[1]` found none to arm
                        // on — the waiter then fell into the simulator's
                        // "not a real signal" delta-yield and woke instantly at
                        // t=0 instead of blocking. Give each element the same
                        // identity a scalar event gets, so the existing
                        // name-keyed machinery (trigger / `@` / `.triggered`)
                        // works on elements unchanged.
                        if matches!(
                            &dd.data_type,
                            DataType::Simple {
                                kind: SimpleType::Event,
                                ..
                            }
                        ) {
                            elab.events.insert(decl.name.name.clone());
                            if hi >= lo && (hi - lo) < 4096 {
                                for i in lo..=hi {
                                    let en = format!("{}[{}]", decl.name.name, i);
                                    elab.events.insert(en.clone());
                                    signals_insert_traced(
                                        &mut elab.signals,
                                        line!(),
                                        en.clone(),
                                        Signal {
                                            is_const: false,
                                            name: en.into(),
                                            width: 1,
                                            is_signed: false,
                                            is_real: false,
                                            direction: None,
                                            value: Value::zero(1),
                                            type_name: Some("event".to_string()),
                                        },
                                    );
                                }
                            }
                        }
                        // Element type, for the type-directed `%p` renderer.
                        elab.var_decl_types
                            .insert(decl.name.name.clone(), dd.data_type.clone());
                        // An UNPACKED struct element keeps each member in its own
                        // signal (recursively: nested unpacked members expand, nested
                        // packed members get a signal + slice layout). Without this
                        // they are created lazily on first assignment and lose their
                        // declared type (a `real` member reads back as raw bits).
                        if let DataType::Struct(su) =
                            resolve_typedef_chain(&dd.data_type, &elab.typedef_types).clone()
                        {
                            if !su.packed && hi >= lo && (hi - lo) < 4096 {
                                for i in lo..=hi {
                                    let ebase = format!("{}[{}]", decl.name.name, i);
                                    register_unpacked_aggregate(&mut elab, &ebase, &dd.data_type);
                                }
                            }
                        }
                        // LRM §8.4: if the array element type is a known
                        // class, stash the class name so the simulator's
                        // `arr[i] = new(...)` path can construct the right
                        // instance. (Detection done here at the unpacked-
                        // array branch — also mirrored in the 2D and N-D
                        // branches below.)
                        if let DataType::TypeReference { name, .. } = &dd.data_type {
                            let tn = &name.name.name;
                            if !elab.classes.contains_key(tn) {
                                // class definitions get inserted at the
                                // start of elaborate_module_with_defs; if
                                // not yet present, the simulator's
                                // late check still resolves at access
                                // time, but we record speculatively here.
                            }
                            // Always record the type name; the simulator
                            // verifies against `module.classes` at use time.
                            elab.array_elem_class
                                .insert(decl.name.name.clone(), tn.clone());
                        }
                        // Register the FLATTENED packed-struct field layout
                        // (including nested dotted paths) under the array
                        // name. Same flattening as `flatten_struct_fields` so
                        // `arr[i].outer.inner.leaf` chains work identically
                        // to `var.outer.inner.leaf` on a standalone struct.
                        register_packed_for_array(&mut elab);
                        // Track descending arrays (left > right in the declaration)
                        if let Some(UnpackedDimension::Range { left, right, .. }) =
                            effective_dims.first()
                        {
                            let l = const_eval_i64_with_params(left, Some(&elab.parameters))
                                .unwrap_or(0);
                            let r = const_eval_i64_with_params(right, Some(&elab.parameters))
                                .unwrap_or(0);
                            if l > r {
                                elab.descending_arrays.insert(decl.name.name.clone());
                            }
                        }
                        // Per-element Signals are synthesized by Simulator::new
                        // from the `arrays` metadata; no per-element HashMap
                        // inserts here. This alone is the largest memory win
                        // on designs with testbench memory arrays.
                        let _ = (is_signed, width);
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
                            } else if !is_dynamic_dim {
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
                        }
                    } else {
                        let is_real = is_type_real_resolved(&dd.data_type, &elab.typedef_types);
                        let w = width;
                        let (init_val, procedural_init) = if let Some(init_expr) = &decl.init {
                            if is_const_expr(init_expr, &elab.parameters) {
                                // §6.16: a `string` has no declared length — `w`
                                // is the 1024-bit PLACEHOLDER, and fitting the
                                // initializer to it truncates the FRONT of any
                                // text past 128 characters (a packed string
                                // keeps its text in the low bits). The runtime
                                // stores were already exempt (issues #63/#64);
                                // this DECLARATION-initializer path was the
                                // last one still fitting (issue #65:
                                // `string cmd = "<144 chars>";` lost its
                                // "echo_SAFE_" prefix while the identical
                                // procedural assignment was correct).
                                let is_string_decl = matches!(
                                    &dd.data_type,
                                    DataType::Simple {
                                        kind: SimpleType::String,
                                        ..
                                    }
                                );
                                let mut rv = if is_string_decl {
                                    eval_const_expr_val(init_expr, &elab.parameters)
                                } else {
                                    eval_init_for_target(init_expr, &elab.parameters, w, is_real)
                                };
                                // §11.8.1: the DECLARED type decides signedness — an
                                // initializer's sign must never leak into it.
                                // Only SETTING the flag left `int unsigned x = -1`
                                // and `bit [15:0] u = -1` behaving as signed, so
                                // `x > 0` was false and `u + 10` was 9 instead of
                                // 65545. (Parameters had the same bug; this is the
                                // variable-declaration twin.)
                                if !is_real {
                                    rv.is_signed = is_signed;
                                }
                                if is_real {
                                    rv = Value::from_f64(rv.to_f64());
                                }
                                // §6.3.1/§6.11: converting to a 2-STATE type
                                // maps x/z to 0. The procedural-assign path
                                // already did this; the declaration
                                // initializer skipped it, so `bit b = 1'bx;`
                                // stored an "impossible" x in a 2-state var.
                                if !is_real
                                    && is_type_two_state_resolved(
                                        &dd.data_type,
                                        &elab.typedef_types,
                                    )
                                {
                                    rv = rv.to_two_state();
                                }
                                (rv, None)
                            } else {
                                (
                                    default_value_for_type_resolved(
                                        &dd.data_type,
                                        w,
                                        &elab.typedef_types,
                                    ),
                                    Some(init_expr.as_ref().clone()),
                                )
                            }
                        } else {
                            (
                                default_value_for_type_resolved(
                                    &dd.data_type,
                                    w,
                                    &elab.typedef_types,
                                ),
                                None,
                            )
                        };

                        let sig = Signal {
                            is_const: dd.const_kw,
                            name: decl.name.name.clone().into(),
                            width: w,
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
                        if matches!(
                            &dd.data_type,
                            DataType::Simple {
                                kind: SimpleType::Event,
                                ..
                            }
                        ) {
                            elab.events.insert(decl.name.name.clone());
                        }
                        if is_type_two_state_resolved(&dd.data_type, &elab.typedef_types) {
                            elab.two_state_signals.insert(decl.name.name.clone());
                        }
                        // §6.6.7 + §10.3.1: a USER-DEFINED-NETTYPE net's
                        // declaration initializer is a CONTINUOUS DRIVER of
                        // that net, subject to its resolution function — not
                        // just the high-hold seed this declaration would
                        // otherwise write. Without it the resolver never saw
                        // the initializer, so a resolver that keys on driver
                        // COUNT (issue #1204) resolved as if the net had one
                        // fewer driver. A non-constant initializer drives the
                        // net the same way, instead of the one-time
                        // procedural write a variable gets below.
                        let nettype_net = declared_user_nettype(&elab, &dd.data_type).is_some();
                        if nettype_net
                            && let Some(d) = nettype_net_delay(dd, decl, &elab.parameters)
                        {
                            elab.net_delays.insert(decl.name.name.clone(), d);
                        }
                        if nettype_net && let Some(init_expr) = decl.init.as_ref() {
                            let ca = nettype_declaration_driver(
                                dd,
                                &decl.name.name,
                                init_expr,
                                true,
                                &elab.parameters,
                            );
                            // A delayed driver has not arrived yet: the net
                            // starts from its type's default, not the value.
                            if (ca.delay != 0 || ca.delay_exprs.is_some())
                                && let Some(sig) = elab.signals.get_mut(&decl.name.name)
                            {
                                sig.value = default_value_for_type_resolved(
                                    &dd.data_type,
                                    w,
                                    &elab.typedef_types,
                                );
                            }
                            elab.continuous_assigns.push(ca);
                        }
                        if let Some(view) = &data_modport_view {
                            elab.modport_views
                                .insert(decl.name.name.clone(), view.clone());
                        }

                        if let Some(expr) = procedural_init.filter(|_| !nettype_net) {
                            // §6.20.6: a `const` declaration's initializer is its
                            // one legal write — record it so the const-write
                            // check exempts this synthetic assignment.
                            if dd.const_kw {
                                elab.const_decl_inits.insert(decl.name.name.clone());
                            }
                            elab.initial_blocks.push(InitialBlock {
                                stmt: Statement::new(
                                    StatementKind::BlockingAssign {
                                        lvalue: make_ident_expr(&decl.name.name),
                                        rvalue: expr,
                                    },
                                    decl.name.span,
                                ),
                                scope: String::new(),
                            });
                        }
                        // Unpacked-struct member default initializers:
                        //   struct { bit [3:0] lo = c; ... } p1;
                        // Packed structs forbid member defaults (IEEE 7.2.2).
                        // Owned so later `&mut elab` calls (member pre-registration)
                        // don't conflict with a borrow of `elab.typedef_types`.
                        let dt_resolved_owned: DataType =
                            if let DataType::TypeReference { name, .. } = &dd.data_type {
                                // §26.3: a SCOPED reference (`P::T`) names the
                                // package's typedef — qualified key first, so a
                                // same-named local typedef can't capture it.
                                let scoped = lookup_scoped_type(name, &elab.typedef_types);
                                scoped
                                    .or_else(|| elab.typedef_types.get(&name.name.name))
                                    .cloned()
                                    .unwrap_or_else(|| dd.data_type.clone())
                            } else {
                                dd.data_type.clone()
                            };
                        // Follow the WHOLE typedef chain, not one hop. One hop
                        // lands on another TypeReference whenever the declared
                        // type is an ALIAS of a struct typedef — `typedef T T2;
                        // T2 b;` and, since a nettype registers its own data
                        // type here, `nettype T wT; wT n;`. The `Struct` arms
                        // below (notably `register_unpacked_aggregate`) then
                        // never fired, so the declaration got ONE flat
                        // container signal instead of per-member leaves: member
                        // writes had nowhere to land and every member read back
                        // 0 / x.
                        let dt_resolved_owned: DataType =
                            resolve_typedef_chain(&dt_resolved_owned, &elab.typedef_types).clone();
                        let dt_resolved: &DataType = &dt_resolved_owned;
                        // Member dims of a scoped package type reference the
                        // OWNING package's params by bare name (see
                        // scoped_type_owner) — overlay them for the layout walk;
                        // dt_resolved is already the raw Struct, so the walk
                        // itself can't recover the owner.
                        let layout_own;
                        let layout_stacked;
                        let layout_params: &dyn ParamLookup =
                            match scoped_type_owner(&dd.data_type, &elab.typedef_types) {
                                Some(pkg) => {
                                    layout_own = owner_param_overrides(&pkg, &elab.parameters);
                                    layout_stacked = StackedParamEnv {
                                        base: &elab.parameters,
                                        top: &layout_own,
                                    };
                                    &layout_stacked
                                }
                                None => &elab.parameters,
                            };
                        if let Some(fields) = flatten_struct_fields(
                            dt_resolved,
                            layout_params,
                            &elab.typedefs,
                            &elab.typedef_types,
                        ) {
                            if !fields.is_empty() {
                                tls_register_struct_layout(&decl.name.name, &fields);
                                // Only register packed-struct layouts in
                                // `packed_struct_fields`. Unpacked structs
                                // store members as separate signals (see the
                                // !su.packed arm below) and writing through
                                // bit-slice offsets into the parent signal
                                // would clobber unrelated state.
                                if let DataType::Struct(su) = dt_resolved {
                                    if su.packed {
                                        elab.packed_struct_fields
                                            .insert(decl.name.name.clone(), fields);
                                    }
                                }
                            }
                        }
                        // §7.4.2: a PACKED ARRAY of packed struct
                        // (`typedef word [1:0] dword; dword foo;`) is one
                        // contiguous vector of N structs. `dt_resolved` is a
                        // TypeReference (not a bare Struct), so the block above
                        // does not register it. Register the element's field
                        // layout (element-relative offsets) under `foo` plus the
                        // element width, so `foo[i].field` resolves to
                        // `i*elem_w + field_off` in the single backing signal.
                        // §7.4.2 packed dims written on a STRUCT TYPEDEF
                        // (`some_t [0:0][1:0] arr;`). Registered independently of
                        // the field-layout block below, which is skipped once
                        // `packed_struct_fields` already holds the name — that is
                        // exactly the case for a struct-typed declaration, so the
                        // dimensions were never recorded and `arr[i]` decayed to a
                        // 1-bit select.
                        if decl.dimensions.is_empty()
                            && !elab.packed_full_dims.contains_key(&decl.name.name)
                        {
                            let chain2 =
                                resolve_typedef_chain(&dd.data_type, &elab.typedef_types).clone();
                            if matches!(&chain2, DataType::Struct(su) if su.packed) {
                                let sw = flatten_struct_fields(
                                    &chain2,
                                    &elab.parameters,
                                    &elab.typedefs,
                                    &elab.typedef_types,
                                )
                                .map(|f| f.iter().map(|(_, o, w)| o + w).max().unwrap_or(0))
                                .unwrap_or(0);
                                if let Some(fdims) =
                                    packed_typedef_array_dims(&dd.data_type, sw, &elab.parameters)
                                {
                                    let total: i64 =
                                        fdims.iter().map(|(l, r)| (l - r).abs() + 1).product();
                                    let (ol, orr) = fdims[0];
                                    let outer = (ol - orr).abs() + 1;
                                    if outer > 0 && total > 0 {
                                        elab.packed_signal_elem_widths
                                            .insert(decl.name.name.clone(), (total / outer) as u32);
                                    }
                                    elab.packed_full_dims.insert(decl.name.name.clone(), fdims);
                                }
                            }
                        }
                        if !elab.packed_struct_fields.contains_key(&decl.name.name)
                            && decl.dimensions.is_empty()
                        {
                            let chain =
                                resolve_typedef_chain(dt_resolved, &elab.typedef_types).clone();
                            if let DataType::Struct(su) = &chain {
                                if su.packed {
                                    if let Some(fields) = flatten_struct_fields(
                                        &chain,
                                        &elab.parameters,
                                        &elab.typedefs,
                                        &elab.typedef_types,
                                    ) {
                                        let struct_w =
                                            fields.iter().map(|(_, o, w)| o + w).max().unwrap_or(0);
                                        // Packed dims written on the TYPEDEF itself
                                        // (`some_t [0:0][1:0] arr;`). Register the
                                        // full dimension list — including a single
                                        // `[0:0]`, where `width == struct_w` and the
                                        // element gate below never fired, leaving
                                        // `arr[0]` a 1-bit select.
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
                                            tls_register_struct_layout(&decl.name.name, &fields);
                                            elab.packed_struct_fields
                                                .insert(decl.name.name.clone(), fields);
                                        } else if struct_w > 0
                                            && width > struct_w
                                            && width % struct_w == 0
                                        {
                                            elab.packed_signal_elem_widths
                                                .insert(decl.name.name.clone(), struct_w);
                                            tls_register_struct_layout(&decl.name.name, &fields);
                                            elab.packed_struct_fields
                                                .insert(decl.name.name.clone(), fields);
                                        }
                                    }
                                }
                            }
                        }
                        // Record top-level member names in DECLARATION order for
                        // `%p` (LRM §21.2.1.7). Applies to packed and unpacked
                        // structs alike, since neither existing map preserves
                        // source order. Skip declarators carrying unpacked
                        // dimensions (`rec_t arr[N]`, `rec_t m[int]`): those are
                        // ARRAYS of structs, and `%p` must print them as an
                        // element list, not as a single struct.
                        elab.var_decl_types
                            .insert(decl.name.name.clone(), dd.data_type.clone());
                        if decl.dimensions.is_empty() {
                            if let DataType::Struct(su) = dt_resolved {
                                let names: Vec<String> = su
                                    .members
                                    .iter()
                                    .flat_map(|m| m.declarators.iter().map(|d| d.name.name.clone()))
                                    .collect();
                                if !names.is_empty() {
                                    elab.struct_members.insert(decl.name.name.clone(), names);
                                }
                            }
                        }
                        // §7.8: an ASSOCIATIVE array OF STRUCTS
                        // (`S sa[string]`) — the struct-var path never
                        // registered the container, so `num()/exists()/
                        // foreach` all treated `sa` as a scalar while the
                        // composed element writes worked.
                        if matches!(dt_resolved, DataType::Struct(_)) {
                            if let Some(UnpackedDimension::Associative {
                                data_type: key_dt, ..
                            }) = decl.dimensions.first()
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
                            }
                        }
                        // Per-field packed-array element widths so that
                        // `obj.field[i]` slices instead of bit-selects when
                        // the field is `logic [3:0][7:0] field;`. Walks
                        // struct members directly (skipping nested recursion
                        // for now — covers the most common case).
                        if let DataType::Struct(su) = dt_resolved {
                            for m in &su.members {
                                // §7.2.1: a DYNAMIC member (`int d[]` /
                                // `int q[$]` / `int a[key_t]`) is its own
                                // collection object under "var.member".
                                // Unregistered, `new[n]`, `.size()` and
                                // `push_back` on the member silently no-op'd
                                // (size read 0 while direct element writes
                                // worked) — the whole struct-with-dynamic-
                                // member family was broken.
                                for mdecl in &m.declarators {
                                    let dyn_dim = mdecl.dimensions.first().filter(|d| {
                                        matches!(
                                            d,
                                            UnpackedDimension::Unsized(_)
                                                | UnpackedDimension::Queue { .. }
                                                | UnpackedDimension::Associative { .. }
                                        )
                                    });
                                    if let Some(dyn_dim) = dyn_dim {
                                        let key = format!("{}.{}", decl.name.name, mdecl.name.name);
                                        let mw = resolve_type_width(
                                            &m.data_type,
                                            Some(&elab.parameters),
                                            Some(&elab.typedefs),
                                        )
                                        .max(1);
                                        match dyn_dim {
                                            UnpackedDimension::Associative {
                                                data_type: kdt,
                                                ..
                                            } => {
                                                let is_str = kdt.as_ref().is_some_and(|dt| {
                                                    matches!(
                                                        dt.as_ref(),
                                                        DataType::Simple {
                                                            kind: SimpleType::String,
                                                            ..
                                                        }
                                                    )
                                                });
                                                elab.associative_arrays.insert(key, is_str);
                                            }
                                            _ => {
                                                elab.dynamic_arrays.insert(key.clone());
                                                if matches!(
                                                    dyn_dim,
                                                    UnpackedDimension::Queue { .. }
                                                ) {
                                                    elab.queue_vars.insert(key.clone());
                                                }
                                                if let UnpackedDimension::Queue {
                                                    max_size: Some(ms),
                                                    ..
                                                } = dyn_dim
                                                {
                                                    if let Some(n) = const_eval_i64_with_params(
                                                        ms,
                                                        Some(&elab.parameters),
                                                    )
                                                    .filter(|n| *n >= 0)
                                                    {
                                                        elab.queue_max_sizes
                                                            .insert(key.clone(), (n + 1) as u32);
                                                    }
                                                }
                                                elab.arrays.insert(key, (0, 63, mw));
                                            }
                                        }
                                    }
                                }
                                let (ew, fd) = packed_member_meta(
                                    &m.data_type,
                                    &elab.parameters,
                                    &elab.typedefs,
                                    &elab.typedef_types,
                                );
                                if let Some(ew) = ew {
                                    for mdecl in &m.declarators {
                                        let key = format!("{}.{}", decl.name.name, mdecl.name.name);
                                        elab.packed_signal_elem_widths.insert(key, ew);
                                    }
                                }
                                if let Some(fdims) = fd {
                                    for mdecl in &m.declarators {
                                        let key = format!("{}.{}", decl.name.name, mdecl.name.name);
                                        elab.packed_full_dims.insert(key, fdims.clone());
                                    }
                                }
                                // §7.4.2: member is a packed array of packed struct
                                // (`row_entry_t [1:0] sub_list;`). Register the
                                // ELEMENT-relative field layout + element width +
                                // full dims under `decl.member`, so indexed member
                                // paths (`main.sub_list[i].f`) and element selects
                                // (`main.sub_list[i]`) resolve at runtime.
                                if let Some((dims, elem_dt)) = packed_struct_array_info(
                                    &m.data_type,
                                    &elab.parameters,
                                    &elab.typedef_types,
                                ) {
                                    let elem_fields = flatten_struct_fields(
                                        &elem_dt,
                                        &elab.parameters,
                                        &elab.typedefs,
                                        &elab.typedef_types,
                                    )
                                    .unwrap_or_default();
                                    let elem_w = elem_fields
                                        .iter()
                                        .map(|(_, o, w)| o + w)
                                        .max()
                                        .unwrap_or(0);
                                    if elem_w > 0 {
                                        let mut fdims = dims.clone();
                                        fdims.push((elem_w as i64 - 1, 0));
                                        for mdecl in &m.declarators {
                                            let key =
                                                format!("{}.{}", decl.name.name, mdecl.name.name);
                                            elab.packed_signal_elem_widths
                                                .insert(key.clone(), elem_w);
                                            elab.packed_full_dims
                                                .insert(key.clone(), fdims.clone());
                                            elab.packed_struct_fields
                                                .insert(key, elem_fields.clone());
                                        }
                                    }
                                }
                            }
                        }
                        if let DataType::Struct(su) = dt_resolved {
                            let _is_union = matches!(su.kind, StructUnionKind::Union);
                            if su.packed {
                                for member in &su.members {
                                    for mdecl in &member.declarators {
                                        if mdecl.init.is_some() {
                                            return Err(format!(
                                                "Packed struct member '{}.{}' cannot have a default value (IEEE 7.2.2)",
                                                decl.name.name, mdecl.name.name
                                            ));
                                        }
                                    }
                                }
                                // packed_struct_fields already populated by flatten_struct_fields above.
                            }
                            if !su.packed {
                                // Pre-register member signals with their declared widths,
                                // so later assignments from wider rvalues don't widen them.
                                // Recursive: an array member expands per element and a
                                // nested packed member gets its own slice layout, so
                                // `c.nodes[1].status` addresses its own signal.
                                register_unpacked_aggregate(
                                    &mut elab,
                                    &decl.name.name,
                                    &dd.data_type,
                                );
                                let mut stmts: Vec<Statement> = Vec::new();
                                for member in &su.members {
                                    for mdecl in &member.declarators {
                                        if let Some(init) = &mdecl.init {
                                            let lval = Expression::new(
                                                ExprKind::MemberAccess {
                                                    expr: Box::new(make_ident_expr(
                                                        &decl.name.name,
                                                    )),
                                                    member: mdecl.name.clone(),
                                                },
                                                Span::dummy(),
                                            );
                                            stmts.push(Statement::new(
                                                StatementKind::BlockingAssign {
                                                    lvalue: lval,
                                                    rvalue: init.clone(),
                                                },
                                                Span::dummy(),
                                            ));
                                        }
                                    }
                                }
                                if !stmts.is_empty() {
                                    elab.initial_blocks.push(InitialBlock {
                                        stmt: Statement::new(
                                            StatementKind::SeqBlock { name: None, stmts: stmts.into() },
                                            Span::dummy(),
                                        ),
                                        scope: String::new(),
                                    });
                                }
                            }
                        }
                    }
                }
            }
            ModuleItem::ParameterDeclaration(pd) | ModuleItem::LocalparamDeclaration(pd) => {
                // §6.20.3 body type parameter (`localparam type T1 = logic [A-1:0];`)
                // — register as a typedef so `T1 x;` / `$bits(T1)` resolve.
                if let ParameterKind::Type { assignments } = &pd.kind {
                    for a in assignments {
                        if let Some(dt) = &a.init {
                            let w = resolve_type_width(
                                dt,
                                Some(&elab.parameters),
                                Some(&elab.typedefs),
                            );
                            typedefs_insert_traced(
                                &mut elab.typedefs,
                                "insert:type_param_body",
                                a.name.name.clone(),
                                w,
                            );
                            elab.typedef_types.insert(a.name.name.clone(), dt.clone());
                            // §6.24.1: a cast to the type parameter in a constant
                            // expression (`T'(45)`) reads its declared type from the
                            // shape table, like a typedef.
                            tls_register_typedef_shape(&a.name.name, dt, &[]);
                            register_anonymous_enum_members(dt, &mut elab);
                            sync_typedefs_tls(&elab.typedefs);
                        }
                    }
                }
                if let ParameterKind::Data {
                    data_type,
                    assignments,
                } = &pd.kind
                {
                    let mut width =
                        resolve_type_width(data_type, Some(&elab.parameters), Some(&elab.typedefs));
                    // §6.20.2: resolve through typedefs — a parameter declared
                    // with a typedef'd SIGNED type (`typedef logic signed [1:0]
                    // T; localparam T C = …`) must read the typedef's sign.
                    let mut signed = is_type_signed_resolved(data_type, &elab.typedef_types);
                    let is_real = is_type_real_resolved(data_type, &elab.typedef_types);
                    // A `string` parameter renders as text (`%p` quotes it).
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
                    // IEEE 1800-2017 §6.20.2: an implicit-typed parameter takes
                    // the type of its VALUE. Width is refined per-assignment
                    // below (sized literal keeps its own width); signedness
                    // likewise — see `untyped_param_is_signed`.
                    let implicit_untyped = matches!(data_type, DataType::Implicit { dimensions, .. } if dimensions.is_empty());
                    if implicit_untyped {
                        width = 32;
                        // `localparam unsigned U = -4'sd1` is unsigned (15).
                        signed = !matches!(
                            data_type,
                            DataType::Implicit {
                                signing: Some(Signing::Unsigned),
                                ..
                            }
                        );
                    }
                    for assign in assignments {
                        // The pre-seed exemption only vouches for the
                        // parameter's OWN fixpoint-seeded value. If the name
                        // has a recorded declaration site by now, something
                        // else (an enum member, an imported symbol) declared
                        // it first — the pre-seed merely overwrote it, and
                        // consuming the exemption silently accepted e.g.
                        // `typedef enum {BUSY} …; parameter int BUSY = 5;`,
                        // which every other simulator rejects.
                        let self_seeded = preseed_dup_exempt.remove(&assign.name.name)
                            && !elab.decl_sites.contains_key(&assign.name.name);
                        if (elab.signals.contains_key(&assign.name.name)
                            || elab.parameters.contains_key(&assign.name.name))
                            && !self_seeded
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
                        // IEEE 1800-2023: keyed assignment-pattern init for
                        // §6.16: remember STRING-typed parameters so const-eval
                        // treats `{A, B}` over them as text concatenation.
                        if matches!(
                            data_type,
                            DataType::Simple {
                                kind: SimpleType::String,
                                ..
                            }
                        ) {
                            tls_register_string_param(&assign.name.name);
                        }
                        // §6.20.2 unpacked-array parameter in a module BODY
                        // (`localparam int A [0:2] = '{7,8,9};`) — only the
                        // header pass called register_array_param, so a body
                        // decl fell to the scalar path and every element read
                        // 0. Same registration as the header site.
                        if !assign.dimensions.is_empty() {
                            if register_array_param(
                                &mut elab,
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
                        // associative-array typed parameters. Materialize
                        // `'{ "K": V, ... }` as `<param>["K"]` signals so
                        // `WEIGHT["HIGH"]` reads back the supplied value.
                        //
                        // An index-keyed pattern on a MULTI-DIM PACKED vector
                        // (`parameter bit [1:0][7:0] K = '{1: v1, 0: v0}`,
                        // §10.9.1) is NOT an associative literal — pack it
                        // by element instead; the assoc materialization
                        // would leave the parameter itself x.
                        if let Some(init) = &assign.init {
                            if let ExprKind::AssignmentPattern(items) =
                                &peel_unpacked_typed_pattern(init).kind
                            {
                                let all_keyed = !items.is_empty()
                                    && items
                                        .iter()
                                        .all(|it| matches!(it, AssignmentPatternItem::Keyed(_, _)));
                                if all_keyed
                                    && pack_packed_vector_pattern(
                                        data_type,
                                        init,
                                        &elab.parameters,
                                        &elab.typedef_types,
                                    )
                                    .is_none()
                                {
                                    elab.associative_arrays
                                        .insert(assign.name.name.clone(), true);
                                    for it in items {
                                        if let AssignmentPatternItem::Keyed(k, v) = it {
                                            let key_str = match &k.kind {
                                                ExprKind::StringLiteral(s) => {
                                                    crate::value::encode_name_key(s).into_owned()
                                                }
                                                _ => eval_const_expr_val(k, &elab.parameters)
                                                    .to_dec_string(),
                                            };
                                            let val_v = eval_param_init(
                                                data_type,
                                                v,
                                                &elab.parameters,
                                                &elab.typedef_types,
                                                width,
                                            );
                                            signals_insert_traced(
                                                &mut elab.signals,
                                                line!(),
                                                format!("{}[{}]", assign.name.name, key_str),
                                                Signal {
                                                    is_const: true,
                                                    name: format!(
                                                        "{}[{}]",
                                                        assign.name.name, key_str
                                                    ).into(),
                                                    width,
                                                    is_signed: signed,
                                                    is_real: false,
                                                    direction: None,
                                                    value: val_v,
                                                    type_name: None,
                                                },
                                            );
                                        }
                                    }
                                    continue;
                                }
                            }
                        }
                        register_packed_param_shape(&mut elab, &assign.name.name, data_type);

                        // IEEE 1800-2017 §6.20: struct/union-typed parameter with
                        // an assignment-pattern value — pack by field offset and
                        // register the field layout so later `P.f` selects work.
                        let struct_fields = flatten_struct_fields(
                            data_type,
                            &elab.parameters,
                            &elab.typedefs,
                            &elab.typedef_types,
                        );

                        let existing_ov = if elab.parameters.contains_key(&assign.name.name)
                            && !preseeded_params.contains(&assign.name.name)
                        {
                            Some(
                                elab.parameters
                                    .get(&assign.name.name)
                                    .cloned()
                                    .unwrap_or(Value::zero(width)),
                            )
                        } else {
                            None
                        };
                        let prebound_init: Option<Expression> = assign
                            .init
                            .as_ref()
                            .filter(|init| existing_ov.is_none() && expr_mentions_bits(init))
                            .map(|init| {
                                let via_signals = prebind_bits_of_signals(
                                    init,
                                    &elab.signals,
                                    &elab.parameters,
                                    "",
                                    &elab.typedefs,
                                    &elab.typedef_types,
                                    &elab.packed_struct_fields,
                                    &elab.arrays,
                                );
                                if expr_mentions_bits(&via_signals) {
                                    let mut decls = HashMap::default();
                                    let mut elem_decls = HashMap::default();
                                    collect_declared_types(
                                        module.ports(),
                                        module.items(),
                                        &mut decls,
                                        &mut elem_decls,
                                    );
                                    prebind_bits_from_declared_types(
                                        &via_signals,
                                        &decls,
                                        &elem_decls,
                                        &elab.parameters,
                                        &elab.typedefs,
                                        &elab.typedef_types,
                                    )
                                } else {
                                    via_signals
                                }
                            });
                        let res = resolve_param_decl_value(
                            &mut elab,
                            data_type,
                            prebound_init.as_ref().or(assign.init.as_ref()),
                            assign.init.as_ref(),
                            existing_ov.as_ref(),
                            width,
                            signed,
                            is_real,
                            ParamDeclPolicy {
                                unresolved_call: UnresolvedCallPolicy::DeferZero {
                                    name: &assign.name.name,
                                },
                                promote_implicit_real: true,
                                narrow_implicit_string_lit: false,
                                force_signed_on_override: true,
                                eval_packed_aggregate: true,
                                require_known_idents: false,
                                signed_from_pkg_helper: false,
                            },
                        );
                        let mut current_width = res.width;
                        let current_is_real = res.is_real;
                        let mut current_signed = res.signed;
                        let mut val = res.val;

                        // §6.20.2: an implicit-type parameter takes the SELF-
                        // DETERMINED size of its init; an unbased-unsized
                        // literal is 1 bit, so `parameter P = '1` is 1'b1 (a
                        // reference-simulator-verified reading: `wire [3:0] w
                        // = P;` yields 4'b0001, NOT a fill).
                        if matches!(data_type, DataType::Implicit { dimensions, .. } if dimensions.is_empty())
                            && !elab.parameters.contains_key(&assign.name.name)
                        {
                            if let Some(init) = &assign.init {
                                if let ExprKind::Number(NumberLiteral::UnbasedUnsized(c)) =
                                    &init.kind
                                {
                                    val = Value::fill_of(*c);
                                    val.is_fill = false; // materialize at 1 bit
                                    // The registered signal must match, or a
                                    // signed-32 declared shell sign-extends the
                                    // 1-bit payload at consumers.
                                    current_width = 1;
                                    current_signed = false;
                                }
                            }
                        }

                        if let Some(fields) = struct_fields {
                            tls_register_struct_layout(&assign.name.name, &fields);
                            elab.packed_struct_fields
                                .entry(assign.name.name.clone())
                                .or_insert(fields);
                        }
                        if !elab.parameters.contains_key(&assign.name.name) {
                            elab.set_param(line!(), assign.name.name.clone(), val.clone());
                        }

                        // Also add as a signal so it can be read in expressions
                        signals_insert_traced(
                            &mut elab.signals,
                            line!(),
                            assign.name.name.clone(),
                            Signal {
                                is_const: false,
                                name: assign.name.name.clone().into(),
                                width: current_width,
                                is_signed: current_signed,
                                is_real: current_is_real,
                                direction: None,
                                value: val,
                                type_name: get_type_name(data_type),
                            },
                        );
                    }
                }
            }
            ModuleItem::TypedefDeclaration(td) => {
                // §6.18: a typedef may not reuse a name already declared as a
                // variable/net/port in the same scope (reference: "'T' already
                // declared as a non-typedef"). Forward declarations and the
                // legal restatement of a forward name are exempt (they pass
                // through process_typedef's own handling).
                if !td.forward && elab.typed_decls.contains_key(&td.name.name) {
                    return Err(duplicate_decl_error(
                        &elab,
                        &td.name.name,
                        td.name.span,
                        "typedef",
                    ));
                }
                // IEEE 1800-2017 §7.2.1: a struct/union may not contain a member
                // of its own type (it would have infinite size). Reject with a
                // clean diagnostic instead of recursing into a stack overflow.
                if let Some(cycle) =
                    struct_typedef_self_reference(&td.name.name, &td.data_type, &elab.typedef_types)
                {
                    // An empty path means the cycle closed through typedef
                    // ALIASES only (`typedef T1 T2; typedef T2 T1;`) with no
                    // struct member on the way — a circular definition rather
                    // than a self-containing struct. Say which it is.
                    return Err(if cycle.is_empty() {
                        format!(
                            "type '{}' is defined circularly (its definition resolves \
                             back to itself) — IEEE 1800-2017 §6.18",
                            td.name.name
                        )
                    } else {
                        format!(
                            "type '{}' contains a member of its own type via '{}' \
                             — recursive struct/union is illegal (IEEE 1800-2017 §7.2.1)",
                            td.name.name, cycle
                        )
                    });
                }
                process_local_typedef(td, &mut elab);
            }
            ModuleItem::TimeunitsDecl(td) => {
                if let Some(u) = &td.unit {
                    elab.timeunit_exp = time_literal_to_exp(u);
                }
                if let Some(p) = &td.precision {
                    elab.timeprecision_exp = time_literal_to_exp(p);
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
                check_non_class_null_return(fd)?;
                if sub_default_static
                    && fd.lifetime != Some(Lifetime::Automatic)
                    && fd.name.scopes.is_empty()
                {
                    let mod_name = elab.name.clone();
                    check_implicit_static_inits(
                        &fd.items,
                        &elab,
                        StaticInitScope {
                            kind: "function",
                            name: &fd.name.name.name,
                            owner_kind: "module",
                            owner: &mod_name,
                        },
                    )?;
                }
                // Out-of-class method definitions (`function Class::method`)
                // have `scope.is_some()` — they belong in the class, not in
                // the module's free-function namespace. Inserting them here
                // silently overrides same-named free functions, so a bare call
                // dispatches the class body without `this` binding.
                if fd.name.scopes.is_empty() {
                    elab.functions.insert(fd.name.name.name.clone(), fd.clone());
                }
            }
            ModuleItem::TaskDeclaration(td) => {
                if sub_default_static
                    && td.lifetime != Some(Lifetime::Automatic)
                    && td.name.scopes.is_empty()
                {
                    let mod_name = elab.name.clone();
                    check_implicit_static_inits(
                        &td.items,
                        &elab,
                        StaticInitScope {
                            kind: "task",
                            name: &td.name.name.name,
                            owner_kind: "module",
                            owner: &mod_name,
                        },
                    )?;
                }
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
                // Out-of-class method definitions (`task Class::method`) have
                // `scope.is_some()` — they belong in the class, not in the
                // module's free-task namespace. Inserting them here silently
                // overrides same-named free tasks (e.g. `task run_test` in
                // uvm_globals.svh is replaced by `task uvm_root::run_test`),
                // so a bare `run_test()` dispatches the class body without
                // `this` binding and crashes.
                if td.name.scopes.is_empty() {
                    // §3.3 one task per name per scope — the reference rejects
                    // a redefinition; silently letting the later one win made
                    // every call dispatch the wrong body.
                    if elab.tasks.contains_key(&td.name.name.name)
                        && !elab.pkg_subr_owner.contains_key(&td.name.name.name)
                    {
                        return Err(duplicate_decl_error(
                            &elab,
                            &td.name.name.name,
                            td.name.name.span,
                            "task",
                        ));
                    }
                    elab.note_decl_site(&td.name.name.name, td.name.name.span, "task", true);
                    elab.tasks.insert(td.name.name.name.clone(), td.clone());
                }
            }
            ModuleItem::AliasDecl(terms) => {
                // §10.11: resolve each term to a flat name; widths must
                // agree. The whole statement names ONE physical net, so it
                // is recorded as a GROUP (see `alias_groups`).
                let Ok(names) = alias_term_names(terms) else {
                    return Err(
                        "alias operands must be plain nets (IEEE 1800-2017 \u{00a7}10.11)"
                            .to_string(),
                    );
                };
                if names.len() != terms.len() {
                    return Err(
                        "alias operands must be plain nets (IEEE 1800-2017 \u{00a7}10.11)"
                            .to_string(),
                    );
                }
                let w0 = names
                    .first()
                    .and_then(|n| elab.signals.get(n))
                    .map(|s| s.width);
                for n in &names[1..] {
                    let w = elab.signals.get(n).map(|s| s.width);
                    if w0.is_some() && w.is_some() && w != w0 {
                        return Err(format!(
                            "alias operands must have identical widths ('{}': {:?} vs {:?}) — IEEE 1800-2017 \u{00a7}10.11",
                            n, w0, w
                        ));
                    }
                }
                elab.alias_groups.push(names);
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
                    if !expand_whole_array_assign(lhs, &rhs_final, delay, &delay_exprs, &mut elab) {
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
                // Synthesise a continuous-assign equivalent for each gate
                // (and/or/xor/nand/nor/xnor/buf/not). The top items loop
                // dropped these on the floor previously, which left every
                // gate output stuck at its X default.
                gate_inst_to_assigns(gi, &mut elab);
            }
            ModuleItem::AlwaysConstruct(ac) => {
                // §21.2.1.7: include generate block scope in the instance path for %m.
                // If this always block was inside a generate block, ac.gen_scope
                // contains the generate block's scope name and should be included
                // in the block's scope.
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
                    eprintln!("[xezim][elab] elaborate_items: pushing initial (top-level path)");
                }
                // §21.2.1.7: include generate block scope in the instance path for %m.
                elab.initial_blocks.push(InitialBlock {
                    stmt: ic.stmt.clone(),
                    scope: ic.gen_scope.clone(),
                });
            }
            // LRM §16.5: module-level `assert/assume/cover property (…)`.
            // Previously the elaborator ignored AssertionItem entirely,
            // so a top-level concurrent assertion did nothing. Hoist it
            // into a synthetic initial block: the simulator's
            // AssertionStatement handler then registers it (for
            // is_property: true → SvaClocked, the executor adds a
            // clocked-site that fires every clock cycle).
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
                // LRM §9.2.3 — `final` executes once after the event loop
                // exits (e.g. on $finish). Collected here; the simulator drains
                // `final_blocks` before VCD/coverage flush.
                // §24.9 — a final block runs like a function: nonblocking
                // assignments are illegal inside it. Reject at elaboration.
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
            ModuleItem::GenerateRegion(gr) => {
                // Recursively process generate region items. A region is not
                // a scope (§27.3).
                elaborate_items(&gr.items, &mut elab, cls_defs)?;
            }
            ModuleItem::GenerateIf(gi) => {
                elaborate_generate_if(gi, &mut elab, cls_defs)?;
            }
            ModuleItem::GenerateCase(gc) => {
                elaborate_generate_case(gc, &mut elab, cls_defs)?;
            }
            ModuleItem::GenerateFor(gf) => {
                elaborate_generate_for(gf, &mut elab, cls_defs)?;
            }
            ModuleItem::CovergroupDeclaration(cg) => {
                elab.covergroups.insert(cg.name.name.clone(), cg.clone());
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
                register_class_enum_members(cd, &mut elab);
                register_class_covergroups(cd, &mut elab);
                register_class_scoped_typedef_aliases(cd, None, &mut elab);
                let mut ec = elaborate_class_with_params(cd, Some(&elab.parameters));
                // A module-scope class remembers its module (issue #155).
                ec.declaring_module = Some(module.name().to_string());
                let cls = std::sync::Arc::new(ec);
                elab.classes.insert(cd.name.name.clone(), cls);
                register_nested_classes(cd, &cd.name.name, &mut elab);
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
                    register_sva_port_defaults(&mut elab, &sd.name.name, &sd.port_defaults);
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
                    register_sva_port_defaults(&mut elab, &pd.name.name, &pd.port_defaults);
                }
            }
            // LRM §17.2 — register the checker name and store its
            // declaration so instantiations can inline the body with
            // formal→actual port substitution. When the checker has
            // no formal ports, also inline the body at the declaration
            // site (the legacy "always-on" shape).
            ModuleItem::CheckerDeclaration(cd) => {
                elab.sequences.insert(cd.name.name.clone());
                elab.checker_decls.insert(cd.name.name.clone(), cd.clone());
                let has_ports = !matches!(cd.ports, crate::ast::module::PortList::Empty);
                if !has_ports {
                    let body = cd.items.clone();
                    elaborate_items(&body, &mut elab, all_defs)?;
                }
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
                elaborate_module_paths(&mut elab, &sb.paths, &delay_vals, &|e| e.clone());
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
                        &mut elab,
                        &sb.timing_checks,
                        "",
                        &def_name,
                        &timing_consts,
                        &|e| e.clone(),
                    );
                }
            }
            ModuleItem::ModuleInstantiation(inst) => {
                for hi in &inst.instances {
                    // Register the instance name so it's recognized during validation.
                    // It will be fully elaborated during inlining.
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
                                is_real: false,
                                direction: None,
                                value: Value::new(1),
                                type_name: Some(inst.module_name.name.clone()),
                            },
                        );
                    }
                }
            }
            ModuleItem::ImportDeclaration(imp) => {
                if let Some(defs) = all_defs {
                    process_import(imp, &mut elab, defs, false)?;
                }
            }
            ModuleItem::DPIImport(di) => {
                register_dpi_import(di, &mut elab, None)?;
            }
            ModuleItem::DPIExport(e) => {
                register_dpi_export(e, &mut elab);
            }
            ModuleItem::OutOfClassConstraint {
                class_name,
                constraint_name,
                items,
            } => {
                elab.out_of_class_constraints
                    .insert((class_name.clone(), constraint_name.clone()));
                install_ooc_constraint_body(&mut elab, class_name, constraint_name, items);
            }
            _ => {}
        }
    }

    // §6.20 — parameters whose initializer referenced a parameter declared
    // LATER in the module. The walk above evaluates each one where it appears,
    // so `localparam A = $clog2(B) - 6;` ahead of `localparam B = 4096;` saw
    // nothing for B, fell back to 0, and produced -6 — read back unsigned that
    // is 4294967290, which becomes a `[4294967289:0]` packed range and
    // collapses the whole bus to ONE BIT. The only symptom is a width warning;
    // the design then simulates wrongly. A reference simulator resolves the
    // declarations order-independently.
    // §6.6.7 user-defined nettype drivers are NOT resolved here. A nettype net
    // can be driven from several module INSTANCES through ports — the
    // loading-effect topology user-defined nettypes exist for — and those
    // drivers only land on the net during `inline_instantiations`, which runs
    // after this. Child module bodies also come in through `inline_module_items`
    // rather than this function, so their drivers are not even visible yet.
    //
    // Folding the locally visible drivers now would resolve them separately
    // from the inlined ones and then resolve the two results again — correct
    // only for an additive resolver, wrong for any other.
    //
    // Publish the registry instead; `resolve_user_nettype_drivers` folds each
    // net's whole driver set once, after inlining. (The registry itself was
    // published right after the pre-pass above, before the items were walked,
    // so that a generate-scope declaration could recognise the nettype.)

    // §7.2.2: whole-struct continuous assigns expand member-wise.
    // §35.5.4: an `export "DPI-C"` declared in a package this module never
    // imports still names a GLOBAL C symbol. Register it under the
    // package-qualified subroutine name (with its C alias) and bring the
    // subroutine in under that key so the callback can reach it.
    if let Some(defs) = all_defs {
        let mut pkg_names: Vec<&String> = defs
            .iter()
            .filter(|(_, d)| matches!(d, Definition::Package(_)))
            .map(|(n, _)| n)
            .collect();
        pkg_names.sort();
        for pname in pkg_names {
            let Some(Definition::Package(p)) = defs.get(pname) else {
                continue;
            };
            for item in &p.items {
                let crate::ast::decl::PackageItem::DPIExport(e) = item else {
                    continue;
                };
                let sv = dpi_proto_sv_name(&e.proto);
                let q = format!("{}::{}", pname, sv);
                if elab.dpi_exports.contains(&sv) || elab.dpi_exports.contains(&q) {
                    continue;
                }
                let mut found = false;
                for it in &p.items {
                    match it {
                        crate::ast::decl::PackageItem::Task(td) if td.name.name.name == sv => {
                            elab.tasks.entry(q.clone()).or_insert_with(|| td.clone());
                            found = true;
                        }
                        crate::ast::decl::PackageItem::Function(fd) if fd.name.name.name == sv => {
                            elab.functions
                                .insert_if_absent_with(q.clone(), || fd.clone());
                            found = true;
                        }
                        _ => {}
                    }
                }
                if found {
                    elab.pkg_subr_owner
                        .entry(sv.clone())
                        .or_insert_with(|| pname.clone());
                    elab.dpi_exports.push(q);
                    elab.dpi_export_c_names.push(e.c_name.clone().unwrap_or(sv));
                }
            }
        }
    }
    crate::oom_trace::checkpoint(
        "elaborate.items.ready",
        &[
            ("signals", elab.signals.len()),
            ("signals_capacity", elab.signals.capacity()),
            ("var_decl_types", elab.var_decl_types.len()),
            ("var_types_capacity", elab.var_decl_types.as_map().capacity()),
            ("signal_inline_bytes", std::mem::size_of::<Signal>()),
            ("type_inline_bytes", std::mem::size_of::<DataType>()),
            ("shape_inline_bytes", std::mem::size_of::<StoredDeclShape>()),
        ],
    );
    expand_whole_struct_continuous_assigns(&mut elab);

    // IEEE 1800-2017 §6.10: Implicit nets — identifiers used in continuous assigns
    // or port connections that are not explicitly declared become implicit 1-bit wires.
    let mut port_conn_nets: Vec<String> = Vec::new();
    collect_port_connection_net_candidates(module.items(), &mut port_conn_nets);
    // §6.6.8 coercion: which of those actuals connect to a nettype formal.
    let mut nettype_actuals: HashMap<String, String> = HashMap::default();
    collect_nettype_port_actuals(
        module.items(),
        all_defs,
        &user_nettypes,
        &mut nettype_actuals,
    );
    create_implicit_nets(&mut elab, &port_conn_nets, &nettype_actuals)?;

    // Validate that all identifiers in procedural blocks are declared.
    // §27.6: make every labelled generate block a known SCOPE name before the
    // undeclared-identifier pass. `collect_generate_labels` walks nested
    // regions, so one call over the module's items covers every depth —
    // per-arm registration in the item loop would miss the ones that
    // `elaborate_items` handles on its own recursion.
    crate::oom_trace::checkpoint("elaborate.labels.begin", &[("signals", elab.signals.len())]);
    register_generate_labels(module.items(), &mut elab);
    crate::oom_trace::checkpoint("elaborate.labels.ready", &[("signals", elab.signals.len())]);
    // §23.9: a NAMED block's locals are reachable hierarchically
    // (`nb.q` from a sibling process), so every block label in the module is
    // a legal reference root — collect them all before validating.
    let block_labels: HashSet<String> = {
        fn collect_block_labels(s: &Statement, out: &mut HashSet<String>) {
            match &s.kind {
                StatementKind::SeqBlock { name, stmts }
                | StatementKind::ParBlock { name, stmts, .. } => {
                    if let Some(n) = name {
                        out.insert(n.name.clone());
                    }
                    for c in stmts {
                        collect_block_labels(c, out);
                    }
                }
                StatementKind::If {
                    then_stmt,
                    else_stmt,
                    ..
                } => {
                    collect_block_labels(then_stmt, out);
                    if let Some(e) = else_stmt {
                        collect_block_labels(e, out);
                    }
                }
                StatementKind::Case { items, .. } => {
                    for it in items {
                        collect_block_labels(&it.stmt, out);
                    }
                }
                StatementKind::For { body, .. }
                | StatementKind::While { body, .. }
                | StatementKind::DoWhile { body, .. }
                | StatementKind::Repeat { body, .. }
                | StatementKind::Forever { body }
                | StatementKind::Foreach { body, .. } => collect_block_labels(body, out),
                StatementKind::TimingControl { stmt, .. } | StatementKind::Wait { stmt, .. } => {
                    collect_block_labels(stmt, out)
                }
                _ => {}
            }
        }
        let mut out = HashSet::default();
        for ib in &elab.initial_blocks {
            collect_block_labels(&ib.stmt, &mut out);
        }
        for ab in &elab.always_blocks {
            collect_block_labels(&ab.stmt, &mut out);
        }
        out
    };
    for ib in &elab.initial_blocks {
        validate_stmt_idents(&ib.stmt, &elab, &mut block_labels.clone())?;
    }
    for ab in &elab.always_blocks {
        validate_stmt_idents(&ab.stmt, &elab, &mut block_labels.clone())?;
    }
    for ca in &elab.continuous_assigns {
        validate_expr_idents(&ca.lhs, &elab, &HashSet::default())?;
        validate_expr_idents(&ca.rhs, &elab, &HashSet::default())?;
    }

    crate::oom_trace::checkpoint("elaborate.identifiers.ready", &[("signals", elab.signals.len())]);

    // IEEE 1800-2017 §6.20.6: a `const` variable may be assigned only once, in
    // its declaration. The `validate_stmt_idents` check above exempts a const
    // that carries a (non-constant) declaration initializer — that initializer
    // is lowered to a single synthetic initial-block assignment (its one legal
    // write). Any *further* procedural write is still illegal. Each block that
    // writes a name contributes one entry below (the synthetic init is its own
    // standalone block), so a decl-initialized const written by more than one
    // block has an illegal re-assignment.
    if !elab.const_decl_inits.is_empty() {
        let mut write_block_count: HashMap<String, usize> = HashMap::default();
        for ib in &elab.initial_blocks {
            let mut s = HashSet::default();
            collect_written_idents(&ib.stmt, &mut s);
            for n in s {
                *write_block_count.entry(n).or_default() += 1;
            }
        }
        for ab in &elab.always_blocks {
            let mut s = HashSet::default();
            collect_written_idents(&ab.stmt, &mut s);
            for n in s {
                *write_block_count.entry(n).or_default() += 1;
            }
        }
        for name in &elab.const_decl_inits {
            if write_block_count.get(name).copied().unwrap_or(0) > 1 {
                return Err(format!("Illegal write to constant identifier '{}'", name));
            }
        }
    }

    // §6.18: every bare forward type declaration (`typedef name;`) must resolve
    // to a real data type — a later full typedef, an enum, a class, or a
    // package/interface type. An unresolved forward type is an error.
    for name in &elab.forward_typedef_names {
        let resolved = elab
            .typedef_types
            .get(name)
            .is_some_and(|dt| !matches!(dt, DataType::Void(_)))
            || elab.classes.contains_key(name)
            || elab.enum_members.contains_key(name)
            || elab.packed_struct_fields.contains_key(name);
        if !resolved {
            return Err(format!(
                "Forward typedef '{}' does not resolve to a data type",
                name
            ));
        }
    }

    // IEEE 1800-2017 §6.5: a variable cannot have multiple continuous drivers,
    // nor mix continuous and procedural drivers.
    validate_driver_conflicts(&elab, module, all_defs)?;

    // IEEE 1800-2017 §8.21/§8.26: class instantiation legality.
    let scope_typedefs = all_defs.map(|defs| non_class_typedef_names(defs, &module));
    validate_class_usage(&elab, scope_typedefs.as_ref())?;

    // IEEE 1800-2023 §8.20.5: a derived class may not override a `final`
    // method of any ancestor class; `:extends`/`:initial` markers must
    // agree with the actual override status.
    if sv_parser::is_sv2023() {
        validate_final_method_overrides(&elab)?;
        validate_method_override_markers(&elab)?;
    }

    // IEEE 1800-2017 §9.2.2.4: `always_ff` admits exactly one event
    // control, applied at the outermost level. Nested event/timing
    // control in the body is illegal.
    validate_always_ff_event_controls(&elab)?;
    validate_constant_part_select_bounds(&elab)?;

    // IEEE 1800-2017 §13.5.2: arguments to `ref` formals must be
    // variables (i.e. assignable lvalues), not arbitrary expressions.
    validate_ref_arg_lvalues(&elab)?;

    // LRM §25.4 modport direction enforcement.
    // Done at the AST level over every module Definition (not on the
    // post-inlined `elab`, whose `modport_views` only carries the top
    // module's own modport-bound ports). For each module whose port list
    // contains a `modport_t.view`-typed port, walk that module's body and
    // flag continuous-assign or procedural-assign LHSs of the form
    // `<port_name>.<member>` where `<member>` is declared `input` from
    // the modport's perspective.
    if let Some(defs) = all_defs {
        validate_modport_writes_at_ast(defs)?;
        // Pre-compute the per-`(iface, modport)` member-direction maps so
        // the runtime virtual-interface dispatch can consult them without
        // re-walking interface AST. LRM §25.4.
        for d in defs.values() {
            if let Definition::Package(p) = d {
                for item in &p.items {
                    if let crate::ast::decl::PackageItem::Class(c) = item {
                        elab.class_decl_pkg
                            .insert(c.name.name.clone(), p.name.name.clone());
                    }
                }
            }
            if let Definition::Interface(iface) = d {
                let iface_name = iface.name.name.clone();
                // LRM §25.9: register the interface name so runtime
                // detects virtual-interface task formals.
                elab.interfaces.insert(iface_name.clone());
                let mut defaults: Vec<(String, Option<String>)> = Vec::new();
                for pd in iface.params.iter().filter(|pd| !pd.local) {
                    match &pd.kind {
                        crate::ast::decl::ParameterKind::Data { assignments, .. } => {
                            for a in assignments {
                                let d = a
                                    .init
                                    .as_ref()
                                    .and_then(|e| const_eval_i64_with_params(e, None))
                                    .map(|n| n.to_string());
                                defaults.push((a.name.name.clone(), d));
                            }
                        }
                        crate::ast::decl::ParameterKind::Type { assignments } => {
                            for a in assignments {
                                let d = a.init.as_ref().and_then(data_type_to_spec_fragment);
                                defaults.push((a.name.name.clone(), d));
                            }
                        }
                    }
                }
                elab.interface_param_defaults
                    .insert(iface_name.clone(), defaults);
                for item in &iface.items {
                    if let ModuleItem::ModportDeclaration(md) = item {
                        for mp in &md.items {
                            let mut dirs = HashMap::default();
                            for p in &mp.ports {
                                dirs.insert(p.name.name.clone(), p.direction);
                            }
                            elab.modport_member_dirs
                                .insert((iface_name.clone(), mp.name.name.clone()), dirs);
                        }
                    }
                }
            }
        }
    }

    // IEEE 1800-2017 §6.19.3: an assignment to an enum-typed variable
    // requires the RHS value (when constant) to be one of the typedef's
    // declared members. Casts bypass the check.
    validate_enum_assignments(&elab)?;

    register_nd_struct_array_members(&mut elab);

    null_init_class_handles(&mut elab);

    // LRM §20.7 — populate ARRAYS_TLS so any subsequent const-eval
    // (parameter-default rewrite, runtime const eval, etc.) of
    // `$size`/`$left`/`$right`/`$high`/`$low`/`$dimensions` on an array
    // identifier resolves. Mirrors the TYPEDEFS_TLS refresh inside
    // process_typedef.
    {
        let mut snapshot: HashMap<String, (i64, i64, u32)> = HashMap::default();
        for (k, &v) in &elab.arrays {
            snapshot.insert(k.clone(), v);
        }
        ARRAYS_TLS.with(|cell| {
            *cell.borrow_mut() = Some(snapshot);
        });
    }

    // LRM §24: when the elaboration root is a `program` declaration, its
    // initial blocks belong to the reactive region. Re-route them so the
    // simulator schedules their statements via `pending_reactive`.
    if matches!(module, Definition::Program(_)) {
        elab.materialize_pending();
        let initials = std::mem::take(&mut elab.initial_blocks);
        elab.program_initial_blocks.extend(initials);
    }

    check_packed_widths()?;
    Ok(elab)
}
