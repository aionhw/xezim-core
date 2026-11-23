use super::*;

type BindResolveStep<'a> = dyn FnMut(
    &mut ElaboratedModule,
) -> Result<Vec<(String, Vec<crate::ast::decl::BindDirective>)>, String>
    + 'a;

struct PortElisionGuard;
impl Drop for PortElisionGuard {
    fn drop(&mut self) {
        PORT_ELISION_DOTTED.with(|d| *d.borrow_mut() = None);
    }
}

/// Handles recursive/multi-level hierarchies by walking all levels depth-first.
pub fn inline_instantiations(
    elab: &mut ElaboratedModule,
    definitions: &HashMap<String, Definition>,
) -> Result<(), String> {
    inline_instantiations_core(elab, definitions, None).map(|_| ())
}

/// Inline the hierarchy rooted at `elab.name` and resolve any nested `bind`
/// fixed-point incrementally on newly introduced targets. Returns `Ok(true)` if
/// a rare cross-pass edge case requires a full root rebuild from the populated
/// `elab.resolved_binds`.
pub(crate) fn inline_instantiations_with_binds(
    elab: &mut ElaboratedModule,
    definitions: &HashMap<String, Definition>,
    unit_binds: &[crate::ast::decl::BindDirective],
    resolve_step: &mut BindResolveStep<'_>,
) -> Result<bool, String> {
    inline_instantiations_core(elab, definitions, Some((unit_binds, resolve_step)))
}

fn inline_instantiations_core(
    elab: &mut ElaboratedModule,
    definitions: &HashMap<String, Definition>,
    bind_driver: Option<(&[crate::ast::decl::BindDirective], &mut BindResolveStep<'_>)>,
) -> Result<bool, String> {
    let _oom_trace = crate::oom_trace::session();
    PACKED_WIDTH_ERROR.with(|slot| slot.take());
    let _oom_inline = crate::oom_trace::scope("inline hierarchy", "", &elab.name, &elab.name);
    port_elision_setup();
    let _port_elision_guard = PortElisionGuard;
    let needs_rebuild = inline_instantiations_inner(elab, definitions, bind_driver)?;
    if needs_rebuild {
        return Ok(true);
    }
    elab.elided_port_hashes.sort_unstable();
    elab.elided_port_hashes.dedup();
    // The instances' and interfaces' own arrays, as the top's.
    register_nd_struct_array_members(elab);
    check_packed_widths()?;
    Ok(false)
}

fn inline_instantiations_inner(
    elab: &mut ElaboratedModule,
    definitions: &HashMap<String, Definition>,
    bind_driver: Option<(&[crate::ast::decl::BindDirective], &mut BindResolveStep<'_>)>,
) -> Result<bool, String> {
    let header_values: Vec<_> = definitions
        .get(&elab.name)
        .into_iter()
        .flat_map(|def| def.params())
        .flat_map(|pd| match &pd.kind {
            ParameterKind::Data { assignments, .. } => assignments
                .iter()
                .map(|a| a.name.name.as_str())
                .collect::<Vec<_>>(),
            ParameterKind::Type { .. } => Vec::new(),
        })
        .filter_map(|name| {
            elab.parameters.get(name).map(|value| {
                (
                    name.to_string(),
                    value.clone(),
                    elab.signals.get(name).cloned(),
                )
            })
        })
        .collect();

    let mut imports: Vec<(String, Option<String>)> = Vec::new();
    for (name, def) in definitions {
        match def {
            Definition::Module(d) => {
                for item in &d.items {
                    if let ModuleItem::ImportDeclaration(imp) = item {
                        for ii in &imp.items {
                            imports.push((
                                ii.package.name.clone(),
                                ii.item.as_ref().map(|i| i.name.clone()),
                            ));
                        }
                    }
                }
            }
            Definition::Interface(d) => {
                for item in &d.items {
                    if let ModuleItem::ImportDeclaration(imp) = item {
                        for ii in &imp.items {
                            imports.push((
                                ii.package.name.clone(),
                                ii.item.as_ref().map(|i| i.name.clone()),
                            ));
                        }
                    }
                }
            }
            Definition::Program(d) => {
                for item in &d.items {
                    if let ModuleItem::ImportDeclaration(imp) = item {
                        for ii in &imp.items {
                            imports.push((
                                ii.package.name.clone(),
                                ii.item.as_ref().map(|i| i.name.clone()),
                            ));
                        }
                    }
                }
            }
            // §26.3: a package's OWN imports (a class method / package
            // function in `p` reading a bare name that `p` `import`s) are
            // `PackageItem::Import` items; include them so the runtime can
            // resolve such a bare name to its exporting package.
            Definition::Package(p) => {
                use crate::ast::decl::PackageItem as PI;
                for item in &p.items {
                    if let PI::Import(imp) = item {
                        for ii in &imp.items {
                            imports.push((
                                ii.package.name.clone(),
                                ii.item.as_ref().map(|i| i.name.clone()),
                            ));
                        }
                    }
                }
            }
            _ => {}
        }
        if !imports.is_empty() {
            imports.dedup();
            elab.def_pkg_imports.insert(name.clone(), imports.clone());
            imports.clear();
        }
    }
    // Populate class and covergroup definitions from global scope
    for (name, def) in definitions {
        match def {
            Definition::Class(c) => {
                register_class_enum_members(c, elab);
                register_class_scoped_typedef_aliases(c, None, elab);
                let cls = elaborate_class_with_params(c, Some(&elab.parameters));
                elab.classes.insert(name.clone(), std::sync::Arc::new(cls));
                register_nested_classes(c, name, elab);
            }
            Definition::Covergroup(cg) => {
                elab.covergroups.insert(name.clone(), (*cg).clone());
            }
            Definition::Package(p) => {
                elab.packages.insert(name.clone());
                // Forward-reference fixpoint: package items may reference
                // parameters/localparams declared LATER in include order.
                // black-parrot's bp_common_pkg includes aviary_pkgdef (which has
                // `typedef enum bit [lg_max_cfgs-1:0] {...} bp_params_e;` and
                // `parameter bp_proc_param_s [max_cfgs-1:0] all_cfgs_gp`) BEFORE
                // aviary_cfg_pkgdef (which defines max_cfgs / lg_max_cfgs). A
                // single in-order pass resolves those widths to garbage — the
                // enum collapses to 1 bit and its member values truncate, so the
                // config selector `bp_params_e` is wrong. Pre-resolve parameters
                // and typedefs to a fixpoint first; both paths only overwrite
                // elab.parameters/typedefs/typedef_types/enum_members (idempotent),
                // so repeating is safe and the side-effecting Data initializers in
                // the main pass below run exactly once. Three passes cover the
                // chains here (max_cfgs → lg_max_cfgs → enum width → member values).
                // §13.4.3: package sizing functions must be visible to the
                // parameter passes below.
                for item in &p.items {
                    if let crate::ast::decl::PackageItem::Function(fd) = item
                        && fd.name.scopes.is_empty()
                    {
                        elab.functions
                            .insert_if_absent_with(fd.name.name.name.clone(), || fd.clone());
                    }
                }
                set_funcs_tls(&elab.functions);
                let mut __pkg_imp_overlay = overlay_pkg_params(p, elab);
                for _ in 0..3 {
                    for item in &p.items {
                        match item {
                            crate::ast::decl::PackageItem::Parameter(pd) => {
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
                                    let is_implicit = matches!(data_type, DataType::Implicit { dimensions, .. } if dimensions.is_empty());
                                    for assign in assignments {
                                        if register_visible_array_param(
                                            elab, name, assign, data_type,
                                        ) {
                                            continue;
                                        }
                                        let width = if is_implicit {
                                            assign
                                                .init
                                                .as_ref()
                                                .and_then(|i| {
                                                    untyped_param_width(i, &elab.parameters)
                                                })
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
                                        register_packed_param_index(
                                            elab,
                                            &assign.name.name,
                                            data_type,
                                            None,
                                        );
                                        if let Some(init) = &assign.init {
                                            // §13.4.3 const-function calls.
                                            let subbed_init6;
                                            let init: &Expression = if expr_has_call(init) {
                                                match substitute_const_fn_calls(
                                                    init,Some(&elab.parameters),
                                                    elab,
                                                    0,
                                                )
                                                .filter(|e| !expr_has_call(e))
                                                {
                                                    Some(e) => {
                                                        subbed_init6 = e;
                                                        &subbed_init6
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
                                            alias_pkg_param(elab, name, &assign.name.name, &v);
                                            let scoped = format!("{name}.{}", assign.name.name);
                                            register_pkg_param_elem(elab, "", &scoped, data_type);
                                            __pkg_imp_overlay.push((
                                                assign.name.name.clone(),
                                                elab.parameters.get(&assign.name.name).cloned(),
                                            ));
                                            elab.set_param(line!(), assign.name.name.clone(), v);
                                            // The package's own elaboration records this
                                            // layout; the design top that actually
                                            // simulates the call does not inherit that
                                            // table. Without it `pkg::ENC[i].exp_bits`
                                            // inside a function reads 0.
                                            if let Some(fields) = flatten_struct_fields(
                                                data_type,
                                                &elab.parameters,
                                                &elab.typedefs,
                                                &elab.typedef_types,
                                            ) {
                                                if !fields.is_empty() {
                                                    tls_register_struct_layout(
                                                        &assign.name.name,
                                                        &fields,
                                                    );
                                                    elab.packed_struct_fields.insert(
                                                        assign.name.name.clone(),
                                                        fields,
                                                    );
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            crate::ast::decl::PackageItem::Typedef(td) => {
                                process_typedef(td, elab);
                                register_scoped_typedef_alias(name, td, elab);
                            }
                            _ => {}
                        }
                    }
                }
                // §26.3: record this package's enum members under the package
                // name so `pkg::NAME` stays resolvable when a local
                // declaration shadows the bare `NAME`. Read back out of
                // `enum_members`, which `process_typedef` has just filled with
                // the fully-resolved values (ranges expanded, widths settled).
                for item in &p.items {
                    let crate::ast::decl::PackageItem::Typedef(td) = item else {
                        continue;
                    };
                    if !matches!(td.data_type, DataType::Enum(_)) {
                        continue;
                    }
                    let Some(members) = elab.enum_members.get(&td.name.name).cloned() else {
                        continue;
                    };
                    let w = elab
                        .typedefs
                        .get(&td.name.name)
                        .copied()
                        .unwrap_or(32)
                        .max(1);
                    // §6.19 wide base: the (u64, width) table truncates past
                    // 64 bits, so ALSO park the full Value under the
                    // qualified spelling in `parameters` — the runtime's
                    // qualified lookup consults it first for wide members.
                    if w > 64 {
                        if let DataType::Enum(et) = &td.data_type {
                            for (m, v) in wide_enum_value_map(et, w, &elab.parameters) {
                                elab.set_param(line!(), format!("{}::{}", name, m), v);
                            }
                        }
                    }
                    let slot = elab.package_enum_members.entry(name.clone()).or_default();
                    for (m, v) in members {
                        slot.insert(m, (v, w));
                    }
                }
                for item in &p.items {
                    match item {
                        crate::ast::decl::PackageItem::Covergroup(cg) => {
                            register_package_covergroup(name, cg, elab);
                        }
                        crate::ast::decl::PackageItem::Class(c) => {
                            register_class_enum_members(c, elab);
                            register_class_scoped_typedef_aliases(c, Some(name.as_str()), elab);
                            let cls = std::sync::Arc::new(elaborate_class_with_params(
                                c,
                                Some(&elab.parameters),
                            ));
                            let pkg_scoped = format!("{}::{}", name, c.name.name);
                            elab.classes.insert(pkg_scoped.clone(), cls.clone());
                            elab.classes.insert(c.name.name.clone(), cls);
                            // Register the nested subtree ONCE (under the bare
                            // `Class::Inner ...` keying); the fully-qualified
                            // `pkg::Class::Inner ...` spellings alias the SAME
                            // Arcs, so a class-heavy package tree is not
                            // elaborated once per outer spelling (previously
                            // it was done twice, doubling every inner class).
                            for key in register_nested_classes(c, &c.name.name, elab) {
                                let qualified = format!("{}::{}", name, key);
                                if let Some(existing) = elab.classes.get(&key) {
                                    let arc = existing.clone();
                                    elab.classes.insert(qualified, arc);
                                }
                            }
                        }
                        crate::ast::decl::PackageItem::Typedef(td) => {
                            process_typedef(td, elab);
                            register_scoped_typedef_alias(name, td, elab);
                        }
                        crate::ast::decl::PackageItem::Parameter(pd) => {
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
                                let is_implicit = matches!(data_type, DataType::Implicit { dimensions, .. } if dimensions.is_empty());
                                for assign in assignments {
                                    // §6.20.2: an unpacked-array parameter was
                                    // registered element by element in the
                                    // passes above. `eval_param_value` reads
                                    // the data type alone, without the
                                    // declarator's dimensions, so folding it
                                    // here wrote the bare name as 0.
                                    if !assign.dimensions.is_empty() {
                                        continue;
                                    }
                                    // Implicit-typed param: use the sized-
                                    // literal width from the initializer when
                                    // present, instead of defaulting to 32.
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
                                        // §13.4.3 const-function calls. If the
                                        // call does NOT reduce, skip: evaluating
                                        // it raw yields 0 and CLOBBERS the value
                                        // the package hoist already healed
                                        // (`LOG = LOG2(DEPTH)` went 6 -> 0 here,
                                        // re-shrinking every typedef processed
                                        // after this point).
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
                                                None => continue,
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
                                        __pkg_imp_overlay.push((
                                            assign.name.name.clone(),
                                            elab.parameters.get(&assign.name.name).cloned(),
                                        ));
                                        elab.set_param(line!(), assign.name.name.clone(), v);
                                    }
                                }
                            }
                        }
                        // Package-scope variable declarations. riscv-dv's target
                        // ISA config lives here as dynamic-array / queue globals
                        // (`supported_isa[$] = {RV32I,...}`); without populating
                        // them the generator has nothing to emit. Mirror the
                        // module-scope array-initializer path: register the array
                        // and emit its element initializers as a synthetic
                        // initial block so the runtime assignment machinery fills
                        // it at time 0 (enum members are already in scope, having
                        // been processed from this same package's typedefs).
                        crate::ast::decl::PackageItem::Data(dd) => {
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
                                        &format!("{}::{}", name, decl.name.name),
                                        nt,
                                        Some(&dd.data_type),
                                    );
                                }
                            }
                            // §26.3: keep each package variable's own type even
                            // when its bare name is shared or shadowed.
                            for decl in &dd.declarators {
                                elab.var_decl_types.insert(
                                    format!("{}::{}", name, decl.name.name),
                                    dd.data_type.clone(),
                                );
                            }
                            // §8.25: a package-level class variable keeps its
                            // specialization (`C #(byte) v;`) for `v = new`,
                            // as a module-level one does.
                            if let DataType::TypeReference { type_args, .. } = &dd.data_type
                                && !type_args.is_empty()
                            {
                                for decl in &dd.declarators {
                                    elab.class_type_args
                                        .entry(decl.name.name.clone())
                                        .or_insert_with(|| type_args.clone());
                                    elab.class_type_args.insert(
                                        format!("{}::{}", name, decl.name.name),
                                        type_args.clone(),
                                    );
                                }
                            }
                            let width = resolve_type_width(
                                &dd.data_type,
                                Some(&elab.parameters),
                                Some(&elab.typedefs),
                            );
                            let is_signed =
                                is_type_signed_resolved(&dd.data_type, &elab.typedef_types);
                            for decl in &dd.declarators {
                                // §6.18/§7.4: a variable of an array / queue /
                                // associative TYPEDEF (`aa_t m;`) inherits the
                                // typedef's unpacked dimensions, as the
                                // module-scope path's `effective_dims` does; the
                                // package arm read `decl.dimensions` alone, so
                                // the variable was a scalar of the element type.
                                let typed_decl;
                                // §7.4.5: dimensions on the declarator come
                                // before the typedef's (`fa_t v [0:1]` with
                                // `typedef int fa_t [0:3]` is `int v[0:1][0:3]`).
                                let decl = match &dd.data_type {
                                    DataType::TypeReference {
                                        name: tn,
                                        dimensions: pd,
                                        ..
                                    } if pd.is_empty() => {
                                        match lookup_scoped_type(tn, &elab.typedef_unpacked_dims) {
                                            Some(dims) => {
                                                let mut d = decl.clone();
                                                d.dimensions.extend(dims.iter().cloned());
                                                typed_decl = d;
                                                &typed_decl
                                            }
                                            None => decl,
                                        }
                                    }
                                    _ => decl,
                                };
                                // §26.3: package arrays own their qualified
                                // storage. A module declaration with the same
                                // leaf must not share either cells or shape.
                                let qualified_decl;
                                let decl = if !decl.dimensions.is_empty()
                                    && (elab.local_decl_displaces(&decl.name.name)
                                        || decl.name.name.starts_with(&format!("{}::", name)))
                                {
                                    let mut d = decl.clone();
                                    if !d.name.name.starts_with(&format!("{}::", name)) {
                                        d.name.name = format!("{}::{}", name, decl.name.name);
                                    }
                                    elab.pkg_var_decls.insert(
                                        d.name.name.clone(),
                                        Signal {
                                            is_const: dd.const_kw,
                                            name: d.name.name.clone().into(),
                                            width,
                                            is_signed,
                                            is_real: false,
                                            direction: None,
                                            value: Value::zero(width),
                                            type_name: get_type_name(&dd.data_type),
                                        },
                                    );
                                    qualified_decl = d;
                                    &qualified_decl
                                } else {
                                    decl
                                };
                                // §10.9.1: package array patterns need the same
                                // element type and declared bounds as module arrays.
                                if !decl.dimensions.is_empty() {
                                    elab.var_decl_types
                                        .entry(decl.name.name.clone())
                                        .or_insert_with(|| dd.data_type.clone());
                                    if let Some(dims) =
                                        declared_unpacked_dims(&decl.dimensions, &elab.parameters)
                                    {
                                        register_fixed_unpacked_array(
                                            elab,
                                            &decl.name.name,
                                            &dims,
                                            width,
                                            is_type_two_state_resolved(
                                                &dd.data_type,
                                                &elab.typedef_types,
                                            ),
                                        );
                                    }
                                }
                                let shape_dims = normalize_unpacked_dims(
                                    &decl.dimensions,
                                    &elab.parameters,
                                    &elab.typedef_types,
                                );
                                record_coll_shape(elab, &decl.name.name, &shape_dims, None);
                                // `[N]` sized by a parameter is fixed, not
                                // associative: read the normalized dims (see
                                // the generate-scope path).
                                let first_dim = shape_dims.first();
                                let is_dynamic_dim = first_dim.is_some_and(|d| {
                                    matches!(
                                        d,
                                        UnpackedDimension::Unsized(_)
                                            | UnpackedDimension::Queue { .. }
                                    )
                                });
                                let is_assoc = matches!(
                                    first_dim,
                                    Some(UnpackedDimension::Associative { .. })
                                );
                                if is_dynamic_dim {
                                    elab.dynamic_arrays.insert(decl.name.name.clone());
                                }
                                // Same element-class registration the module-scope
                                // path does — a PACKAGE-level collection of class
                                // handles (`seed_map lookup [string];`, the UVM
                                // seed-pool shape) otherwise had no recorded element
                                // class, so `lookup[k] = new` stored X.
                                if is_dynamic_dim || is_assoc {
                                    if let DataType::TypeReference { name: tn, .. } = &dd.data_type
                                    {
                                        elab.array_elem_class
                                            .insert(decl.name.name.clone(), tn.name.name.clone());
                                    }
                                }
                                if is_assoc {
                                    // The key type was hardcoded non-string here,
                                    // unlike the module-scope path — a package-level
                                    // `[string]` map indexed by a string key then
                                    // hashed through the integer path.
                                    let is_string_key = matches!(
                                        first_dim,
                                        Some(UnpackedDimension::Associative { data_type: Some(kdt), .. })
                                            if matches!(
                                                kdt.as_ref(),
                                                DataType::Simple { kind: SimpleType::String, .. }
                                            )
                                    );
                                    elab.associative_arrays
                                        .insert(decl.name.name.clone(), is_string_key);
                                    // Record the element DataType keyed by the
                                    // base name so an inline `arr[k] = new` can
                                    // resolve the element CLASS from its declared
                                    // type (package-scoped `uvm_seed_map m[string]`
                                    // then `m[k] = new()` stored an opaque handle
                                    // that deref'd null in uvm_create_random_seed).
                                    elab.var_decl_types
                                        .insert(decl.name.name.clone(), dd.data_type.clone());
                                    // §6.8/§7.9.11: `int aa[string] = '{"x": 11}` —
                                    // the initializer runs once before any initial
                                    // block, as a whole-array assignment (the
                                    // module-scope lowering), so keyed items,
                                    // `default:` and struct elements all take the
                                    // runtime pattern machinery. It was dropped.
                                    if let Some(init_expr) = &decl.init {
                                        elab.static_init_blocks.push(InitialBlock {
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
                                // §7.4.2/§7.4.5: a fixed MULTI-dimensional
                                // package array (`int v [0:1][0:3]`, or a
                                // dimensioned typedef plus declarator dims)
                                // registers its whole shape, as the
                                // module-scope path does. Only the first
                                // dimension was registered, so `v[i][j]` was a
                                // bit-select and `foreach (v[i, j])` walked bits.
                                // Read the normalized dimensions: the parser
                                // gives `[N]` as an associative dimension keyed
                                // by "type" `N`, so `d [N][2]` failed this check
                                // and was registered one-dimensional.
                                if shape_dims.len() >= 2
                                    && shape_dims.iter().all(|d| {
                                        matches!(
                                            d,
                                            UnpackedDimension::Range { .. }
                                                | UnpackedDimension::Expression { .. }
                                        )
                                    })
                                {
                                    let shape: Option<Vec<(i64, i64)>> = shape_dims
                                        .iter()
                                        .map(|d| {
                                            extract_array_range(
                                                std::slice::from_ref(d),
                                                &elab.parameters,
                                            )
                                        })
                                        .collect();
                                    if let Some(shape) = shape {
                                        let name = decl.name.name.clone();
                                        if shape.len() == 2 {
                                            elab.arrays_2d
                                                .insert(name.clone(), (shape[0], shape[1], width));
                                        } else {
                                            elab.arrays_nd.insert(name.clone(), (shape, width));
                                        }
                                        if let Some(ud) = declared_unpacked_dims(
                                            &decl.dimensions,
                                            &elab.parameters,
                                        ) {
                                            elab.unpacked_decl_dims.insert(name.clone(), ud);
                                        }
                                        if is_type_two_state_resolved(
                                            &dd.data_type,
                                            &elab.typedef_types,
                                        ) {
                                            elab.two_state_signals.insert(name.clone());
                                        }
                                        elab.var_decl_types
                                            .insert(name.clone(), dd.data_type.clone());
                                        if let Some(init_expr) = &decl.init {
                                            elab.static_init_blocks.push(InitialBlock {
                                                stmt: Statement::new(
                                                    StatementKind::BlockingAssign {
                                                        lvalue: make_ident_expr(&name),
                                                        rvalue: init_expr.as_ref().clone(),
                                                    },
                                                    Span::dummy(),
                                                ),
                                                scope: String::new(),
                                            });
                                        }
                                        continue;
                                    }
                                }
                                // Element reads/writes go through `module.arrays`
                                // (see the Index eval path), so any unpacked array
                                // must be registered there with a backing range —
                                // matching the module-scope path's use of
                                // `extract_array_range` (dynamic/queue → 0..63).
                                if let Some((lo, hi)) =
                                    extract_array_range(&decl.dimensions, &elab.parameters)
                                {
                                    elab.arrays.insert(decl.name.name.clone(), (lo, hi, width));
                                    // §6.8: a 2-state ELEMENT type means the array's
                                    // slots default to 0 (the simulator consults this
                                    // when it builds the element storage).
                                    if is_type_two_state_resolved(
                                        &dd.data_type,
                                        &elab.typedef_types,
                                    ) {
                                        elab.two_state_signals.insert(decl.name.name.clone());
                                    }
                                    if let Some(UnpackedDimension::Range { left, right, .. }) =
                                        first_dim
                                    {
                                        let l = const_eval_i64_with_params(
                                            left,
                                            Some(&elab.parameters),
                                        )
                                        .unwrap_or(0);
                                        let r = const_eval_i64_with_params(
                                            right,
                                            Some(&elab.parameters),
                                        )
                                        .unwrap_or(0);
                                        if l > r {
                                            elab.descending_arrays.insert(decl.name.name.clone());
                                        }
                                    }
                                }
                                // SCALAR package variable (`enum integer {A,B} e = A;`,
                                // `integer n = 42;`): nothing below handles it — the
                                // arm only registered arrays, so the signal never
                                // existed, its initializer never applied (`P::e`
                                // read x), and an anonymous enum's members/methods
                                // had no registration (`P::e.first` was empty).
                                // Mirror the module-scope declaration path.
                                if decl.dimensions.is_empty() {
                                    register_anonymous_enum_members(&dd.data_type, elab);
                                    let is_anon_enum =
                                        anon_enum_members_ordered(&dd.data_type, &elab.parameters);
                                    if let Some(members) = &is_anon_enum {
                                        elab.enum_members
                                            .insert(decl.name.name.clone(), members.clone());
                                    }
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
                                    let w = width.max(1);
                                    let is_real =
                                        is_type_real_resolved(&dd.data_type, &elab.typedef_types);
                                    // `C c = new;` cannot const-evaluate — run
                                    // it as a static init (same machinery the
                                    // array initializers use) so `P::c.f1()`
                                    // has a live handle. NOTE: no-parens `new`
                                    // parses as a bare IDENT, not a Call, so
                                    // expr_has_call alone misses it.
                                    // §6.21: a CLASS-typed package variable
                                    // initialized from ANOTHER package
                                    // variable (`uvm_printer uvm_default_printer
                                    // = uvm_default_table_printer;`) carries a
                                    // HANDLE that only exists at runtime —
                                    // const-eval stored 0 and the alias read
                                    // null (UVM 1.2 hello_world died on
                                    // `uvm_default_printer.knobs`). Route any
                                    // class-typed initializer through the
                                    // static-init machinery; source order
                                    // keeps the referenced var initialized
                                    // first.
                                    let class_typed = matches!(
                                        &dd.data_type,
                                        DataType::TypeReference { name, .. }
                                            if elab.classes.contains_key(&name.name.name)
                                                || matches!(
                                                    definitions.get(&name.name.name),
                                                    Some(Definition::Class(_))
                                                )
                                    );
                                    // §6.8/§10.9.2: an UNPACKED struct has no
                                    // single packed value — its members are
                                    // separate cells, so a const-evaluated
                                    // initializer (`plain_st_t s = '{x: 9, y: 11}`)
                                    // landed in a container nobody reads and the
                                    // members kept their defaults. Run it as a
                                    // static assignment, which spreads it.
                                    let unpacked_struct_typed = matches!(
                                        resolve_typedef_chain(&dd.data_type, &elab.typedef_types),
                                        DataType::Struct(su)
                                            if !su.packed
                                                && !(matches!(su.kind, StructUnionKind::Union)
                                                    && !su.tagged)
                                    );
                                    let init_has_call = decl.init.as_ref().is_some_and(|e| {
                                        unpacked_struct_typed
                                            || expr_has_call(e)
                                            || matches!(&e.kind, ExprKind::Ident(h)
                                                if h.path.len() == 1
                                                    && h.path[0].name.name == "new")
                                            || (class_typed
                                                && matches!(&e.kind, ExprKind::Ident(_)))
                                    });
                                    if init_has_call {
                                        if let Some(init_expr) = &decl.init {
                                            elab.pkg_var_init_blocks.push((
                                                elab.static_init_blocks.len(),
                                                format!("{}::{}", name, decl.name.name),
                                            ));
                                            elab.static_init_blocks.push(InitialBlock {
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
                                    let v = match &decl.init {
                                        Some(e) if !init_has_call => {
                                            let mut v = eval_init_for_target(
                                                e,
                                                &elab.parameters,
                                                w,
                                                is_real,
                                            );
                                            if is_real {
                                                v = Value::from_f64(v.to_f64());
                                            } else {
                                                v = package_var_init_value(
                                                    v,
                                                    &dd.data_type,
                                                    &elab.typedef_types,
                                                );
                                            }
                                            v
                                        }
                                        _ => default_value_for_type_resolved(
                                            &dd.data_type,
                                            w,
                                            &elab.typedef_types,
                                        ),
                                    };
                                    let tn = if is_anon_enum.is_some() {
                                        Some(decl.name.name.clone())
                                    } else {
                                        get_type_name(&dd.data_type)
                                    };
                                    // A packed-STRUCT package variable needs its
                                    // field layout registered, or `P::s.x`
                                    // (and any member select) reads x.
                                    if let Some(fields) = packed_struct_field_layout(
                                        &dd.data_type,
                                        &elab.parameters,
                                        &elab.typedefs,
                                        &elab.typedef_types,
                                    ) {
                                        if !fields.is_empty() {
                                            tls_register_struct_layout(&decl.name.name, &fields);
                                            elab.packed_struct_fields
                                                .entry(decl.name.name.clone())
                                                .or_insert(fields);
                                        }
                                    }
                                    if unpacked_struct_typed {
                                        register_unpacked_aggregate(
                                            elab,
                                            &decl.name.name,
                                            &dd.data_type,
                                        );
                                    }
                                    elab.var_decl_types
                                        .entry(decl.name.name.clone())
                                        .or_insert_with(|| dd.data_type.clone());
                                    // §6.16: a package `string` variable reads
                                    // as text, like a module-scope one.
                                    if matches!(
                                        &dd.data_type,
                                        DataType::Simple {
                                            kind: SimpleType::String,
                                            ..
                                        }
                                    ) {
                                        elab.string_signals.insert(decl.name.name.clone());
                                    }
                                    let qualified = format!("{}::{}", name, decl.name.name);
                                    // §26.3: retain this declaration's own type,
                                    // even when another package owns the bare name.
                                    let owned_type =
                                        if let DataType::TypeReference { name: tn, .. } =
                                            &dd.data_type
                                            && !tn.has_scope()
                                            && elab
                                                .typedef_types
                                                .contains_key(&format!("{name}::{}", tn.name.name))
                                        {
                                            scope_local_typerefs(
                                                &dd.data_type,
                                                &std::collections::HashSet::from([tn
                                                    .name
                                                    .name
                                                    .clone()]),
                                                &format!("{name}::"),
                                            )
                                        } else {
                                            dd.data_type.clone()
                                        };
                                    elab.var_decl_types
                                        .entry(qualified.clone())
                                        .or_insert(owned_type);
                                    elab.pkg_var_decls.insert(
                                        qualified.clone(),
                                        Signal {
                                            is_const: false,
                                            name: qualified.into(),
                                            width: w,
                                            is_signed,
                                            is_real,
                                            direction: None,
                                            value: v.clone(),
                                            type_name: tn.clone(),
                                        },
                                    );
                                    elab.signals
                                        .entry(decl.name.name.clone())
                                        .or_insert(Signal {
                                            is_const: false,
                                            name: decl.name.name.clone().into(),
                                            width: w,
                                            is_signed,
                                            is_real,
                                            direction: None,
                                            value: v,
                                            type_name: tn,
                                        });
                                    continue;
                                }
                                let Some(init_expr) = &decl.init else {
                                    continue;
                                };
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
                                    elab.static_init_blocks.push(InitialBlock {
                                        stmt: Statement::new(
                                            StatementKind::BlockingAssign {
                                                lvalue: make_ident_expr(&decl.name.name),
                                                rvalue: init_expr.as_ref().clone(),
                                            },
                                            Span::dummy(),
                                        ),
                                        scope: String::new(),
                                    });
                                } else if !init_items.is_empty() && !decl.dimensions.is_empty() {
                                    // Emit explicit per-element initializers. The
                                    // array is registered in `arrays` above, so
                                    // `name[i] = item` lands where reads look.
                                    let mut stmts: Vec<Statement> = Vec::new();
                                    for (i, item_expr) in init_items.iter().enumerate() {
                                        let lval = Expression::new(ExprKind::Index {
                                            expr: Box::new(make_ident_expr(&decl.name.name)),
                                            index: Box::new(Expression::new(ExprKind::Number(crate::ast::expr::NumberLiteral::Integer { size: None, signed: false, base: crate::ast::expr::NumberBase::Decimal, value: i.to_string(), cached_val: crate::ast::cache::LiteralCache::new(None) }), Span::dummy())),
                                        }, Span::dummy());
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
                                        signals_insert_traced(
                                            &mut elab.signals,
                                            line!(),
                                            size_name.clone(),
                                            Signal {
                                                is_const: false,
                                                name: size_name.into(),
                                                width: 32,
                                                is_signed: false,
                                                is_real: false,
                                                direction: None,
                                                value: Value::from_u64(init_items.len() as u64, 32),
                                                type_name: None,
                                            },
                                        );
                                    }
                                    elab.static_init_blocks.push(InitialBlock {
                                        stmt: Statement::new(
                                            StatementKind::SeqBlock { name: None, stmts: stmts.into() },
                                            Span::dummy(),
                                        ),
                                        scope: String::new(),
                                    });
                                } else if decl.dimensions.is_empty() {
                                    let _ = (width, is_signed);
                                    elab.static_init_blocks.push(InitialBlock {
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
                        }
                        _ => {}
                    }
                }
                restore_overlay(elab, __pkg_imp_overlay);
            }
            _ => {}
        }
    }

    let module_name = elab.name.clone();
    if elab_trace_enabled() {
        eprintln!("[xezim][elab] start top={}", module_name);
    }
    let top_def = match definitions.get(&module_name) {
        Some(m) => *m,
        None => {
            return Err(format!(
                "Top module '{}' not found in module map",
                module_name
            ));
        }
    };
    // Recursively inline starting from the top module's items
    MODPORT_EXPR_TLS.with(|m| m.borrow_mut().clear());
    for (name, value, signal) in header_values {
        elab.set_param(line!(), name.clone(), value);
        if let Some(signal) = signal {
            signals_insert_traced(&mut elab.signals, line!(), name, signal);
        }
    }
    let top_params = elab.parameters.clone();
    // Snapshot the now-complete package/$unit parameters as the const-eval
    // fallback so sub-module header localparams (evaluated in the instance-merge
    // context, which only carries the sub-instance's own params) can still
    // resolve imported package parameters like black-parrot's `all_cfgs_gp`.
    set_param_fallback(&top_params);
    set_typedef_types_tls(&elab.typedef_types);
    set_typedef_widths_tls(&elab.typedefs);
    let mut cache = InlineCache::default();
    let bind_driver = if let Some(binds) = bind_driver.as_ref().and_then(|(unit_binds, _)| {
        super::bind_inline::unit_module_binds(unit_binds, definitions, &elab.checker_decls)
    }) {
        cache.unit_module_binds = binds;
        None
    } else {
        bind_driver
    };
    let mut root_defparams = absolute_defparams(&module_name, definitions, &top_params);
    root_defparams.extend(upward_defparams(&module_name, definitions));
    // §23.10/§26.3: the snapshot is held once; each scope takes from it only
    // the entries its definition can name (#740).
    let param_scope =
        param_scope::ParamScope::new(&top_params, definitions, &elab.resolved_binds, &elab.lets);
    let mut top_scope = param_scope.top_scope(top_def, definitions);
    let mut bind_state = bind_driver.as_ref().and_then(|(unit_binds, _)| {
        BindTargetFilter::collect(
            top_def.name(),
            unit_binds,
            definitions,
            &elab.checker_decls,
        )
        .map(|filter| BindWorklistState {
            filter,
            scopes: HashMap::default(),
            needs_full_rebuild: false,
            kept_bound_ports: false,
        })
    });
    let top_meta = inline_module_items(
        elab,
        top_def,
        "",
        definitions,
        &mut HashMap::default(),
        &top_scope,
        &mut cache,
        &HashMap::default(),
        &root_defparams,
        &param_scope,
        bind_state.as_mut(),
    )?;
    if let Some(bs) = bind_state.as_mut()
        && bs.filter.can_target_top
    {
        let top_defparams = if !top_meta.was_flat_leaf {
            top_meta.defparams
        } else {
            root_defparams
        };
        bs.scopes.insert(
            String::new(),
            TargetScope {
                def_name: module_name.clone(),
                local_names: top_meta.local_names,
                local_typedefs: top_meta.local_typedefs,
                interface_map: HashMap::default(),
                port_map: Rc::new(HashMap::default()),
                local_params: std::mem::take(&mut top_scope),
                defparams: top_defparams,
                type_overlay: None,
                items_end: top_meta.items_end,
                was_flat_leaf: top_meta.was_flat_leaf,
            },
        );
    }
    if let (Some((_, resolve_step)), Some(mut bs)) = (bind_driver, bind_state) {
        // The bound scopes inlined here are elaborated again by the root
        // elaboration below, which reports their diagnostics once.
        let discovered = crate::with_elab_diags_muted(|| -> Result<bool, String> {
            for pass in 0..64 {
                let new_binds = resolve_step(elab)?;
                if new_binds.is_empty() {
                    break;
                }
                if pass == 63 {
                    return Err("bind hierarchy does not converge (§23.11)".into());
                }
                for (target_path, directives) in new_binds {
                    inline_bound_items(
                        elab,
                        &target_path,
                        &directives,
                        definitions,
                        &mut cache,
                        &param_scope,
                        &mut bs,
                    )?;
                    if bs.needs_full_rebuild {
                        return Ok(true);
                    }
                }
            }
            Ok(false)
        })?;
        if discovered {
            return Ok(true);
        }
        // §23.11: a bound instance is inlined as if written at the end of its
        // target's items, so it precedes the target's later siblings in the
        // instance, signal and process order. The walk above appended the
        // bound hierarchy after the whole design: it only discovers the
        // complete set of bind targets. Elaborate the root once more with
        // all of them, which yields the same design as a fixed point that
        // rebuilds the root on every pass.
        if !elab.resolved_binds.is_empty() || bs.kept_bound_ports {
            return Ok(true);
        }
        drop(bs);
    }
    crate::oom_trace::model("inline.top.ready", elab, Some(cache.prepared.len()));
    if elab_trace_enabled() {
        eprintln!("[xezim][elab] finished inline top={}", module_name);
    }

    // IEEE 1800-2017 §6.10: Implicit nets for cont-assigns that came in via
    // pending sub-module bodies. The initial create_implicit_nets (in
    // elaborate_module_with_defs) only scanned the top-level
    // continuous_assigns vec. Sub-module bodies are deferred into
    // pending_cont_assign and didn't get their implicit nets created —
    // c910's wid_for_axi4 has `assign create_en = a && b;` with no
    // `wire create_en` declaration; the cont-assign got dropped at
    // compile time because xezim couldn't resolve `create_en` to a
    // signal_id, so create_en stayed X and the wid-tracking FIFO froze
    // → c910 memcpy hang. Scan pending_cont_assign now and create
    // implicit 1-bit wires for any prefixed names that don't yet exist.
    create_implicit_nets_for_pending(elab);

    // Identify interface instances at top level (declared or bound directly to top)
    let mut top_interface_names = HashSet::default();
    for item in top_def.items() {
        if let ModuleItem::ModuleInstantiation(inst) = item {
            if definitions
                .get(&inst.module_name.name)
                .is_some_and(|d| matches!(d, Definition::Interface(_)))
            {
                for hi in &inst.instances {
                    top_interface_names.insert(hi.name.name.clone());
                }
            }
        }
    }
    if let Some(top_binds) = elab.resolved_binds.get("") {
        for b in top_binds {
            if definitions
                .get(&b.instantiation.module_name.name)
                .is_some_and(|d| matches!(d, Definition::Interface(_)))
            {
                for hi in &b.instantiation.instances {
                    top_interface_names.insert(hi.name.name.clone());
                }
            }
        }
    }

    // Final rewrite of all blocks to convert MemberAccess to HierarchicalIdentifier and handle local signals
    // #7 default: keep pending_* lazy. The bytecode compiler in
    // simulator.rs drains pending_always / pending_initial /
    // pending_cont_assign one-at-a-time inside classify_always_blocks /
    // build_comb_entries / event_loop, materializing per block instead
    // of accumulating everything in always_blocks/initial_blocks/
    // continuous_assigns first. Measured: c910 hello sim 220 s → 194 s
    // (-12%) with lazy default; c906 hello sim 36.8 s → 35.3 s (-4%).
    // Memory unchanged (the saving is materialize_pending wall time
    // skipped, not peak memory).
    //
    // Set XEZIM_NO_LAZY_PREFIX=1 to fall back to eager materialization,
    // useful for tools that need ElaboratedModule fully populated
    // (e.g. write_compiled-then-read-back artifact roundtrips, since
    // pending_* fields are #[serde(skip)]).
    if std::env::var("XEZIM_NO_LAZY_PREFIX").ok().as_deref() == Some("1") {
        elab.materialize_pending();
    }

    let local_names = elab
        .signals
        .keys()
        .cloned()
        .collect::<std::collections::HashSet<_>>();
    crate::oom_trace::model("inline.local_names.ready", elab, Some(cache.prepared.len()));
    let port_map = HashMap::default();
    let mut interface_map = HashMap::default();
    for name in top_interface_names {
        interface_map.insert(name.clone(), name);
    }
    let prefix = "";

    // §9.3/§23.6: an identity rewrite may retain shared root syntax.
    // Instances, interfaces, specialization and populated contextual
    // caches still take the complete rewrite and invalidation path.
    let root_identity = prefix.is_empty() && port_map.is_empty() && interface_map.is_empty();
    let rewrite_root = |stmt: &Statement| {
        if root_identity && identity_rewrite::can_preserve_root_stmt(stmt) {
            stmt.clone()
        } else {
            if root_identity && crate::oom_trace::enabled() {
                identity_rewrite::trace_root_rejection(stmt);
            }
            rewrite_stmt(stmt, prefix, &port_map, &local_names, &interface_map)
        }
    };
    for (index, block) in elab.always_blocks.iter_mut().enumerate() {
        crate::oom_trace::checkpoint("inline.root_always", &[("block_index", index)]);
        block.stmt = rewrite_root(&block.stmt);
    }
    crate::oom_trace::checkpoint("inline.root_always.ready", &[]);
    for (index, block) in elab.initial_blocks.iter_mut().enumerate() {
        crate::oom_trace::checkpoint("inline.root_initial", &[("block_index", index)]);
        block.stmt = rewrite_root(&block.stmt);
    }
    for assign in &mut elab.continuous_assigns {
        assign.lhs = rewrite_expr(&assign.lhs, prefix, &port_map, &local_names, &interface_map);
        assign.rhs = rewrite_expr(&assign.rhs, prefix, &port_map, &local_names, &interface_map);
    }
    drop(local_names);
    crate::oom_trace::model("inline.root_rewrites.ready", elab, Some(cache.prepared.len()));

    validate_inlined_bodies(elab, definitions)?;
    crate::oom_trace::model("inline.validation.ready", elab, Some(cache.prepared.len()));

    // §8.2: reject illegal `local`/`protected` member access at compile time
    // (the reference simulators report `Illegal access to local/protected
    // member` at elaboration). Only accesses proven illegal are rejected.
    validate_member_visibility(elab)?;

    Ok(false)
}
