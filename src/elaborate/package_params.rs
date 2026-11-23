use super::*;

/// Evaluate every package's parameters to a fixpoint, registering each under
/// its scoped `pkg::name` alias. Bare names are NOT registered — visibility
/// stays with the import machinery (`import p::A` must not expose `B`).
///
/// Three passes: parameters may reference other packages' parameters through
/// scoped names or import chains, and `defs` is a HashMap, so a single pass in
/// iteration order resolved a dependent parameter only when its dependency
/// happened to hash first. Values are recomputed each pass, so pass N heals
/// what pass N-1 computed from missing inputs; anything still unresolvable
/// (genuine forward cycles) keeps the last computed value exactly as before.
/// Overlay a package's OWN parameters onto the bare map (from their scoped
/// aliases) for the duration of processing THAT package's items, returning
/// what to restore. A package typedef sized by its own parameter
/// (`logic [LOG-1:0]`) resolves through the bare map inside `process_typedef`;
/// without the overlay the width came from whatever the bare slot held
/// design-wide, and with a permanent bare insert an un-imported parameter
/// would leak into every scope.
pub(super) fn overlay_pkg_imports(
    p: &crate::ast::module::PackageDeclaration,
    elab: &mut ElaboratedModule,
) -> Vec<(String, Option<Value>)> {
    let mut saved: Vec<(String, Option<Value>)> = Vec::new();
    for item in &p.items {
        let crate::ast::decl::PackageItem::Import(imp) = item else {
            continue;
        };
        for ii in &imp.items {
            let src_pkg = &ii.package.name;
            if let Some(sym) = &ii.item {
                let key = format!("{src_pkg}::{}", sym.name);
                if let Some(v) = elab.parameters.get(&key).cloned() {
                    saved.push((sym.name.clone(), elab.parameters.get(&sym.name).cloned()));
                    elab.set_param(line!(), sym.name.clone(), v);
                }
                let arr_prefix = format!("{key}[");
                let dot_prefix = format!("{key}.");
                let sub_values: Vec<_> = elab
                    .parameters
                    .iter()
                    .filter(|(name, _)| {
                        name.starts_with(&arr_prefix) || name.starts_with(&dot_prefix)
                    })
                    .map(|(name, value)| {
                        (name[src_pkg.len() + 2..].to_string(), value.clone())
                    })
                    .collect();
                for (name, value) in sub_values {
                    saved.push((name.clone(), elab.parameters.get(&name).cloned()));
                    elab.set_param(line!(), name, value);
                }
            } else {
                let prefix = format!("{src_pkg}::");
                let values: Vec<_> = elab
                    .parameters
                    .iter()
                    .filter_map(|(name, value)| {
                        let rest = name.strip_prefix(&prefix)?;
                        if rest.contains("::") {
                            return None;
                        }
                        Some((rest.to_string(), value.clone()))
                    })
                    .collect();
                for (name, value) in values {
                    saved.push((name.clone(), elab.parameters.get(&name).cloned()));
                    elab.set_param(line!(), name, value);
                }
            }
        }
    }
    saved
}

pub(super) fn overlay_pkg_params(
    p: &crate::ast::module::PackageDeclaration,
    elab: &mut ElaboratedModule,
) -> Vec<(String, Option<Value>)> {
    let mut saved = overlay_pkg_imports(p, elab);
    for item in &p.items {
        let crate::ast::decl::PackageItem::Parameter(pd) = item else {
            continue;
        };
        let ParameterKind::Data { assignments, .. } = &pd.kind else {
            continue;
        };
        for a in assignments {
            let key = format!("{}::{}", p.name.name, a.name.name);
            // §26.3: later package passes need the same bounded visibility
            // for array elements as for scalar parameters.
            if !a.dimensions.is_empty() {
                let prefix = format!("{key}[");
                let values: Vec<_> = elab
                    .parameters
                    .iter()
                    .filter(|(name, _)| name.starts_with(&prefix))
                    .map(|(name, value)| (name[p.name.name.len() + 2..].to_string(), value.clone()))
                    .collect();
                for (name, value) in values {
                    saved.push((name.clone(), elab.parameters.get(&name).cloned()));
                    elab.set_param(line!(), name, value);
                }
            }
            if let Some(v) = elab.parameters.get(&key).cloned() {
                saved.push((
                    a.name.name.clone(),
                    elab.parameters.get(&a.name.name).cloned(),
                ));
                elab.set_param(line!(), a.name.name.clone(), v);
            }
        }
    }
    // §26.3, §6.19: an enum member of `p` that a declaration of the
    // elaborated scope displaces (`local_decl_displaces`) is not registered
    // under its bare name, which holds the local member instead.
    if !(elab.wildcard_shadowed.is_empty() && elab.foreign_package_names.is_empty()) {
        overlay_pkg_members(p, elab, &mut saved, |elab, nm| {
            elab.local_decl_displaces(nm)
        });
    }
    saved
}

/// §26.3, §6.19: bind each enum member of `p` that `pick` selects to its bare
/// name, from its `p::NAME` entry, recording the entry it replaces in
/// `saved`. `p`'s own constants (`localparam int PE = EEW8;` in `p`) read
/// `p`'s member while `p`'s items are evaluated, like `p`'s parameters, even
/// where the bare name holds a `$unit` or local member of the same name.
pub(super) fn overlay_pkg_members(
    p: &crate::ast::module::PackageDeclaration,
    elab: &mut ElaboratedModule,
    saved: &mut Vec<(String, Option<Value>)>,
    pick: impl Fn(&ElaboratedModule, &str) -> bool,
) {
    for item in &p.items {
        let crate::ast::decl::PackageItem::Typedef(td) = item else {
            continue;
        };
        let DataType::Enum(et) = &td.data_type else {
            continue;
        };
        let signed = is_type_signed_resolved(&td.data_type, &elab.typedef_types);
        for member in &et.members {
            for nm in enum_member_names(member, &elab.parameters) {
                if !pick(elab, &nm) {
                    continue;
                }
                let key = format!("{}::{nm}", p.name.name);
                let Some(mut v) = elab.parameters.get(&key).cloned() else {
                    continue;
                };
                if !v.is_real {
                    v.is_signed = signed;
                }
                saved.push((nm.clone(), elab.parameters.get(&nm).cloned()));
                elab.set_param(line!(), nm, v);
            }
        }
    }
}

pub(super) fn restore_overlay(elab: &mut ElaboratedModule, saved: Vec<(String, Option<Value>)>) {
    for (k, prev) in saved.into_iter().rev() {
        match prev {
            Some(v) => {
                elab.set_param(line!(), k, v);
            }
            None => {
                elab.remove_param(&k);
            }
        }
    }
}

/// §10.9.2 / §26.3: re-evaluate STRUCT-typed package parameters once the
/// package typedefs exist. `hoist_package_params` runs before any typedef is
/// registered (typedefs may be sized by package parameters), so a struct
/// parameter's type does not resolve there and its assignment pattern folds
/// to 0. A module localparam built from it before the package is imported
/// (`build_config(cva6_config_pkg::cva6_cfg)`) then read that 0. Only the
/// `pkg::name` alias is updated, as in the hoist; bare visibility stays with
/// the import machinery.
/// `enc_t [0:N] ENC = '{ '{exp, man}, ... }`. The first pattern item is the
/// left index and, for `[0:N]`, the MS element. Each item is one struct.
fn pack_packed_struct_array(
    dt: &DataType,
    init: &Expression,
    width: u32,
    elab: &ElaboratedModule,
) -> Option<Value> {
    let DataType::TypeReference { dimensions, .. } = dt else {
        return None;
    };
    let PackedDimension::Range { left, right, .. } = dimensions.first()? else {
        return None;
    };
    let l = const_eval_i64_with_params(left, Some(&elab.parameters))?;
    let r = const_eval_i64_with_params(right, Some(&elab.parameters))?;
    let n = (l - r).unsigned_abs() as usize + 1;
    let ExprKind::AssignmentPattern(items) = &peel_unpacked_typed_pattern(init).kind else {
        return None;
    };
    if items.len() != n {
        return None;
    }
    let mut elem_ty = dt.clone();
    if let DataType::TypeReference { dimensions, .. } = &mut elem_ty {
        dimensions.clear();
    }
    let elem_w = width / n as u32;
    if elem_w == 0 {
        return None;
    }
    let mut elems = Vec::with_capacity(n);
    for item in items {
        let packed = pack_struct_const_value(
            &elem_ty,
            item.expr(),
            &elab.parameters,
            &elab.typedefs,
            &elab.typedef_types,
        )?;
        elems.push(packed.resize(elem_w));
    }
    // Pattern order is left-to-right; `[0:N]` stores the left item at the MSB.
    // Prepend each earlier item so the first pattern item ends on the left.
    let mut acc = Value::zero(0);
    for elem in elems.iter().rev() {
        acc = elem.concat_with(&acc);
    }
    Some(acc.resize(width))
}

pub(super) fn hoist_package_struct_params(
    defs: &HashMap<String, Definition>,
    elab: &mut ElaboratedModule,
) {
    let mut pkgs: Vec<&crate::ast::module::PackageDeclaration> = defs
        .values()
        .filter_map(|d| match d {
            Definition::Package(p) => Some(*p),
            _ => None,
        })
        .collect();
    pkgs.sort_by(|a, b| a.name.name.cmp(&b.name.name));
    // Two passes: a struct parameter may be built from another package's.
    for _pass in 0..2 {
        for p in &pkgs {
            let mut own_overlay = overlay_pkg_params(p, elab);
            for item in &p.items {
                let crate::ast::decl::PackageItem::Parameter(pd) = item else {
                    continue;
                };
                let ParameterKind::Data {
                    data_type,
                    assignments,
                } = &pd.kind
                else {
                    continue;
                };
                // A package-local type name binds THIS package's typedef,
                // ahead of a same-named one elsewhere.
                let local_dt = match data_type {
                    DataType::TypeReference {
                        name, dimensions, ..
                    } if !name.has_scope() && dimensions.is_empty() => elab
                        .typedef_types
                        .get(&format!("{}::{}", p.name.name, name.name.name))
                        .cloned(),
                    _ => None,
                };
                let dt = local_dt.as_ref().unwrap_or(data_type);
                if !matches!(resolve_typedef_chain(dt, &elab.typedef_types), DataType::Struct(_)) {
                    continue;
                }
                let width = resolve_type_width(dt, Some(&elab.parameters), Some(&elab.typedefs));
                if width == 0 {
                    continue;
                }
                for assign in assignments {
                    // Element width has to exist before any module localparam
                    // calls a package function that indexes this array.
                    // `hoist_package_params` has not registered it yet, and a
                    // top-level `fp_width` folded in between read one bit.
                    register_packed_array_elem_w(
                        &assign.name.name,
                        data_type,
                        &elab.typedefs,
                        &elab.parameters,
                    );
                    let Some(init) = &assign.init else { continue };
                    if !assign.dimensions.is_empty() {
                        continue;
                    }
                    // `enc_t [0:4] ENC = '{...}` resolves to the element
                    // struct, so this hoist would pack the array pattern as
                    // one struct and alias that over the real array value.
                    // It runs after `hoist_package_params`, so the clobber is
                    // what a following module localparam sees (high elements
                    // zero, `fp_width` returns 1).
                    if matches!(
                        data_type,
                        DataType::TypeReference { dimensions, .. } if !dimensions.is_empty()
                    ) {
                        // Repack element-by-element now that typedefs exist.
                        // `hoist_package_params` ran before them and left the
                        // high elements at 0; the module parameter pass is
                        // next and would freeze `fp_width` at 1. A typeless
                        // eval of the pattern does the same.
                        if let Some(v) = pack_packed_struct_array(data_type, init, width, elab) {
                            alias_pkg_param(elab, &p.name.name, &assign.name.name, &v);
                            elab.set_param(line!(), assign.name.name.clone(), v);
                        }
                        // Field offsets of ONE element, so `ENC[i].exp_bits`
                        // slices the element and then the field. The array
                        // type is not itself a struct, so the layout pass
                        // below does not see it.
                        let mut elem_ty = data_type.clone();
                        if let DataType::TypeReference { dimensions, .. } = &mut elem_ty {
                            dimensions.clear();
                        }
                        if let Some(fields) = flatten_struct_fields(
                            &elem_ty,
                            &elab.parameters,
                            &elab.typedefs,
                            &elab.typedef_types,
                        ) {
                            if !fields.is_empty() {
                                let bare = assign.name.name.clone();
                                let dotted = format!("{}.{}", p.name.name, bare);
                                let qualified = format!("{}::{}", p.name.name, bare);
                                for key in [&bare, &dotted, &qualified] {
                                    tls_register_struct_layout(key, &fields);
                                    // The runtime member read of an element
                                    // (`p::ENC[f].man_bits` in a class
                                    // method, which reaches it as `p.ENC`)
                                    // needs the layout too; it read 0.
                                    elab.packed_struct_fields
                                        .entry(key.clone())
                                        .or_insert_with(|| fields.clone());
                                }
                                // ... and its element width and bounds under
                                // the qualified spellings.
                                for key in [&dotted, &qualified] {
                                    register_packed_param_index(elab, key, data_type, None);
                                }
                            }
                        }
                        continue;
                    }
                    let subbed;
                    let init: &Expression = if expr_has_call(init) {
                        match substitute_const_fn_calls(init,Some(&elab.parameters), elab, 0)
                            .filter(|e| !expr_has_call(e))
                        {
                            Some(e) => {
                                subbed = e;
                                &subbed
                            }
                            None => continue,
                        }
                    } else {
                        init
                    };
                    let v = match pack_struct_const_value(
                        dt,
                        init,
                        &elab.parameters,
                        &elab.typedefs,
                        &elab.typedef_types,
                    ) {
                        Some(v) => v.resize(width),
                        None => {
                            eval_param_init(dt, init, &elab.parameters, &elab.typedef_types, width)
                        }
                    };
                    alias_pkg_param(elab, &p.name.name, &assign.name.name, &v);
                    if let Some(fields) = flatten_struct_fields(
                        dt,
                        &elab.parameters,
                        &elab.typedefs,
                        &elab.typedef_types,
                    ) {
                        if !fields.is_empty() {
                            // §26.3: the bare name is visible only where the
                            // package is imported (`register_bare_struct_param`).
                            let bare = assign.name.name.clone();
                            let dotted = format!("{}.{}", p.name.name, bare);
                            let qualified = format!("{}::{}", p.name.name, bare);
                            for key in [&dotted, &qualified] {
                                tls_register_struct_layout(key, &fields);
                                elab.packed_struct_fields
                                    .entry(key.clone())
                                    .or_insert_with(|| fields.clone());
                                register_struct_param_members(
                                    |k, v| {
                                        elab.set_param(line!(), k, v);
                                    },
                                    key,
                                    &v,
                                    &fields,
                                );
                                register_struct_member_elem_widths(
                                    key,
                                    dt,
                                    &elab.parameters,
                                    &elab.typedef_types,
                                );
                            }
                        }
                    }
                    // Later parameters of this package see it bare.
                    own_overlay.push((
                        assign.name.name.clone(),
                        elab.parameters.get(&assign.name.name).cloned(),
                    ));
                    elab.set_param(line!(), assign.name.name.clone(), v);
                }
            }
            restore_overlay(elab, own_overlay);
        }
    }
}

pub(super) fn hoist_package_params(
    defs: &HashMap<String, Definition>,
    elab: &mut ElaboratedModule,
) {
    let mut pkgs: Vec<&crate::ast::module::PackageDeclaration> = defs
        .values()
        .filter_map(|d| match d {
            Definition::Package(p) => Some(*p),
            _ => None,
        })
        .collect();
    pkgs.sort_by(|a, b| a.name.name.cmp(&b.name.name));
    // §13.4.3: sizing-helper FUNCTIONS must be visible before any parameter
    // init is evaluated — `LOG = LOG2(DEPTH)` hoisted before LOG2 registered
    // silently evaluated the call to 0, and every scoped `p::LOG` dimension
    // resolved against that 0 until the import path healed it, too late for
    // module signal widths. Same registration shape as the import path
    // (bare or_insert + qualified insert), so ordering can't change outcomes.
    // §26.2: hoist package-scope named properties/sequences into the same
    // maps a module-level declaration populates, so an importing module's
    // `assert property (p(...))` resolves them.
    // §26.3: each is also registered as `pkg::name`, the spelling
    // `pkg_scope` gives a reference when two packages declare the name.
    for p in &pkgs {
        for item in &p.items {
            let (name, body, ports, defaults) = match item {
                crate::ast::decl::PackageItem::Property(pd) => {
                    (&pd.name.name, &pd.body, &pd.ports, &pd.port_defaults)
                }
                crate::ast::decl::PackageItem::Sequence(sd) => {
                    (&sd.name.name, &sd.body, &sd.ports, &sd.port_defaults)
                }
                _ => continue,
            };
            let qualified = format!("{}::{}", p.name.name, name);
            elab.sequences.insert(name.clone());
            elab.sequences.insert(qualified.clone());
            if let Some(body) = body {
                let params: Vec<String> = ports.iter().map(|p| p.name.clone()).collect();
                elab.property_decls
                    .entry(name.clone())
                    .or_insert_with(|| Rc::new(body.clone()));
                elab.property_params
                    .entry(name.clone())
                    .or_insert_with(|| params.clone());
                elab.property_decls.insert(qualified.clone(), Rc::new(body.clone()));
                if defaults.iter().any(|d| d.is_some()) {
                    elab.property_param_defaults
                        .entry(name.clone())
                        .or_insert_with(|| defaults.clone());
                    elab.property_param_defaults
                        .insert(qualified.clone(), defaults.clone());
                }
                elab.property_params.insert(qualified, params);
            }
        }
    }
    // §11.13 / §26.3: a package let is reachable as `pkg::name` without an
    // import; register it under that key (an import adds the bare name).
    for p in &pkgs {
        for item in &p.items {
            if let crate::ast::decl::PackageItem::Let(l) = item {
                elab.lets
                    .insert(format!("{}::{}", p.name.name, l.name.name), l.clone());
            }
        }
    }
    for p in &pkgs {
        for item in &p.items {
            let crate::ast::decl::PackageItem::Function(f) = item else {
                continue;
            };
            if f.name.has_scope() {
                continue;
            }
            elab.functions
                .insert_if_absent_with(f.name.name.name.clone(), || f.clone());
            elab.functions
                .insert(format!("{}::{}", p.name.name, f.name.name.name), f.clone());
            elab.pkg_subr_owner
                .entry(f.name.name.name.clone())
                .or_insert_with(|| p.name.name.clone());
        }
    }
    // Refresh the TLS function table consulted by const_eval for DIRECT
    // fn calls in range dimensions (`logic [p::LOG2(64)-1:0] x;`) — before
    // this, TLS held whatever the last package elaboration left, so a
    // module-context dimension call silently missed and the dim fell to 1.
    set_funcs_tls(&elab.functions);
    for _pass in 0..3 {
        // Bare visibility of EVERY package's params (read back from their
        // pkg:: aliases, i.e. the PREVIOUS pass's values) for the whole pass.
        // Without this each pass restarted blind: a reference to a parameter
        // that this pass has not reached yet — a forward reference, or a bare
        // cross-package reference to a package that sorts later — missed and
        // const-eval defaulted it to 0, so `X - 6` froze at -6 and the
        // fixpoint could never heal it. Restored at the end of the pass, so
        // nothing leaks past the hoist.
        let mut pass_overlay: Vec<(String, Option<Value>)> = Vec::new();
        for p in &pkgs {
            pass_overlay.extend(overlay_pkg_params(p, elab));
        }
        for p in &pkgs {
            // This package's OWN params win over a same-named param from
            // another package while its items are evaluated.
            let own_overlay = overlay_pkg_params(p, elab);
            // A bare call inside THIS package binds this package's own
            // function even when another package registered the same bare
            // name first (`pa::f` won the or_insert; `pb`'s `W = f(3)` must
            // still call pb::f). Override bare entries for the duration of
            // this package's params, then restore.
            let mut fn_overlay: Vec<(String, Option<FunctionDeclaration>)> = Vec::new();
            for item in &p.items {
                let crate::ast::decl::PackageItem::Function(f) = item else {
                    continue;
                };
                if f.name.has_scope() {
                    continue;
                }
                let key = f.name.name.name.clone();
                fn_overlay.push((key.clone(), elab.functions.get(&key).cloned()));
                elab.functions.insert(key, f.clone());
            }
            // Sequential bare visibility of this package's OWN params while
            // its inits are evaluated (`LOG2(SZ)` — the formal binds the bare
            // name), restored after the package so nothing leaks unimported.
            let mut pkg_overlay: Vec<(String, Option<Value>)> = Vec::new();
            for item in &p.items {
                let crate::ast::decl::PackageItem::Parameter(pd) = item else {
                    continue;
                };
                let ParameterKind::Data {
                    data_type,
                    assignments,
                } = &pd.kind
                else {
                    continue;
                };
                let base_width =
                    resolve_type_width(data_type, Some(&elab.parameters), Some(&elab.typedefs));
                for assign in assignments {
                    let Some(init) = &assign.init else { continue };
                    // §6.20.2/§26.3: an UNPACKED-ARRAY package parameter
                    // (`localparam int unsigned LIM [4] = '{1,2,4,8};`). The
                    // scalar fold below collapses the whole pattern to one
                    // value, so a scoped element reference
                    // (`int mem [pkg::LIM[3]]`) read a garbage bit and a
                    // dimension sized by it vanished. Register each element
                    // under the SCOPED key (`pkg::LIM[i]` — the same
                    // spelling `alias_pkg_param` uses) via the same
                    // `register_array_param` the module body uses. Bare
                    // visibility stays owned by the import machinery
                    // (§26.2.2), exactly like the scalar alias below.
                    if !assign.dimensions.is_empty() {
                        let scoped_type;
                        let data_type = if let DataType::TypeReference { name, .. } = data_type
                            && !name.has_scope()
                            && elab
                                .typedef_types
                                .contains_key(&format!("{}::{}", p.name.name, name.name.name))
                        {
                            let own = std::collections::HashSet::from([name.name.name.clone()]);
                            scoped_type = scope_local_typerefs(
                                data_type,
                                &own,
                                &format!("{}::", p.name.name),
                            );
                            &scoped_type
                        } else {
                            data_type
                        };
                        let scoped_name = format!("{}::{}", p.name.name, assign.name.name);
                        if register_array_param(
                            &mut *elab,
                            "",
                            &scoped_name,
                            &assign.dimensions,
                            assign.init.as_ref(),
                            None,
                            data_type,
                            None,
                        ) {
                            // §26.3: later declarations in this package can
                            // use its own array without a qualification. Keep
                            // that visibility within the bounded overlay.
                            let head = format!("{scoped_name}[");
                            let own: Vec<_> = elab
                                .parameters
                                .iter()
                                .filter(|(name, _)| name.starts_with(&head))
                                .map(|(name, value)| {
                                    (name[p.name.name.len() + 2..].to_string(), value.clone())
                                })
                                .collect();
                            for (name, value) in own {
                                pkg_overlay
                                    .push((name.clone(), elab.parameters.get(&name).cloned()));
                                elab.set_param(line!(), name, value);
                            }
                            continue;
                        }
                    }
                    let base_is_real = is_type_real_resolved(data_type, &elab.typedef_types);
                    let res = resolve_param_decl_value(
                        &mut *elab,
                        data_type,
                        Some(init),
                        None,
                        None,
                        base_width,
                        false,
                        base_is_real,
                        ParamDeclPolicy {
                            unresolved_call: UnresolvedCallPolicy::SkipIfUnresolved,
                            promote_implicit_real: false,
                            narrow_implicit_string_lit: false,
                            force_signed_on_override: false,
                            eval_packed_aggregate: true,
                            require_known_idents: false,
                            signed_from_pkg_helper: true,
                        },
                    );
                    if res.skipped {
                        // The call didn't reduce — registering the
                        // 0 that eval_init_for_width would produce
                        // poisons every dimension sized by this
                        // param. Leave it for a later pass / the
                        // import path.
                        continue;
                    }
                    let v = res.val;
                    pkg_overlay.push((
                        assign.name.name.clone(),
                        elab.parameters.get(&assign.name.name).cloned(),
                    ));
                    elab.set_param(line!(), assign.name.name.clone(), v.clone());
                    // SCOPED alias only. Registering bare names here would
                    // make every package parameter visible everywhere — an
                    // explicit `import p::A;` must NOT expose `B` (§26.2.2,
                    // and the repro_import_too_much guard). Bare visibility
                    // stays owned by the import machinery; scopes that need a
                    // package's own params for its own typedefs get a bounded
                    // overlay in the hoist loop below.
                    alias_pkg_param(elab, &p.name.name, &assign.name.name, &v);
                    let scoped = format!("{}.{}", p.name.name, assign.name.name);
                    register_pkg_param_elem(elab, "", &scoped, data_type);
                }
            }
            // §26.6: alias exported parameters from imported packages under
            // this package's name (`p::sym`), so downstream packages that
            // import `p` see re-exported parameters in `overlay_pkg_imports`.
            let referenced = package_referenced_names(p);
            for item in &p.items {
                let PackageItem::Import(inner) = item else {
                    continue;
                };
                for ii2 in &inner.items {
                    match &ii2.item {
                        Some(sym) => {
                            if package_exports(p, &ii2.package.name, Some(&sym.name))
                                && let Some(v) = elab.parameters.get(&sym.name).cloned()
                            {
                                alias_pkg_param(elab, &p.name.name, &sym.name, &v);
                            }
                        }
                        None => {
                            if !package_exports(p, &ii2.package.name, None) {
                                continue;
                            }
                            if let Some(src) = pkgs.iter().find(|q| q.name.name == ii2.package.name)
                            {
                                for spi in &src.items {
                                    for n in package_item_names(spi) {
                                        let explicit = p.items.iter().any(|pi| {
                                            matches!(pi, PackageItem::Export(e) if e.items.iter().any(|it|
                                                (it.package.name == "*" || it.package.name == ii2.package.name)
                                                    && it.item.as_ref().is_some_and(|i| i.name == n)))
                                        });
                                        if (explicit || referenced.contains(&n))
                                            && let Some(v) = elab
                                                .parameters
                                                .get(&format!("{}::{}", ii2.package.name, n))
                                                .or_else(|| elab.parameters.get(&n))
                                                .cloned()
                                        {
                                            alias_pkg_param(elab, &p.name.name, &n, &v);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            restore_overlay(elab, pkg_overlay);
            restore_overlay(elab, own_overlay);
            for (k, prev) in fn_overlay.into_iter().rev() {
                match prev {
                    Some(f) => {
                        elab.functions.insert(k, f);
                    }
                    None => {
                        elab.functions.remove(&k);
                    }
                }
            }
        }
        restore_overlay(elab, pass_overlay);
    }
}
