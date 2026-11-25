use super::*;

/// §26.3: mirror a package typedef under its qualified `pkg::name` key so a
/// SCOPED reference resolves even when a module-local typedef shadows the bare
/// name (`typedef int T;` in the module vs `P::T`). The bare registration is
/// unchanged — imports keep working exactly as before.
pub fn register_scoped_typedef_alias(
    pkg: &str,
    td: &TypedefDeclaration,
    elab: &mut ElaboratedModule,
) {
    let key = format!("{}::{}", pkg, td.name.name);
    if let Some(w) = elab.typedefs.get(&td.name.name).copied() {
        typedefs_insert_traced(&mut elab.typedefs, "insert:scoped_alias", key.clone(), w);
    }
    // §26.3 / §6.19: the members of a package ENUM under `pkg::MEMBER` too.
    // Members are hoisted under their bare name only (last package wins), so
    // `f_pkg::ADD` in a constant context — a declaration initializer, a
    // localparam, the inliner's spelling of a member two packages both
    // declare — read `a_pkg::ADD`'s value.
    if let DataType::Enum(et) = &td.data_type {
        if let Some(members) = elab.enum_members.get(&td.name.name).cloned() {
            // §18.3 / §26.3 (#862): qualified struct member types retain
            // their own enum domain when packages share a typedef name.
            elab.enum_members.insert(key.clone(), members.clone());
            let w = elab
                .typedefs
                .get(&td.name.name)
                .copied()
                .unwrap_or(32)
                .max(1);
            let signed = is_type_signed_resolved(&td.data_type, &elab.typedef_types);
            let mut displaced = None;
            for (m, ordinal) in members {
                // §6.19: preserve the typed member, including its X/Z bits.
                // A displaced bare name belongs to the importing scope. Get
                // that member from the enum declaration itself.
                let bare = elab
                    .parameters
                    .get(&m)
                    .filter(|_| !elab.local_decl_displaces(&m));
                let mut value = bare.cloned().unwrap_or_else(|| {
                    displaced
                        .get_or_insert_with(|| wide_enum_value_map(et, w, &elab.parameters))
                        .remove(&m)
                        .unwrap_or_else(|| Value::from_u64(ordinal, w))
                });
                value.is_signed = signed;
                alias_pkg_param(elab, pkg, &m, &value);
            }
        }
    }
    // §6.18 / §26.3: qualifying an alias must retain its collection
    // dimensions and packed element width, as well as its element type.
    // Nested member references may already use this qualified key.
    if let Some(dims) = elab.typedef_unpacked_dims.get(&td.name.name).cloned() {
        elab.typedef_unpacked_dims.insert(key.clone(), dims);
    }
    if let Some(width) = elab.typedef_elem_widths.get(&td.name.name).copied() {
        elab.typedef_elem_widths.insert(key.clone(), width);
    }
    if let Some(dt) = elab.typedef_types.get(&td.name.name).cloned() {
        let prefix = format!("{pkg}::");
        fn referenced(
            dt: &DataType,
            prefix: &str,
            known: &HashMap<String, DataType>,
            out: &mut std::collections::HashSet<String>,
        ) {
            match dt {
                DataType::TypeReference { name, .. }
                    if !name.has_scope()
                        && known.contains_key(&format!("{prefix}{}", name.name.name)) =>
                {
                    out.insert(name.name.name.clone());
                }
                DataType::Struct(s) => {
                    for field in &s.members {
                        referenced(&field.data_type, prefix, known, out);
                    }
                }
                DataType::Enum(e) => {
                    if let Some(base) = &e.base_type {
                        referenced(base, prefix, known, out);
                    }
                }
                _ => {}
            }
        }
        let mut own = std::collections::HashSet::new();
        referenced(&dt, &prefix, &elab.typedef_types, &mut own);
        let dt = scope_local_typerefs(&dt, &own, &prefix);
        let dims = elab
            .typedef_unpacked_dims
            .get(&key)
            .cloned()
            .unwrap_or_default();
        tls_register_typedef_shape(&key, &dt, &dims);
        elab.typedef_types.insert(key, dt);
    }
    // `process_typedef` refreshes the const-eval snapshot, but it runs BEFORE
    // this alias exists — so `$bits(pkg::T)` never saw the qualified key.
    type_trace_tls_refresh("scoped_alias", &elab.typedefs);
    sync_typedefs_tls(&elab.typedefs);
}

/// §26.3 / §8.23: look a (possibly `::`-chained) type name up in one of
/// the elaborator's string-keyed typedef tables. The FULL chain key
/// (`pkg::cls::td`) is tried first — package walks and class-scope
/// registration both key it — then the bare leaf, which preserves the
/// old single-link behavior exactly (`pkg::td` tried `pkg::td`, then
/// `td`).
pub fn lookup_scoped_type<'a, T>(
    name: &crate::ast::types::TypeName,
    table: &'a HashMap<String, T>,
) -> Option<&'a T> {
    lookup_scoped_type_at(name, table, 0)
}

/// `lookup_scoped_type` after `depth` rewrites of the name (a bound on
/// alias cycles).
fn lookup_scoped_type_at<'a, T>(
    name: &crate::ast::types::TypeName,
    table: &'a HashMap<String, T>,
    depth: u32,
) -> Option<&'a T> {
    if name.scopes.is_empty() {
        return table.get(&name.name.name);
    }
    const MAX_REWRITES: u32 = 8;
    // §8.25.1: `Cls#(args)::t` whose typedef names a member of a type
    // parameter is that argument's member type; the `Cls::t` key below is
    // the default specialization's.
    if depth < MAX_REWRITES
        && let Some(alt) = class_scope_types::specialized(name)
        && let Some(found) = lookup_scoped_type_at(&alt, table, depth + 1)
    {
        return Some(found);
    }
    table
        .get(&name.qualified())
        .or_else(|| {
            // §6.20.3: a type parameter or typedef used as a class scope
            // (`C::t`) names the class it is bound to.
            (depth < MAX_REWRITES)
                .then(|| class_scope_types::through_alias(name))
                .flatten()
                .and_then(|alt| lookup_scoped_type_at(&alt, table, depth + 1))
        })
        .or_else(|| table.get(&name.name.name))
}

/// §6.18, §7.4.4: the member declarator supplies the outer dimensions
/// of an unpacked array. A typedef can supply additional inner dimensions.
pub fn struct_member_dims<'a>(
    dt: &DataType,
    declared: &'a [UnpackedDimension],
    typedef_dims: &HashMap<String, Vec<UnpackedDimension>>,
) -> std::borrow::Cow<'a, [UnpackedDimension]> {
    if let DataType::TypeReference { name, dimensions, .. } = dt
        && dimensions.is_empty()
        && let Some(inner) = lookup_scoped_type(name, typedef_dims)
        && !inner.is_empty()
    {
        let mut dims = declared.to_vec();
        dims.extend_from_slice(inner);
        return std::borrow::Cow::Owned(dims);
    }
    std::borrow::Cow::Borrowed(declared)
}

/// A (possibly nested) `MemberAccess` chain rooted at a plain identifier —
/// the expression shape of `pkg::wide_t` / `pkg::cls::t` — flattened into
/// (scope links, leaf name). `None` when the expression is not a pure
/// name chain (calls, selects, arithmetic, …).
pub fn member_access_chain_as_scopes(
    e: &crate::ast::expr::Expression,
) -> Option<(Vec<crate::ast::types::TypeScope>, Identifier)> {
    let mut links: Vec<Identifier> = Vec::new();
    let mut cur = e;
    for _ in 0..16 {
        match &cur.kind {
            crate::ast::expr::ExprKind::MemberAccess { expr, member } => {
                links.push(member.clone());
                cur = expr;
            }
            crate::ast::expr::ExprKind::Ident(h)
                if h.path.len() == 1 && h.path[0].selects.is_empty() =>
            {
                links.push(h.path[0].name.clone());
                links.reverse();
                let leaf = links.pop()?;
                let scopes = links
                    .into_iter()
                    .map(|name| crate::ast::types::TypeScope {
                        name,
                        type_args: Vec::new(),
                    })
                    .collect();
                return Some((scopes, leaf));
            }
            _ => return None,
        }
    }
    None
}

/// Type names a typedef's own definition refers to — its base type and, for a
/// struct/union, its members' types. Used to order typedef processing so a
/// typedef is always registered after the ones whose widths it needs.
fn typedef_type_deps(dt: &DataType, out: &mut Vec<String>) {
    match dt {
        // §8.23: a scoped reference depends on its QUALIFIED key — the
        // registration tables key class/package aliases that way, and the
        // bare leaf would order against the wrong entry.
        DataType::TypeReference { name, .. } => out.push(if name.scopes.is_empty() {
            name.name.name.clone()
        } else {
            name.qualified()
        }),
        DataType::Struct(su) => {
            for m in &su.members {
                typedef_type_deps(&m.data_type, out);
            }
        }
        DataType::Enum(e) => {
            if let Some(base) = &e.base_type {
                typedef_type_deps(base, out);
            }
        }
        _ => {}
    }
}

/// The `Definition::Typedef` entries of `defs`, in dependency order: a typedef
/// referenced by another comes first. Ties (and cycles, which a forward
/// `typedef name;` legitimately creates) fall back to name order, so the result
/// is deterministic and never depends on HashMap iteration.
pub(super) fn ordered_typedefs<'a>(
    defs: &HashMap<String, Definition<'a>>,
) -> Vec<&'a TypedefDeclaration> {
    let mut by_name: Vec<(&str, &'a TypedefDeclaration)> = defs
        .iter()
        .filter_map(|(k, d)| match d {
            Definition::Typedef(td) => Some((k.as_str(), *td)),
            _ => None,
        })
        .collect();
    by_name.sort_by(|a, b| a.0.cmp(b.0));
    let index: HashMap<&str, usize> = by_name
        .iter()
        .enumerate()
        .map(|(i, (n, _))| (*n, i))
        .collect();

    let mut state = vec![0u8; by_name.len()]; // 0 = unvisited, 1 = on stack, 2 = done
    let mut out: Vec<&'a TypedefDeclaration> = Vec::with_capacity(by_name.len());
    // Iterative DFS: a typedef chain can be arbitrarily deep, and recursion here
    // would put that depth on the elaborator's stack.
    for start in 0..by_name.len() {
        if state[start] != 0 {
            continue;
        }
        let mut stack = vec![(start, false)];
        while let Some((i, expanded)) = stack.pop() {
            if expanded {
                if state[i] != 2 {
                    state[i] = 2;
                    out.push(by_name[i].1);
                }
                continue;
            }
            if state[i] != 0 {
                continue; // done, or already on the stack (cycle) — leave it
            }
            state[i] = 1;
            stack.push((i, true));
            let mut deps = Vec::new();
            typedef_type_deps(&by_name[i].1.data_type, &mut deps);
            deps.sort();
            deps.dedup();
            // Reversed so that, once popped, dependencies are visited in the
            // sorted order above.
            for d in deps.iter().rev() {
                if let Some(&j) = index.get(d.as_str()) {
                    if j != i && state[j] == 0 {
                        stack.push((j, false));
                    }
                }
            }
        }
    }
    out
}

/// §20.6.2: `$bits` inside a TYPE's packed dims (`typedef
/// logic[$bits(sig)-1:0] t;`) — rewrite the dims with the signal's known
/// width so `resolve_type_width` sees a constant. Without this the dim
/// silently evaluated to nothing and the typedef registered 1 bit wide.
fn prebind_type_dims(dt: &DataType, elab: &ElaboratedModule) -> Option<DataType> {
    fn dims_mention_bits(dims: &[PackedDimension]) -> bool {
        dims.iter().any(|d| match d {
            PackedDimension::Range { left, right, .. } => {
                expr_mentions_bits(left) || expr_mentions_bits(right)
            }
            PackedDimension::Unsized(_) => false,
        })
    }
    let rewrite = |dims: &[PackedDimension]| -> Vec<PackedDimension> {
        dims.iter()
            .map(|d| match d {
                PackedDimension::Range { left, right, span } => PackedDimension::Range {
                    left: Box::new(prebind_bits_of_signals(
                        left,
                        &elab.signals,
                        &elab.parameters,
                        "",
                        &elab.typedefs,
                        &elab.typedef_types,
                        &elab.packed_struct_fields,
                        &elab.arrays,
                    )),
                    right: Box::new(prebind_bits_of_signals(
                        right,
                        &elab.signals,
                        &elab.parameters,
                        "",
                        &elab.typedefs,
                        &elab.typedef_types,
                        &elab.packed_struct_fields,
                        &elab.arrays,
                    )),
                    span: *span,
                },
                other => other.clone(),
            })
            .collect()
    };
    match dt {
        DataType::IntegerVector {
            kind,
            signing,
            dimensions,
            span,
        } if dims_mention_bits(dimensions) => Some(DataType::IntegerVector {
            kind: *kind,
            signing: *signing,
            dimensions: rewrite(dimensions),
            span: *span,
        }),
        DataType::Implicit {
            signing,
            dimensions,
            span,
        } if dims_mention_bits(dimensions) => Some(DataType::Implicit {
            signing: *signing,
            dimensions: rewrite(dimensions),
            span: *span,
        }),
        DataType::TypeReference { dimensions, .. } if dims_mention_bits(dimensions) => {
            let mut bound = dt.clone();
            if let DataType::TypeReference {
                dimensions: dims, ..
            } = &mut bound
            {
                *dims = rewrite(dimensions);
            }
            Some(bound)
        }
        DataType::Struct(su) => {
            // A member's type must retain its declaration-scope widths after
            // serialization, just as the enclosing typedef does (§7.2, §27).
            let mut bound = dims_mention_bits(&su.dimensions).then(|| {
                let mut s = su.clone();
                s.dimensions = rewrite(&s.dimensions);
                s
            });
            for (i, member) in su.members.iter().enumerate() {
                if let Some(dt) = prebind_type_dims(&member.data_type, elab) {
                    bound.get_or_insert_with(|| su.clone()).members[i].data_type = dt;
                }
            }
            bound.map(DataType::Struct)
        }
        DataType::Enum(et) => {
            let mut bound = dims_mention_bits(&et.dimensions).then(|| {
                let mut e = et.clone();
                e.dimensions = rewrite(&e.dimensions);
                e
            });
            if let Some(base) = &et.base_type
                && let Some(dt) = prebind_type_dims(base, elab)
            {
                bound.get_or_insert_with(|| et.clone()).base_type = Some(Box::new(dt));
            }
            bound.map(DataType::Enum)
        }
        _ => None,
    }
}

/// §6.19: an enum's member names are implicitly declared in the ENCLOSING
/// scope, so two members of the same enum may not share a name --
/// `typedef enum { IDLE, RUN, IDLE } state_t;` is a duplicate declaration and
/// was accepted in silence, leaving `IDLE` bound to whichever member happened
/// to register first.
///
/// Checked against the enum's OWN member list rather than at registration,
/// because registration deliberately tolerates a name that is already present:
/// a package's enum members are re-registered once per import site and per
/// re-export hop (see the §26.3 note in `process_typedef`), and those repeats
/// are not duplicates. Comparing within one declaration cannot confuse the
/// two. Ranged members are expanded first, so a `[0:1]` range colliding with a
/// literal sibling is caught as well.
pub(super) fn check_enum_member_duplicates(
    td: &TypedefDeclaration,
    elab: &ElaboratedModule,
) -> Result<(), String> {
    let DataType::Enum(et) = &td.data_type else {
        return Ok(());
    };
    let mut seen: HashSet<String> = HashSet::default();
    let mut next_val: u64 = 0;
    for member in &et.members {
        let (entries, nv) = expand_enum_member(member, next_val, &elab.parameters);
        next_val = nv;
        for (nm, _) in entries {
            if !seen.insert(nm.clone()) {
                // `kind` reads as a short noun in the message template
                // ("duplicate {kind} declaration is at ..."), so it stays
                // "enum member"; the enum's own name is already evident from
                // the reported location.
                return Err(duplicate_decl_error(
                    elab,
                    &nm,
                    member.name.span,
                    "enum member",
                ));
            }
        }
    }
    Ok(())
}

thread_local! {
    /// True while `process_local_typedef` registers a typedef that the scope
    /// being elaborated declares itself.
    static LOCAL_TYPEDEF: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// `process_typedef` for a typedef the elaborated scope declares itself. Its
/// enum members ARE the local declarations that `local_decl_displaces`
/// names, so they are registered under their bare names; only a package's
/// same-named members give way to them (§26.3, §6.19). Without this a
/// module's own `typedef enum {.., EEW8} EEW_e;` registered no `EEW8` of its
/// own when an un-imported package also declared one, and `EEW8` read the
/// package's value.
pub(super) fn process_local_typedef(td: &TypedefDeclaration, elab: &mut ElaboratedModule) {
    let prev = LOCAL_TYPEDEF.with(|c| c.replace(true));
    process_typedef(td, elab);
    LOCAL_TYPEDEF.with(|c| c.set(prev));
}

/// §26.3, §3.12.1, §6.19: the bare-name entries of the `$unit` enum members
/// that a package also declares, as the `$unit` enums just registered them.
pub(super) fn contested_unit_member_slots(
    defs: &HashMap<String, Definition>,
    elab: &ElaboratedModule,
) -> Vec<(String, Value, Signal)> {
    if !crate::pkg_scope::any_member_qualified() {
        return Vec::new();
    }
    let mut slots = Vec::new();
    for td in ordered_typedefs(defs) {
        let DataType::Enum(et) = &td.data_type else {
            continue;
        };
        for member in &et.members {
            for nm in enum_member_names(member, &elab.parameters) {
                if !crate::pkg_scope::member_is_qualified(&nm) {
                    continue;
                }
                if let (Some(v), Some(sig)) =
                    (elab.parameters.get(&nm), elab.signals.get(nm.as_str()))
                {
                    slots.push((nm.clone(), v.clone(), sig.clone()));
                }
            }
        }
    }
    slots
}

/// §26.3, §3.12.1, §6.19: put each `$unit` enum member that a package also
/// declares back under its bare name once the design is elaborated.
///
/// Every package registers its enum members under their bare names,
/// imported or not, and the last registration wins; the package
/// registration that runs while instances are inlined comes after the
/// `$unit` typedefs. `pkg_scope` has already spelled each run-time reference
/// to a package's member `pkg::NAME` wherever the package's declaration is
/// the one in scope, so a bare run-time reference that is left names the
/// `$unit` member. Only those members' parameter and signal entries are put
/// back, from `unit_member_slots`; the typedef tables, other members and a
/// member the top module declares itself (which displaces the `$unit` one as
/// it does a package's) are left as they are. Constant contexts were
/// evaluated during elaboration and keep what they read then. Without this,
/// the testbench package's `EEW8 = 8` replaced the RTL's `$unit` `EEW8 = 2`,
/// which a 3-bit `EEW_e` truncates to `EEW_NONE`.
pub fn reassert_unit_enum_members(elab: &mut ElaboratedModule) {
    for (nm, v, sig) in std::mem::take(&mut elab.unit_member_slots) {
        if elab.local_decl_displaces(&nm) {
            continue;
        }
        elab.set_param(line!(), nm.clone(), v);
        signals_insert_traced(&mut elab.signals, line!(), nm, sig);
    }
}

/// The names one enum member declaration declares (`A[2]` declares `A0`,
/// `A1`; §6.19).
pub(super) fn enum_member_names(
    member: &EnumMember,
    params: &HashMap<String, Value>,
) -> Vec<String> {
    expand_enum_member(member, 0, params)
        .0
        .into_iter()
        .map(|(name, _)| name)
        .collect()
}

pub fn process_typedef(td: &TypedefDeclaration, elab: &mut ElaboratedModule) {
    // A later package may reuse a bare typedef name with scalar geometry.
    // Do not carry an earlier declaration's packed element stride into it.
    if !matches!(td.data_type, DataType::Void(_)) {
        elab.typedef_elem_widths.remove(&td.name.name);
    }
    // §6.18: a bare forward type declaration `typedef name;`. Record it for the
    // resolution check and register a placeholder, but never clobber a name that
    // a real (non-forward) typedef has already resolved — `typedef_test_0`
    // legally restates the forward name both before and after the full typedef.
    if td.forward {
        elab.forward_typedef_names.insert(td.name.name.clone());
        let already_resolved = elab
            .typedef_types
            .get(&td.name.name)
            .is_some_and(|dt| !matches!(dt, DataType::Void(_)));
        if !already_resolved {
            elab.typedef_types
                .entry(td.name.name.clone())
                .or_insert_with(|| td.data_type.clone());
            if !elab.typedefs.contains_key(&td.name.name) {
                typedefs_insert_traced(
                    &mut elab.typedefs,
                    "insert:forward_placeholder",
                    td.name.name.clone(),
                    0,
                );
            }
        }
        return;
    }
    if let DataType::Enum(et) = &td.data_type {
        // §6.19: the enum takes its BASE type's signedness (default base `int`
        // is signed), and every member constant carries it — `enum byte {Y0=-3}`
        // makes Y0 equal to -3, not 253. Members were registered unconditionally
        // unsigned.
        let enum_signed = is_type_signed_resolved(&td.data_type, &elab.typedef_types);
        let base_width = et
            .base_type
            .as_ref()
            .map(|bt| resolve_type_width(bt, Some(&elab.parameters), Some(&elab.typedefs)))
            .unwrap_or(32);
        let mut next_val: u64 = 0;
        let mut members_ordered: Vec<(String, u64)> = Vec::new();
        let wide_vals =
            (base_width > 64).then(|| wide_enum_value_map(et, base_width, &elab.parameters));
        for member in &et.members {
            let (entries, nv) = expand_enum_member(member, next_val, &elab.parameters);
            next_val = nv;
            for (nm, val) in entries {
                let mut v = enum_member_4state(member, val, base_width, &elab.parameters);
                if let Some(w) = wide_vals.as_ref().and_then(|m| m.get(&nm)) {
                    v = w.clone();
                }
                if !v.is_real {
                    v.is_signed = enum_signed;
                }
                // §26.3: a local declaration shadows a wildcard-imported name,
                // and the enum members of an imported package are registered
                // under their BARE name. The declaration walk removes the
                // shadowed member when it reaches the local decl, but
                // `process_typedef` runs several more times for the same
                // package afterwards (once per import site and per re-export
                // hop), and each of those re-inserted the member — silently
                // undoing the shadow. The local then read the enum's value and
                // carried the enum's WIDTH, so `int INIT_STATE = 500;` sitting
                // under `import p::*` became a 2-bit signal reading 0.
                //
                // The member still joins `members_ordered`, so it stays
                // reachable the only way §26.3 allows once shadowed: qualified
                // as `pkg::NAME`. A typedef of the scope itself
                // (`process_local_typedef`) is that local declaration, so its
                // members are registered.
                if !LOCAL_TYPEDEF.with(|c| c.get()) && elab.local_decl_displaces(&nm) {
                    members_ordered.push((nm.clone(), val));
                    continue;
                }
                // §6.19: an enum member name belongs to its ENCLOSING scope,
                // but these are registered in one flat namespace, so a later
                // enum with a same-named member silently overwrote an earlier
                // one — `class ca; enum {DUP=5} …` and `class cb; enum
                // {DUP=11} …` both resolved to 11. Scoping the namespace is a
                // deeper change; until then, never let the clobber be silent.
                // Only a CONFLICTING value is reported: re-registering the same
                // name with the same value is harmless (e.g. a package enum
                // imported into several scopes).
                if let Some(prev) = elab.parameters.get(&nm) {
                    // §26.3: a member two packages declare is read through
                    // its package-qualified spelling (`pkg_scope`), so the
                    // overwrite here is not the value those references see.
                    if prev.to_u64() != Some(val) && !crate::pkg_scope::member_is_qualified(&nm) {
                        let prev_s = prev
                            .to_u64()
                            .map(|x| x.to_string())
                            .unwrap_or_else(|| "x".into());
                        crate::elab_diag(format!(
                            "[xezim][warning] enum member '{nm}' redefined with a different value ({prev_s} -> {val}); the later definition wins for unqualified references. Enum member names share one namespace here, so qualify the reference (`pkg::{nm}` / `Class::{nm}`) or rename one member (IEEE 1800-2017 \u{00a7}6.19)."
                        ));
                    }
                }
                elab.note_decl_site(
                    &nm,
                    member.name.span,
                    format!("enum member of '{}'", td.name.name),
                    false,
                );
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
                        is_real: false,
                        direction: None,
                        value: v.into(),
                        type_name: Some(td.name.name.as_str().into()),
                    },
                );
                members_ordered.push((nm.clone(), val));
            }
        }
        // Register the typedef width AND its type. Only the non-enum branch
        // recorded `typedef_types`, so a variable declared with an enum typedef
        // (`eb_t e;`) could not be resolved back to the enum — the type walkers
        // stopped at the bare TypeReference and the variable read UNSIGNED even
        // when the enum's base was signed.
        let enum_width = resolve_type_width(
            &td.data_type, Some(&elab.parameters), Some(&elab.typedefs),
        );
        typedefs_insert_traced(
            &mut elab.typedefs,
            "insert:process_typedef_enum",
            td.name.name.clone(),
            enum_width,
        );
        let enum_dt = fold_packed_dims_with(&td.data_type, &elab.parameters, &|_, _| true)
            .unwrap_or_else(|| td.data_type.clone());
        elab.typedef_types.insert(td.name.name.clone(), enum_dt);
        elab.enum_members
            .insert(td.name.name.clone(), members_ordered);
    } else {
        // Non-enum typedef: resolve width from the underlying type.
        // `$bits(<signal>)` in the dims is prebound against the signal
        // table first (and the REWRITTEN type is what gets recorded, so
        // every later resolution agrees).
        let bound_dt = prebind_type_dims(&td.data_type, elab);
        let bound_dt = size_struct_member_dims(
            bound_dt.as_ref().unwrap_or(&td.data_type),
            &elab.parameters,
            &elab.typedef_types,
            true,
        )
        .or(bound_dt);
        let bound_dt = fold_packed_dims_with(
            bound_dt.as_ref().unwrap_or(&td.data_type),
            &elab.parameters,
            &|_, _| true,
        )
        .or(bound_dt);
        let eff_dt: &DataType = bound_dt.as_ref().unwrap_or(&td.data_type);
        // A `typedef class foo_pool;` is parsed as a Void placeholder with
        // `forward:false` (a forward CLASS declaration — §6.18). When the same
        // name is later/more-specifically defined as a REAL typedef alias to a
        // parameterized class (`typedef base#(args) foo_pool;`), this Void
        // placeholder must not CLOBBER the resolved typedef. If we already have
        // a non-Void value under this name, preserve it.
        if matches!(eff_dt, DataType::Void(_))
            && elab
                .typedef_types
                .get(&td.name.name)
                .is_some_and(|prev| !matches!(prev, DataType::Void(_)))
        {
            // preserve the resolved typedef — placeholder Void, no override
        } else {
            let w = resolve_type_width(eff_dt, Some(&elab.parameters), Some(&elab.typedefs));
            typedefs_insert_traced(
                &mut elab.typedefs,
                "insert:process_typedef",
                td.name.name.clone(),
                w,
            );
            if let Some(ew) = packed_inner_elem_width(eff_dt, &elab.parameters, &elab.typedefs) {
                elab.typedef_elem_widths.insert(td.name.name.clone(), ew);
            }
            elab.typedef_types
                .insert(td.name.name.clone(), eff_dt.clone());
            // Keep the field range IDENTIFIERS of a struct typedef before they
            // are folded away (captured from the pre-fold declared type), so
            // the port width-mismatch diagnostic can name the underflowed
            // parameter (`[P:0]` collapses to `[0:0]` in `typedef_types`).
            let mut range_ids: HashMap<String, Vec<String>> = HashMap::default();
            if let DataType::Struct(su) = &td.data_type {
                for m in &su.members {
                    let mut ids: Vec<String> = Vec::new();
                    if let DataType::IntegerVector { dimensions, .. } = &m.data_type {
                        for d in dimensions {
                            if let PackedDimension::Range { left, right, .. } = d {
                                collect_ident_names(left, &mut ids);
                                collect_ident_names(right, &mut ids);
                            }
                        }
                    }
                    ids.dedup();
                    if !ids.is_empty() {
                        for d in &m.declarators {
                            range_ids.insert(d.name.name.clone(), ids.clone());
                        }
                    }
                }
            }
            if !range_ids.is_empty() {
                elab.struct_field_range_idents
                    .insert(td.name.name.clone(), range_ids);
            }
        }
    }
    // §6.18/§7.4: record any unpacked dimensions on the typedef
    // (`typedef logic [7:0] A [0:3];`) so a variable `A v;` inherits them.
    // §6.18/§7.4.5: an alias of a dimensioned typedef (`typedef A B;`,
    // `typedef A C [2];`) carries the base's unpacked dimensions after its
    // own, and its element type is the base's element type. Recording only
    // the alias's own dimensions made `B v;` a scalar of the element width.
    let base_dims = match &td.data_type {
        DataType::TypeReference {
            name, dimensions, ..
        } if dimensions.is_empty() && name.qualified() != td.name.name => {
            lookup_scoped_type(name, &elab.typedef_unpacked_dims)
                .cloned()
                .map(|d| (d, lookup_scoped_type(name, &elab.typedef_types).cloned()))
        }
        _ => None,
    };
    if let Some((bd, elem)) = base_dims {
        let mut dims = fold_unpacked_dims(&td.dimensions, &elab.parameters, &elab.typedef_types);
        dims.extend(bd);
        elab.typedef_unpacked_dims
            .insert(td.name.name.clone(), dims);
        if let Some(elem) = elem {
            elab.typedef_types.insert(td.name.name.clone(), elem);
        }
    } else if !td.dimensions.is_empty() {
        let dims = fold_unpacked_dims(&td.dimensions, &elab.parameters, &elab.typedef_types);
        elab.typedef_unpacked_dims
            .insert(td.name.name.clone(), dims);
    } else if !matches!(td.data_type, DataType::Void(_)) {
        elab.typedef_unpacked_dims.remove(&td.name.name);
    }
    // §20.6.2/§20.7: const-eval sizes `$bits(arr_t)` / `$dimensions(v)` from
    // the full definition, not just the element width.
    if let Some(dt) = elab.typedef_types.get(&td.name.name) {
        let dims = elab
            .typedef_unpacked_dims
            .get(&td.name.name)
            .unwrap_or(&td.dimensions);
        tls_register_typedef_shape(&td.name.name, dt, dims);
    }
    // Refresh the thread-local typedef snapshot so any subsequent
    // const-eval `$bits(typedef_name)` call sees this typedef (M2).
    type_trace_tls_refresh("process_typedef", &elab.typedefs);
    sync_typedefs_tls(&elab.typedefs);
}
