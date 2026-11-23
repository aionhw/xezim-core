use super::*;

/// §7.6: one side of a continuous copy between fixed arrays of an unpacked
/// structure type: its constant storage path (a plain, hierarchical `u.a`
/// or member `x.arr` array name, optionally with leading constant indices,
/// a row `a[4]`), the fixed dimensions left below that path, and the element
/// structure. None for any other expression.
fn struct_array_side<'e>(
    elab: &'e ElaboratedModule,
    expr: &Expression,
) -> Option<(String, &'e [(i64, i64)], &'e StructUnionType)> {
    let path = const_parameter_path(expr, Some(&elab.parameters))?;
    let mut base = path.as_str();
    let mut rank = 0;
    while base.ends_with(']') {
        let bracket = base.rfind('[')?;
        base[bracket + 1..base.len() - 1].parse::<i64>().ok()?;
        base = &base[..bracket];
        rank += 1;
    }
    // Built-in net arrays can have member storage without member driver
    // resolution. Keep their drivers on the array path.
    if elab.z_init_signals.contains(base) {
        return None;
    }
    let dims = elab.unpacked_decl_dims.get(base)?.get(rank..)?;
    if dims.is_empty() {
        return None;
    }
    let dt = elab
        .var_decl_types
        .get(base)
        .or_else(|| declared_type_name(elab, base).and_then(|tn| elab.typedef_types.get(&tn)))?;
    match resolve_typedef_chain(dt, &elab.typedef_types) {
        DataType::Struct(su)
            if !su.packed && !su.members.is_empty() && su.kind == StructUnionKind::Struct =>
        {
            Some((path, dims, su))
        }
        _ => None,
    }
}

/// §7.6, §10.3: a continuous copy between fixed arrays, or rows of them, of
/// one unpacked structure type, as one assignment per element pair in
/// left-to-right order, so the member pass drives each element's members.
/// None for any other shape.
pub(super) fn struct_array_copy_parts(
    elab: &ElaboratedModule,
    ca: &ContinuousAssignment,
) -> Option<Vec<ContinuousAssignment>> {
    let (lhs_path, lhs_dims, lhs_su) = struct_array_side(elab, &ca.lhs)?;
    let (rhs_path, rhs_dims, rhs_su) = struct_array_side(elab, &ca.rhs)?;
    let lhs_base = lhs_path.split('[').next().unwrap_or(&lhs_path);
    // §6.22.2 / §7.6: both sides name the same element type (one
    // declaration, whatever spelling reached it: `S` through an import and
    // `p::S`), and each pair of dimensions has equal counts.
    let same_type = std::ptr::eq(lhs_su, rhs_su)
        || (lhs_su.span != Span::dummy() && lhs_su.span == rhs_su.span);
    if !same_type
        || lhs_dims.len() != rhs_dims.len()
        || lhs_dims
            .iter()
            .zip(rhs_dims)
            .any(|(&(ll, lr), &(rl, rr))| ll.abs_diff(lr) != rl.abs_diff(rr))
        || declared_type_name(elab, lhs_base)
            .and_then(|ty| elab.nettype_resolvers.get(&ty))
            .is_some_and(|resolver| !resolver.is_empty())
    {
        return None;
    }
    // Only arrays with registered member signals can use the member pass.
    let first_element = |path: &str, dims: &[(i64, i64)]| {
        dims.iter().fold(path.to_string(), |mut path, (left, _)| {
            use std::fmt::Write;
            let _ = write!(path, "[{left}]");
            path
        })
    };
    if !elab
        .struct_members
        .contains_key(&first_element(&lhs_path, lhs_dims))
        || !elab
            .struct_members
            .contains_key(&first_element(&rhs_path, rhs_dims))
    {
        return None;
    }
    let lhs_indices = cartesian_index_tuples(&bounded_declared_index_lists(lhs_dims)?);
    let rhs_indices = cartesian_index_tuples(&bounded_declared_index_lists(rhs_dims)?);
    Some(
        lhs_indices
            .into_iter()
            .zip(rhs_indices)
            .map(|(lhs_indices, rhs_indices)| ContinuousAssignment {
                lhs: lhs_indices.into_iter().fold(ca.lhs.clone(), index_expr),
                rhs: rhs_indices.into_iter().fold(ca.rhs.clone(), index_expr),
                ..ca.clone()
            })
            .collect(),
    )
}

/// §6.6.7 user-defined nettype resolution, over the WHOLE elaborated design.
///
/// Runs after `inline_instantiations`, so a net driven from several module
/// instances through ports — the loading-effect topology user-defined nettypes
/// exist for — has all of its drivers in hand:
///
/// ```text
///     module src(inout rnet p);  assign p = V;  endmodule
///     rnet node;  src u1(.p(node));  src u2(.p(node));  assign node = local;
/// ```
///
/// Every driver rewrites onto `node` during inlining; this folds them all,
/// instance and parent alike, into ONE call:
///
/// ```text
/// assign node = res('{d0, d1, d2});
/// ```
///
/// Resolving per module instead would fold each module's drivers separately and
/// then resolve the results again — correct only for an additive resolver.
///
/// Must run BEFORE `resolve_multi_driver_nets`: that folds multi-driven nets
/// with the bitwise `$__wres` chain, which is meaningless for a nettype. After
/// this pass a nettype net has exactly one driver, so it is left alone there.
/// §7.2.2: expand a whole-struct continuous assign into one assign per member,
/// over the WHOLE elaborated design.
///
/// An unpacked struct is stored as one signal per member, so `assign s = <expr>`
/// has nowhere to land — every member reads back 0. The per-module expansion
/// catches the ones written in the module being elaborated, but a child module's
/// assign arrives later, through `inline_instantiations`:
///
/// ```text
///     module ch #(parameter real P = 3.5) (output S o);
///       assign o = '{P, 1.0};        // o.a read 0 in the parent
/// ```
///
/// Nothing expanded that, because by the time it exists the per-module pass has
/// already run. Doing it here catches both.
///
/// Runs after `resolve_user_nettype_drivers`, which does its own member
/// expansion for nettype nets (it has to — the resolver call only exists there);
/// those emerge with leaf-path targets (`n.V`), which name no struct, and are
/// left alone.
pub fn expand_unpacked_struct_assigns(elab: &mut ElaboratedModule) {
    if !has_unpacked_struct_type(elab) {
        return;
    }
    // §23.3.3.5: instance-array splitting produces `w[k]` actuals. They
    // still denote whole structs, but `ident_flat_name` deliberately rejects
    // selects. Recover only constant storage paths here, not arbitrary
    // expressions: evaluating an index per member could repeat side effects.
    let struct_target = |elab: &ElaboratedModule, expr: &Expression| {
        let name = const_parameter_path(expr, Some(&elab.parameters))?;
        let mut base = name.as_str();
        let mut rank = 0;
        while base.ends_with(']') {
            let bracket = base.rfind('[')?;
            base[bracket + 1..base.len() - 1].parse::<i64>().ok()?;
            base = &base[..bracket];
            rank += 1;
        }
        // Only consume unpacked dimensions, never packed bit selects or a
        // partial array. The element's declared type lives on the array.
        if elab.unpacked_decl_dims.get(base).map_or(0, Vec::len) != rank {
            return None;
        }
        let dt = elab.var_decl_types.get(base).or_else(|| {
            declared_type_name(elab, base).and_then(|tn| elab.typedef_types.get(&tn))
        })?;
        match resolve_typedef_chain(dt, &elab.typedef_types) {
            // A PACKED struct keeps a contiguous bit layout that a
            // whole-value write already fills correctly.
            DataType::Struct(su) if !su.packed && !su.members.is_empty() => {
                Some((name, su.clone()))
            }
            _ => None,
        }
    };

    // A sub-module body may still sit in the LAZY pending list, which the loop
    // below never sees: `assign o = '{x, 7};` in a child of the usual (lazily
    // inlined) kind kept its whole-struct lhs, wrote a container no reader
    // looks at, and the parent's port copy read the leaves' defaults. Bring
    // exactly the entries landing on an unpacked struct into the eager list.
    // Whole fixed arrays first need the same ordered split as the eager drain.
    {
        let has_fixed_arrays = !elab.unpacked_decl_dims.is_empty();
        let pending = std::mem::take(&mut elab.pending_cont_assign);
        for pca in pending {
            let lhs = pca.materialize_lhs();
            if struct_target(elab, &lhs).is_some() {
                let ca = pca.materialize(&elab.parameters);
                elab.continuous_assigns.push(ca);
            } else if has_fixed_arrays
                && struct_array_side(elab, &lhs).is_some()
                && let Some(parts) =
                    struct_array_copy_parts(elab, &pca.clone().materialize(&elab.parameters))
            {
                elab.continuous_assigns.extend(parts);
            } else {
                elab.pending_cont_assign.push(pca);
            }
        }
    }

    // The per-module pass's expansion: ordered and NAMED patterns are taken
    // apart item by item, nested structs and array members recurse, and each
    // leaf is named by a hierarchical path (`u.o.a`) that resolves to the
    // member's own signal — a `real` member stays real (a `MemberAccess` lhs
    // here wrote `4.5` as `5`).
    let mut out: Vec<ContinuousAssignment> = Vec::new();
    let has_fixed_arrays = !elab.unpacked_decl_dims.is_empty();
    for ca in std::mem::take(&mut elab.continuous_assigns) {
        if let Some((base, su)) = struct_target(elab, &ca.lhs) {
            expand_struct_driver(elab, &ca, &base, &su, &mut out);
            continue;
        }
        // A whole copy the per-module pass left unsplit: a multidimensional
        // array, a row, a hierarchical or a member array (§7.6).
        let parts = has_fixed_arrays
            .then(|| struct_array_copy_parts(elab, &ca))
            .flatten();
        let Some(parts) = parts else {
            out.push(ca);
            continue;
        };
        for part in parts {
            match struct_target(elab, &part.lhs) {
                Some((base, su)) => expand_struct_driver(elab, &part, &base, &su, &mut out),
                None => out.push(part),
            }
        }
    }
    elab.continuous_assigns = out;
}

/// §6.6.8: the nettype net an element select names. `a[0]` where `a` is a
/// nettype ARRAY names the ELEMENT's own resolvable net `a[0]`; the driver
/// count of that element stays independent of a sibling (`a[1]`). A plain
/// identifier returns its own name (an Index/RangeSelect names the base for
/// non-array selects). None when the expression is not a nettype-net LHS.
fn net_base_of(elab: &ElaboratedModule, e: &Expression) -> Option<String> {
    if let Some(n) = ident_flat_name(e) {
        return Some(n);
    }
    match &e.kind {
        ExprKind::Index {
            expr: base,
            index,
            ..
        } => {
            let bn = whole_net_ident_name(base)?;
            if !elab.arrays.contains_key(&bn) {
                return None;
            }
            let idx = eval_const_expr_val(index, &elab.parameters).to_i64()?;
            let (lo, hi, _) = elab.arrays[&bn];
            if idx < lo.min(hi) || idx > lo.max(hi) {
                return None;
            }
            let elem = format!("{bn}[{idx}]");
            // §5.6.1: an escaped identifier (`\a[0] `) is ONE declared scalar
            // whose flat name is `a[0]`; array elements live under the base
            // (§7.4.2) and are NEVER separate `signals` entries. If a signal of
            // that spelling exists, it is the escaped scalar, a DIFFERENT
            // object from element `a[idx]` — leave the element to the ordinary
            // (runtime) path so two different objects stay separate.
            if elab.signals.contains_key(&elem) {
                return None;
            }
            Some(elem)
        }
        _ => None,
    }
}

/// §6.6.7, §10.3.1: the declaration assignment of a user-defined-nettype net
/// (`rn #3 n = e;`) is a continuous driver of the net, subject to its
/// resolution function. §10.3.3: its delay belongs to that driver. The parser
/// keeps the `#3` in the type's argument list, which the delay pass has already
/// scaled to ticks for a nettype name.
pub(super) fn nettype_declaration_driver(
    dd: &crate::ast::decl::DataDeclaration,
    name: &str,
    init: &Expression,
    rhs_parent_scoped: bool,
    params: &HashMap<String, Value>,
) -> ContinuousAssignment {
    let (delay, delay_fall, delay_off, delay_exprs) = nettype_delay(dd, params);
    ContinuousAssignment {
        gate_delay_fall: None,
        delay_exprs,
        delay_select: None,
        origin: Some((init.span, top_origin_scope())),
        lhs: make_ident_expr(name),
        rhs: init.clone(),
        delay,
        rhs_parent_scoped,
        delay_fall,
        delay_off,
    }
}

/// The (rise, fall, turn-off) ticks of a nettype net declaration's delay.
fn nettype_delay(
    dd: &crate::ast::decl::DataDeclaration,
    params: &HashMap<String, Value>,
) -> (u64, Option<u64>, Option<u64>, Option<DelayExpressions>) {
    let args: &[Expression] = match &dd.data_type {
        DataType::TypeReference { type_args, .. } => type_args,
        _ => &[],
    };
    cont_assign_delays([args.first(), args.get(1), args.get(2)], params)
}

/// §6.7.1, §10.3.3: without a declaration assignment, a nettype net's delay
/// is a net delay, which delays every driver of the net (`rn #2 n;`).
pub(super) fn nettype_net_delay(
    dd: &crate::ast::decl::DataDeclaration,
    decl: &crate::ast::stmt::VarDeclarator,
    params: &HashMap<String, Value>,
) -> Option<(u64, Option<u64>, Option<u64>, Option<DelayExpressions>)> {
    if decl.init.is_some() || !decl.dimensions.is_empty() {
        return None;
    }
    let (rise, fall, off, exprs) = nettype_delay(dd, params);
    (rise != 0 || fall.unwrap_or(0) != 0 || off.unwrap_or(0) != 0 || exprs.is_some())
        .then_some((rise, fall, off, exprs))
}

/// §6.6.8: an emit LHS naming an ARRAY ELEMENT (`a[0]`) must be a real Index
/// expression — a flat ident literally named `a[0]` does not resolve to the
/// element's storage.
pub(super) fn make_net_lhs_expr(name: &str) -> Expression {
    if let Some(open) = name.rfind('[')
        && name.ends_with(']')
        && let Ok(idx) = name[open + 1..name.len() - 1].parse::<i64>()
    {
        let base = &name[..open];
        return Expression::new(
            ExprKind::Index {
                expr: Box::new(make_ident_expr(base)),
                index: Box::new(int_literal(idx, Span::dummy())),
            },
            Span::dummy(),
        );
    }
    make_ident_expr(name)
}

/// Qualify unscoped type keys in a resolved-nettype struct driver pattern from
/// `scope` (for example, a module type parameter or local typedef `T:` inside an
/// inlined child instance whose folded resolver CA has no origin scope).
fn qualify_nettype_pattern_types(
    expr: Expression,
    struct_members: Option<&[(String, DataType, Vec<UnpackedDimension>)]>,
    scope: &str,
    elab: &ElaboratedModule,
) -> Expression {
    if scope.is_empty() {
        return expr;
    }
    fn rewrite_pattern(
        expr: Expression,
        struct_members: Option<&[(String, DataType, Vec<UnpackedDimension>)]>,
        scope: &str,
        elab: &ElaboratedModule,
    ) -> Expression {
        let span = expr.span;
        let kind = match expr.kind {
            ExprKind::TypedPattern { ty, pattern } => ExprKind::TypedPattern {
                ty,
                pattern: Box::new(rewrite_pattern(*pattern, struct_members, scope, elab)),
            },
            ExprKind::AssignmentPattern(items) => {
                let mut pos = 0usize;
                let out = items
                    .into_iter()
                    .map(|item| {
                        let child_members = |item: &AssignmentPatternItem, pos: usize| {
                            let ms = struct_members?;
                            let dt = match item {
                                AssignmentPatternItem::Named(id, _) => ms
                                    .iter()
                                    .find(|(m, _, _)| *m == id.name)
                                    .map(|(_, dt, dims)| (dt, dims)),
                                AssignmentPatternItem::Ordered(_) => {
                                    ms.get(pos).map(|(_, dt, dims)| (dt, dims))
                                }
                                _ => None,
                            }?;
                            if !dt.1.is_empty() {
                                return None;
                            }
                            match resolve_typedef_chain(dt.0, &elab.typedef_types) {
                                DataType::Struct(su) if !su.packed => Some(
                                    su.members
                                        .iter()
                                        .flat_map(|m| {
                                            m.declarators.iter().map(|d| {
                                                (
                                                    d.name.name.clone(),
                                                    m.data_type.clone(),
                                                    d.dimensions.clone(),
                                                )
                                            })
                                        })
                                        .collect::<Vec<_>>(),
                                ),
                                _ => None,
                            }
                        };
                        let nested_ms = child_members(&item, pos);
                        if matches!(item, AssignmentPatternItem::Ordered(_)) {
                            pos += 1;
                        }
                        if let AssignmentPatternItem::Named(ref k, ref v) = item
                            && k.type_key.is_none()
                        {
                            let is_member = struct_members
                                .is_some_and(|ms| ms.iter().any(|(m, _, _)| *m == k.name));
                            if !is_member
                                && !is_param_in_scope(&k.name, scope, &elab.parameters)
                                && !is_signal_in_scope(&k.name, scope, elab)
                                && let Some(key) =
                                    lookup_typedef_key_in_scope(&k.name, scope, &elab.typedef_types)
                                && key != k.name
                            {
                                let dt = DataType::TypeReference {
                                    name: TypeName {
                                        scopes: Vec::new(),
                                        name: Identifier {
                                            name: key,
                                            span: k.span,
                                        },
                                        span: k.span,
                                        bound: Default::default(),
                                    },
                                    dimensions: Vec::new(),
                                    type_args: Vec::new(),
                                    span: k.span,
                                };
                                let v2 =
                                    rewrite_pattern(v.clone(), nested_ms.as_deref(), scope, elab);
                                return AssignmentPatternItem::Typed(dt, v2);
                            }
                        }
                        match item {
                            AssignmentPatternItem::Ordered(v) => AssignmentPatternItem::Ordered(
                                rewrite_pattern(v, nested_ms.as_deref(), scope, elab),
                            ),
                            AssignmentPatternItem::Named(k, v) => AssignmentPatternItem::Named(
                                k,
                                rewrite_pattern(v, nested_ms.as_deref(), scope, elab),
                            ),
                            AssignmentPatternItem::Typed(t, v) => AssignmentPatternItem::Typed(
                                t,
                                rewrite_pattern(v, nested_ms.as_deref(), scope, elab),
                            ),
                            AssignmentPatternItem::Default(v) => AssignmentPatternItem::Default(
                                rewrite_pattern(v, nested_ms.as_deref(), scope, elab),
                            ),
                            AssignmentPatternItem::Keyed(k, v) => AssignmentPatternItem::Keyed(
                                k,
                                rewrite_pattern(v, nested_ms.as_deref(), scope, elab),
                            ),
                        }
                    })
                    .collect();
                ExprKind::AssignmentPattern(out)
            }
            other => other,
        };
        Expression::new(kind, span)
    }
    rewrite_pattern(expr, struct_members, scope, elab)
}

fn is_signal_in_scope(name: &str, scope: &str, elab: &ElaboratedModule) -> bool {
    if !scope.is_empty() {
        let mut cur = scope;
        loop {
            if elab.signals.contains_key(&format!("{cur}.{name}")) {
                return true;
            }
            let Some((outer, _)) = cur.rsplit_once('.') else {
                break;
            };
            cur = outer;
        }
    }
    elab.signals.contains_key(name)
}

/// Compact index-based Disjoint-Set Union with path halving and union by size.
struct IndexDsu {
    parent: Vec<u32>,
    size: Vec<u32>,
}

impl IndexDsu {
    fn new(n: usize) -> Self {
        Self {
            parent: (0..n as u32).collect(),
            size: vec![1; n],
        }
    }

    fn find(&mut self, mut x: u32) -> u32 {
        while self.parent[x as usize] != x {
            let p = self.parent[x as usize];
            let gp = self.parent[p as usize];
            self.parent[x as usize] = gp;
            x = gp;
        }
        x
    }

    fn union(&mut self, a: u32, b: u32) -> u32 {
        let mut ra = self.find(a);
        let mut rb = self.find(b);
        if ra == rb {
            return ra;
        }
        if self.size[ra as usize] < self.size[rb as usize] {
            std::mem::swap(&mut ra, &mut rb);
        }
        self.parent[rb as usize] = ra;
        self.size[ra as usize] += self.size[rb as usize];
        ra
    }

    fn push_singleton(&mut self) -> u32 {
        let id = self.parent.len() as u32;
        self.parent.push(id);
        self.size.push(1);
        id
    }
}

/// Compute `alias` equivalence classes over `alias_groups` + `net_port_merges`
/// in O((G + M) * α(N)) with zero string allocations during union/find.
/// Each returned group contains its members in `unify_alias_nets` priority
/// order (declared alias groups first, then port-merge additions) and the
/// chosen canonical net name (if any member is a known net/signal).
pub(super) fn collect_alias_components<'a>(
    elab: &'a ElaboratedModule,
) -> Vec<(Option<String>, Vec<String>)> {
    if elab.alias_groups.is_empty() {
        return Vec::new();
    }
    let mut id_of: HashMap<&'a str, u32> = HashMap::default();
    let mut names: Vec<&'a str> = Vec::new();
    let mut dsu = IndexDsu::new(0);
    let mut has_alias: Vec<bool> = Vec::new();

    let mut intern = |s: &'a str, dsu: &mut IndexDsu, has_alias: &mut Vec<bool>| -> u32 {
        if let Some(&id) = id_of.get(s) {
            return id;
        }
        let id = dsu.push_singleton();
        id_of.insert(s, id);
        names.push(s);
        has_alias.push(false);
        id
    };

    for group in &elab.alias_groups {
        if group.len() < 2 {
            continue;
        }
        let first = intern(group[0].as_str(), &mut dsu, &mut has_alias);
        has_alias[dsu.find(first) as usize] = true;
        for n in &group[1..] {
            let id = intern(n.as_str(), &mut dsu, &mut has_alias);
            let r = dsu.union(first, id);
            has_alias[r as usize] = true;
        }
    }
    for (formal, actual) in &elab.net_port_merges {
        let f_id = intern(formal.as_str(), &mut dsu, &mut has_alias);
        let a_id = intern(actual.as_str(), &mut dsu, &mut has_alias);
        let fa = has_alias[dsu.find(f_id) as usize] || has_alias[dsu.find(a_id) as usize];
        let r = dsu.union(f_id, a_id);
        has_alias[r as usize] |= fa;
    }

    let mut comp_members: HashMap<u32, Vec<String>> = HashMap::default();
    let mut comp_order: Vec<u32> = Vec::new();
    let mut seen: HashSet<&'a str> = HashSet::default();
    for group in &elab.alias_groups {
        if group.len() < 2 {
            continue;
        }
        for n in group {
            if !seen.insert(n.as_str()) {
                continue;
            }
            let root = dsu.find(id_of[n.as_str()]);
            if !comp_members.contains_key(&root) {
                comp_order.push(root);
            }
            comp_members.entry(root).or_default().push(n.clone());
        }
    }
    for (formal, actual) in &elab.net_port_merges {
        for n in [formal.as_str(), actual.as_str()] {
            if !seen.insert(n) {
                continue;
            }
            let root = dsu.find(id_of[n]);
            if !has_alias[root as usize] {
                continue;
            }
            if !comp_members.contains_key(&root) {
                comp_order.push(root);
            }
            comp_members.entry(root).or_default().push(n.to_string());
        }
    }

    comp_order
        .into_iter()
        .map(|root| {
            let members = comp_members.remove(&root).unwrap_or_default();
            let canon = members
                .iter()
                .find(|n| elab.nets.contains(n.as_str()) || elab.signals.contains_key(n.as_str()))
                .cloned();
            (canon, members)
        })
        .collect()
}

pub fn resolve_user_nettype_drivers(elab: &mut ElaboratedModule) -> Result<(), String> {
    if elab.nettype_resolvers.is_empty() {
        return Ok(());
    }

    // A nettype net that is an UNPACKED ARRAY resolves per element (§6.6.7,
    // §6.6.8): `interconnect realN a[1]; source s(a[0]); load l(a[0]);` — a
    // port connection drives the ELEMENT `a[0]`, an Index expression whose
    // base is the array. `ident_flat_name` returns None for a select, so such
    // a driver would be invisible to the fold below. Resolve the LHS to its
    // NETTYPE ARRAY first, then treat an ELEMENT select as a driver of that
    // element (`a[0]`), which the seeding above put in the resolver. A
    // bare array name (`a`) keeps the whole-array key a driver may have.

    // §6.18, §26.5: a variable whose type name the top module's own typedef
    // or type parameter takes from an outer nettype is not a nettype net.
    let hidden =
        |name: &str, tn: &str| elab.shadowed_nettypes.contains(tn) && !elab.nets.contains(name);
    // net name -> resolver, for every signal whose declared type is a nettype.
    let mut net_resolver: HashMap<String, String> = HashMap::default();
    for (name, sig) in &elab.signals {
        if let Some(tn) = &sig.type_name {
            if let Some(r) = elab.nettype_resolvers.get(tn)
                && !hidden(name, tn)
            {
                net_resolver.insert(name.clone(), r.clone());
            }
        }
    }
    // §6.6.7(d) + §7.2: a nettype over an UNPACKED STRUCT has no signal under
    // its own name inside an instance — the sub-module declaration path
    // registers the member LEAVES and returns, because an unpacked struct is
    // per-member storage. The scan above reads `signals[..].type_name`, so such
    // a net was invisible here: its drivers were never gathered, the resolution
    // function never ran, and every read came back with the members' defaults.
    // Silently, and only below the top level — the same declaration in the root
    // module resolved correctly, because that path does leave a base signal
    // behind.
    //
    // `var_decl_types` is the record the instance path DOES write, so take the
    // declared type from there for any name the signal scan missed.
    let mut from_decls: Vec<(String, String)> = Vec::new();
    for (name, dt) in &elab.var_decl_types {
        if net_resolver.contains_key(name) {
            continue;
        }
        if let Some(tn) = get_type_name(dt) {
            if let Some(r) = elab.nettype_resolvers.get(&tn)
                && !hidden(name, &tn)
            {
                from_decls.push((name.clone(), r.clone()));
            }
        }
    }
    // Deterministic: `var_decl_types` iteration order must not reach the output.
    from_decls.sort();
    for (name, resolver) in from_decls {
        net_resolver.insert(name, resolver);
    }
    // §6.6.8: a nettype net that is an UNPACKED ARRAY resolves PER ELEMENT
    // (`interconnect realN a[1]; source s(a0); load l(a1);` — element a[1]
    // must resolve its own drivers, independent of a[0]). Seed each declared
    // element `a[lo]`..`a[hi]` with the base array's resolver, so an
    // element-select driver (`assign a[0] = ...`) is folded onto its OWN
    // element instead of the whole array.
    // §5.6.1: an escaped identifier (`\a[0] `) is ONE identifier whose name
    // contains the brackets — it lands in `signals` as the flat name `a[0]`,
    // a DIFFERENT object from element 0 of the array `a` (§7.4.2). Do not
    // seed an element key over a declared signal of that spelling: the
    // declared object keeps its own (resolver-less) treatment.
    let mut elem_resolvers: Vec<(String, String)> = Vec::new();
    if !elab.arrays.is_empty() {
        for (base, resolver) in &net_resolver {
            if let Some(&(lo, hi, _)) = elab.arrays.get(base)
                && !resolver.is_empty()
            {
                for i in lo..=hi {
                    let elem = format!("{base}[{i}]");
                    if elab.signals.contains_key(&elem) {
                        continue;
                    }
                    elem_resolvers.push((elem, resolver.clone()));
                }
            }
        }
    }
    elem_resolvers.sort();
    for (elem, resolver) in elem_resolvers {
        net_resolver.insert(elem, resolver);
    }
    if net_resolver.is_empty() {
        return Ok(());
    }

    // §23.6, §27.6: a continuous driver can reach a resolved net from a
    // different module or through an indexed generate scope. Qualify the
    // latter in the writing instance, just as for an indexed port actual.
    let driver_net = |elab: &ElaboratedModule, e: &Expression, scope: &str| {
        if let Some(mut name) = net_base_of(elab, e) {
            // The parser can retain "$root" as the first path segment.
            let absolute = name.strip_prefix("$root.").unwrap_or(&name);
            if let Some(short) = absolute.strip_prefix(&elab.name).and_then(|s| s.strip_prefix('.'))
                && net_resolver.contains_key(short)
                && !net_resolver.contains_key(&name)
            {
                name = short.to_owned();
            }
            return Some(name);
        }
        if !matches!(e.kind, ExprKind::MemberAccess { .. } | ExprKind::Ident(_)) {
            return None;
        }
        let prefix = scope.trim_end_matches('.');
        let prefix = if prefix.is_empty() { String::new() } else { format!("{prefix}.") };
        scope_indexed_net_name(e, &prefix, elab)
    };

    // A sub-module body may still sit in the LAZY pending list, where two
    // instances driving one parent net are invisible. Materialize exactly the
    // entries landing on a nettype net — the treatment
    // `resolve_multi_driver_nets` gives its own folds.
    {
        let pending = std::mem::take(&mut elab.pending_cont_assign);
        for pca in pending {
            let lhs = pca.materialize_lhs();
            // A member of one too (`u.p.V`): a port connection taken apart.
            // §6.6.8: an element select of a nettype ARRAY (`a[0]`) names that
            // element's resolvable net too.
            if driver_net(elab, &lhs, &pca.ctx.prefix).is_some_and(|n| {
                net_resolver.contains_key(&n)
                    || n.match_indices('.')
                        .any(|(i, _)| net_resolver.contains_key(&n[..i]))
            }) {
                let ca = pca.materialize(&elab.parameters);
                elab.continuous_assigns.push(ca);
            } else {
                elab.pending_cont_assign.push(pca);
            }
        }
    }

    // A nettype net connected through a module PORT is elaborated as its own
    // signal joined to the parent's by an identity continuous assign
    // (`assign node = u1.p;`). Resolving each of those nets separately would
    // run the resolution function once per port net and then AGAIN on the
    // results — invisible for an associative resolver like a sum, badly wrong
    // for anything else (Millman's theorem over Thevenin drivers collapsed to
    // zero). §6.6.7 resolves the drivers of a net ONCE.
    //
    // So union the nets joined by identity assigns and treat each connected
    // component as the single net it physically is: gather every real driver in
    // the component, resolve once onto a representative, and alias the rest.
    // Precompute alias-group canonical map so scalar/vector nettype aliases
    // pick the same canonical storage name as `unify_alias_nets` and skip
    // emitting redundant `m = root` copies that `resolve_multi_driver_nets`
    // would otherwise count as extra drivers on the aliased net.
    let alias_canon_preview: HashMap<String, String> = if elab.alias_groups.is_empty() {
        HashMap::default()
    } else {
        let mut map = HashMap::default();
        for (canon_opt, members) in collect_alias_components(elab) {
            if let Some(canon) = canon_opt {
                for m in members {
                    map.insert(m, canon.clone());
                }
            }
        }
        map
    };

    // Index-based union-find over `net_resolver` keys (zero string cloning on
    // find/union, path halving, and lazy member collection for non-singletons).
    let mut all_nets: Vec<String> = net_resolver.keys().cloned().collect();
    all_nets.sort();
    let mut net_id: HashMap<String, u32> = HashMap::with_capacity_and_hasher(
        all_nets.len(),
        Default::default(),
    );
    for (i, n) in all_nets.iter().enumerate() {
        net_id.insert(n.clone(), i as u32);
    }
    let mut dsu = IndexDsu::new(all_nets.len());

    // §10.11: an `alias` statement declares multiple names for the same physical
    // net, so their drivers must join one component and resolve together once.
    for group in &elab.alias_groups {
        if group.len() < 2 {
            continue;
        }
        let first_id = group.iter().find_map(|n| net_id.get(n.as_str()).copied());
        if let Some(fid) = first_id {
            for n in group {
                if let Some(&id) = net_id.get(n.as_str()) {
                    dsu.union(fid, id);
                }
            }
        }
        // Aliased unpacked nettype arrays (`alias a1 = a2;`) share elements pairwise.
        if !elab.arrays.is_empty()
            && let Some((base0, &(lo, hi, _))) = group
                .iter()
                .find_map(|n| elab.arrays.get(n.as_str()).map(|b| (n.as_str(), b)))
        {
            for i in lo..=hi {
                let elem0 = format!("{base0}[{i}]");
                let Some(&e0) = net_id.get(&elem0) else {
                    continue;
                };
                for n in group {
                    if n == base0 {
                        continue;
                    }
                    let elem = format!("{n}[{i}]");
                    if let Some(&ei) = net_id.get(&elem) {
                        dsu.union(e0, ei);
                    }
                }
            }
        }
    }

    // net -> its real drivers with their own delays and origin scope (§10.3.3).
    let mut real_drivers: HashMap<String, Vec<(Expression, u64, String)>> = HashMap::default();
    let mut order: Vec<String> = Vec::new();
    let mut delays: HashMap<String, u64> = HashMap::default();
    let mut kept: Vec<ContinuousAssignment> = Vec::new();

    // Member-wise drivers of resolver-less nets: net -> member -> count.
    let mut member_drivers: HashMap<String, HashMap<String, usize>> = HashMap::default();
    // The nettype net a member path (`u.p.V`) belongs to, and the member.
    let net_member = |name: &str| -> Option<(String, String)> {
        name.match_indices('.')
            .map(|(i, _)| (&name[..i], &name[i + 1..]))
            .find(|(net, _)| net_resolver.contains_key(*net))
            .map(|(net, m)| (net.to_string(), m.to_string()))
    };
    for ca in std::mem::take(&mut elab.continuous_assigns) {
        let scope = ca.origin.as_ref().map_or("", |(_, s)| s.as_ref());
        let Some(lhs_name) = driver_net(elab, &ca.lhs, scope).filter(|n| net_resolver.contains_key(n))
        else {
            // §6.6.7, §23.3.3: a port connection of a resolver-less
            // unpacked-struct net arrives member by member (`n.V = u.p.V`).
            // It joins the two nets for the one-driver count, as the
            // whole-net link below does, and stays an ordinary assignment.
            let joined = ident_flat_name(&ca.lhs)
                .and_then(|l| net_member(&l))
                .zip(ident_flat_name(&ca.rhs).and_then(|r| net_member(&r)))
                .filter(|((ln, lm), (rn, rm))| {
                    lm == rm
                        && ln != rn
                        && net_resolver[ln].is_empty()
                        && net_resolver[rn].is_empty()
                });
            if let Some(((ln, _), (rn, _))) = joined {
                if let (Some(&a), Some(&b)) = (net_id.get(&ln), net_id.get(&rn)) {
                    dsu.union(a, b);
                }
            } else if let Some((net, m)) = ident_flat_name(&ca.lhs)
                .and_then(|l| net_member(&l))
                .filter(|(net, _)| net_resolver[net].is_empty())
            {
                // A whole-net driver an earlier pass already took apart.
                *member_drivers.entry(net).or_default().entry(m).or_insert(0) += 1;
            }
            kept.push(ca);
            continue;
        };
        // §6.6.7: without a resolver the driver is an ordinary assignment.
        // Keep it (and its port links) for `expand_unpacked_struct_assigns`:
        // the resolver emitter selects members of an evaluated struct, but
        // an assignment pattern needs type-directed expansion instead.
        // Still gather the drivers below for the existing count check.
        if net_resolver[&lhs_name].is_empty() {
            kept.push(ca.clone());
        }
        // A port CONNECTION to another nettype net merges the two nets
        // (§23.3.3.7.1: "any port connection with an interconnect net shall
        // merge"). An `origin` marks a user BODY continuous assign
        // (`assign o = i;`), which stays a DIRECTIONAL driver of `o` reading
        // `i` — a buffer must not backward-resolve its input, so its internal
        // assignment is not a merge even though both ends are nettype nets.
        // An element select on the RHS (`u.i = a[0]`) is likewise a directional
        // read of the element, whose own fold writes the element's storage.
        if let Some(rhs_name) = ca.origin.is_none().then(|| driver_net(elab, &ca.rhs, scope)).flatten() {
            if net_resolver.contains_key(&rhs_name) && rhs_name != lhs_name {
                if let (Some(&a), Some(&b)) = (net_id.get(&lhs_name), net_id.get(&rhs_name)) {
                    dsu.union(a, b);
                }
                continue;
            }
        }
        if let std::collections::hash_map::Entry::Vacant(entry) = delays.entry(lhs_name.clone()) {
            entry.insert(ca.delay);
            order.push(lhs_name.clone());
        }
        let scope = ca
            .origin
            .as_ref()
            .map(|(_, s)| s.to_string())
            .unwrap_or_default();
        real_drivers
            .entry(lhs_name)
            .or_default()
            .push((ca.rhs, ca.delay, scope));
    }

    // Choose a deterministic representative name for each component:
    // prefer the `alias` canonical net (if any) or a member registered in
    // `elab.signals` so staged delay nets and reads align on one slot.
    let mut dsu_rep: Vec<u32> = (0..all_nets.len() as u32).collect();
    let rep_rank: Vec<u8> = all_nets
        .iter()
        .map(|n| {
            if alias_canon_preview.get(n).is_some_and(|c| c == n) {
                2
            } else if elab.signals.contains_key(n) {
                1
            } else {
                0
            }
        })
        .collect();
    for (idx, _) in all_nets.iter().enumerate() {
        let root = dsu.find(idx as u32);
        let cur_rep = dsu_rep[root as usize];
        if rep_rank[idx] > rep_rank[cur_rep as usize] {
            dsu_rep[root as usize] = idx as u32;
        }
    }

    // Only non-singleton components need member lists (avoids allocating a
    // `Vec<String>` for every un-aliased, un-merged net in large designs).
    let mut comp_members: HashMap<String, Vec<String>> = HashMap::default();
    for (idx, n) in all_nets.iter().enumerate() {
        let root = dsu.find(idx as u32);
        if dsu.size[root as usize] > 1 {
            let rep = &all_nets[dsu_rep[root as usize] as usize];
            comp_members
                .entry(rep.clone())
                .or_default()
                .push(n.clone());
        }
    }

    // Component -> its drivers, in first-seen order (deterministic: the emitted
    // CA order is observable through settle ordering). Each driver keeps its
    // OWN delay (§10.3.3: a delay on one continuous assignment delays that
    // driver's contribution alone, before resolution folds the others in).
    let mut comp_drivers: HashMap<String, Vec<(Expression, u64, String)>> = HashMap::default();
    let mut comp_first_lhs: HashMap<String, String> = HashMap::default();
    let mut comp_order: Vec<String> = Vec::new();
    let mut comp_delay: HashMap<String, u64> = HashMap::default();
    for n in &order {
        let root_id = dsu.find(net_id[n.as_str()]);
        let rep = all_nets[dsu_rep[root_id as usize] as usize].clone();
        if !comp_drivers.contains_key(&rep) {
            comp_order.push(rep.clone());
            comp_first_lhs.insert(rep.clone(), n.clone());
            comp_delay.insert(rep.clone(), *delays.get(n).unwrap_or(&0));
        }
        let ds = real_drivers.remove(n).unwrap_or_default();
        comp_drivers.entry(rep).or_default().extend(ds);
    }

    // §14.16: an output clockvar has a driver even before its first
    // synchronous drive. It is written by the clocking scheduler.
    let mut clock_driven = HashSet::default();
    for cb in elab.clocking_blocks.values() {
        for signal in &cb.signals {
            if signal.direction == crate::ast::types::PortDirection::Input {
                continue;
            }
            let target = match &signal.bound_to {
                Some(e) => driver_net(elab, e, ""),
                None => Some(signal.name.name.clone()),
            };
            if let Some(id) = target.and_then(|s| net_id.get(&s).copied()) {
                clock_driven.insert(dsu.find(id));
            }
        }
    }

    // §6.7.3: each undriven physical net gets one time-zero call with
    // an empty driver array. Keep the existing order of driven components,
    // and append undriven representatives in their stable declaration-key
    // order. Unpacked arrays resolve on their elements, not their container.
    for (idx, name) in all_nets.iter().enumerate() {
        let root_id = dsu.find(idx as u32);
        if dsu_rep[root_id as usize] == idx as u32
            && !net_resolver[name].is_empty()
            && !comp_drivers.contains_key(name)
            && !elab.arrays.contains_key(name)
            && !clock_driven.contains(&root_id)
        {
            comp_order.push(name.clone());
        }
    }

    // §6.6.7: count the drivers of each resolver-less net over its whole
    // component, member-wise ones included (a driver taken apart counts once,
    // as its most-driven member).
    for (idx, n) in all_nets.iter().enumerate() {
        let root_id = dsu.find(idx as u32);
        if dsu_rep[root_id as usize] != idx as u32 || !net_resolver[n.as_str()].is_empty() {
            continue;
        }
        let mut per_member: HashMap<&str, usize> = HashMap::default();
        if let Some(members) = comp_members.get(n.as_str()) {
            for net in members {
                for (m, c) in member_drivers.get(net).into_iter().flatten() {
                    *per_member.entry(m.as_str()).or_insert(0) += c;
                }
            }
        } else {
            for (m, c) in member_drivers.get(n.as_str()).into_iter().flatten() {
                *per_member.entry(m.as_str()).or_insert(0) += c;
            }
        }
        let total = comp_drivers.get(n.as_str()).map_or(0, |d| d.len())
            + per_member.values().copied().max().unwrap_or(0);
        if total > 1 {
            return Err(format!(
                "net '{}' of an unresolved nettype has {} continuous drivers; a nettype declared without a resolution function permits only one (IEEE 1800-2017 6.6.7)",
                n, total
            ));
        }
    }

    // Struct members of a nettype net (name, type, unpacked dimensions), or
    // None for a scalar one.
    type NetMembers = Option<Vec<(String, DataType, Vec<UnpackedDimension>)>>;
    let struct_members = |elab: &ElaboratedModule, name: &str| -> NetMembers {
        declared_type_name(elab, name)
            .and_then(|tn| elab.typedef_types.get(&tn).cloned())
            .and_then(|dt| match resolve_typedef_chain(&dt, &elab.typedef_types) {
                DataType::Struct(su) if !su.packed => {
                    let ms: Vec<_> = su
                        .members
                        .iter()
                        .flat_map(|m| {
                            m.declarators.iter().map(|d| {
                                (
                                    d.name.name.clone(),
                                    m.data_type.clone(),
                                    struct_member_dims(
                                        &m.data_type,
                                        &d.dimensions,
                                        &elab.typedef_unpacked_dims,
                                    )
                                    .into_owned(),
                                )
                            })
                        })
                        .collect();
                    if ms.is_empty() { None } else { Some(ms) }
                }
                _ => None,
            })
    };

    // §5.6.1: a declared escaped scalar can end in brackets. Only an
    // unpacked element, which has no separate signal declaration, needs
    // its brackets rebuilt as an Index expression.
    let net_expr = |elab: &ElaboratedModule, name: &str| {
        if name.ends_with(']') && elab.signals.contains_key(name) {
            make_ident_expr(name)
        } else {
            make_net_lhs_expr(name)
        }
    };
    // Emit `lhs = rhs`, expanded member-wise when the nettype wraps an unpacked
    // struct (one signal per member, so a whole-struct write has nowhere to go).
    let emit = |kept: &mut Vec<ContinuousAssignment>,
                lhs: &str,
                rhs: Expression,
                members: &NetMembers,
                delay: u64,
                span: Span,
                elab: &ElaboratedModule| {
        match members {
            Some(ms) => {
                for (m, mdt, mdims) in ms {
                    let mident = Identifier {
                        name: m.clone(),
                        span: Span::dummy(),
                    };
                    // Each member is its own signal: name it by its leaf
                    // path (`n.V`), as `emit_struct_member_assigns` does, so
                    // the assign compiles to bytecode instead of taking the
                    // AST path on every settle. A `MemberAccess` lhs never
                    // compiled, and neither did one on an identifier rhs.
                    let mut mlhs = member_ref_expr(&make_ident_expr(lhs), &mident);
                    mlhs.span = span;
                    let mut mrhs = member_ref_expr(&rhs, &mident);
                    mrhs.span = span;
                    if !mdims.is_empty() {
                        // §7.2, §7.4: an unpacked array member has no storage
                        // of its own; each element is its own leaf, and gets
                        // that element of the resolved value (§6.6.7).
                        let template = ContinuousAssignment {
                            gate_delay_fall: None,
                            delay_exprs: None,
                            delay_select: None,
                            origin: None,
                            lhs: mlhs.clone(),
                            rhs: mrhs.clone(),
                            delay,
                            rhs_parent_scoped: true,
                            delay_fall: None,
                            delay_off: None,
                        };
                        emit_member_elem_assigns(
                            mlhs,
                            mrhs,
                            false,
                            &[],
                            mdt,
                            mdims,
                            &template,
                            &elab.typedef_types,
                            &elab.typedef_unpacked_dims,
                            &elab.parameters,
                            None,
                            kept,
                            0,
                        );
                        continue;
                    }
                    kept.push(ContinuousAssignment {
                        gate_delay_fall: None,
                        delay_exprs: None,
                        delay_select: None,
                        origin: None,
                        lhs: mlhs,
                        rhs: mrhs,
                        delay,
                        rhs_parent_scoped: true,
                        delay_fall: None,
                        delay_off: None,
                    });
                }
            }
            None => {
                kept.push(ContinuousAssignment {
                    gate_delay_fall: None,
                    delay_exprs: None,
                    delay_select: None,
                    origin: None,
                    // §6.6.8: an element name (`a[0]`) must emit a real
                    // Index LHS, not a flat ident literally named `a[0]`.
                    lhs: net_expr(elab, lhs),
                    rhs,
                    delay,
                    rhs_parent_scoped: true,
                    delay_fall: None,
                    delay_off: None,
                })
            }
        }
    };

    for root in comp_order {
        let drivers = comp_drivers.remove(&root).unwrap_or_default();
        let resolver = net_resolver[&root].clone();
        let span = drivers.first().map_or_else(Span::dummy, |d| d.0.span);
        let members = struct_members(elab, &root);
        // §10.3.3: a delay on one continuous assignment delays that driver's
        // contribution alone, before resolution folds the others in. A single
        // folded resolver call can carry only ONE delay, so when a SCALAR
        // net's drivers reach it with DIFFERENT delays (issue #1204), stage
        // each delayed driver onto its own `<net>$drv<k>` signal and fold the
        // stages undelayed; the resolver then re-evaluates the moment any
        // driver's staged contribution changes. Uniform delays (all equal, 0
        // included) keep the current single folded call — equal-delay drivers
        // collapse exactly onto it.
        let staged = members.is_none()
            && drivers.len() > 1
            && drivers[1..].iter().any(|(_, d, _)| *d != drivers[0].1);
        let mut delay = comp_delay.remove(&root).unwrap_or(0);
        if staged {
            delay = 0;
        }

        let rhs = if resolver.is_empty() {
            // §6.6.7: a nettype declared without a resolution function accepts
            // at most one driver — counted over the whole connected net, so two
            // instances driving one node is an error just as two local
            // continuous assigns would be.
            if drivers.len() > 1 {
                return Err(format!(
                    "net '{}' of an unresolved nettype has {} continuous drivers; a nettype declared without a resolution function permits only one (IEEE 1800-2017 6.6.7)",
                    root,
                    drivers.len()
                ));
            }
            // For an unresolved unpacked-struct nettype aliased to undriven
            // siblings (`US usa, usb; alias usa = usb;`), copy member leaves
            // from the driven member onto its siblings.
            if members.is_some()
                && let Some(src) = comp_first_lhs.get(&root)
                && let Some(ms) = comp_members.get(&root)
            {
                for m in ms {
                    if m == src {
                        continue;
                    }
                    let mm = struct_members(elab, m);
                    emit(
                        &mut kept,
                        m,
                        net_expr(elab, src),
                        &mm,
                        0,
                        span,
                        elab,
                    );
                }
            }
            // The original assignments and links were retained above. This
            // also preserves their delay and scope metadata.
            continue;
        } else {
            // §6.6.7: the resolution function must exist, be `automatic`, and
            // take a single unpacked-array input. Checked here because this is
            // where the call is emitted; a bad one otherwise resolves to a
            // silently wrong value rather than a diagnostic. The nettype name
            // is recovered from the net's declared type for the message.
            let nt_name = declared_type_name(elab, &root).unwrap_or_else(|| root.clone());
            validate_resolver(elab, &nt_name, &resolver)?;
            // A nettype wrapping an unpacked struct is stored as ONE SIGNAL
            // PER MEMBER, which is why `emit` below expands the write side
            // member-wise. The driver side needs the same treatment and did
            // not get it: a driver that is already an assignment pattern
            // (`assign n = '{i: x, v: y};`) is member-wise as written and
            // survives, but a driver that names a struct VARIABLE or a
            // struct-typed PORT (`assign n = t;`) has no whole-struct value
            // to read -- the members are separate signals -- so the resolver
            // received uninitialised memory: every member arrived as nan, or
            // as zero once a later pass defaulted it.
            //
            // Both forms are legal. 10.3 gives `net_assignment ::=
            // net_lvalue = expression`, and an expression may name a
            // variable; the only restriction the clause places on a
            // user-defined nettype is on the LEFT ("shall not contain any
            // indexing or select"). So the fix is to expand, not to reject.
            // Each driver keeps its own fold contribution: its ORIGINAL value
            // when undelayed or uniform, or (when `staged`) the identifier of
            // its own `<net>$drv<k>` delay stage.
            let mut stage_rhs: Vec<(String, Expression, u64)> = Vec::new();
            let mut items: Vec<crate::ast::expr::AssignmentPatternItem> =
                Vec::with_capacity(drivers.len());
            let mut k: u32 = 0;
            for (driver, dly, driver_scope) in drivers.iter() {
                let fold = if staged && *dly != 0 {
                    let stage = format!("{root}$drv{k}");
                    k += 1;
                    // §10.3.3: synthesize the driver's own delay stage — a
                    // signal cloned from the net, driven by the driver's value
                    // behind its OWN delay, and read undelayed by the resolver.
                    // The `<net>$drv<k>` spelling is the same stage-net shape
                    // `resolve_multi_driver_nets` synthesizes for ordinary
                    // nets, so it is not a design object in dumps/scope.
                    if let Some(sig) = elab.signals.get(&root) {
                        let mut s = sig.clone();
                        s.name = stage.clone().into();
                        s.direction = None;
                        elab.signals.insert(stage.clone(), s);
                    }
                    stage_rhs.push((stage.clone(), driver.clone(), *dly));
                    Expression::new(make_ident_expr(&stage).kind, driver.span)
                } else {
                    driver.clone()
                };
                let d = match (&members, &fold.kind) {
                    // Already member-wise.
                    (Some(ms), ExprKind::AssignmentPattern(_)) => {
                        qualify_nettype_pattern_types(fold, Some(ms), driver_scope, elab)
                    }
                    (Some(ms), ExprKind::TypedPattern { pattern, .. }) => {
                        qualify_nettype_pattern_types((**pattern).clone(), Some(ms), driver_scope, elab)
                    }
                    // Name it member by member instead: '{d.m0, d.m1, ..}
                    (Some(ms), _) => {
                        let span = fold.span;
                        let fields: Vec<crate::ast::expr::AssignmentPatternItem> = ms
                            .iter()
                            .map(|(m, _, mdims)| {
                                let mident = Identifier {
                                    name: m.clone(),
                                    span: Span::dummy(),
                                };
                                let mut e = member_ref_expr(&fold, &mident);
                                e.span = span;
                                // An unpacked array member is read
                                // element by element (§7.4).
                                if let Some(lists) = (!mdims.is_empty())
                                    .then(|| {
                                        fixed_unpacked_index_lists(
                                            mdims,
                                            &elab.parameters,
                                            &elab.typedef_types,
                                        )
                                    })
                                    .flatten()
                                {
                                    e = element_pattern(&e, &lists);
                                }
                                crate::ast::expr::AssignmentPatternItem::Ordered(e)
                            })
                            .collect();
                        Expression::new(ExprKind::AssignmentPattern(fields), span)
                    }
                    _ => fold,
                };
                items.push(crate::ast::expr::AssignmentPatternItem::Ordered(d));
            }
            // A delayed driver's stage is driven by its own value behind its
            // OWN delay, so a change to that one driver re-resolves on its
            // own schedule (and zeroes/holds the stage's initial 0 in the
            // delay's first period — what the reference nettype resolution
            // shows at 1 ns in issue #1204). Scalar stages have no members.
            for (stage, drv, dly) in stage_rhs {
                emit(
                    &mut kept,
                    &stage,
                    drv,
                    &None,
                    dly,
                    span,
                    elab,
                );
            }
            Expression::new(
                ExprKind::Call {
                    func: Box::new(make_ident_expr(&resolver)),
                    args: vec![Expression::new(ExprKind::AssignmentPattern(items), span)],
                },
                span,
            )
        };
        emit(
            &mut kept,
            &root,
            rhs,
            &members,
            delay,
            span,
            elab,
        );

        // Every other net in the component names the same physical node.
        // Scalar nets sharing an `alias_canon` group will be storage-aliased
        // by `unify_alias_nets`, so skip emitting a redundant `m = root` copy
        // that `resolve_multi_driver_nets` would fold as a second driver.
        if let Some(ms) = comp_members.get(&root) {
            let root_canon = alias_canon_preview.get(&root);
            for m in ms {
                if m == &root {
                    continue;
                }
                if members.is_none()
                    && root_canon.is_some()
                    && alias_canon_preview.get(m) == root_canon
                {
                    continue;
                }
                let mm = struct_members(elab, m);
                emit(
                    &mut kept,
                    m,
                    net_expr(elab, &root),
                    &mm,
                    0,
                    span,
                    elab,
                );
            }
        }
    }

    // Propagate drivers across aliased/merged members of an unresolved
    // unpacked-struct nettype whose continuous driver was already expanded
    // member-wise into `member_drivers` (`US usa, usb; alias usa = usb;
    // assign usa = '{4.5, 9};`). Components with a whole-net driver in
    // `comp_first_lhs` were already propagated above.
    if !member_drivers.is_empty() && !comp_members.is_empty() {
        let mut kept_lhs: HashSet<String> = HashSet::default();
        for ca in &kept {
            if let Some(lhs) = ident_flat_name(&ca.lhs) {
                if let Some((net, m)) = net_member(&lhs) {
                    let head = m.split(['.', '[']).next().unwrap_or(&m);
                    kept_lhs.insert(format!("{net}.{head}"));
                } else {
                    kept_lhs.insert(lhs);
                }
            }
        }
        let mut seen_roots: HashSet<&str> = HashSet::default();
        for (idx, _) in all_nets.iter().enumerate() {
            let root_id = dsu.find(idx as u32);
            let root = all_nets[dsu_rep[root_id as usize] as usize].as_str();
            if !seen_roots.insert(root)
                || !net_resolver[root].is_empty()
                || comp_first_lhs.contains_key(root)
            {
                continue;
            }
            let Some(ms) = comp_members.get(root) else {
                continue;
            };
            let Some(members) = struct_members(elab, root) else {
                continue;
            };
            for mem_spec in &members {
                let mname = &mem_spec.0;
                let Some(src) = ms.iter().find(|s| {
                    member_drivers.get(s.as_str()).is_some_and(|pm| {
                        pm.keys().any(|k| {
                            k == mname
                                || k.strip_prefix(mname.as_str())
                                    .is_some_and(|rest| rest.starts_with('.') || rest.starts_with('['))
                        })
                    })
                }) else {
                    continue;
                };
                let single_mem = Some(vec![mem_spec.clone()]);
                for dest in ms {
                    if dest == src || kept_lhs.contains(&format!("{dest}.{mname}")) {
                        continue;
                    }
                    emit(
                        &mut kept,
                        dest,
                        net_expr(elab, src),
                        &single_mem,
                        0,
                        Span::dummy(),
                        elab,
                    );
                }
            }
        }
    }

    elab.continuous_assigns = kept;
    Ok(())
}

/// The nets a continuous-assign target (or UDP output) writes, each with
/// whether it writes the WHOLE net: `w` → [(w, true)], `w[3]` / `w[3:0]` /
/// `w.m` → [(w, false)], `{w, v[1]}` → [(w, true), (v, false)].
/// `is_net` decides whether a dotted member access names a net itself (a
/// hierarchical `u.w`) rather than a member of its prefix.
pub(super) fn lvalue_nets(
    e: &Expression,
    is_net: &dyn Fn(&str) -> bool,
    out: &mut Vec<(String, bool)>,
) {
    match &e.kind {
        ExprKind::Ident(h) => {
            let Some((last, init)) = h.path.split_last() else {
                return;
            };
            if init.iter().any(|s| !s.selects.is_empty()) {
                return;
            }
            let name = h
                .path
                .iter()
                .map(|s| s.name.name.as_str())
                .collect::<Vec<_>>()
                .join(".");
            out.push((name, last.selects.is_empty()));
        }
        ExprKind::MemberAccess { expr, .. } => match ident_flat_name(e) {
            Some(n) if is_net(&n) => out.push((n, true)),
            _ => {
                let at = out.len();
                lvalue_nets(expr, is_net, out);
                for t in &mut out[at..] {
                    t.1 = false;
                }
            }
        },
        ExprKind::Index { expr, .. } | ExprKind::RangeSelect { expr, .. } => {
            let at = out.len();
            lvalue_nets(expr, is_net, out);
            for t in &mut out[at..] {
                t.1 = false;
            }
        }
        ExprKind::Concatenation(parts) => {
            for p in parts {
                lvalue_nets(p, is_net, out);
            }
        }
        ExprKind::Paren(inner) => lvalue_nets(inner, is_net, out),
        _ => {}
    }
}

/// True when `e` is made of nets only: a net, a select of one, or a
/// concatenation of those — the shapes a port collapses onto (§23.3.3.7).
pub(super) fn is_net_lvalue(e: &Expression, is_net: &dyn Fn(&str) -> bool) -> bool {
    match &e.kind {
        ExprKind::Concatenation(parts) => {
            !parts.is_empty() && parts.iter().all(|p| is_net_lvalue(p, is_net))
        }
        ExprKind::Paren(inner)
        | ExprKind::Index { expr: inner, .. }
        | ExprKind::RangeSelect { expr: inner, .. } => is_net_lvalue(inner, is_net),
        ExprKind::Ident(_) => {
            let mut v = Vec::new();
            lvalue_nets(e, is_net, &mut v);
            v.len() == 1 && is_net(&v[0].0)
        }
        _ => false,
    }
}

/// Retarget every write of net `from` inside the target `e` to net `to`,
/// keeping any select: `w[3]` → `to[3]`. The inverse walk of `lvalue_nets`.
pub(super) fn retarget_lvalue_net(e: &mut Expression, from: &str, to: &str) {
    if ident_flat_name(e).as_deref() == Some(from) {
        *e = Expression::new(make_ident_expr(to).kind, e.span);
        return;
    }
    match &mut e.kind {
        ExprKind::Ident(h) => {
            let Some((last, init)) = h.path.split_last() else {
                return;
            };
            if init.iter().any(|s| !s.selects.is_empty()) {
                return;
            }
            let name = h
                .path
                .iter()
                .map(|s| s.name.name.as_str())
                .collect::<Vec<_>>()
                .join(".");
            if name == from {
                let selects = last.selects.clone();
                let span = last.name.span;
                h.path = vec![HierPathSegment {
                    name: Identifier {
                        name: to.to_string(),
                        span,
                    },
                    selects,
                }];
                h.cached_signal_id = crate::ast::cache::SignalCache::new(None);
                h.cached_resolved_name = crate::ast::cache::NameCache::new();
            }
        }
        ExprKind::MemberAccess { expr, .. }
        | ExprKind::Index { expr, .. }
        | ExprKind::RangeSelect { expr, .. }
        | ExprKind::Paren(expr) => retarget_lvalue_net(expr, from, to),
        ExprKind::Concatenation(parts) => {
            for p in parts {
                retarget_lvalue_net(p, from, to);
            }
        }
        _ => {}
    }
}

thread_local! {
    static VPI_NET_DRIVERS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Retain continuous-driver values for an elaboration whose nets can receive
/// VPI deposits (IEEE 1800-2023 §38.34), including an exported image.
pub fn set_vpi_net_drivers(enabled: bool) {
    VPI_NET_DRIVERS.set(enabled);
}

/// Whether the current elaboration must preserve the value of each driver.
pub fn vpi_net_drivers() -> bool {
    VPI_NET_DRIVERS.get()
}

/// A deposit holds until a driver's value changes. Put the driver's value in
/// its own signal before resolution folds several contributions together. An
/// input transition that recomputes the same contribution then has no event
/// to propagate, even though the visible net differs from that contribution.
pub(crate) fn stage_vpi_net_drivers(elab: &mut ElaboratedModule) {
    if !vpi_net_drivers() {
        return;
    }
    elab.materialize_pending_cont_assigns();
    let mut seq = 0usize;
    for mut ca in std::mem::take(&mut elab.continuous_assigns) {
        let name = whole_net_ident_name_scoped(&ca.lhs, elab);
        let signal = name
            .as_deref()
            .filter(|name| is_net_name(elab, name))
            .and_then(|name| elab.signals.get(name))
            .filter(|_| ca.origin.is_some() && !cont_assign_has_own_delay(&ca))
            .cloned();
        if let Some(mut signal) = signal {
            // Keep strength on the contribution consumed by the resolver.
            let rhs = match &mut ca.rhs {
                Expression {
                    kind: ExprKind::SystemCall { name, args },
                    ..
                } if matches!(
                    name.as_str(),
                    "$__drive" | "$__weak" | "$__pull" | "$__supply"
                ) =>
                {
                    args.first_mut()
                }
                rhs => Some(rhs),
            };
            if let Some(rhs) = rhs
                && !matches!(&rhs.kind, ExprKind::Ident(h) if h.path.iter().all(|seg| seg.selects.is_empty()))
                && !matches!(
                    &rhs.kind,
                    ExprKind::Number(_) | ExprKind::AssignmentPattern(_)
                )
            {
                let stage = loop {
                    let candidate = format!("{}$vpidrv{seq}", signal.name);
                    seq += 1;
                    if !elab.signals.contains_key(candidate.as_str()) {
                        break candidate;
                    }
                };
                let value = std::mem::replace(rhs, make_ident_expr(&stage));
                signal.name = stage.clone().into();
                signal.direction = None;
                // A stage carries the underlying value. Giving it the nettype
                // again would call that type's resolution function twice.
                signal.type_name = None;
                elab.signals.insert(stage.clone(), signal);
                let mut producer = ca.clone();
                producer.lhs = make_ident_expr(&stage);
                producer.rhs = value;
                ca.origin = None;
                elab.continuous_assigns.push(producer);
            }
        }
        elab.continuous_assigns.push(ca);
    }
}

/// A stage net that elaboration synthesized to carry delays — a delayed
/// net's driver side `<net>$netdrv` or per-bit stage `<net>$netbit<i>`
/// (`apply_net_delays`), a delayed driver's own net `<net>$drv<k>`
/// (`resolve_multi_driver_nets`). Not a design object: dumps and scope
/// listings leave it out.
pub fn is_delay_stage_net(name: &str) -> bool {
    let leaf = name.rsplit('.').next().unwrap_or(name);
    let Some(at) = leaf.rfind('$') else {
        return false;
    };
    let tail = &leaf[at + 1..];
    let numbered = |p: &str| {
        tail.strip_prefix(p)
            .is_some_and(|d| !d.is_empty() && d.bytes().all(|b| b.is_ascii_digit()))
    };
    tail == "netdrv"
        || numbered("netbit")
        || numbered("drv")
        || numbered("vpidrv")
        || numbered("structdelay")
}

/// Record a `tran`/`tranif0`/`tranif1` instantiation. `map` brings each terminal
/// into the enclosing scope (identity at the top level, `rewrite_expr` when the
/// gate lives in an inlined sub-module). Returns true if `gi` was a switch.
pub(super) fn record_tran_switches<F>(
    gi: &GateInstantiation,
    elab: &mut ElaboratedModule,
    map: F,
) -> bool
where
    F: Fn(&Expression) -> Expression,
{
    if !matches!(
        gi.gate_type,
        GateType::Tran
            | GateType::Rtran
            | GateType::Tranif0
            | GateType::Rtranif0
            | GateType::Tranif1
            | GateType::Rtranif1
    ) {
        return false;
    }
    let conditional = !matches!(gi.gate_type, GateType::Tran | GateType::Rtran);
    // An unconditional `tran` always conducts: it is modelled with a synthetic
    // control of 1, so it must be ACTIVE HIGH. Treating it like a `tranif0`
    // left the switch permanently open.
    let active_high =
        !conditional || matches!(gi.gate_type, GateType::Tranif1 | GateType::Rtranif1);
    for inst in &gi.instances {
        if inst.terminals.len() < 2 {
            continue;
        }
        let ctl = if conditional {
            match inst.terminals.get(2) {
                Some(c) => Some(map(c)),
                None => continue,
            }
        } else {
            None
        };
        elab.tran_switches.push(TranSwitch {
            a: map(&inst.terminals[0]),
            b: map(&inst.terminals[1]),
            ctl,
            active_high,
        });
    }
    true
}
