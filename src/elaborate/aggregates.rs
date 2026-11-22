use super::*;

impl ArraySlot<'_> {
    /// The value of the parameter `name` of the assignment's scope.
    fn param(&self, name: &str) -> Option<&Value> {
        if self.scope.is_empty() {
            self.params.get(name)
        } else {
            self.params.get(&format!("{}.{}", self.scope, name))
        }
    }

    /// Append to `out` the item of every element below index prefix `idx`
    /// that the item `e` gives over the dimensions `lists` (each in declared
    /// order, outermost first). §10.9.1: each pattern level is one dimension,
    /// whose elements are set by position (a replication is the whole
    /// dimension), by index key, by the last matching type key, else by
    /// `default:`; an element no key covers, a repeated index or an index
    /// outside the range leaves the member to the caller.
    pub(super) fn bind(
        &self,
        e: &Expression,
        lists: &[Vec<i64>],
        idx: &mut Vec<i64>,
        out: &mut Vec<(Vec<i64>, Expression)>,
        outer_types: &[(DataType, Expression)],
    ) -> Option<()> {
        let Some((list, rest)) = lists.split_first() else {
            let mut matched = None;
            for (key_dt, val) in outer_types.iter().rev() {
                if pattern_type_signature(key_dt, self.typedef_types, self.params)?
                    == pattern_type_signature(self.elem_dt, self.typedef_types, self.params)?
                {
                    matched = Some(val);
                    break;
                }
            }
            out.push((idx.clone(), matched.unwrap_or(e).clone()));
            return Some(());
        };
        let elems: Vec<(Expression, Vec<(DataType, Expression)>)> =
            match &peel_unpacked_typed_pattern(e).kind {
                ExprKind::AssignmentPattern(items) => {
                    self.level(items, list, !rest.is_empty(), outer_types, e.span)?
                }
                _ => list
                    .iter()
                    .map(|&i| (index_expr_of(e.clone(), i), outer_types.to_vec()))
                    .collect(),
            };
        for (&i, (x, elem_outer)) in list.iter().zip(&elems) {
            idx.push(i);
            self.bind(x, rest, idx, out, elem_outer)?;
            idx.pop();
        }
        Some(())
    }

    /// The items of the elements `list` of one pattern level.
    fn level(
        &self,
        items: &[AssignmentPatternItem],
        list: &[i64],
        subarray: bool,
        outer_types: &[(DataType, Expression)],
        span: Span,
    ) -> Option<Vec<(Expression, Vec<(DataType, Expression)>)>> {
        if let Some(ordered) = ordered_pattern_items(items, self.params) {
            return (ordered.len() == list.len()).then(|| {
                ordered
                    .into_iter()
                    .map(|e| (e, outer_types.to_vec()))
                    .collect()
            });
        }
        let mut keyed: Vec<Option<&Expression>> = vec![None; list.len()];
        let mut keys = PatternKeys::default();
        for item in items {
            if let Some((dt, v)) =
                pattern_item_type_key(item, self.typedef_types, self.params, self.scope, &|n| {
                    self.param(n).is_some()
                })
            {
                keys.types.push((dt, v.clone()));
                continue;
            }
            let (index, v) = match item {
                AssignmentPatternItem::Keyed(k, v) => (
                    const_eval_pattern_index(
                        k,
                        Some(self.params),
                        (*list.first()?, *list.last()?),
                    )?,
                    v,
                ),
                // A parameter name is an index key, not a member name.
                AssignmentPatternItem::Named(k, v) if self.param(&k.name).is_some() => {
                    (self.param(&k.name)?.to_i64()?, v)
                }
                _ if keys.add(item, self.typedef_types, self.params, self.scope) => continue,
                _ => return None,
            };
            let pos = list.iter().position(|&i| i == index)?;
            if keyed[pos].replace(v).is_some() {
                return None;
            }
        }
        keyed
            .into_iter()
            .map(|v| match v {
                Some(v) => Some((v.clone(), outer_types.to_vec())),
                None => keys.value_for(
                    self.elem_dt,
                    subarray,
                    outer_types,
                    self.typedef_types,
                    self.params,
                    span,
                    |d| {
                        !subarray
                            && self.default_types.is_some_and(|elab| {
                                continuous_default_matches(elab, self.scope, d, self.elem_dt, &[])
                                    .is_some()
                            })
                    },
                ),
            })
            .collect()
    }
}

/// Constant element indices of every FIXED unpacked dimension, outermost
/// first, each in declared order (left bound first: `[1:0]` is `[1, 0]`).
/// `None` when any dimension is dynamic or unresolvable, or the element
/// count would explode.
pub(super) fn fixed_unpacked_index_lists(
    dims: &[UnpackedDimension],
    params: &HashMap<String, Value>,
    typedef_types: &HashMap<String, DataType>,
) -> Option<Vec<Vec<i64>>> {
    let dims = normalize_unpacked_dims(dims, params, typedef_types);
    bounded_declared_index_lists(&declared_unpacked_dims(&dims, params)?)
}

pub(super) fn bounded_declared_index_lists(declared: &[(i64, i64)]) -> Option<Vec<Vec<i64>>> {
    let mut total: u64 = 1;
    let mut out = Vec::with_capacity(declared.len());
    for &(l, r) in declared {
        let n = l.abs_diff(r).checked_add(1)?;
        total = total.saturating_mul(n);
        if total > 4096 {
            return None;
        }
        out.push(if l <= r {
            (l..=r).collect()
        } else {
            (r..=l).rev().collect()
        });
    }
    Some(out)
}

/// Every index tuple of `lists`, last dimension varying fastest.
pub(super) fn cartesian_index_tuples(lists: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let mut tuples: Vec<Vec<i64>> = vec![Vec::new()];
    for list in lists {
        let mut next = Vec::with_capacity(tuples.len() * list.len());
        for t in &tuples {
            for &i in list {
                let mut t2 = t.clone();
                t2.push(i);
                next.push(t2);
            }
        }
        tuples = next;
    }
    tuples
}

/// The ordered pattern `'{base[i0], base[i1], ...}` of the elements of
/// `base` over the dimensions `lists`, one nested level per dimension.
pub(super) fn element_pattern(base: &Expression, lists: &[Vec<i64>]) -> Expression {
    let Some((list, rest)) = lists.split_first() else {
        return base.clone();
    };
    let items = list
        .iter()
        .map(|&i| {
            AssignmentPatternItem::Ordered(element_pattern(&index_expr_of(base.clone(), i), rest))
        })
        .collect();
    Expression::new(ExprKind::AssignmentPattern(items), base.span)
}

/// `base[idx]` as an expression.
pub(super) fn index_expr_of(base: Expression, idx: i64) -> Expression {
    // §7.4.2 / §10.9.1: negative declared indices select array elements too.
    // As for whole-array assignments, synthesize unary minus (§5.7.1), not
    // a numeric token containing a sign, which loses the negative leaf.
    if idx < 0 {
        return index_expr(base, idx);
    }
    let span = base.span;
    Expression::new(
        ExprKind::Index {
            expr: Box::new(base),
            index: Box::new(Expression::new(
                ExprKind::Number(NumberLiteral::Integer {
                    size: None,
                    signed: true,
                    base: crate::ast::expr::NumberBase::Decimal,
                    value: idx.to_string(),
                    cached_val: crate::ast::cache::LiteralCache::new(None),
                }),
                span,
            )),
        },
        span,
    )
}

/// §7.2.2: expand every continuous assignment whose TARGET is an UNPACKED
/// struct into one assignment per member.
///
/// §7.2.2 / §6.6.7: continuous assignment whose TARGET is an UNPACKED
/// struct. xezim stores an unpacked struct as one signal per member
/// (`s.f1`, `s.f2`), so a whole-struct `assign s = <expr>;` had nowhere to
/// land — every member read back 0. That hit plain struct CAs
/// (`assign s = '{1.5, 1'b1}`, `assign s = other_struct`) and, once nettype
/// resolution started emitting `assign n = res('{...})`, every struct-typed
/// user-defined nettype as well.
///
/// Expand one whole-struct assign into one assign per member:
///
/// ```text
/// assign s = e;   ->   assign s.f1 = e.f1;  assign s.f2 = e.f2;
/// ```
///
/// Member-select on an arbitrary RHS (including a call result) is already
/// supported, so each expanded CA evaluates through existing machinery and
/// keeps normal dependency tracking. Note the RHS is evaluated once per
/// member; §6.6.7 requires a resolution function to be side-effect free, so
/// repeating the call is observationally equivalent (it costs N calls).
/// Does any type name resolve to an UNPACKED struct or union with members?
/// Both whole-struct assign expansions split only assigns to such a type, so
/// a design without one (every signal a plain vector) skips their walk over
/// every continuous assign.
pub(super) fn has_unpacked_struct_type(elab: &ElaboratedModule) -> bool {
    elab.typedef_types.values().any(|dt| {
        matches!(
            resolve_typedef_chain(dt, &elab.typedef_types),
            DataType::Struct(su) if !su.packed && !su.members.is_empty()
        )
    })
}

/// §10.3.3: an inertial delay on a whole unpacked structure compares the
/// whole value. Splitting the delay across leaves lets an unchanged leaf's
/// earlier event survive when a sibling changes before delivery.
pub(super) fn expand_struct_driver(
    elab: &mut ElaboratedModule,
    ca: &ContinuousAssignment,
    base: &str,
    su: &crate::ast::types::StructUnionType,
    out: &mut Vec<ContinuousAssignment>,
) {
    let start = out.len();
    emit_struct_member_assigns(
        &make_ident_expr(base),
        &ca.rhs,
        su,
        ca,
        &elab.typedef_types,
        &elab.typedef_unpacked_dims,
        &elab.parameters,
        Some(&*elab),
        out,
        0,
    );
    if ca.delay == 0 || out.len() - start < 2 || ca.delay_fall.is_some() || ca.delay_off.is_some() {
        return;
    }
    fn leaf_name(e: &Expression, elab: &ElaboratedModule) -> Option<String> {
        match &e.kind {
            ExprKind::Index { expr, index } => Some(format!(
                "{}[{}]",
                leaf_name(expr, elab)?,
                const_eval_i64_with_params(index, Some(&elab.parameters))?
            )),
            ExprKind::MemberAccess { expr, member } => {
                Some(format!("{}.{}", leaf_name(expr, elab)?, member.name))
            }
            _ => ident_flat_name(e),
        }
    }
    let defaults: Option<Vec<_>> = out[start..]
        .iter()
        .map(|leaf| {
            let name = leaf_name(&leaf.lhs, elab)?;
            if let Some(sig) = elab.signals.get(&name) {
                return (!sig.is_real && sig.width > 0).then(|| sig.value.resize(sig.width));
            }
            // Array cells are normally allocated only when the simulator starts.
            // Their source declaration already carries the leaf type and default.
            let mut container = su;
            let mut path = name
                .strip_prefix(base)?
                .strip_prefix('.')?
                .split('.')
                .peekable();
            while let Some(part) = path.next() {
                let member = part.split('[').next()?;
                let dt = &container
                    .members
                    .iter()
                    .find(|m| m.declarators.iter().any(|d| d.name.name == member))?
                    .data_type;
                let dt = resolve_typedef_chain(dt, &elab.typedef_types);
                if path.peek().is_none() {
                    let width =
                        resolve_type_width(dt, Some(&elab.parameters), Some(&elab.typedefs));
                    let value = default_value_for_type(dt, width);
                    return (!value.is_real && width > 0).then_some(value);
                }
                let DataType::Struct(inner) = dt else {
                    return None;
                };
                container = inner;
            }
            None
        })
        .collect();
    let Some(defaults) = defaults else {
        return;
    };
    let initial = Value::concat(&defaults);
    let width = initial.width;
    let span = ca.lhs.span;
    let mut seq = start;
    let stage = loop {
        let name = format!("{base}$structdelay{seq}");
        if !elab.signals.contains_key(&name) {
            break name;
        }
        seq += 1;
    };
    elab.signals.insert(
        stage.clone(),
        Signal {
            name: stage.clone().into(),
            width,
            is_const: false,
            is_signed: false,
            is_real: false,
            type_name: None,
            direction: None,
            value: initial,
        },
    );
    let mut parts = Vec::with_capacity(defaults.len());
    let mut hi = width;
    for (leaf, initial) in out[start..].iter_mut().zip(defaults) {
        let lo = hi - initial.width;
        let slice = Expression::new(
            ExprKind::RangeSelect {
                expr: Box::new(make_ident_expr(&stage)),
                kind: crate::ast::expr::RangeKind::Constant,
                left: Box::new(int_literal(i64::from(hi - 1), span)),
                right: Box::new(int_literal(i64::from(lo), span)),
            },
            span,
        );
        hi = lo;
        let rhs = std::mem::replace(&mut leaf.rhs, slice);
        parts.push(make_syscall(
            "$__xz_size_cast",
            vec![int_literal(i64::from(initial.width), span), rhs],
            span,
        ));
        leaf.delay = 0;
        leaf.delay_exprs = None;
        leaf.origin = None;
        leaf.delay_select = None;
    }
    let mut delayed = ca.clone();
    delayed.lhs = make_ident_expr(&stage);
    delayed.rhs = Expression::new(ExprKind::Concatenation(parts), span);
    out.push(delayed);
}

pub fn expand_whole_struct_continuous_assigns(elab: &mut ElaboratedModule) {
    if !has_unpacked_struct_type(elab) {
        return;
    }
    let mut expanded: Vec<ContinuousAssignment> = Vec::new();
    for ca in std::mem::take(&mut elab.continuous_assigns) {
        let members = simple_lhs_name(&ca.lhs)
            .and_then(|n| {
                let tn = elab.signals.get(&n).and_then(|s| s.type_name.clone())?;
                Some((n, tn))
            })
            .and_then(|(n, tn)| {
                // §6.6.7: a nettype net WITH a resolution function is expanded
                // after that resolver runs, in `resolve_user_nettype_drivers`,
                // which groups drivers by whole-net LHS once every instance's
                // have landed. Splitting it here would hide them from that
                // pass. A nettype without a resolver has nothing to wait for
                // and takes the ordinary path.
                if elab
                    .nettype_resolvers
                    .get(&tn)
                    .is_some_and(|r| !r.is_empty())
                {
                    return None;
                }
                let dt = elab.typedef_types.get(&tn)?;
                match resolve_typedef_chain(dt, &elab.typedef_types) {
                    // PACKED structs keep a contiguous bit layout that a
                    // whole-value write already fills correctly; only
                    // UNPACKED ones are stored per member.
                    DataType::Struct(su) if !su.packed && !su.members.is_empty() => {
                        Some((n, su.clone()))
                    }
                    _ => None,
                }
            });
        match members {
            Some((base, su)) => {
                expand_struct_driver(elab, &ca, &base, &su, &mut expanded);
            }
            None => expanded.push(ca),
        }
    }
    elab.continuous_assigns = expanded;
}

/// §7.2: is an inlined instance's port of this type stored member-wise — an
/// unpacked struct (not an untagged union, which is one piece of storage) —
/// and named by a type the later whole-design passes can still resolve?
///
/// A port typed by one of the instance's TYPE PARAMETERS is left out: the
/// parameter is bound only while the instance is inlined (`saved_type_binds`
/// restores the slot), so `expand_unpacked_struct_assigns` cannot see that
/// it names a struct. Such a port keeps the packed container layout it had.
pub(super) fn inlined_port_member_wise(
    dt: &DataType,
    typedef_types: &HashMap<String, DataType>,
    type_binds: &[(String, Option<u32>, Option<DataType>)],
) -> bool {
    if let DataType::TypeReference { name, .. } = dt {
        if name.scopes.is_empty() && type_binds.iter().any(|(n, _, _)| *n == name.name.name) {
            return false;
        }
    }
    matches!(
        resolve_typedef_chain(dt, typedef_types),
        DataType::Struct(su) if !su.packed
            && !(matches!(su.kind, StructUnionKind::Union) && !su.tagged)
    )
}

/// §7.4.2, §7.2: an element of a fixed multi-dimensional unpacked array of
/// unpacked structures keeps each member in a signal of its own
/// (`a[1][0].v`), as an element of a one-dimensional one does. Without it a
/// member had no signal, so a continuous assignment reading it never woke
/// (§10.3.2) and a copy of the array (§13.5.1) had no members to copy.
/// Runs after the top is elaborated (its generate blocks included) and
/// again after the instances are inlined; an array of more than 4096
/// elements keeps the lazy members, as a one-dimensional one does.
pub(super) fn register_nd_struct_array_members(elab: &mut ElaboratedModule) {
    let mut arrays: Vec<(String, Vec<(i64, i64)>)> = elab
        .arrays_2d
        .iter()
        .map(|(n, &(d0, d1, _))| (n.clone(), vec![d0, d1]))
        .chain(
            elab.arrays_nd
                .iter()
                .map(|(n, (shape, _))| (n.clone(), shape.clone())),
        )
        .filter(|(n, _)| {
            !elab.dynamic_arrays.contains(n)
                && !elab.queue_vars.contains(n)
                && !elab.associative_arrays.contains_key(n)
        })
        .collect();
    arrays.sort();
    for (name, shape) in arrays {
        let Some(dt) = elab.var_decl_types.get(&name).cloned() else {
            continue;
        };
        if !matches!(
            resolve_typedef_chain(&dt, &elab.typedef_types),
            DataType::Struct(su) if !su.packed && matches!(su.kind, StructUnionKind::Struct)
        ) {
            continue;
        }
        let count = shape.iter().try_fold(1usize, |n, &(lo, hi)| {
            (hi >= lo).then(|| n.saturating_mul((hi - lo + 1) as usize))
        });
        if !count.is_some_and(|n| n <= 4096) {
            continue;
        }
        for suffix in index_tuples(&shape) {
            let ebase = format!("{name}{suffix}");
            if !elab.struct_members.contains_key(&ebase) {
                register_unpacked_aggregate(elab, &ebase, &dt);
            }
        }
    }
}

pub(super) fn register_unpacked_aggregate(elab: &mut ElaboratedModule, base: &str, dt: &DataType) {
    let resolved = resolve_typedef_chain(dt, &elab.typedef_types).clone();
    let DataType::Struct(su) = resolved else {
        return;
    };
    if su.packed {
        return;
    }
    // §23.6: aggregate member paths retain their owning declaration;
    // they must not fall back to a namesake in another generate scope.
    elab.struct_members.entry(base.to_string()).or_insert_with(|| {
        su.members.iter().flat_map(|m| m.declarators.iter())
            .map(|d| d.name.name.clone()).collect()
    });
    // IEEE 1800-2017 §7.3: a union is ONE piece of storage accessed through any
    // of its member names — writing `u.a` must be readable as `u.b`. So an
    // untagged union gets a single signal whose members all start at bit 0,
    // exactly like a packed one. (A TAGGED union is tag-checked: §7.3.2.)
    if matches!(su.kind, StructUnionKind::Union) && !su.tagged {
        let w = resolve_type_width(dt, Some(&elab.parameters), Some(&elab.typedefs)).max(1);
        elab.signals.entry(base.to_string()).or_insert(Signal {
            is_const: false,
            name: base.to_string().into(),
            width: w,
            is_signed: false,
            is_real: false,
            direction: None,
            value: Value::new(w),
            type_name: None,
        });
        if let Some(fields) =
            flatten_struct_fields(dt, &elab.parameters, &elab.typedefs, &elab.typedef_types)
        {
            if !fields.is_empty() {
                elab.packed_struct_fields.insert(base.to_string(), fields);
            }
        }
        return;
    }
    for member in &su.members {
        for mdecl in &member.declarators {
            let mbase = format!("{}.{}", base, mdecl.name.name);
            // §6.18, §7.4.5: a member typed by a dimensioned typedef takes the
            // typedef's unpacked dimensions after its own.
            let dims = struct_member_dims(
                &member.data_type,
                &mdecl.dimensions,
                &elab.typedef_unpacked_dims,
            );
            // §7.2.1: a DYNAMIC member (`int d[]`, `int q[$]`, `int a[key]`)
            // is its own collection object under `var.member`, registered as
            // the module-scope declaration path does. Here a queue was taken
            // for a fixed 64-element array (`size()` read 65) and an
            // associative member was never registered (`num()` read 0).
            // `m[N]` with `N` a constant parses as an associative dimension
            // keyed by the type `N`; classify the normalized dimensions.
            let mdims =
                normalize_unpacked_dims(&dims, &elab.parameters, &elab.typedef_types);
            record_coll_shape(elab, &mbase, &mdims, None);
            match mdims.first() {
                Some(UnpackedDimension::Associative { data_type: kdt, .. }) => {
                    let is_str = kdt.as_ref().is_some_and(|dt| {
                        matches!(
                            dt.as_ref(),
                            DataType::Simple {
                                kind: SimpleType::String,
                                ..
                            }
                        )
                    });
                    elab.associative_arrays
                        .entry(mbase.clone())
                        .or_insert(is_str);
                    elab.var_decl_types
                        .insert(mbase.clone(), member.data_type.clone());
                    continue;
                }
                Some(d @ (UnpackedDimension::Unsized(_) | UnpackedDimension::Queue { .. })) => {
                    let w = resolve_type_width(
                        &member.data_type,
                        Some(&elab.parameters),
                        Some(&elab.typedefs),
                    )
                    .max(1);
                    elab.dynamic_arrays.insert(mbase.clone());
                    if let UnpackedDimension::Queue { max_size, .. } = d {
                        elab.queue_vars.insert(mbase.clone());
                        if let Some(n) = max_size
                            .as_ref()
                            .and_then(|ms| const_eval_i64_with_params(ms, Some(&elab.parameters)))
                            .filter(|n| *n >= 0)
                        {
                            elab.queue_max_sizes.insert(mbase.clone(), (n + 1) as u32);
                        }
                    }
                    elab.arrays.entry(mbase.clone()).or_insert((0, 63, w));
                    elab.var_decl_types
                        .insert(mbase.clone(), member.data_type.clone());
                    continue;
                }
                _ => {}
            }
            if mdims.is_empty() {
                register_member_leaf(elab, &mbase, &member.data_type);
            } else {
                let dims = mdims;
                let shape: Option<Vec<(i64, i64)>> = dims
                    .iter()
                    .map(|d| extract_array_range(std::slice::from_ref(d), &elab.parameters))
                    .collect();
                if let Some(shape) = shape.filter(|s| !s.is_empty()) {
                    // IEEE 1800-2017 §7.4.2: every fixed unpacked dimension
                    // belongs to the member's array shape. Recording only the
                    // first one made the next subscript select a packed bit of
                    // that element instead of selecting the next unpacked
                    // dimension.
                    let ew = resolve_type_width(
                        &member.data_type,
                        Some(&elab.parameters),
                        Some(&elab.typedefs),
                    )
                    .max(1);
                    match shape.as_slice() {
                        [one] => {
                            elab.arrays
                                .entry(mbase.clone())
                                .or_insert((one.0, one.1, ew));
                        }
                        [one, two] => {
                            elab.arrays_2d
                                .entry(mbase.clone())
                                .or_insert((*one, *two, ew));
                        }
                        _ => {
                            elab.arrays_nd
                                .entry(mbase.clone())
                                .or_insert((shape.clone(), ew));
                        }
                    }
                    if let Some(declared) = declared_unpacked_dims(&dims, &elab.parameters) {
                        elab.unpacked_decl_dims.insert(mbase.clone(), declared);
                    }
                    elab.var_decl_types
                        .insert(mbase.clone(), member.data_type.clone());
                    for suffix in index_tuples(&shape) {
                        register_member_leaf(
                            elab,
                            &format!("{}{}", mbase, suffix),
                            &member.data_type,
                        );
                    }
                }
            }
            // Dynamic / queue / associative members stay lazily created.
        }
    }
}

/// Top-level member names of a struct/union type in DECLARATION order (packed
/// or unpacked). `None` for a non-struct type. Nested members are not expanded.
pub fn struct_member_names(
    dt: &DataType,
    typedef_types: &HashMap<String, DataType>,
) -> Option<Vec<String>> {
    match resolve_typedef_chain(dt, typedef_types) {
        DataType::Struct(su) => Some(
            su.members
                .iter()
                .flat_map(|m| m.declarators.iter().map(|d| d.name.name.clone()))
                .collect(),
        ),
        _ => None,
    }
}

/// Owning package of a scoped type-reference chain (`cfg::req_t` → "cfg").
/// A package typedef's member dimensions reference the OWNING package's
/// parameters by BARE name (`logic [LOG_DEPTH-1:0] addr;`), but consumers
/// resolve layouts with the USING scope's parameter map, where those names
/// only exist under their `pkg::` aliases — so member widths silently went
/// to 0 in any module that didn't import the package.
pub(super) fn scoped_type_owner(
    dt: &DataType,
    typedef_types: &HashMap<String, DataType>,
) -> Option<String> {
    let mut cur = dt;
    let mut owner: Option<String> = None;
    for _ in 0..64 {
        let DataType::TypeReference { name, .. } = cur else {
            break;
        };
        if !name.scopes.is_empty() {
            let key = name.qualified();
            if let Some(next) = typedef_types.get(&key) {
                owner = Some(name.scope_prefix());
                cur = next;
                continue;
            }
        }
        match typedef_types.get(&name.name.name) {
            Some(next) => cur = next,
            None => break,
        }
    }
    owner
}

/// Overlay `pkg::X` parameter aliases as bare `X` for evaluating the members
/// of a scoped package type. Package params override same-named module ones
/// here — inside the package's own typedef, bare names bind to the package.
pub(super) fn owner_param_overrides(
    owner: &str,
    params: &dyn ParamLookup,
) -> HashMap<String, Value> {
    let pfx = format!("{}::", owner);
    let mut m = HashMap::default();
    for (k, v) in params.rows() {
        if let Some(bare) = k.strip_prefix(&pfx) {
            if !bare.contains("::") {
                m.insert(bare.to_string(), v.clone());
            }
        }
    }
    m
}

pub fn packed_struct_field_layout(
    dt: &DataType,
    params: &HashMap<String, Value>,
    typedefs: &HashMap<String, u32>,
    typedef_types: &HashMap<String, DataType>,
) -> Option<Vec<(String, u32, u32)>> {
    packed_struct_field_layout_env(dt, params, typedefs, typedef_types)
}

pub(crate) fn packed_struct_field_layout_env(
    dt: &DataType,
    params: &dyn ParamLookup,
    typedefs: &HashMap<String, u32>,
    typedef_types: &HashMap<String, DataType>,
) -> Option<Vec<(String, u32, u32)>> {
    match resolve_typedef_chain(dt, typedef_types) {
        DataType::Struct(su) if su.packed => {}
        _ => return None,
    }
    flatten_struct_fields(dt, params, typedefs, typedef_types)
}

/// Recursively flatten nested struct/union members so multi-segment paths
/// like `u.s.a` resolve via a single `packed_struct_fields` lookup. A member
/// that is a packed array of packed structs expands into per-element
/// pseudo-fields (`dw[1]`, `dw[1].value`, §7.4.2). One walker for every
/// declaration path: the inlined-instance paths used a variant without the
/// expansion, so `b_o.dw[0].value <= d` in a sub-module had no layout to land
/// in and left the whole variable x, while the same code in the top module
/// worked.
pub(super) fn flatten_struct_fields(
    dt: &DataType,
    params: &dyn ParamLookup,
    typedefs: &HashMap<String, u32>,
    typedef_types: &HashMap<String, DataType>,
) -> Option<Vec<(String, u32, u32)>> {
    // A NESTED member typed by ANOTHER package's scoped typedef
    // (`q::inner_t` inside p's struct) needs q's params bare for ITS member
    // dims — re-derive the owner at every nesting level.
    let owner_own;
    let stacked;
    let params: &dyn ParamLookup = match scoped_type_owner(dt, typedef_types) {
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
    // §6.18: a CIRCULAR typedef makes this nesting
    // infinite (`typedef T1; struct packed { T1 x; } T2;
    // typedef T2 [1:0] T3; typedef T3 T1;`) — the walk
    // recursed until the stack overflowed and the
    // process ABORTED (ivtest sv_typedef_circular2).
    // Bound the depth so malformed input is diagnosed
    // instead of crashing the tool. Real designs nest
    // far shallower than this.
    thread_local! {
        static SUBFIELD_DEPTH: std::cell::Cell<u32> =
            const { std::cell::Cell::new(0) };
    }
    struct DepthGuard;
    impl Drop for DepthGuard {
        fn drop(&mut self) {
            SUBFIELD_DEPTH.with(|c| c.set(c.get().saturating_sub(1)));
        }
    }
    let depth = SUBFIELD_DEPTH.with(|c| {
        let d = c.get();
        c.set(d + 1);
        d
    });
    let _guard = DepthGuard;
    if depth > 32 {
        return None;
    }
    // Field-count cap; see the resource guard at the end.
    const MAX_FLAT_FIELDS: usize = 8192;
    let resolved = resolve_typedef_chain(dt, typedef_types);
    if let DataType::Struct(su) = resolved {
        let is_union = matches!(su.kind, StructUnionKind::Union);
        let mut raw: Vec<(String, u32, DataType)> = Vec::new();
        for member in &su.members {
            let mw = resolve_type_width_env(&member.data_type, Some(&params), Some(typedefs));
            for mdecl in &member.declarators {
                raw.push((mdecl.name.name.clone(), mw, member.data_type.clone()));
            }
        }
        // §7.4.2: a member that is a PACKED ARRAY of packed
        // struct (`row_entry_t [1:0] sub_list;`) expands into
        // per-element pseudo-fields `sub_list[i]` plus their
        // subfields `sub_list[i].f`, so indexed member paths
        // resolve through the parent's flat layout. Plain
        // recursion would mis-register `sub_list.f` aliasing
        // only element 0; it is kept only for a member too
        // large to expand within MAX_FLAT_FIELDS, which then
        // keeps the rest of the layout instead of losing it.
        let expand_member = |mn: &str,
                             mw: u32,
                             mdt: &DataType,
                             base_off: u32,
                             out: &mut Vec<(String, u32, u32)>| {
            // §26.3: a member typed by a package's struct (`q::entry_t [N-1:0]
            // a`) sizes the element's fields with that package's parameters,
            // while the bounds written on the member are this scope's. The
            // element comes back as a bare struct, which no longer names its
            // package, so take the owner from the member's type here.
            let elem_own;
            let elem_stacked;
            let elem_params: &dyn ParamLookup = match scoped_type_owner(mdt, typedef_types) {
                Some(pkg) => {
                    elem_own = owner_param_overrides(&pkg, params);
                    elem_stacked = StackedParamEnv {
                        base: params,
                        top: &elem_own,
                    };
                    &elem_stacked
                }
                None => params,
            };
            if let Some((dims, elem_dt)) = packed_struct_array_info_env(mdt, params, typedef_types)
            {
                let counts: Vec<u64> = dims
                    .iter()
                    .map(|(l, r)| (l - r).unsigned_abs() + 1)
                    .collect();
                let n: u64 = counts.iter().product();
                if n > 0 && mw as u64 % n == 0 {
                    let elem_w = (mw as u64 / n) as u32;
                    let elem_subs =
                        flatten_struct_fields(&elem_dt, elem_params, typedefs, typedef_types)
                            .unwrap_or_default();
                    let expanded = (n as usize).saturating_mul(1 + elem_subs.len());
                    if out.len().saturating_add(expanded) > MAX_FLAT_FIELDS {
                        return false;
                    }
                    // Enumerate every index tuple (odometer).
                    let mut idx: Vec<i64> = dims.iter().map(|(l, r)| *l.min(r)).collect();
                    loop {
                        if let Some(lo) = packed_elem_lsb_offset(&dims, &idx, elem_w) {
                            let mut nm = mn.to_string();
                            for i in &idx {
                                nm.push_str(&format!("[{}]", i));
                            }
                            out.push((nm.clone(), base_off + lo, elem_w));
                            for (sn, so, sw) in &elem_subs {
                                out.push((format!("{}.{}", nm, sn), base_off + lo + so, *sw));
                            }
                        }
                        // advance odometer (innermost fastest)
                        let mut j = dims.len();
                        loop {
                            if j == 0 {
                                return true;
                            }
                            j -= 1;
                            let (l, r) = dims[j];
                            let hi = l.max(r);
                            if idx[j] < hi {
                                idx[j] += 1;
                                break;
                            }
                            idx[j] = l.min(r);
                        }
                    }
                }
                return true; // array member: skip plain recursion
            }
            false
        };
        let mut out: Vec<(String, u32, u32)> = Vec::new();
        if is_union {
            for (mn, mw, mdt) in &raw {
                out.push((mn.clone(), 0, *mw));
                if expand_member(mn, *mw, mdt, 0, &mut out) {
                    continue;
                }
                if let Some(subs) = flatten_struct_fields(mdt, params, typedefs, typedef_types) {
                    for (sn, so, sw) in subs {
                        out.push((format!("{}.{}", mn, sn), so, sw));
                    }
                }
            }
        } else {
            let mut offset: u32 = 0;
            for (mn, mw, mdt) in raw.iter().rev() {
                out.push((mn.clone(), offset, *mw));
                if expand_member(mn, *mw, mdt, offset, &mut out) {
                    offset += mw;
                    continue;
                }
                if let Some(subs) = flatten_struct_fields(mdt, params, typedefs, typedef_types) {
                    for (sn, so, sw) in subs {
                        out.push((format!("{}.{}", mn, sn), offset + so, sw));
                    }
                }
                offset += mw;
            }
        }
        // Resource guard, paired with the depth bound
        // above: each level of a packed-array-of-struct
        // member MULTIPLIES the generated field names,
        // so a circular typedef is exponential in depth
        // — bounding depth alone still spun for minutes
        // formatting names. Capping each level's result
        // bounds the whole walk. A real packed struct
        // has orders of magnitude fewer leaves; say so
        // rather than silently truncating.
        if out.len() > MAX_FLAT_FIELDS {
            crate::elab_diag(format!(
                "[xezim][warning] packed layout for a struct flattens to over {} fields — \
                 not registering it (a circular typedef, per IEEE 1800-2017 §6.18, \
                 reaches this); member selects on it will not resolve through the layout.",
                MAX_FLAT_FIELDS
            ));
            return None;
        }
        Some(out)
    } else {
        None
    }
}

/// Pack a struct/union assignment-pattern literal into a packed `Value`,
/// honoring declaration order (first member = MSB) so a struct-typed
/// parameter `parameter cfg_t C = '{base:.., len:..}` evaluates at elaboration
/// (IEEE 1800-2017 §6.20, §10.9.2). Handles named (`'{f:v}`), ordered
/// (`'{v0,v1}`), and `default:` items, and recurses for nested struct fields.
/// Returns None if `dt` is not a struct/union or `expr` is not a pattern.
pub(super) fn pack_struct_const_value(
    dt: &DataType,
    expr: &Expression,
    params: &dyn ParamLookup,
    typedefs: &HashMap<String, u32>,
    typedef_types: &HashMap<String, DataType>,
) -> Option<Value> {
    pack_struct_const_value_with_outer(dt, expr, params, typedefs, typedef_types, &[])
}

pub(super) fn pack_struct_const_value_with_outer(
    dt: &DataType,
    expr: &Expression,
    params: &dyn ParamLookup,
    typedefs: &HashMap<String, u32>,
    typedef_types: &HashMap<String, DataType>,
    outer_types: &[(DataType, Expression)],
) -> Option<Value> {
    // See scoped_type_owner — same bare-name rule as flatten_struct_fields.
    let owner_own;
    let stacked;
    let params: &dyn ParamLookup = match scoped_type_owner(dt, typedef_types) {
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
    if let ExprKind::TypedPattern { ty, pattern } = &expr.kind {
        return pack_typed_pattern(ty, pattern, params, typedefs, typedef_types);
    }
    let su = match resolve_typedef_chain(dt, typedef_types) {
        DataType::Struct(su) => su.clone(),
        _ => return None,
    };
    let items = match &expr.kind {
        ExprKind::AssignmentPattern(items) => items,
        _ => return None,
    };
    // Top-level members in declaration order (first = MSB).
    let mut members: Vec<(String, u32, DataType)> = Vec::new();
    for member in &su.members {
        let mw = resolve_type_width_env(&member.data_type, Some(&params), Some(typedefs));
        for mdecl in &member.declarators {
            members.push((mdecl.name.name.clone(), mw, member.data_type.clone()));
        }
    }
    let is_member = |name: &str| members.iter().any(|(mn, _, _)| mn == name);
    // Index the pattern: named-by-field, type keys, ordered-by-position, and default.
    let mut named: HashMap<String, &Expression> = HashMap::default();
    let mut local_types: Vec<(DataType, Expression)> = Vec::new();
    let mut ordered: Vec<&Expression> = Vec::new();
    let mut default_expr: Option<&Expression> = None;
    for it in items {
        if let AssignmentPatternItem::Named(id, v) = it
            && is_member(&id.name)
        {
            named.insert(id.name.clone(), v);
            continue;
        }
        if let AssignmentPatternItem::Keyed(k, v) = it
            && let ExprKind::Ident(h) = &k.kind
            && h.root.is_none()
            && h.path.len() == 1
            && h.path[0].selects.is_empty()
            && is_member(&h.path[0].name.name)
        {
            named.insert(h.path[0].name.name.clone(), v);
            continue;
        }
        if let Some((kt, v)) = pattern_item_type_key(it, typedef_types, params, "", &is_member) {
            local_types.push((kt, v.clone()));
            continue;
        }
        match it {
            AssignmentPatternItem::Ordered(v) => ordered.push(v),
            AssignmentPatternItem::Default(v) => default_expr = Some(v),
            AssignmentPatternItem::Keyed(k, v) => {
                if let ExprKind::Ident(h) = &k.kind
                    && let Some(last) = h.path.last()
                {
                    named.insert(last.name.name.clone(), v);
                }
            }
            _ => {}
        }
    }
    // §7.2.1: packed structures cannot contain unpacked array members.
    // Unpacked const-eval uses the typedef shapes registered during elaboration.
    // §10.9.2, A.6.7.1: the count is a constant expression. Match the
    // replication shape before the member scan.
    if let Some(expanded) = struct_pattern_replication_with(items, members.len(), &mut |count| {
        struct_pattern_count_value(&eval_const_expr_val_env(count, &params))
    }) && (su.packed
        || !TYPEDEF_SHAPES_TLS
            .with(|shapes| struct_pattern_has_array_member(&su, typedef_types, &shapes.borrow().1)))
    {
        ordered = expanded;
    }
    let mut combined_types = local_types;
    combined_types.extend(outer_types.iter().cloned());
    let use_ordered = named.is_empty() && combined_types.is_empty() && !ordered.is_empty();
    // Build MSB-first parts (declaration order) and concat.
    let mut parts: Vec<Value> = Vec::new();
    for (idx, (mn, mw, mdt)) in members.iter().enumerate() {
        let matched_outer = outer_types.iter().rev().find_map(|(kt, ve)| {
            let msig = pattern_type_signature(mdt, typedef_types, params)?;
            (pattern_type_signature(kt, typedef_types, params)? == msig).then_some(ve)
        });
        let explicit = if let Some(ov) = matched_outer {
            Some(ov)
        } else if let Some(nv) = named.get(mn).copied() {
            Some(nv)
        } else if use_ordered {
            ordered.get(idx).copied()
        } else {
            combined_types.iter().rev().find_map(|(kt, ve)| {
                let msig = pattern_type_signature(mdt, typedef_types, params)?;
                (pattern_type_signature(kt, typedef_types, params)? == msig).then_some(ve)
            })
        };
        let empty_pat;
        let ve = match explicit.or(default_expr) {
            Some(e) => Some(e),
            None if !combined_types.is_empty()
                && pattern_slot_is_aggregate(mdt, typedef_types) == Some(true) =>
            {
                empty_pat = Expression::new(ExprKind::AssignmentPattern(Vec::new()), expr.span);
                Some(&empty_pat)
            }
            None => None,
        };
        let sub_outer: &[(DataType, Expression)] = if explicit.is_some() {
            outer_types
        } else {
            &combined_types
        };
        let val = match ve {
            Some(e) => {
                if let Some(sub) = pack_struct_const_value_with_outer(
                    mdt,
                    e,
                    params,
                    typedefs,
                    typedef_types,
                    sub_outer,
                ) {
                    sub.resize(*mw)
                } else if let Some(sub) = pack_packed_dt_pattern(
                    mdt,
                    e,
                    params,
                    Some(typedefs),
                    typedef_types,
                    sub_outer,
                ) {
                    // A nested pattern on a packed-VECTOR member
                    // (`bit [2:0][3:0] y` given `'{4,5,6}`).
                    sub.resize(*mw)
                } else {
                    // §6.12.2: a real item CONVERTS (rounds) to the member
                    // type; the width-fit would reinterpret its IEEE-754 bits.
                    let raw = eval_const_expr_val_env(e, &params);
                    if raw.is_real {
                        let r = raw.to_f64().round() as i64;
                        let m = if *mw >= 64 {
                            u64::MAX
                        } else {
                            (1u64 << *mw) - 1
                        };
                        Value::from_u64(r as u64 & m, *mw)
                    } else if explicit.is_some() {
                        eval_init_for_width(e, params, *mw)
                    } else {
                        // §10.8: default correspondence is self-determined.
                        raw.resize_for_assign(*mw)
                    }
                }
            }
            None => Value::zero(*mw),
        };
        parts.push(val);
    }
    Some(Value::concat(&parts))
}
