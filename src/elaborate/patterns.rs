use super::*;

/// assigned LSB-first by walking members in reverse. Returns None if `dt`
/// does not resolve to a struct/union.
/// Bit-slice layout (name, offset, width) of a *packed* struct type, or `None`
/// for a non-struct or an *unpacked* struct. An unpacked struct's members are
/// separate storage, not bit-packed, so their offsets are meaningless and must
/// never be registered as a packed slice layout. Used by the simulator to give
/// a local packed-struct variable the same whole/member aliasing that
/// module-level packed-struct signals get.
/// `arr[N]` where `N` is a *parameter* is indistinguishable, to the parser, from
/// `arr[key_t]` (an associative array keyed by type `key_t`) — a bare identifier
/// before `]` is assumed to name a type. Rewrite an associative dimension whose
/// "key type" is really a known parameter (and not a known type) back into a
/// fixed-size dimension. Without this, `rec_t a[N];` is registered as an
/// associative array and never gets a size (`%p`, `$size`, `foreach` all lose).
pub fn normalize_unpacked_dims(
    dims: &[UnpackedDimension],
    params: &HashMap<String, Value>,
    typedef_types: &HashMap<String, DataType>,
) -> Vec<UnpackedDimension> {
    normalize_unpacked_dims_env(dims, params, typedef_types)
}

pub(crate) fn normalize_unpacked_dims_env(
    dims: &[UnpackedDimension],
    params: &dyn ParamLookup,
    typedef_types: &HashMap<String, DataType>,
) -> Vec<UnpackedDimension> {
    dims.iter()
        .map(|d| match d {
            UnpackedDimension::Associative {
                data_type: Some(dt),
                span,
            } => {
                if let Some(fixed) = scoped_const_dim(d, params) {
                    return fixed;
                }
                if let DataType::TypeReference { name, .. } = dt.as_ref() {
                    let n = &name.name.name;
                    if !typedef_types.contains_key(n)
                        && (params.contains_key(n) || param_fallback_get(n).is_some())
                    {
                        return UnpackedDimension::Expression {
                            expr: Box::new(make_ident_expr(n)),
                            span: *span,
                        };
                    }
                }
                d.clone()
            }
            other => other.clone(),
        })
        .collect()
}

/// Constant element indices of the first unpacked dimension.
/// Empty for a scalar; empty for dynamic/queue/associative (size unknown here).
/// Element count of a declarator's FIXED unpacked dimensions (§7.4.2), for
/// width computations. Dynamic / queue / associative dimensions have no static
/// size and count as one, leaving the pre-existing behaviour for those.
pub(super) fn unpacked_dims_elem_count<P: ParamLookup>(
    dims: &[UnpackedDimension],
    params: Option<&P>,
) -> u32 {
    let mut n: u32 = 1;
    for d in dims {
        let c = match d {
            UnpackedDimension::Expression { expr, .. } => {
                match const_eval_i64_with_params_env(expr, params) {
                    Some(v) if v > 0 => v as u32,
                    _ => 1,
                }
            }
            UnpackedDimension::Range { left, right, .. } => match (
                const_eval_i64_with_params_env(left, params),
                const_eval_i64_with_params_env(right, params),
            ) {
                (Some(l), Some(r)) => ((l - r).abs() + 1) as u32,
                _ => 1,
            },
            // §7.4.2/§20.6.2: `m[SP]` / `m[cls::N]` parses as an associative
            // dimension keyed by a "type" (the parser cannot tell a type from
            // a constant); a parameter that names no type is a size.
            UnpackedDimension::Associative { .. } => params
                .and_then(|p| assoc_dim_const_size(d, &p.to_hashmap()))
                .map_or(1, |v| v.clamp(1, u32::MAX as i64) as u32),
            _ => 1,
        };
        n = n.saturating_mul(c.max(1));
    }
    n
}

/// The size an associative-looking dimension names when its "key type" is
/// really a constant: a class-scoped / package constant (`[cls::N]`, see
/// [`scoped_const_dim`]) or a bare parameter no typedef shadows (`[SP]`).
fn assoc_dim_const_size(d: &UnpackedDimension, params: &HashMap<String, Value>) -> Option<i64> {
    if let Some(UnpackedDimension::Expression { expr, .. }) = scoped_const_dim(d, params) {
        return const_eval_i64_with_params(&expr, Some(params));
    }
    let UnpackedDimension::Associative {
        data_type: Some(dt),
        ..
    } = d
    else {
        return None;
    };
    let DataType::TypeReference {
        name, dimensions, ..
    } = dt.as_ref()
    else {
        return None;
    };
    if !dimensions.is_empty() || !name.scopes.is_empty() {
        return None;
    }
    let n = &name.name.name;
    if typedefs_snapshot(|td| td.is_some_and(|t| t.contains_key(n))) {
        return None;
    }
    params.get(n)?.to_i64()
}

pub(super) fn const_dim_indices(
    dims: &[UnpackedDimension],
    params: &dyn ParamLookup,
) -> Option<Vec<i64>> {
    let p_ref = &params;
    match dims.first() {
        None => Some(Vec::new()),
        Some(UnpackedDimension::Expression { expr, .. }) => {
            match const_eval_i64_with_params_env(expr, Some(&p_ref)) {
                Some(n) if n > 0 && n <= 4096 => Some((0..n).collect()),
                _ => None,
            }
        }
        Some(UnpackedDimension::Range { left, right, .. }) => {
            match (
                const_eval_i64_with_params_env(left, Some(&p_ref)),
                const_eval_i64_with_params_env(right, Some(&p_ref)),
            ) {
                (Some(l), Some(r)) => {
                    let (lo, hi) = if l <= r { (l, r) } else { (r, l) };
                    if hi - lo < 4096 {
                        Some((lo..=hi).collect())
                    } else {
                        None
                    }
                }
                _ => None,
            }
        }
        _ => None,
    }
}

pub(super) fn register_member_leaf(elab: &mut ElaboratedModule, name: &str, dt: &DataType) {
    let w = resolve_type_width(dt, Some(&elab.parameters), Some(&elab.typedefs)).max(1);
    // §6.18: unpacked members retain the signing of an aliased type.
    let signed = is_type_signed_resolved(dt, &elab.typedef_types);
    // A member typed by a TYPEDEF (`typedef shortreal F; F v;`) reached this
    // point as a type REFERENCE, so the unresolved test said "not a real" and
    // the leaf was stored as an integral vector — the f64 bit pattern then
    // read back as a huge integer. Resolve the typedef first (§6.18: a
    // typedef names the SAME type it aliases).
    let real = is_type_real_resolved(dt, &elab.typedef_types);
    let resolved = resolve_typedef_chain(dt, &elab.typedef_types).clone();
    // §7.2 / §6.16 / §6.17: member access retains the declared type,
    // including string formatting, event identity and packed dimensions.
    elab.var_decl_types.insert(name.to_string(), dt.clone());
    if matches!(&resolved, DataType::Simple { kind: SimpleType::String, .. }) {
        elab.string_signals.insert(name.to_string());
    }
    if matches!(&resolved, DataType::Simple { kind: SimpleType::Event, .. }) {
        elab.events.insert(name.to_string());
    }
    let (elem_width, dims) = packed_member_meta(
        dt, &elab.parameters, &elab.typedefs, &elab.typedef_types,
    );
    if let Some(width) = elem_width {
        elab.packed_signal_elem_widths.insert(name.to_string(), width);
    }
    if let Some(dims) = dims {
        elab.packed_full_dims.insert(name.to_string(), dims);
    }
    // §6.12/§20.5: a SHORTREAL holds an IEEE binary32 value, so a write
    // rounds to binary32 (16777216.25 -> 16777216.0). Mark the leaf so the
    // runtime rounds it; a `real` (binary64) keeps every bit.
    let shortreal = matches!(
        resolved,
        DataType::Real {
            kind: crate::ast::types::RealType::ShortReal,
            ..
        }
    );
    match &resolved {
        // A nested PACKED struct member keeps a contiguous bit layout: give it
        // its own signal plus the field offsets so `base.m.f` can slice it.
        DataType::Struct(su) if su.packed => {
            elab.signals.entry(name.to_string()).or_insert(Signal {
                is_const: false,
                name: name.to_string().into(),
                width: w,
                is_signed: signed,
                is_real: false,
                direction: None,
                value: Value::new(w),
                type_name: None,
            });
            if let Some(fields) =
                flatten_struct_fields(dt, &elab.parameters, &elab.typedefs, &elab.typedef_types)
            {
                if !fields.is_empty() {
                    elab.packed_struct_fields.insert(name.to_string(), fields);
                }
            }
        }
        // §7.2 / §23.3.3: a nested unpacked struct is itself a valid port
        // actual. It has no container signal, so retain its type for the
        // whole-struct expansion of `parent.member = inst.port` as well as
        // registering its leaves. Resolve the alias while its scope is live.
        DataType::Struct(_) => {
            elab.var_decl_types
                .insert(name.to_string(), resolved.clone());
            register_unpacked_aggregate(elab, name, dt);
        }
        _ => {
            elab.signals.entry(name.to_string()).or_insert(Signal {
                is_const: false,
                name: name.to_string().into(),
                width: w,
                is_signed: signed,
                is_real: real,
                direction: None,
                value: if real {
                    Value::from_f64(0.0)
                } else {
                    Value::new(w)
                },
                type_name: if shortreal {
                    Some("shortreal".to_string())
                } else {
                    None
                },
            });
        }
    }
}

/// Recursively pre-register the per-member signals of an UNPACKED aggregate
/// rooted at `base` (e.g. `arr[3]`, `c`). Each leaf keeps its declared width /
/// signedness / real-ness, array members expand per element, and nested packed
/// members get their own signal + bit-slice layout. Without this, elements are
/// created lazily on first assignment and lose their type (a `real` reads back
/// as raw bits) or alias each other through a bogus packed layout.
/// IEEE 1800-2017 §6.20.2: an UNPACKED-ARRAY parameter — `u32_t A[N] = {a, b}`.
/// Give each element its own const signal (`<prefix>A[i]`) so `A[i]` reads at
/// run time, and register the array so `A[i]` is an element select rather than
/// a bit-select of a scalar.
///
/// An OVERRIDE arrives already collapsed to one packed value, so slice it:
/// `{a, b}` puts `a` in the high bits (§11.4.12) and `a` is element 0.
/// Returns false when the size or the element values can't be resolved, so the
/// caller falls back to treating the parameter as a scalar.
///
/// `params` is optional: when `None`, the elaboration-wide parameter map is
/// used directly (the common case, avoiding a whole-table clone borrow
/// workaround); pass `Some(map)` when the elements must resolve against a
/// different overlay (e.g. a package-visible or sub-instance scope).
pub(super) fn register_array_param(
    elab: &mut ElaboratedModule,
    prefix: &str,
    name: &str,
    dims: &[UnpackedDimension],
    init: Option<&Expression>,
    override_val: Option<&Value>,
    data_type: &DataType,
    params: Option<&HashMap<String, Value>>,
) -> bool {
    // Compute the registration data against a read-only view, so `params` may
    // borrow `&elab.parameters` without conflicting with the later `&mut`.
    let computed = match params {
        Some(p) => array_params::compute(
            &*elab, prefix, name, dims, init, override_val, data_type, p, p,
        ),
        None => {
            let read_only: &ElaboratedModule = elab;
            array_params::compute(
                read_only,
                prefix,
                name,
                dims,
                init,
                override_val,
                data_type,
                &read_only.parameters,
                &read_only.parameters,
            )
        }
    };
    match computed {
        Some(registered) => {
            registered.apply(elab, prefix);
            true
        }
        None => false,
    }
}

/// An index of a multi-dimensional packed parameter is an element select, not
/// a bit select, the same registration the variable path does.
pub(super) fn register_packed_param_shape(
    elab: &mut ElaboratedModule,
    name: &str,
    data_type: &DataType,
) {
    if let Some(elem_w) = packed_inner_elem_width(data_type, &elab.parameters, &elab.typedefs) {
        // The CONST-eval index arm reads its own TLS table (only
        // `register_packed_array_elem_w` fed it, which handles a typedef'd
        // element type). Without this a `localparam logic [1:0][7:0] MP`
        // element select `MP[0]` in another localparam bit-selected instead.
        // The runtime map is `register_packed_param_index`.
        tls_register_elem_w(name, elem_w);
    }
    if let Some((ew, msb0, low)) =
        packed_outer_elem(data_type, &elab.parameters, &elab.typedef_types)
    {
        tls_register_elem_w(name, ew);
        tls_register_elem_low(name, low);
        tls_register_elem_inner(name, data_type, &elab.parameters, &elab.typedef_types);
        if msb0 {
            tls_register_elem_msb0(name);
        }
    }
    // A typedef'd array (`exp_arr_t EXPS`, `enc_t [0:4] LOCAL`) has its dims on
    // the typedef or as a single ascending range. `packed_inner_elem_width` /
    // `packed_full_dims_of` miss those, so a variable index bit-selects or
    // reads the last element.
    register_packed_param_index(elab, name, data_type, None);
}

/// `base.member` as a hierarchical IDENTIFIER when `base` is a whole-net
/// identifier, falling back to a `MemberAccess` node otherwise.
///
/// An inlined instance port is a FLAT signal whose NAME contains dots
/// (`u1.o`), so `MemberAccess(Ident("u1.o"), a)` has no resolution path — the
/// member lookup wants a struct object, not a dotted signal key. Appending the
/// member as a path SEGMENT yields `u1.o.a`, which is exactly the registered
/// leaf. For an ordinary base (`s`) the two forms resolve identically.
pub(super) fn member_ref_expr(base: &Expression, member: &Identifier) -> Expression {
    if let ExprKind::Ident(h) = &base.kind {
        if h.root.is_none() && !h.path.is_empty() && h.path.iter().all(|sg| sg.selects.is_empty()) {
            let mut segs = h.path.clone();
            segs.push(HierPathSegment {
                name: member.clone(),
                selects: Vec::new(),
            });
            return Expression::new(
                ExprKind::Ident(HierarchicalIdentifier {
                    root: None,
                    path: segs,
                    span: base.span,
                    cached_signal_id: crate::ast::cache::SignalCache::new(None),
                    cached_resolved_name: crate::ast::cache::NameCache::new(),
                    bound: crate::ast::binding::Bound::UNSET,
                }),
                base.span,
            );
        }
    }
    Expression::new(
        ExprKind::MemberAccess {
            expr: Box::new(base.clone()),
            member: member.clone(),
        },
        base.span,
    )
}

/// IEEE 1800-2023 §10.9.2: a count must match before expansion. Unlike
/// `to_i64`, this conversion neither masks x/z nor discards high bits.
pub fn struct_pattern_count_value(value: &Value) -> Option<i64> {
    if value.is_real
        || value.has_xz()
        || (value.is_signed
            && value.width > 0
            && value.get_bit(value.width as usize - 1) == crate::value::LogicBit::One)
        || (63..value.width as usize).any(|i| value.get_bit(i) != crate::value::LogicBit::Zero)
    {
        return None;
    }
    value.to_i64().filter(|&n| n >= 0)
}

/// IEEE 1800-2023 §5.7.1, §10.9.2: only integer literals need no
/// expression evaluation. All other count forms keep the existing handling.
pub fn struct_pattern_count(expr: &Expression) -> Option<i64> {
    let ExprKind::Number(NumberLiteral::Integer {
        size,
        signed,
        base,
        value,
        ..
    }) = &expr.kind
    else {
        return None;
    };
    let radix = match base {
        NumberBase::Binary => 2,
        NumberBase::Octal => 8,
        NumberBase::Hex => 16,
        NumberBase::Decimal => 10,
    };
    let digits = value.replace('_', "");
    if digits.contains(['x', 'X', 'z', 'Z', '?']) || size.is_some_and(|w| w > Value::MAX_WIDTH) {
        return None;
    }
    let mut value = Value::from_str_radix(&digits, radix, size.unwrap_or(32));
    value.is_signed = *signed;
    let count = struct_pattern_count_value(&value)?;
    // Do not accept a wider unsized literal after a 32-bit truncation.
    if size.is_none() && i64::from_str_radix(&digits, radix).ok() != Some(count) {
        return None;
    }
    Some(count)
}

/// IEEE 1800-2023 §10.9.2: remove a structure replication's inner braces,
/// mapping each expression to a member rather than concatenating its bits.
/// Check the exact member count before allocating, including overflow. Side
/// effects may be evaluated per member: §10.9.2 leaves their count undefined.
pub fn struct_pattern_replication(
    items: &[AssignmentPatternItem],
    members: usize,
) -> Option<Vec<&Expression>> {
    struct_pattern_replication_with(items, members, &mut |_| None)
}

/// `struct_pattern_replication` for a count that is not an integer literal:
/// A.6.7.1 makes it a constant expression (a parameter, a localparam, a
/// constant operation), which `count_of` evaluates in the caller's scope
/// (`struct_pattern_count_value` gives the same lossless rule).
pub fn struct_pattern_replication_with<'a>(
    items: &'a [AssignmentPatternItem],
    members: usize,
    count_of: &mut dyn FnMut(&Expression) -> Option<i64>,
) -> Option<Vec<&'a Expression>> {
    let [AssignmentPatternItem::Ordered(e)] = items else {
        return None;
    };
    let ExprKind::Replication { count, exprs } = &e.kind else {
        return None;
    };
    let count = match struct_pattern_count(count) {
        Some(n) => n,
        None => count_of(count)?,
    };
    let count = usize::try_from(count).ok()?;
    if exprs.is_empty() || count.checked_mul(exprs.len())? != members {
        return None;
    }
    Some((0..count).flat_map(|_| exprs.iter()).collect())
}

/// IEEE 1800-2023 §10.9.1/§10.9.2: array-member patterns need their own
/// binding. Until that path handles replication, keep the existing structure
/// handling, including when the array is inside a nested structure.
/// Visit each referenced structure once, without scanning the typedef table.
pub fn struct_pattern_has_array_member(
    su: &crate::ast::types::StructUnionType,
    typedef_types: &HashMap<String, DataType>,
    typedef_unpacked_dims: &HashMap<String, Vec<UnpackedDimension>>,
) -> bool {
    let mut pending = vec![su];
    let mut seen = HashSet::default();
    while let Some(su) = pending.pop() {
        if !seen.insert(su as *const crate::ast::types::StructUnionType) {
            continue;
        }
        for member in &su.members {
            if member.declarators.iter().any(|d| !d.dimensions.is_empty()) {
                return true;
            }
            let mut dt = &member.data_type;
            for _ in 0..64 {
                let DataType::TypeReference { name, .. } = dt else {
                    break;
                };
                if lookup_scoped_type(name, typedef_unpacked_dims)
                    .is_some_and(|dims| !dims.is_empty())
                {
                    return true;
                }
                let Some(next) = lookup_scoped_type(name, typedef_types) else {
                    break;
                };
                dt = next;
            }
            if let DataType::Struct(inner) = dt {
                pending.push(inner);
            }
        }
    }
    false
}

/// Emit one continuous assign per LEAF of an unpacked struct, recursing into
/// members that are themselves unpacked structs.
///
/// A single-level expansion is not enough: `assign nn = <expr>;` where member
/// `nn.inner` is itself a struct produced `assign nn.inner = <expr>.inner;`,
/// and THAT has nowhere to land either — `nn.inner` is not a stored signal
/// (only its leaves are), and the pass had already moved past it, so a nested
/// member read back 0 while sibling scalar members were correct.
#[allow(clippy::too_many_arguments)]
pub(super) fn emit_struct_member_assigns(
    lhs_base: &Expression,
    rhs: &Expression,
    su: &crate::ast::types::StructUnionType,
    ca: &ContinuousAssignment,
    typedef_types: &HashMap<String, DataType>,
    typedef_unpacked_dims: &HashMap<String, Vec<UnpackedDimension>>,
    params: &HashMap<String, Value>,
    default_types: Option<&ElaboratedModule>,
    out: &mut Vec<ContinuousAssignment>,
    depth: u32,
) {
    // Bounded against a malformed self-referential typedef.
    if depth > 16 {
        out.push(ContinuousAssignment {
            gate_delay_fall: None,
            delay_exprs: ca.delay_exprs.clone(),
            delay_select: ca.delay_select,
            origin: ca.origin.clone(),
            lhs: lhs_base.clone(),
            rhs: rhs.clone(),
            delay: ca.delay,
            rhs_parent_scoped: ca.rhs_parent_scoped,
            delay_fall: ca.delay_fall,
            delay_off: ca.delay_off,
        });
        return;
    }
    // Flat (member, declared type, unpacked dims) list in declaration order —
    // the order an ORDERED assignment pattern maps onto position-wise.
    let mut flat: Vec<(String, DataType, Vec<UnpackedDimension>)> = Vec::new();
    for m in &su.members {
        for d in &m.declarators {
            flat.push((
                d.name.name.clone(),
                m.data_type.clone(),
                struct_member_dims(&m.data_type, &d.dimensions, typedef_unpacked_dims).into_owned(),
            ));
        }
    }
    // An assignment pattern on the RHS is taken APART here, item by item.
    // Member-selecting the literal instead (`'{1.5, 1'b1}.f1`) has no
    // evaluation path and yields 0 -- silently, which is why every form of
    // §10.9.2 is bound to its members explicitly (`bind_struct_pattern`):
    // by position, by member name, by type key and by `default:`.
    let pat_items: Option<Vec<(Expression, Vec<(DataType, Expression)>)>> =
        match &peel_unpacked_typed_pattern(rhs).kind {
            ExprKind::AssignmentPattern(items) => bind_struct_pattern(
                items,
                &flat,
                typedef_types,
                params,
                ca.origin.as_ref().map_or("", |(_, scope)| scope),
                default_types,
                rhs.span,
            ),
            _ => None,
        };
    let pat_items = match &peel_unpacked_typed_pattern(rhs).kind {
        ExprKind::AssignmentPattern(items)
            if !struct_pattern_has_array_member(su, typedef_types, typedef_unpacked_dims) =>
        {
            struct_pattern_replication(items, flat.len())
                .map(|items| {
                    items
                        .into_iter()
                        .map(|e| (e.clone(), Vec::new()))
                        .collect()
                })
                .or(pat_items)
        }
        _ => pat_items,
    };
    for (i, (mname, mdt, mdims)) in flat.iter().enumerate() {
        let mident = Identifier {
            name: mname.clone(),
            span: Span::dummy(),
        };
        let mlhs = member_ref_expr(lhs_base, &mident);
        let (mrhs, m_outer_types) = match &pat_items {
            Some(items) => (items[i].0.clone(), items[i].1.clone()),
            None => (member_ref_expr(rhs, &mident), Vec::new()),
        };
        emit_member_elem_assigns(
            mlhs,
            mrhs,
            pat_items.is_some(),
            &m_outer_types,
            mdt,
            mdims,
            ca,
            typedef_types,
            typedef_unpacked_dims,
            params,
            default_types,
            out,
            depth,
        );
    }
}

/// IEEE 1800-2017 §7.2/§7.4.2: the continuous assigns for ONE member of an
/// unpacked struct, `lhs = rhs`. A member with fixed unpacked dimensions has
/// no storage of its own — every element is its own leaf — so it expands to
/// one assign per element (`lhs[i][j] = rhs[i][j]`, or the matching item of
/// a nested pattern when `rhs_is_item`); a member that is (an array of) an
/// unpacked struct recurses into its own members. A whole-member assign had
/// nowhere to land, so every array member of a struct port or a struct
/// continuous assign read back x.
#[allow(clippy::too_many_arguments)]
pub(super) fn emit_member_elem_assigns(
    lhs: Expression,
    rhs: Expression,
    rhs_is_item: bool,
    outer_types: &[(DataType, Expression)],
    mdt: &DataType,
    mdims: &[UnpackedDimension],
    ca: &ContinuousAssignment,
    typedef_types: &HashMap<String, DataType>,
    typedef_unpacked_dims: &HashMap<String, Vec<UnpackedDimension>>,
    params: &HashMap<String, Value>,
    default_types: Option<&ElaboratedModule>,
    out: &mut Vec<ContinuousAssignment>,
    depth: u32,
) {
    let push_leaf = |out: &mut Vec<ContinuousAssignment>, lhs: Expression, rhs: Expression| {
        match resolve_typedef_chain(mdt, typedef_types) {
            DataType::Struct(inner) if !inner.packed && !inner.members.is_empty() => {
                let inner = inner.clone();
                emit_struct_member_assigns(
                    &lhs,
                    &rhs,
                    &inner,
                    ca,
                    typedef_types,
                    typedef_unpacked_dims,
                    params,
                    default_types,
                    out,
                    depth + 1,
                );
            }
            _ => out.push(ContinuousAssignment {
                gate_delay_fall: None,
                delay_exprs: ca.delay_exprs.clone(),
                delay_select: ca.delay_select,
                origin: ca.origin.clone(),
                lhs,
                rhs,
                delay: ca.delay,
                rhs_parent_scoped: ca.rhs_parent_scoped,
                delay_fall: ca.delay_fall,
                delay_off: ca.delay_off,
            }),
        }
    };
    let lists = if mdims.is_empty() {
        None
    } else {
        fixed_unpacked_index_lists(mdims, params, typedef_types)
    };
    let Some(lists) = lists else {
        push_leaf(out, lhs, rhs);
        return;
    };
    if rhs_is_item {
        // A pattern item supplies the elements through one nested pattern
        // level per dimension (§10.9.1): by position, by replication, by index
        // key, by type key or by `default:`. An item that is not a pattern
        // is an array value, read element by element.
        let mut leaves: Vec<(Vec<i64>, Expression)> = Vec::new();
        let elem = ArraySlot {
            elem_dt: mdt,
            typedef_types,
            params,
            scope: ca.origin.as_ref().map_or("", |(_, scope)| scope),
            default_types,
        };
        if elem
            .bind(&rhs, &lists, &mut Vec::new(), &mut leaves, outer_types)
            .is_none()
        {
            // Not bindable here: keep the whole-member form.
            push_leaf(out, lhs, rhs);
            return;
        }
        for (idx, rhs_e) in leaves {
            let lhs_e = idx.iter().fold(lhs.clone(), |e, &i| index_expr_of(e, i));
            push_leaf(out, lhs_e, rhs_e);
        }
        return;
    }
    for tup in cartesian_index_tuples(&lists) {
        let rhs_e = tup.iter().fold(rhs.clone(), |e, &i| index_expr_of(e, i));
        let lhs_e = tup.iter().fold(lhs.clone(), |e, &i| index_expr_of(e, i));
        push_leaf(out, lhs_e, rhs_e);
    }
}

/// Like [`member_access_chain_as_scopes`], also stepping through an
/// `ExprKind::Specialization` (`PC#(integer)::cw_t` or `pkg::PC#(T)::cw_t`).
fn member_access_chain_as_scopes_or_spec(
    e: &crate::ast::expr::Expression,
) -> Option<(Vec<crate::ast::types::TypeScope>, Identifier)> {
    let mut links: Vec<Identifier> = Vec::new();
    let mut cur = e;
    for _ in 0..16 {
        match &cur.kind {
            ExprKind::MemberAccess { expr, member } => {
                links.push(member.clone());
                cur = expr;
            }
            ExprKind::Specialization { base, .. } => {
                cur = base;
            }
            ExprKind::Ident(h) if h.root.is_none() && h.path.iter().all(|s| s.selects.is_empty()) => {
                for seg in h.path.iter().rev() {
                    links.push(seg.name.clone());
                }
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

/// Whether `expr` is a scoped type reference (`pkg::word_t`, `$unit::word_t`)
/// in `typedef_types` rather than a value parameter in `params`.
fn scoped_type_key_of_expr(
    expr: &Expression,
    typedef_types: &HashMap<String, DataType>,
    params: &dyn ParamLookup,
) -> Option<DataType> {
    let tn = match &expr.kind {
        ExprKind::Ident(h) if h.root.is_none() && h.path.iter().all(|s| s.selects.is_empty()) => {
            if h.path.len() >= 2 {
                let mut scopes = Vec::with_capacity(h.path.len() - 1);
                for seg in &h.path[..h.path.len() - 1] {
                    scopes.push(crate::ast::types::TypeScope {
                        name: seg.name.clone(),
                        type_args: Vec::new(),
                    });
                }
                let leaf = h.path.last()?.name.clone();
                TypeName {
                    scopes,
                    name: leaf,
                    span: expr.span,
                    bound: Default::default(),
                }
            } else if h.path.len() == 1
                && crate::sv_parser::strip_unit_scope_name(&h.path[0].name.name).is_some()
            {
                let bare = crate::sv_parser::strip_unit_scope_name(&h.path[0].name.name)?;
                let key = if typedef_types.contains_key(&h.path[0].name.name) {
                    h.path[0].name.name.as_str()
                } else if typedef_types.contains_key(bare) {
                    bare
                } else {
                    return None;
                };
                if params.contains_key(key) {
                    return None;
                }
                return Some(DataType::TypeReference {
                    name: TypeName {
                        scopes: Vec::new(),
                        name: Identifier {
                            name: key.to_string(),
                            span: expr.span,
                        },
                        span: expr.span,
                        bound: Default::default(),
                    },
                    dimensions: Vec::new(),
                    type_args: Vec::new(),
                    span: expr.span,
                });
            } else {
                return None;
            }
        }
        ExprKind::MemberAccess { .. } => {
            let (scopes, leaf) = member_access_chain_as_scopes_or_spec(expr)?;
            if scopes.is_empty() {
                return None;
            }
            TypeName {
                scopes,
                name: leaf,
                span: expr.span,
                bound: Default::default(),
            }
        }
        _ => return None,
    };
    let qualified = tn.qualified();
    if params.contains_key(&qualified) || !typedef_types.contains_key(&qualified) {
        return None;
    }
    Some(DataType::TypeReference {
        name: tn,
        dimensions: Vec::new(),
        type_args: Vec::new(),
        span: expr.span,
    })
}

/// Whether `name` names a value parameter in `scope` (walking enclosing scopes)
/// or at module/package scope.
pub(super) fn is_param_in_scope(name: &str, scope: &str, params: &dyn ParamLookup) -> bool {
    if !scope.is_empty() {
        let mut cur = scope;
        loop {
            if params.contains_key(&format!("{cur}.{name}")) {
                return true;
            }
            let Some((outer, _)) = cur.rsplit_once('.') else {
                break;
            };
            cur = outer;
        }
    }
    params.contains_key(name)
}

/// The `typedef_types` key for an unscoped type identifier `name` in `scope`,
/// walking enclosing scopes before checking the bare table.
pub(super) fn lookup_typedef_key_in_scope(
    name: &str,
    scope: &str,
    typedef_types: &HashMap<String, DataType>,
) -> Option<String> {
    if !scope.is_empty() {
        let mut cur = scope;
        loop {
            let key = format!("{cur}.{name}");
            if typedef_types.contains_key(&key) {
                return Some(key);
            }
            let Some((outer, _)) = cur.rsplit_once('.') else {
                break;
            };
            cur = outer;
        }
    }
    typedef_types.contains_key(name).then(|| name.to_string())
}

/// Extract `(type_key, value_expr)` when `item` is a pattern type key
/// (built-in type, unscoped typedef/type parameter, or scoped package/class
/// typedef), unless `is_excluded(name)` treats a bare name as a member/index.
pub(super) fn pattern_item_type_key<'a>(
    item: &'a AssignmentPatternItem,
    typedef_types: &HashMap<String, DataType>,
    params: &dyn ParamLookup,
    scope: &str,
    is_excluded: &dyn Fn(&str) -> bool,
) -> Option<(DataType, &'a Expression)> {
    match item {
        AssignmentPatternItem::Typed(t, v) => Some((t.clone(), v)),
        AssignmentPatternItem::Named(k, v) if !is_excluded(&k.name) => {
            if is_param_in_scope(&k.name, scope, params) {
                return None;
            }
            let key = if let Some(tk) = k.type_key.as_deref() {
                typedef_types.contains_key(tk).then(|| tk.to_string())?
            } else {
                lookup_typedef_key_in_scope(&k.name, scope, typedef_types)?
            };
            let span = k.span;
            Some((
                DataType::TypeReference {
                    name: TypeName {
                        scopes: Vec::new(),
                        name: Identifier { name: key, span },
                        span,
                        bound: Default::default(),
                    },
                    dimensions: Vec::new(),
                    type_args: Vec::new(),
                    span,
                },
                v,
            ))
        }
        AssignmentPatternItem::Keyed(k, v) => {
            let dt = scoped_type_key_of_expr(k, typedef_types, params)?;
            Some((dt, v))
        }
        _ => None,
    }
}

impl PatternKeys {
    /// Record one key item of a pattern; false for any other item, or for a
    /// second `default:`.
    pub(super) fn add(
        &mut self,
        item: &AssignmentPatternItem,
        typedef_types: &HashMap<String, DataType>,
        params: &dyn ParamLookup,
        scope: &str,
    ) -> bool {
        if let Some((dt, v)) =
            pattern_item_type_key(item, typedef_types, params, scope, &|_| false)
        {
            self.types.push((dt, v.clone()));
            return true;
        }
        match item {
            AssignmentPatternItem::Default(v) => {
                if self.default.replace(v.clone()).is_some() {
                    return false;
                }
                true
            }
            _ => false,
        }
    }

    /// Merge `outer_types` after `self.types` (last match wins, so `outer_types`
    /// takes precedence over items inside an outer `default:`).
    fn combined_types(&self, outer_types: &[(DataType, Expression)]) -> Vec<(DataType, Expression)> {
        let mut out = Vec::with_capacity(self.types.len() + outer_types.len());
        out.extend(self.types.iter().cloned());
        out.extend(outer_types.iter().cloned());
        out
    }

    /// The value these keys give one member or element of type `dt`, which
    /// is an unpacked (sub)array when `is_array`. The last type key the type
    /// matches wins (§10.9.2); otherwise `default:` applies. An aggregate
    /// (unpacked array or structure, packed structure, multidimensional
    /// packed array; §6.11.1) gets the keys as a pattern of its own, so they
    /// reach its members and elements; a pattern given as the default is the
    /// aggregate's own value. None when nothing covers it, or when a type
    /// key cannot be matched here.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn value_for(
        &self,
        dt: &DataType,
        is_array: bool,
        outer_types: &[(DataType, Expression)],
        typedef_types: &HashMap<String, DataType>,
        params: &dyn ParamLookup,
        span: Span,
        matches_default: impl FnOnce(&Expression) -> bool,
    ) -> Option<(Expression, Vec<(DataType, Expression)>)> {
        let combined = self.combined_types(outer_types);
        let aggregate = is_array || pattern_slot_is_aggregate(dt, typedef_types)?;
        if !is_array {
            let dt_sig = pattern_type_signature(dt, typedef_types, params);
            let mut typed = None;
            if let Some(dt_sig) = dt_sig {
                for (key, v) in &combined {
                    if pattern_type_signature(key, typedef_types, params).as_ref() == Some(&dt_sig) {
                        typed = Some(v);
                    }
                }
            }
            if let Some(v) = typed {
                return Some((v.clone(), Vec::new()));
            }
        }
        if !aggregate {
            return self.default.clone().map(|d| (d, Vec::new()));
        }
        // §10.9.1/§10.9.2: a matching self-determined type takes the whole
        // default. Keep the existing recursive binding for type-key patterns.
        if let Some(d) = &self.default
            && combined.is_empty()
            && matches_default(d)
        {
            return Some((d.clone(), Vec::new()));
        }
        if let Some(d) = &self.default
            && matches!(
                peel_unpacked_typed_pattern(d).kind,
                ExprKind::AssignmentPattern(_)
            )
        {
            if !is_array && matches!(resolve_typedef_chain(dt, typedef_types), DataType::Struct(_)) {
                return Some((d.clone(), combined));
            }
            if combined.is_empty() {
                return Some((d.clone(), Vec::new()));
            }
            if !is_array {
                // Packed aggregate: append combined type keys after the default pattern's
                // items so outer/local type keys still take precedence over `default:`.
                let mut merged = match &peel_unpacked_typed_pattern(d).kind {
                    ExprKind::AssignmentPattern(items) => items.clone(),
                    _ => Vec::new(),
                };
                for (t, v) in &combined {
                    merged.push(AssignmentPatternItem::Typed(t.clone(), v.clone()));
                }
                return Some((
                    Expression::new(ExprKind::AssignmentPattern(merged), d.span),
                    Vec::new(),
                ));
            }
            return Some((d.clone(), combined));
        }
        if combined.is_empty() && self.default.is_none() {
            return None;
        }
        let mut items: Vec<AssignmentPatternItem> = combined
            .iter()
            .map(|(t, v)| AssignmentPatternItem::Typed(t.clone(), v.clone()))
            .collect();
        if let Some(d) = &self.default {
            items.push(AssignmentPatternItem::Default(d.clone()));
        }
        Some((
            Expression::new(ExprKind::AssignmentPattern(items), span),
            Vec::new(),
        ))
    }
}

/// Whether type and `default:` keys reach into a value of type `dt` rather
/// than set it whole (§10.9.1, §10.9.2): a structure, or a packed array of
/// more than one dimension, which is not a simple bit vector type (§6.11.1).
/// None for a union, whose members the keys do not place here.
pub(super) fn pattern_slot_is_aggregate(
    dt: &DataType,
    typedef_types: &HashMap<String, DataType>,
) -> Option<bool> {
    let mut packed_dims = 0usize;
    let mut cur = dt;
    for _ in 0..64 {
        match cur {
            DataType::TypeReference {
                name, dimensions, ..
            } => {
                packed_dims += dimensions.len();
                match lookup_scoped_type(name, typedef_types) {
                    Some(next) => cur = next,
                    None => return Some(packed_dims > 1),
                }
            }
            DataType::Struct(su) => {
                return (su.kind == StructUnionKind::Struct).then_some(true);
            }
            DataType::IntegerVector { dimensions, .. } | DataType::Implicit { dimensions, .. } => {
                return Some(packed_dims + dimensions.len() > 1);
            }
            DataType::Enum(e) => return Some(packed_dims + e.dimensions.len() > 1),
            _ => return Some(packed_dims > 0),
        }
    }
    None
}

/// §6.22.1: a key that two types share when they match, for the types a
/// pattern's type key names (integral, real and string types, and named
/// structures and enumerations, which match only their own declaration).
/// None when it cannot be decided here.
pub(super) fn pattern_type_signature(
    dt: &DataType,
    typedef_types: &HashMap<String, DataType>,
    params: &dyn ParamLookup,
) -> Option<String> {
    pattern_type_signature_with(dt, params, |name, _| {
        lookup_scoped_type(name, typedef_types)
    })
}

fn pattern_type_signature_with<'a>(
    dt: &'a DataType,
    params: &dyn ParamLookup,
    mut resolve: impl FnMut(&TypeName, &[Expression]) -> Option<&'a DataType>,
) -> Option<String> {
    let bounds = |d: &PackedDimension| -> Option<(i64, i64)> {
        match d {
            PackedDimension::Range { left, right, .. } => Some((
                const_eval_i64_with_params_env(left, Some(&params))?,
                const_eval_i64_with_params_env(right, Some(&params))?,
            )),
            PackedDimension::Unsized(_) => None,
        }
    };
    let mut out = String::new();
    let mut cur = dt;
    for _ in 0..64 {
        match cur {
            DataType::TypeReference {
                name,
                dimensions,
                type_args,
                ..
            } => {
                for d in dimensions {
                    let (l, r) = bounds(d)?;
                    out.push_str(&format!("[{l}:{r}]"));
                }
                cur = resolve(name, type_args)?;
            }
            DataType::IntegerVector {
                kind,
                signing,
                dimensions,
                ..
            } => {
                let state = if *kind == IntegerVectorType::Bit {
                    2
                } else {
                    4
                };
                return Some(vector_type_signature(
                    out,
                    state,
                    *signing == Some(Signing::Signed),
                    dimensions,
                    bounds,
                )?);
            }
            DataType::Implicit {
                signing,
                dimensions,
                ..
            } => {
                return Some(vector_type_signature(
                    out,
                    4,
                    *signing == Some(Signing::Signed),
                    dimensions,
                    bounds,
                )?);
            }
            DataType::IntegerAtom { kind, signing, .. } => {
                let (w, state) = match kind {
                    IntegerAtomType::Byte => (8, 2),
                    IntegerAtomType::ShortInt => (16, 2),
                    IntegerAtomType::Int => (32, 2),
                    IntegerAtomType::LongInt => (64, 2),
                    IntegerAtomType::Integer => (32, 4),
                    IntegerAtomType::Time => (64, 4),
                };
                let signed = match signing {
                    Some(s) => *s == Signing::Signed,
                    None => *kind != IntegerAtomType::Time,
                };
                out.push_str(&format!("v{state}{signed}[{}:0]", w - 1));
                return Some(out);
            }
            DataType::Real { kind, .. } => {
                // IEEE 1800-2023 §6.12 treats real and realtime as synonyms.
                out.push_str(match kind {
                    RealType::Real | RealType::RealTime => "rReal",
                    RealType::ShortReal => "rShortReal",
                });
                return Some(out);
            }
            DataType::Simple { kind, .. } => {
                out.push_str(&format!("s{kind:?}"));
                return Some(out);
            }
            DataType::Struct(su) if su.dimensions.is_empty() && su.span != Span::dummy() => {
                out.push_str(&format!("u{}:{}", su.span.start, su.span.end));
                return Some(out);
            }
            DataType::Enum(e) if e.dimensions.is_empty() && e.span != Span::dummy() => {
                out.push_str(&format!("e{}:{}", e.span.start, e.span.end));
                return Some(out);
            }
            _ => return None,
        }
    }
    None
}

/// The signature of a bit vector type: each outer packed dimension, then the
/// innermost range (or none for a scalar).
fn vector_type_signature(
    mut out: String,
    state: u8,
    signed: bool,
    dimensions: &[PackedDimension],
    bounds: impl Fn(&PackedDimension) -> Option<(i64, i64)>,
) -> Option<String> {
    let Some((last, outer)) = dimensions.split_last() else {
        out.push_str(&format!("b{state}{signed}"));
        return Some(out);
    };
    for d in outer {
        let (l, r) = bounds(d)?;
        out.push_str(&format!("[{l}:{r}]"));
    }
    let (l, r) = bounds(last)?;
    out.push_str(&format!("v{state}{signed}[{l}:{r}]"));
    Some(out)
}

/// §6.22.1(b), (d), (f), (h): follow typedefs to the same declaration for
/// nominal types, and compare both bounds of every fixed array dimension.
pub(super) fn continuous_default_matches(
    elab: &ElaboratedModule,
    scope: &str,
    rhs: &Expression,
    dt: &DataType,
    dims: &[UnpackedDimension],
) -> Option<()> {
    CONST_FN_UNIT_TYPES
        .with_borrow(|unit| continuous_default_match_in(elab, unit.as_ref(), scope, rhs, dt, dims))
}

fn continuous_default_match_in(
    elab: &ElaboratedModule,
    unit: Option<&HashMap<String, DataType>>,
    scope: &str,
    rhs: &Expression,
    dt: &DataType,
    dims: &[UnpackedDimension],
) -> Option<()> {
    let (types, params) = (&elab.typedef_types, &elab.parameters);
    let no_dims = &[][..];
    let mut rhs = rhs;
    while let ExprKind::Paren(inner) = &rhs.kind {
        rhs = inner;
    }
    let (rhs_type, rhs_dims) = match &rhs.kind {
        ExprKind::TypedPattern { ty, .. } => (ty.as_ref(), no_dims),
        ExprKind::SystemCall { name, args }
            if matches!(name.as_str(), "$__xz_named_cast" | "$__xz_type_cast")
                && let [target, _] = args.as_slice() =>
        {
            let cast_type = match &target.kind {
                ExprKind::TypeLiteral(ty) => ty.as_ref(),
                ExprKind::Ident(h) if h.bound.has_late_type_declaration() => return None,
                ExprKind::Ident(h)
                    if let Some(name) = simple_lhs_name(target)
                        && !is_param_in_scope(&name, scope, params) =>
                {
                    let key = crate::pkg_scope::external_type_key(h.bound).or_else(|| {
                        (h.bound.as_decl().is_some() || name.contains(['.', ':']))
                            .then(|| lookup_typedef_key_in_scope(&name, scope, types))?
                    })?;
                    continuous_default_typedef(elab, unit, &key, false)?
                }
                _ => {
                    let DataType::TypeReference { name, .. } =
                        scoped_type_key_of_expr(target, types, params)?
                    else {
                        return None;
                    };
                    continuous_default_typedef(elab, unit, &name.qualified(), false)?
                }
            };
            (cast_type, no_dims)
        }
        ExprKind::Ident(h) if h.root.is_none() => {
            let name = ident_flat_name(rhs)?;
            let ty = elab
                .var_decl_types
                .get(&name)
                .or_else(|| elab.param_decl_types.get(&name))?;
            let shape = elab.unpacked_decl_dims.get(&name);
            if elab.dynamic_arrays.contains(&name)
                || elab.associative_arrays.contains_key(&name)
                || elab.coll_shapes.contains_key(&name)
                || (shape.is_none() && is_unpacked_array_name(elab, &name))
            {
                return None;
            }
            (ty, shape.map_or(no_dims, Vec::as_slice))
        }
        _ => return None,
    };
    if dims.is_empty() != rhs_dims.is_empty()
        || (!dims.is_empty() && declared_unpacked_dims(dims, params)?.as_slice() != rhs_dims)
    {
        return None;
    }
    let signature = |dt, has_array_shape| {
        let mut resolved = dt;
        let signature = pattern_type_signature_with(dt, params, |name, type_args| {
            if name.bound.has_late_type_declaration()
                || !type_args.is_empty()
                || name.scopes.iter().any(|s| !s.type_args.is_empty())
            {
                return None;
            }
            let key = match crate::pkg_scope::external_type_key(name.bound) {
                Some(key) => key,
                None if name.has_scope()
                    || name.bound.as_decl().is_some()
                    || name.name.name.contains(['.', ':']) =>
                {
                    name.qualified()
                }
                None => return None,
            };
            resolved = continuous_default_typedef(elab, unit, &key, has_array_shape)?;
            Some(resolved)
        })?;
        // A source offset alone cannot identify a declaration across files.
        let nominal = matches!(resolved, DataType::Struct(_) | DataType::Enum(_))
            .then(|| std::ptr::from_ref(resolved));
        Some((signature, nominal))
    };
    (signature(dt, false)? == signature(rhs_type, !rhs_dims.is_empty())?).then_some(())
}

fn continuous_default_typedef<'a>(
    elab: &'a ElaboratedModule,
    unit: Option<&'a HashMap<String, DataType>>,
    key: &str,
    has_array_shape: bool,
) -> Option<&'a DataType> {
    let unit_name = crate::sv_parser::strip_unit_scope_name(key);
    if !has_array_shape
        && elab
            .typedef_unpacked_dims
            .get(unit_name.unwrap_or(key))
            .is_some_and(|d| !d.is_empty())
    {
        return None;
    }
    match unit_name {
        Some(name) => unit?.get(name),
        None => elab.typedef_types.get(key),
    }
}

/// §10.9.2: the item of each member of `flat` (name, type, unpacked
/// dimensions, in declaration order) in the structure pattern `items`: by
/// position, where a replication sets exactly the members; by member name;
/// by the last type key the member's type matches; else by `default:`
/// (`PatternKeys::value_for`). None when an item cannot be placed here, a
/// member is named twice, or a member is left uncovered.
fn bind_struct_pattern(
    items: &[AssignmentPatternItem],
    flat: &[(String, DataType, Vec<UnpackedDimension>)],
    typedef_types: &HashMap<String, DataType>,
    params: &HashMap<String, Value>,
    scope: &str,
    default_types: Option<&ElaboratedModule>,
    span: Span,
) -> Option<Vec<(Expression, Vec<(DataType, Expression)>)>> {
    if let Some(ordered) = ordered_pattern_items(items, params) {
        return (ordered.len() == flat.len())
            .then(|| ordered.into_iter().map(|e| (e, Vec::new())).collect());
    }
    let mut by_name: HashMap<&str, &Expression> = HashMap::default();
    let mut keys = PatternKeys::default();
    for item in items {
        match item {
            AssignmentPatternItem::Named(k, v) if flat.iter().any(|(m, _, _)| *m == k.name) => {
                if by_name.insert(k.name.as_str(), v).is_some() {
                    return None;
                }
            }
            _ if keys.add(item, typedef_types, params, scope) => {}
            _ => return None,
        }
    }
    flat.iter()
        .map(|(m, mdt, mdims)| match by_name.get(m.as_str()) {
            Some(v) => Some(((*v).clone(), Vec::new())),
            None => keys.value_for(
                mdt,
                !mdims.is_empty(),
                &[],
                typedef_types,
                params,
                span,
                |d| {
                    default_types.is_some_and(|elab| {
                        continuous_default_matches(elab, scope, d, mdt, mdims).is_some()
                    })
                },
            ),
        })
        .collect()
}

/// The items of an ordered pattern, with a replication (`'{2{a, b}}`)
/// spelled out; None when any item is keyed.
pub(super) fn ordered_pattern_items(
    items: &[AssignmentPatternItem],
    params: &HashMap<String, Value>,
) -> Option<Vec<Expression>> {
    if !items
        .iter()
        .all(|it| matches!(it, AssignmentPatternItem::Ordered(_)))
    {
        return None;
    }
    if let [AssignmentPatternItem::Ordered(only)] = items
        && let ExprKind::Replication { count, exprs } = &only.kind
    {
        let c = const_eval_i64_with_params(count, Some(params))?;
        return Some((0..c.max(0)).flat_map(|_| exprs.iter().cloned()).collect());
    }
    Some(items.iter().map(|it| it.expr().clone()).collect())
}
