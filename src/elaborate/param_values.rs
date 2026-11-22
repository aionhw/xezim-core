use super::*;

pub(super) fn is_string_data_type(dt: &DataType) -> bool {
    matches!(
        dt,
        DataType::Simple {
            kind: SimpleType::String,
            ..
        }
    )
}

/// §6.16: a `string` parameter holds its text at the text's own length. A
/// string has no declared width, and fitting the value to the 1024-bit
/// placeholder made `%s` print it behind 125 leading spaces.
pub(super) fn string_param_value(init: &Expression, params: &HashMap<String, Value>) -> Value {
    Value::from_string(&eval_const_expr_val(init, params).to_sv_string())
}

/// Detect whether struct/union type `target` (body `dt`) transitively contains
/// a by-value member of its own type — illegal per IEEE 1800-2017 §7.2.1 (it
/// would have infinite size). Returns the offending member path, or None.
/// Catches direct (`node_t next;`) and mutual (A→B→A) recursion; a `visited`
/// set bounds the walk. Class-handle "linked list" members are NOT flagged
/// (classes live outside `typedef_types`, so they never resolve to a struct).
/// §26.3: register a package parameter under its QUALIFIED name as well as its
/// bare one. Registered only bare, two packages declaring the SAME parameter
/// name collided — whichever elaborated last won, and `p1::step` then read
/// p2's value (ivtest sv_package2). Typedefs already registered both
/// spellings; parameters did not.
pub(super) fn alias_pkg_param(elab: &mut ElaboratedModule, pkg: &str, name: &str, v: &Value) {
    if !pkg.is_empty() {
        elab.set_param(line!(), format!("{}::{}", pkg, name), v.clone());
    }
}

/// IEEE 1800-2017 §7.4.5: a package parameter of a packed multi-dimensional
/// type (`parameter logic [15:0][3:0] P`) gets the element registration a
/// module parameter gets, so `P[i]` and `pkg::P[i]` select an element instead
/// of one bit of the flat vector.
pub(super) fn register_pkg_param_elem(
    elab: &mut ElaboratedModule,
    pkg: &str,
    name: &str,
    data_type: &DataType,
) {
    // The bytecode compiler spells a scoped reference `pkg.name`.
    let mut keys = vec![name.to_string()];
    if !pkg.is_empty() {
        keys.push(format!("{pkg}.{name}"));
    }
    let outer = packed_outer_elem(data_type, &elab.parameters, &elab.typedef_types);
    let msb0 = outer.is_some_and(|(_, msb0, _)| msb0);
    for key in keys {
        register_packed_param_index(elab, &key, data_type, None);
        if let Some(&ew) = elab.packed_signal_elem_widths.get(&key) {
            tls_register_elem_w(&key, ew);
            tls_register_elem_low(&key, outer.map_or(0, |(_, _, low)| low));
            tls_register_elem_inner(&key, data_type, &elab.parameters, &elab.typedef_types);
            // §7.4.5: the left bound of an ascending packed range is the
            // most significant element, in constant expressions as at runtime.
            PACKED_ELEM_MSB0_TLS.with(|c| {
                let mut set = c.borrow_mut();
                if msb0 {
                    set.insert(key.clone());
                } else {
                    set.remove(&key);
                }
            });
        }
    }
}

/// §26.2.2 / §26.3: an imported array retains its element environment and
/// shape under both the visible declaration name and the qualified name.
pub(super) fn register_visible_array_param(
    elab: &mut ElaboratedModule,
    pkg: &str,
    assign: &ParamAssignment,
    data_type: &DataType,
) -> bool {
    if assign.dimensions.is_empty() {
        return false;
    }
    // The initializer and bounds belong to the exporting package, even
    // when only this array is imported into a scope with scalar homonyms.
    let prefix = format!("{pkg}::");
    let own: HashMap<String, Value> = elab
        .parameters
        .iter()
        .filter_map(|(key, value)| {
            key.strip_prefix(&prefix)
                .map(|key| (key.to_string(), value.clone()))
        })
        .collect();
    let (r1, r2) = {
        let env = ParamEnv::Overlay {
            base: &elab.parameters,
            top: &own,
        };
        let Some(r1) = array_params::compute(
            &*elab,
            "",
            &assign.name.name,
            &assign.dimensions,
            assign.init.as_ref(),
            None,
            data_type,
            &env,
            &env,
        ) else {
            return false;
        };
        let r2 = array_params::compute(
            &*elab,
            "",
            &format!("{pkg}::{}", assign.name.name),
            &assign.dimensions,
            assign.init.as_ref(),
            None,
            data_type,
            &env,
            &env,
        );
        (r1, r2)
    };
    r1.apply(elab, "");
    if let Some(r2) = r2 {
        r2.apply(elab, "");
    }
    true
}

pub(super) fn struct_typedef_self_reference(
    target: &str,
    dt: &DataType,
    typedef_types: &HashMap<String, DataType>,
) -> Option<String> {
    fn walk(
        target: &str,
        dt: &DataType,
        typedef_types: &HashMap<String, DataType>,
        visited: &mut Vec<String>,
    ) -> Option<String> {
        // §6.18/§6.19: an ENUM whose BASE type resolves back to the name
        // being defined (`typedef T; typedef enum T {A,B} T;`) is the same
        // circular definition — undetected, every later resolver recursed
        // until the stack overflowed (ivtest sv_typedef_fwd_enum_fail
        // aborted with SIGABRT instead of erroring).
        if let DataType::Enum(e) = dt {
            if let Some(base) = e.base_type.as_deref() {
                if let Some(cycle) = walk(target, base, typedef_types, visited) {
                    return Some(cycle);
                }
            }
            return None;
        }
        let su = match dt {
            DataType::Struct(su) => su,
            // §6.18: the definition can reach the struct THROUGH a typedef
            // alias — `typedef T3 T1;` where `T3` is `T2 [1:0]` and `T2` is a
            // packed struct containing `T1`. Resolving only at MEMBER level
            // missed that, so the cycle went undetected, the typedef was
            // registered, and every later type walker
            // (`flatten_struct_fields`,
            // `is_type_signed_resolved`) recursed on it until the stack
            // overflowed and the process aborted (ivtest sv_typedef_circular2).
            DataType::TypeReference { name, .. } => {
                let mn = &name.name.name;
                // §26.3: a SCOPED reference (`P2::T`) names the PACKAGE's type,
                // not a same-named local one, so `typedef P2::T T;` is a legal
                // alias — comparing leaf names alone reported it as a cycle
                // and rejected a valid design (ivtest sv_typedef_chained).
                // Only an UNQUALIFIED reference can close a cycle on `target`,
                // and a scoped one is followed only via its qualified key:
                // falling back to the bare name would resolve `P2::T` to the
                // local `T` and re-create the same false positive.
                if name.scopes.is_empty() && mn == target {
                    return Some(String::new());
                }
                let key = if name.scopes.is_empty() {
                    mn.clone()
                } else {
                    name.qualified()
                };
                if visited.iter().any(|v| v == &key) {
                    return None;
                }
                let inner = typedef_types.get(&key)?;
                visited.push(key);
                let found = walk(target, inner, typedef_types, visited);
                visited.pop();
                return found;
            }
            _ => return None,
        };
        for member in &su.members {
            let field = member
                .declarators
                .first()
                .map(|d| d.name.name.clone())
                .unwrap_or_default();
            if let DataType::TypeReference { name, .. } = &member.data_type {
                let mn = &name.name.name;
                // Same §26.3 rule as the alias arm above.
                if name.scopes.is_empty() && mn == target {
                    return Some(field);
                }
                let mn = &if name.scopes.is_empty() {
                    mn.clone()
                } else {
                    name.qualified()
                };
                if !visited.iter().any(|v| v == mn) {
                    if let Some(inner) = typedef_types.get(mn) {
                        visited.push(mn.clone());
                        if let Some(p) = walk(target, inner, typedef_types, visited) {
                            return Some(format!("{}.{}", field, p));
                        }
                        visited.pop();
                    }
                }
            } else if let DataType::Struct(_) = &member.data_type {
                if let Some(p) = walk(target, &member.data_type, typedef_types, visited) {
                    return Some(format!("{}.{}", field, p));
                }
            }
        }
        None
    }
    let mut visited = vec![target.to_string()];
    walk(target, dt, typedef_types, &mut visited)
}

/// Flatten a (possibly nested) packed struct/union `DataType` into
/// `(field_path, lsb_offset, width)` tuples for `packed_struct_fields`.
/// First-declared member is the MSB (IEEE 1800-2017 §7.2.1), so offsets are
/// Packed dimensions of `dt`, outermost first, and the width of one leaf
/// element. A `logic` vector's leaf is 1 bit (the ranges ARE the bits). An
/// enum's leaf is the enum base width (`unit_type_t` is 2 bits), and every
/// `typedef T [L:R]` along the chain contributes its range outside that.
pub(super) fn packed_pattern_shape(
    dt: &DataType,
    params: &dyn ParamLookup,
    typedef_types: &HashMap<String, DataType>,
) -> Option<(Vec<PackedDimension>, u32)> {
    let mut dims = Vec::new();
    let mut cur = dt.clone();
    for _ in 0..64 {
        match cur {
            DataType::TypeReference { name, dimensions, .. } => {
                dims.extend(dimensions);
                cur = lookup_scoped_type(&name, typedef_types)?.clone();
            }
            DataType::IntegerVector { dimensions, .. }
            | DataType::Implicit { dimensions, .. } => {
                dims.extend(dimensions);
                return Some((dims, 1));
            }
            DataType::Enum(e) => {
                dims.extend(e.dimensions);
                let w = e
                    .base_type
                    .as_ref()
                    .map(|bt| resolve_type_width_env(bt, Some(&params), None))
                    .unwrap_or(32);
                return Some((dims, w.max(1)));
            }
            _ => return None,
        }
    }
    None
}

/// The outermost packed dimension of `dt` (left and right bound) and the
/// type of one element below it, through typedefs. None when `dt` has no
/// packed dimension with constant bounds.
fn peel_packed_dim_const(
    dt: &DataType,
    params: &dyn ParamLookup,
    typedef_types: &HashMap<String, DataType>,
) -> Option<(i64, i64, DataType)> {
    let bounds = |d: &PackedDimension| -> Option<(i64, i64)> {
        let PackedDimension::Range { left, right, .. } = d else {
            return None;
        };
        Some((
            const_eval_i64_with_params_env(left, Some(&params))?,
            const_eval_i64_with_params_env(right, Some(&params))?,
        ))
    };
    let mut cur = dt.clone();
    for _ in 0..64 {
        match cur {
            DataType::TypeReference {
                name,
                mut dimensions,
                type_args,
                span,
            } => {
                if !dimensions.is_empty() {
                    let first = dimensions.remove(0);
                    let (l, r) = bounds(&first)?;
                    let elem = DataType::TypeReference {
                        name,
                        dimensions,
                        type_args,
                        span,
                    };
                    return Some((l, r, elem));
                }
                cur = lookup_scoped_type(&name, typedef_types)?.clone();
            }
            DataType::Struct(mut su) if su.packed => {
                if su.dimensions.is_empty() {
                    return None;
                }
                let first = su.dimensions.remove(0);
                let (l, r) = bounds(&first)?;
                return Some((l, r, DataType::Struct(su)));
            }
            DataType::IntegerVector {
                kind,
                mut dimensions,
                span,
                ..
            } => {
                if dimensions.is_empty() {
                    return None;
                }
                let first = dimensions.remove(0);
                let (l, r) = bounds(&first)?;
                return Some((
                    l,
                    r,
                    DataType::IntegerVector {
                        kind,
                        signing: None,
                        dimensions,
                        span,
                    },
                ));
            }
            DataType::Implicit {
                signing,
                dimensions,
                span,
            } => {
                cur = DataType::IntegerVector {
                    kind: IntegerVectorType::Logic,
                    signing,
                    dimensions,
                    span,
                };
            }
            DataType::Enum(mut e) => {
                if e.dimensions.is_empty() {
                    return None;
                }
                let first = e.dimensions.remove(0);
                let (l, r) = bounds(&first)?;
                return Some((l, r, DataType::Enum(e)));
            }
            _ => return None,
        }
    }
    None
}

/// The number of elements `dims` span, when every bound is constant.
fn packed_dims_product_const(dims: &[PackedDimension], params: &dyn ParamLookup) -> Option<u32> {
    let mut total: u32 = 1;
    for d in dims {
        let PackedDimension::Range { left, right, .. } = d else {
            return None;
        };
        let l = const_eval_i64_with_params_env(left, Some(&params))?;
        let r = const_eval_i64_with_params_env(right, Some(&params))?;
        total = total.checked_mul(((l - r).unsigned_abs() + 1) as u32)?;
    }
    Some(total)
}

/// The packed width of `dt` with constant bounds; 0 when it cannot be sized.
fn packed_type_width_const(
    dt: &DataType,
    params: &dyn ParamLookup,
    typedefs: Option<&HashMap<String, u32>>,
    typedef_types: &HashMap<String, DataType>,
) -> u32 {
    if let Some(td) = typedefs {
        let w = resolve_type_width_env(dt, Some(&params), Some(td));
        if w > 0 {
            return w;
        }
    }
    let mut cur = dt;
    let mut mul: u32 = 1;
    for _ in 0..64 {
        match cur {
            DataType::TypeReference {
                name, dimensions, ..
            } => {
                let Some(dm) = packed_dims_product_const(dimensions, params) else {
                    return 0;
                };
                mul = mul.saturating_mul(dm);
                let Some(next) = lookup_scoped_type(name, typedef_types) else {
                    return 0;
                };
                cur = next;
            }
            DataType::IntegerVector { dimensions, .. } | DataType::Implicit { dimensions, .. } => {
                let dm = packed_dims_product_const(dimensions, params).unwrap_or(1);
                return mul.saturating_mul(dm).max(1);
            }
            DataType::IntegerAtom { kind, .. } => {
                let w = match kind {
                    IntegerAtomType::Byte => 8,
                    IntegerAtomType::ShortInt => 16,
                    IntegerAtomType::Int | IntegerAtomType::Integer => 32,
                    IntegerAtomType::LongInt | IntegerAtomType::Time => 64,
                };
                return mul.saturating_mul(w);
            }
            DataType::Enum(e) => {
                let dm = packed_dims_product_const(&e.dimensions, params).unwrap_or(1);
                let bw = e
                    .base_type
                    .as_deref()
                    .map(|b| packed_type_width_const(b, params, typedefs, typedef_types))
                    .unwrap_or(32);
                return mul.saturating_mul(dm).saturating_mul(bw);
            }
            DataType::Struct(su) => {
                let dm = packed_dims_product_const(&su.dimensions, params).unwrap_or(1);
                let union = su.kind == StructUnionKind::Union;
                let mut total: u32 = 0;
                for m in &su.members {
                    let mw = packed_type_width_const(&m.data_type, params, typedefs, typedef_types);
                    for _ in &m.declarators {
                        total = if union {
                            total.max(mw)
                        } else {
                            total.saturating_add(mw)
                        };
                    }
                }
                return mul.saturating_mul(dm).saturating_mul(total);
            }
            _ => return resolve_type_width_env(cur, Some(&params), typedefs).saturating_mul(mul),
        }
    }
    0
}

/// Pack an assignment-pattern literal for a PACKED ARRAY OF STRUCTS parameter
/// (`T [N-1:0] p = '{ '{...}, '{...}, ... }`, e.g. black-parrot's
/// `bp_proc_param_s [max_cfgs-1:0] all_cfgs_gp`) into one packed Value. Each
/// pattern element is packed as the element struct type and the elements are
/// concatenated MSB-first (first pattern item = highest index, IEEE 1800-2017
/// §10.9.2 / §7.4.2). Returns None unless `dt` is a packed array of a struct
/// typedef and `expr` is an assignment pattern, so callers fall back cleanly.
pub(super) fn pack_packed_array_const_value(
    dt: &DataType,
    expr: &Expression,
    params: &dyn ParamLookup,
    typedefs: &HashMap<String, u32>,
    typedef_types: &HashMap<String, DataType>,
) -> Option<Value> {
    if let ExprKind::TypedPattern { ty, pattern } = &expr.kind {
        return pack_typed_pattern(ty, pattern, params, typedefs, typedef_types);
    }
    let (_, _, elem_dt) = peel_packed_dim_const(dt, params, typedef_types)?;
    if !matches!(
        resolve_typedef_chain(&elem_dt, typedef_types),
        DataType::Struct(_)
    ) {
        return None;
    }
    pack_packed_dt_pattern(dt, expr, params, Some(typedefs), typedef_types, &[])
}

/// §10.9 / §6.20.2: pack an assignment-pattern value against a MULTI-DIM
/// packed VECTOR type (`parameter bit [1:0][7:0] M = '{8'hAA, 8'hBB}`).
///
/// The generic const-eval cannot pack a pattern — it has no type to take
/// element widths from — so such a parameter silently evaluated to 0, both as
/// a declared default and as an instance `#(.M('{...}))` override, in module,
/// package and interface scope alike.
///
/// The pattern's first element corresponds to the leftmost index of the outer
/// dimension, which is the MS end of packed storage for descending and
/// ascending ranges alike, so filled slots concatenate in slot order. Returns
/// `None` — callers fall back to the previous behavior — for anything not a
/// packed type with a dimension or any pattern shape not understood.
pub(crate) fn pack_packed_vector_pattern(
    dt: &DataType,
    expr: &Expression,
    params: &HashMap<String, Value>,
    typedef_types: &HashMap<String, DataType>,
) -> Option<Value> {
    pack_packed_vector_pattern_env(dt, expr, params, typedef_types)
}

pub(crate) fn pack_packed_vector_pattern_env(
    dt: &DataType,
    expr: &Expression,
    params: &dyn ParamLookup,
    typedef_types: &HashMap<String, DataType>,
) -> Option<Value> {
    if let ExprKind::TypedPattern { ty, pattern } = &expr.kind {
        return pack_packed_vector_pattern_env(ty, pattern, params, typedef_types);
    }
    pack_packed_dt_pattern(dt, expr, params, None, typedef_types, &[])
}

/// §10.9: the constant value of the typed pattern `ty'{...}`, packed against
/// `ty` (a packed array of structs, a struct, or a packed vector).
pub(super) fn pack_typed_pattern(
    ty: &DataType,
    pattern: &Expression,
    params: &dyn ParamLookup,
    typedefs: &HashMap<String, u32>,
    typedef_types: &HashMap<String, DataType>,
) -> Option<Value> {
    pack_packed_array_const_value(ty, pattern, params, typedefs, typedef_types)
        .or_else(|| pack_struct_const_value(ty, pattern, params, typedefs, typedef_types))
        .or_else(|| pack_packed_vector_pattern_env(ty, pattern, params, typedef_types))
}

/// §10.9.1: the constant value of the pattern `expr` for the packed type
/// `dt`, one outermost dimension at a time: index and positional items first,
/// then the last type key that matches the element type (`outer_types` are
/// the keys of enclosing levels), then `default:`.
pub(super) fn pack_packed_dt_pattern(
    dt: &DataType,
    expr: &Expression,
    params: &dyn ParamLookup,
    typedefs: Option<&HashMap<String, u32>>,
    typedef_types: &HashMap<String, DataType>,
    outer_types: &[(DataType, Expression)],
) -> Option<Value> {
    use crate::ast::expr::AssignmentPatternItem;
    let ExprKind::AssignmentPattern(items) = &expr.kind else {
        return None;
    };
    let (l, r, elem_dt) = peel_packed_dim_const(dt, params, typedef_types)?;
    let n = ((l - r).unsigned_abs() + 1) as usize;
    let elem_w = packed_type_width_const(&elem_dt, params, typedefs, typedef_types).max(1);
    let empty_td = HashMap::default();
    let td_ref = typedefs.unwrap_or(&empty_td);
    let eval_elem = |e: &Expression, context: bool, elem_outer: &[(DataType, Expression)]| -> Option<Value> {
        if let Some(v) = pack_struct_const_value_with_outer(
            &elem_dt,
            e,
            params,
            td_ref,
            typedef_types,
            elem_outer,
        ) {
            return Some(v.resize(elem_w));
        }
        if matches!(
            e.kind,
            ExprKind::AssignmentPattern(_) | ExprKind::TypedPattern { .. }
        ) && let Some(v) = pack_packed_dt_pattern(
            &elem_dt,
            e,
            params,
            typedefs,
            typedef_types,
            elem_outer,
        ) {
            return Some(v.resize(elem_w));
        }
        if !elem_outer.is_empty()
            && !matches!(
                e.kind,
                ExprKind::AssignmentPattern(_) | ExprKind::TypedPattern { .. }
            )
            && pattern_slot_is_aggregate(&elem_dt, typedef_types) == Some(true)
        {
            let syn = Expression::new(
                ExprKind::AssignmentPattern(vec![AssignmentPatternItem::Default(e.clone())]),
                e.span,
            );
            if let Some(v) = pack_packed_dt_pattern(
                &elem_dt,
                &syn,
                params,
                typedefs,
                typedef_types,
                elem_outer,
            ) {
                return Some(v.resize(elem_w));
            }
        }
        let raw = eval_const_expr_val_env(e, &params);
        if raw.is_real {
            let r = raw.to_f64().round() as i64;
            let m = if elem_w >= 64 {
                u64::MAX
            } else {
                (1u64 << elem_w) - 1
            };
            return Some(Value::from_u64(r as u64 & m, elem_w));
        }
        Some(if context {
            eval_init_for_width(e, params, elem_w)
        } else {
            raw.resize_for_assign(elem_w)
        })
    };
    // Slot 0 = leftmost index = MS position.
    let slot_of = |idx: i64| -> Option<usize> {
        if idx < l.min(r) || idx > l.max(r) {
            return None;
        }
        Some(if l >= r {
            (l - idx) as usize
        } else {
            (idx - l) as usize
        })
    };
    let mut slots: Vec<Option<Value>> = vec![None; n];
    let mut local_types: Vec<(DataType, Expression)> = Vec::new();
    let mut default_expr: Option<&Expression> = None;
    let mut next_ordered = 0usize;
    for it in items {
        if let Some((kt, v)) = pattern_item_type_key(it, typedef_types, params, "", &|_| false) {
            local_types.push((kt, v.clone()));
            continue;
        }
        match it {
            AssignmentPatternItem::Ordered(v) => {
                if let ExprKind::Replication { count, exprs } = &v.kind {
                    let reps = const_eval_i64_with_params_env(count, Some(&params))?;
                    if reps < 0 {
                        return None;
                    }
                    for _ in 0..reps {
                        for e in exprs {
                            if next_ordered >= n {
                                return None;
                            }
                            slots[next_ordered] = Some(eval_elem(e, true, outer_types)?);
                            next_ordered += 1;
                        }
                    }
                    continue;
                }
                if next_ordered >= n {
                    return None;
                }
                slots[next_ordered] = Some(eval_elem(v, true, outer_types)?);
                next_ordered += 1;
            }
            AssignmentPatternItem::Keyed(k, v) => {
                let idx = const_eval_pattern_index_env(k, Some(&params), (l, r))?;
                *slots.get_mut(slot_of(idx)?)? = Some(eval_elem(v, true, outer_types)?);
            }
            AssignmentPatternItem::Named(id, v) => {
                let idx =
                    const_eval_i64_with_params_env(&make_ident_expr(&id.name), Some(&params))?;
                *slots.get_mut(slot_of(idx)?)? = Some(eval_elem(v, true, outer_types)?);
            }
            AssignmentPatternItem::Default(v) => {
                default_expr = Some(v);
            }
            AssignmentPatternItem::Typed(..) => return None,
        }
    }
    let mut combined = local_types;
    combined.extend(outer_types.iter().cloned());
    let elem_sig = pattern_type_signature(&elem_dt, typedef_types, params);
    let matched_type = elem_sig.and_then(|es| {
        combined.iter().rev().find_map(|(kt, ve)| {
            (pattern_type_signature(kt, typedef_types, params).as_ref() == Some(&es)).then_some(ve)
        })
    });
    let mut parts: Vec<Value> = Vec::with_capacity(n);
    let mut default_val: Option<Value> = None;
    for s in slots {
        match s {
            Some(v) => parts.push(v.resize(elem_w)),
            None => {
                if default_val.is_none() {
                    default_val = if let Some(te) = matched_type {
                        Some(eval_elem(te, true, &[])?)
                    } else if let Some(d) = default_expr {
                        Some(eval_elem(d, false, &combined)?)
                    } else if !combined.is_empty()
                        && pattern_slot_is_aggregate(&elem_dt, typedef_types) == Some(true)
                    {
                        let empty = Expression::new(
                            ExprKind::AssignmentPattern(Vec::new()),
                            expr.span,
                        );
                        Some(eval_elem(&empty, false, &combined)?)
                    } else {
                        return None;
                    };
                }
                parts.push(default_val.clone()?.resize(elem_w));
            }
        }
    }
    Some(Value::concat(&parts))
}

pub(super) fn eval_param_value(
    dt: &DataType,
    init: &Expression,
    params: &HashMap<String, Value>,
    typedefs: &HashMap<String, u32>,
    typedef_types: &HashMap<String, DataType>,
    width: u32,
) -> Value {
    if let Some(v) = pack_packed_array_const_value(dt, init, params, typedefs, typedef_types) {
        return v.resize(width);
    }
    if let Some(v) = pack_struct_const_value(dt, init, params, typedefs, typedef_types) {
        return v.resize(width);
    }
    if let Some(v) = pack_packed_vector_pattern(dt, init, params, typedef_types) {
        return v.resize(width);
    }
    eval_param_init(dt, init, params, typedef_types, width)
}

/// §6.20.2 / §10.7: a parameter with an explicit type or range is ASSIGNED its
/// value, so the declared width is the initializer's context — `localparam
/// int P = A + B` over 8-bit A and B is 300, not the 8-bit wrap 44. An untyped
/// parameter keeps its value's self-determined width, and a real target takes
/// no integral context.
pub(super) fn eval_param_init(
    dt: &DataType,
    init: &Expression,
    params: &HashMap<String, Value>,
    typedef_types: &HashMap<String, DataType>,
    width: u32,
) -> Value {
    if is_string_data_type(dt) {
        return string_param_value(init, params);
    }
    // §6.12.2: an integral value converts to a real parameter whole; fitting
    // it to 64 bits first dropped the high bits of a wider value.
    if is_type_real_resolved(dt, typedef_types) {
        let v = eval_const_expr_val(init, params);
        return if v.is_real {
            v
        } else {
            Value::from_f64(v.to_f64())
        };
    }
    let typed = !matches!(dt, DataType::Implicit { dimensions, .. } if dimensions.is_empty());
    let mut v = if typed
        && !matches!(
            init.kind,
            ExprKind::Number(NumberLiteral::UnbasedUnsized(_))
        ) {
        eval_const_expr_val_ctx(init, params, width).resize_for_assign(width)
    } else {
        eval_const_expr_val(init, params).resize_for_assign(width)
    };
    let resolved_type = typed
        && !matches!(
            resolve_typedef_chain(dt, typedef_types),
            DataType::TypeReference { .. }
        );
    // §6.12.1: a real value of an integral parameter rounds to an integer;
    // `resize_for_assign` keeps a real for a 64-bit width (`parameter time
    // P = 9200s;` in a package held the double).
    if resolved_type && v.is_real {
        v = real_to_integral(v.to_f64(), width);
    }
    // §6.20.2, §6.11.2: the declared type, not the initializer, gives a typed
    // parameter its signedness, and a 2-state type holds x/z as 0. A type
    // name this scope cannot resolve keeps the value's own representation.
    if resolved_type && !v.is_real {
        v.is_signed = is_type_signed_resolved(dt, typedef_types);
        if is_type_two_state_resolved(dt, typedef_types) {
            v = v.to_two_state();
        }
    }
    v
}

#[derive(Clone, Copy)]
pub(super) enum UnresolvedCallPolicy<'a> {
    ContinueOriginal,
    SkipIfUnresolved,
    DeferZero { name: &'a str },
}

/// Shared scalar parameter/localparam resolution pipeline used by package,
/// module header, pre-seed, module body, and generate-scope elaboration.
pub(super) fn resolve_param_decl_value(
    elab: &mut ElaboratedModule,
    data_type: &DataType,
    init: Option<&Expression>,
    raw_init_for_defer: Option<&Expression>,
    override_val: Option<&Value>,
    base_width: u32,
    base_signed: bool,
    base_is_real: bool,
    policy: ParamDeclPolicy<'_>,
) -> ParamResolution {
    let is_implicit =
        matches!(data_type, DataType::Implicit { dimensions, .. } if dimensions.is_empty());
    let mut width = if is_implicit { 32 } else { base_width };
    let mut signed = base_signed;
    let mut is_real = base_is_real;

    // Substitute constant-function calls once so implicit real/width/signed
    // checks and final value evaluation reuse the same reduced expression.
    let subbed_holder: Option<Expression>;
    let init_eval: Option<&Expression> = if override_val.is_none() {
        if let Some(e) = init {
            if expr_has_call(e) {
                match substitute_const_fn_calls(e, Some(&elab.parameters), elab, 0)
                    .filter(|sub| !expr_has_call(sub))
                {
                    Some(sub) => {
                        subbed_holder = Some(sub);
                        subbed_holder.as_ref()
                    }
                    None => match policy.unresolved_call {
                        UnresolvedCallPolicy::SkipIfUnresolved => {
                            return ParamResolution {
                                val: Value::zero(width),
                                width,
                                is_real,
                                signed,
                                skipped: true,
                            };
                        }
                        UnresolvedCallPolicy::DeferZero { name } => {
                            if is_implicit && !matches!(data_type, DataType::Implicit { signing: Some(_), .. }) {
                                width = untyped_param_width(e, &elab.parameters).unwrap_or(width);
                                signed = untyped_param_is_signed(e, &elab.parameters);
                            } else if is_implicit {
                                width = untyped_param_width(e, &elab.parameters).unwrap_or(width);
                            }
                            if let Some(raw) = raw_init_for_defer.or(Some(e)) {
                                elab.deferred_param_exprs
                                    .push((name.to_string(), raw.clone()));
                            }
                            let mut v = Value::zero(width);
                            if !v.is_real {
                                v.is_signed = signed;
                            }
                            return ParamResolution {
                                val: v,
                                width,
                                is_real,
                                signed,
                                skipped: false,
                            };
                        }
                        UnresolvedCallPolicy::ContinueOriginal => Some(e),
                    },
                }
            } else {
                Some(e)
            }
        } else {
            None
        }
    } else {
        None
    };

    if policy.require_known_idents {
        if let Some(e) = init_eval {
            if !expr_idents_all_known(e, &elab.parameters) {
                return ParamResolution {
                    val: Value::zero(width),
                    width,
                    is_real,
                    signed,
                    skipped: true,
                };
            }
        }
    }

    let explicit_signing = matches!(
        data_type,
        DataType::Implicit {
            signing: Some(_),
            dimensions,
            ..
        } if dimensions.is_empty()
    );
    let implicit_sign_expr = if override_val.is_some() && policy.force_signed_on_override {
        init
    } else {
        init_eval
    };
    if is_implicit {
        let init_is_real = if policy.promote_implicit_real {
            if let Some(ov) = override_val {
                ov.is_real
            } else if let Some(e) = init_eval {
                eval_const_expr_val(e, &elab.parameters).is_real
            } else {
                false
            }
        } else {
            false
        };

        if init_is_real {
            width = 64;
            is_real = true;
            if policy.force_signed_on_override {
                signed = false;
            }
        } else if policy.narrow_implicit_string_lit
            && override_val.is_none()
            && let Some(w) = init
                .filter(|e| matches!(e.kind, ExprKind::StringLiteral(_)))
                .and_then(string_literal_width)
        {
            width = w;
        } else {
            if let Some(e) = implicit_sign_expr {
                width = untyped_param_width(e, &elab.parameters).unwrap_or(width);
            }
            if explicit_signing {
                signed = is_type_signed(data_type);
            } else {
                signed = match implicit_sign_expr {
                    Some(e) => untyped_param_is_signed(e, &elab.parameters),
                    None => true,
                };
            }
        }
    } else if policy.signed_from_pkg_helper {
        signed = pkg_param_is_signed(data_type, init_eval, &elab.typedef_types, &elab.parameters);
    }

    let mut val = if let Some(ov) = override_val {
        let mut v = ov.clone();
        if policy.force_signed_on_override && !v.is_real {
            v.is_signed = signed;
        }
        v
    } else if let Some(e) = init_eval {
        let mut v = if policy.eval_packed_aggregate {
            eval_param_value(
                data_type,
                e,
                &elab.parameters,
                &elab.typedefs,
                &elab.typedef_types,
                width,
            )
        } else {
            eval_param_init(data_type, e, &elab.parameters, &elab.typedef_types, width)
        };
        if !v.is_real && (!is_implicit || signed || !is_real) {
            v.is_signed = signed;
        }
        v
    } else {
        let mut v = Value::zero(width);
        if !v.is_real {
            v.is_signed = signed;
        }
        v
    };

    if is_real {
        val = Value::from_f64(val.to_f64());
    } else if val.is_real && width > 0 && !is_implicit && !is_string_data_type(data_type) {
        val = real_to_integral(val.to_f64(), width);
        val.is_signed = signed;
    } else if !val.is_real && is_type_two_state_resolved(data_type, &elab.typedef_types) {
        val = val.to_two_state();
    }
    if is_string_data_type(data_type) && !val.is_real {
        width = val.width;
    }

    ParamResolution {
        val,
        width,
        is_real,
        signed,
        skipped: false,
    }
}

/// Follow a bare type name through `local` — an instance's type-parameter
/// defaults and body typedefs, which the global tables do not hold. `None`
/// for a local name used with extra packed dimensions (`T [1:0] P`), which
/// callers leave alone.
fn bind_local_type<'a>(
    dt: &'a DataType,
    local: &'a HashMap<String, DataType>,
) -> Option<&'a DataType> {
    let mut cur = dt;
    for _ in 0..16 {
        let DataType::TypeReference {
            name, dimensions, ..
        } = cur
        else {
            break;
        };
        if name.has_scope() {
            break;
        }
        match local.get(&name.name.name) {
            Some(next) if dimensions.is_empty() => cur = next,
            Some(_) => return None,
            None => break,
        }
    }
    Some(cur)
}

/// §6.20.2 / §10.7: the integral type a value parameter's declaration gives
/// its value, as `(width, signed, two_state)`. `None` when the value keeps its
/// own type: no type and no range (`parameter P`, `parameter signed P`),
/// `real`, `string`, an unpacked struct, or a type name that does not resolve
/// (a width guessed for it would truncate the value).
pub(super) fn param_integral_target(
    dt: &DataType,
    local: &HashMap<String, DataType>,
    params: &HashMap<String, Value>,
    typedefs: &HashMap<String, u32>,
    typedef_types: &HashMap<String, DataType>,
) -> Option<(u32, bool, bool)> {
    let dt = bind_local_type(dt, local)?;
    let resolved = resolve_typedef_chain(dt, typedef_types);
    let integral = match resolved {
        DataType::IntegerVector { .. } | DataType::IntegerAtom { .. } | DataType::Enum(_) => true,
        DataType::Implicit { dimensions, .. } => !dimensions.is_empty(),
        DataType::Struct(s) => s.packed,
        _ => false,
    };
    if !integral {
        return None;
    }
    let w = resolve_type_width(dt, Some(params), Some(typedefs));
    (w > 0).then(|| {
        (
            w,
            is_type_signed_resolved(dt, typedef_types),
            is_type_two_state_resolved(dt, typedef_types),
        )
    })
}

/// §6.12.2: a real converted to an integral type rounds to the nearest
/// integer, ties away from zero, and then wraps to the target width.
pub(super) fn real_to_integral(f: f64, w: u32) -> Value {
    Value::from_real_wrapped(f, w)
}

/// §6.20.2 / §10.7 / §23.10.2: the value a parameter of integral type
/// `(w, signed, two_state)` holds when assigned `val`. When the source
/// expression is known, it is evaluated with the declared width as its
/// context (`.P(4'hF + 4'h1)` on `[7:0]` is 16, not 0); a real rounds; the
/// result wraps to the declared width, takes the declared signedness, and a
/// 2-state type maps X/Z to 0.
pub(super) fn convert_param_value<P: ParamLookup>(
    val: &Value,
    expr: Option<&Expression>,
    scope: &P,
    (w, signed, two_state): (u32, bool, bool),
) -> Value {
    let ctx;
    let src = match expr {
        Some(e) if !val.is_real => {
            ctx = eval_const_expr_val_with_ctx(
                e,
                scope,
                Some(w),
                &mut const_context::Types::default(),
            );
            &ctx
        }
        _ => val,
    };
    let mut v = if src.is_real {
        real_to_integral(src.to_f64(), w)
    } else {
        src.resize_for_assign(w)
    };
    v.is_signed = signed;
    if two_state {
        v = v.to_two_state();
    }
    v
}
