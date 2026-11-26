//! Typed unpacked parameter elements and their declared shape (§6.20.2 / §7.4).
use super::*;

thread_local! {
    static DEFAULTS: std::cell::RefCell<HashMap<String, Value>> = std::cell::RefCell::new(HashMap::default());
}

pub(crate) struct Scope(HashMap<String, Value>);
impl Drop for Scope {
    fn drop(&mut self) {
        DEFAULTS.with(|values| *values.borrow_mut() = std::mem::take(&mut self.0));
    }
}
pub(crate) fn scope() -> Scope {
    Scope(DEFAULTS.with(|values| std::mem::take(&mut *values.borrow_mut())))
}
pub(super) fn default_value(name: &str) -> Option<Value> {
    DEFAULTS.with(|values| values.borrow().get(name).cloned())
}

fn remember_default(
    name: &str,
    data_type: &DataType,
    params: &dyn ParamLookup,
    elab: &ElaboratedModule,
) {
    let width = resolve_type_width_env(data_type, Some(&params), Some(&elab.typedefs)).max(1);
    let mut value = if is_type_two_state_resolved(data_type, &elab.typedef_types) {
        Value::zero(width)
    } else {
        Value::new(width)
    };
    value.is_signed = is_type_signed_resolved(data_type, &elab.typedef_types);
    DEFAULTS.with(|values| values.borrow_mut().insert(name.to_string(), value));
}

/// Overlay `elab.parameters` beneath `params` (as `top` in `ParamEnv::Overlay`)
/// when `params` alone cannot resolve the unpacked bounds (e.g. package-imported
/// bounds like `import pkg::*; ... A [N]`), without cloning `elab.parameters`.
struct ArrayShapeEnv<'a> {
    base: &'a HashMap<String, Value>,
    top: &'a dyn ParamLookup,
}

impl ParamLookup for ArrayShapeEnv<'_> {
    #[inline]
    fn get(&self, key: &str) -> Option<&Value> {
        self.top.get(key).or_else(|| self.base.get(key))
    }
    #[inline]
    fn contains_key(&self, key: &str) -> bool {
        self.top.contains_key(key) || self.base.contains_key(key)
    }
    fn keys(&self) -> crate::hasher::HashSet<&str> {
        let mut set = self.top.keys();
        set.extend(self.base.keys().map(String::as_str));
        set
    }
    fn rows(&self) -> Vec<(&str, &Value)> {
        let mut out = self.top.rows();
        let seen: crate::hasher::HashSet<&str> = out.iter().map(|(k, _)| *k).collect();
        for (k, v) in self.base {
            if !seen.contains(k.as_str()) {
                out.push((k.as_str(), v));
            }
        }
        out
    }
    #[inline]
    fn as_hashmap_base(&self) -> Option<&HashMap<String, Value>> {
        None
    }
}

fn needs_elab_fallback(
    elab: &ElaboratedModule,
    dims: &[UnpackedDimension],
    params: &dyn ParamLookup,
) -> bool {
    let local = normalize_unpacked_dims_env(dims, params, &elab.typedef_types);
    declared_unpacked_dims_env(&local, params).is_none()
        && !std::ptr::eq(
            params as *const dyn ParamLookup as *const (),
            (&elab.parameters as &dyn ParamLookup) as *const dyn ParamLookup as *const (),
        )
}

/// Share element folding with the instance-local parameter environment, so
/// dependent constants and the eventual signal storage see the same values.
pub(super) fn elements(
    elab: &ElaboratedModule,
    name: &str,
    dims: &[UnpackedDimension],
    init: Option<&Expression>,
    override_val: Option<&Value>,
    data_type: &DataType,
    params: &dyn ParamLookup,
    init_params: &dyn ParamLookup,
) -> Option<Vec<(String, Value)>> {
    elements_with_outer(
        elab,
        name,
        dims,
        init,
        override_val,
        data_type,
        params,
        init_params,
        &[],
    )
}

fn elements_with_outer(
    elab: &ElaboratedModule,
    name: &str,
    dims: &[UnpackedDimension],
    init: Option<&Expression>,
    override_val: Option<&Value>,
    data_type: &DataType,
    params: &dyn ParamLookup,
    init_params: &dyn ParamLookup,
    outer_types: &[(DataType, Expression)],
) -> Option<Vec<(String, Value)>> {
    let overlay;
    let params: &dyn ParamLookup = if needs_elab_fallback(elab, dims, params) {
        overlay = ArrayShapeEnv {
            base: &elab.parameters,
            top: params,
        };
        &overlay
    } else {
        params
    };
    remember_default(name, data_type, params, elab);
    let dims = normalize_unpacked_dims_env(dims, params, &elab.typedef_types);
    let shape = declared_unpacked_dims_env(&dims, params)?;
    let &(left, right) = shape.first()?;
    // Keep the existing parameter-materialization limit before allocating
    // indices, including bounds whose signed difference would overflow.
    if left.abs_diff(right) >= 4096 {
        return None;
    }
    let mut outer: Vec<_> = (left.min(right)..=left.max(right)).collect();
    if left > right {
        outer.reverse();
    }
    if outer.is_empty() {
        return None;
    }
    // §10.9.1: a `default:` that is itself a pattern is a ROW of a nested
    // array — unless the element is a struct, whose literal is a pattern of
    // scalars (`'{default: '{7, 2'd1}}` over `p_t A[2][2]`) and fills every
    // leaf. See `pattern_items`.
    let struct_elem = matches!(
        resolve_typedef_chain(data_type, &elab.typedef_types),
        DataType::Struct(_)
    );
    let items = init.and_then(|e| {
        pattern_items(
            e,
            &outer,
            &dims[1..],
            struct_elem,
            data_type,
            elab,
            init_params,
            outer_types,
        )
    });
    let elem_w = resolve_type_width_env(data_type, Some(&params), Some(&elab.typedefs)).max(1);
    // An initializer that names another unpacked-array parameter (`= pkg::A`)
    // evaluates to that array packed (see `packed`), so slice it like an
    // override.
    let referenced;
    let override_val = match (override_val, &items, init) {
        (None, None, Some(e)) => {
            referenced = eval_const_expr_val_env(e, &init_params);
            Some(&referenced)
        }
        (v, _, _) => v,
    };
    let row_count = dims[1..].iter().try_fold(1usize, |n, d| {
        n.checked_mul(const_dim_indices(std::slice::from_ref(d), params)?.len())
    })?;
    let row_w = row_count.checked_mul(elem_w as usize)?;
    if let Some(v) = override_val {
        if (v.width as usize) < row_w.checked_mul(outer.len())? {
            // A legacy environment may carry only individual array elements.
            if dims.len() == 1
                && let Some(init) = init
                && let Some(copied) =
                    referenced_array_elements(name, &outer, init, init_params, elab)
            {
                return Some(copied);
            }
            return None;
        }
    } else if items.as_ref()?.len() != outer.len() {
        return None;
    }
    let mut out = Vec::new();
    for (position, index) in outer.iter().enumerate() {
        let key = format!("{name}[{index}]");
        let item_pair = items.as_ref().and_then(|v| v.get(position));
        let item = item_pair.map(|(e, _)| e);
        let elem_outer: &[(DataType, Expression)] =
            item_pair.map_or(outer_types, |(_, ot)| ot.as_slice());
        let packed = override_val.map(|v| {
            let low = (outer.len() - 1 - position) * row_w;
            v.range_select(low + row_w - 1, low)
        });
        if dims.len() > 1 {
            out.extend(elements_with_outer(
                elab,
                &key,
                &dims[1..],
                item,
                packed.as_ref(),
                data_type,
                params,
                init_params,
                elem_outer,
            )?);
            continue;
        }
        let mut value = if let Some(v) = packed {
            // §6.20.2: the whole-array transport stores real elements as
            // IEEE 754 bits. Restore their type after slicing, without a
            // numeric integer-to-real conversion.
            if is_type_real_resolved(data_type, &elab.typedef_types) {
                Value::from_f64(f64::from_bits(v.raw_bits().0))
            } else {
                v
            }
        } else {
            let item = item?;
            // §10.9.1: a type key of an enclosing level sets every element
            // of its type that no index key above set, so it also takes
            // precedence over the items of a `default:` row pattern.
            let elem_sig =
                super::pattern_type_signature(data_type, &elab.typedef_types, init_params);
            let item = elem_outer
                .iter()
                .rev()
                .find_map(|(kt, v)| {
                    let ks = super::pattern_type_signature(kt, &elab.typedef_types, init_params)?;
                    (Some(&ks) == elem_sig.as_ref()).then_some(v)
                })
                .unwrap_or(item);
            // §10.9.2: a `default:` value that reaches a structure element
            // together with type keys is the default of that element's own
            // members; the type keys still set the members they match.
            let spread;
            let item = if struct_elem
                && !elem_outer.is_empty()
                && !matches!(
                    super::peel_unpacked_typed_pattern(item).kind,
                    ExprKind::AssignmentPattern(_)
                ) {
                spread = Expression::new(
                    ExprKind::AssignmentPattern(vec![AssignmentPatternItem::Default(item.clone())]),
                    item.span,
                );
                &spread
            } else {
                item
            };
            super::pack_struct_const_value_with_outer(
                data_type,
                item,
                init_params,
                &elab.typedefs,
                &elab.typedef_types,
                elem_outer,
            )
            .or_else(|| {
                super::pack_packed_dt_pattern(
                    data_type,
                    item,
                    init_params,
                    Some(&elab.typedefs),
                    &elab.typedef_types,
                    elem_outer,
                )
            })
            .map(|v| v.resize(elem_w))
            .unwrap_or_else(|| eval_init_for_width(item, init_params, elem_w))
        };
        if !value.is_real {
            value.is_signed = is_type_signed_resolved(data_type, &elab.typedef_types);
            if is_type_two_state_resolved(data_type, &elab.typedef_types) {
                value = value.to_two_state();
            }
        }
        out.push((key, value));
    }
    Some(out)
}

/// Whole-array copy of an unpacked parameter (`localparam t B[N] = pkg::A`,
/// or `#(.B(pkg::A))`). Elements live under `base[index]` (§6.20.2). A
/// pattern is handled by `pattern_items`; this is the name-reference form.
fn referenced_array_elements(
    name: &str,
    outer: &[i64],
    init: &Expression,
    params: &dyn ParamLookup,
    elab: &ElaboratedModule,
) -> Option<Vec<(String, Value)>> {
    let mut keys = Vec::new();
    super::const_index_base_keys(init, Some(&params), &mut keys);
    for key in keys {
        let mut out = Vec::with_capacity(outer.len());
        let mut complete = true;
        for index in outer {
            let elem = params
                .get(&format!("{key}[{index}]"))
                .or_else(|| elab.parameters.get(&format!("{key}[{index}]")))
                .cloned();
            match elem {
                Some(value) => out.push((format!("{name}[{index}]"), value)),
                None => {
                    complete = false;
                    break;
                }
            }
        }
        if complete && !out.is_empty() {
            return Some(out);
        }
    }
    None
}

/// One initializer per index of `outer` (declared order), from pattern `e`.
///
/// §10.9.1: `'{n{a, b}}` replicates pattern elements, `'{k: v}` places `v`
/// at index `k` (not at position `k`), and `default:` fills every index left
/// unset. For a nested array a non-pattern `default:` reaches every leaf, so
/// each missing row becomes `'{default: v}` (`int a [2][3] = '{default: 5}`).
fn subarray_type_matches(
    elem_dt: &DataType,
    rest: &[UnpackedDimension],
    key_dt: &DataType,
    elab: &ElaboratedModule,
    params: &dyn ParamLookup,
) -> bool {
    let DataType::TypeReference {
        name, dimensions, ..
    } = key_dt
    else {
        return false;
    };
    if !dimensions.is_empty() {
        return false;
    }
    let key = if name.scopes.is_empty() {
        name.name.name.clone()
    } else {
        name.qualified()
    };
    let Some(unpacked) = elab.typedef_unpacked_dims.get(&key) else {
        return false;
    };
    let Some(rest_shape) = declared_unpacked_dims_env(rest, params) else {
        return false;
    };
    let norm = normalize_unpacked_dims_env(unpacked, params, &elab.typedef_types);
    let Some(key_shape) = declared_unpacked_dims_env(&norm, params) else {
        return false;
    };
    if rest_shape != key_shape {
        return false;
    }
    let Some(target) = lookup_scoped_type(name, &elab.typedef_types) else {
        return false;
    };
    let Some(ks) = super::pattern_type_signature(target, &elab.typedef_types, params) else {
        return false;
    };
    let Some(es) = super::pattern_type_signature(elem_dt, &elab.typedef_types, params) else {
        return false;
    };
    ks == es
}

fn pattern_items(
    e: &Expression,
    outer: &[i64],
    rest: &[UnpackedDimension],
    struct_elem: bool,
    elem_dt: &DataType,
    elab: &ElaboratedModule,
    params: &dyn ParamLookup,
    outer_types: &[(DataType, Expression)],
) -> Option<Vec<(Expression, Vec<(DataType, Expression)>)>> {
    let nested = !rest.is_empty();
    let items = match &super::peel_unpacked_typed_pattern(e).kind {
        ExprKind::Concatenation(v) => {
            return Some(
                v.iter()
                    .map(|x| (x.clone(), outer_types.to_vec()))
                    .collect(),
            );
        }
        ExprKind::AssignmentPattern(items) => items,
        _ => return None,
    };
    // An empty pattern stands for a row that only the type keys of an
    // enclosing level reach; it has no positional items.
    if !items.is_empty()
        && items
            .iter()
            .all(|it| matches!(it, AssignmentPatternItem::Ordered(_)))
    {
        if let [AssignmentPatternItem::Ordered(only)] = items.as_slice()
            && let ExprKind::Replication { count, exprs } = &only.kind
        {
            let reps = usize::try_from(const_eval_i64_with_params_env(count, Some(&params))?).ok()?;
            if reps.checked_mul(exprs.len())? > outer.len() {
                return None;
            }
            return Some(
                exprs
                    .iter()
                    .cycle()
                    .take(reps * exprs.len())
                    .map(|x| (x.clone(), outer_types.to_vec()))
                    .collect(),
            );
        }
        return Some(
            items
                .iter()
                .map(|it| (it.expr().clone(), outer_types.to_vec()))
                .collect(),
        );
    }
    let mut slots: Vec<Option<&Expression>> = vec![None; outer.len()];
    let mut local_types: Vec<(DataType, Expression)> = Vec::new();
    let mut default = None;
    for it in items {
        if let Some((kt, v)) = super::pattern_item_type_key(
            it,
            &elab.typedef_types,
            params,
            "",
            &|n| params.contains_key(n),
        ) {
            local_types.push((kt, v.clone()));
            continue;
        }
        match it {
            AssignmentPatternItem::Keyed(key, v) => {
                let index = const_eval_pattern_index_env(
                    key,
                    Some(&params),
                    (*outer.first()?, *outer.last()?),
                )?;
                *slots.get_mut(outer.iter().position(|&i| i == index)?)? = Some(v);
            }
            // A bare identifier key (`'{K: v}`) parses as a member name; in
            // an array pattern it is a constant index.
            AssignmentPatternItem::Named(key, v) => {
                let index =
                    const_eval_i64_with_params_env(&make_ident_expr(&key.name), Some(&params))?;
                *slots.get_mut(outer.iter().position(|&i| i == index)?)? = Some(v);
            }
            AssignmentPatternItem::Default(v) => default = Some(v),
            _ => return None,
        }
    }
    let mut combined = local_types;
    combined.extend(outer_types.iter().cloned());
    let matched_type = if nested {
        combined.iter().rev().find_map(|(kt, v)| {
            subarray_type_matches(elem_dt, rest, kt, elab, params).then_some(v)
        })
    } else {
        super::pattern_type_signature(elem_dt, &elab.typedef_types, params).and_then(|esig| {
            combined.iter().rev().find_map(|(kt, v)| {
                (super::pattern_type_signature(kt, &elab.typedef_types, params).as_ref()
                    == Some(&esig))
                .then_some(v)
            })
        })
    };
    let is_agg = nested
        || struct_elem
        || super::pattern_slot_is_aggregate(elem_dt, &elab.typedef_types) == Some(true);
    slots
        .into_iter()
        .map(|slot| match slot {
            Some(v) => Some((v.clone(), outer_types.to_vec())),
            None => {
                if let Some(tv) = matched_type {
                    return Some((tv.clone(), Vec::new()));
                }
                if let Some(d) = default {
                    if nested && !default_is_row(d, struct_elem) {
                        return Some((
                            Expression::new(
                                ExprKind::AssignmentPattern(vec![AssignmentPatternItem::Default(
                                    d.clone(),
                                )]),
                                d.span,
                            ),
                            combined.clone(),
                        ));
                    }
                    return Some((d.clone(), combined.clone()));
                }
                if !combined.is_empty() && is_agg {
                    return Some((
                        Expression::new(ExprKind::AssignmentPattern(Vec::new()), e.span),
                        combined.clone(),
                    ));
                }
                None
            }
        })
        .collect()
}

/// The whole array as one value, the element at the left bound leftmost: the
/// layout an override carries, so a bare reference to the array (`.R(R)`,
/// `= pkg::A`) hands its elements on.
pub(super) fn packed(values: &[(String, Value)]) -> Value {
    Value::concat_refs(values.iter().map(|(_, v)| v))
}

/// Everything `register` computes off a read-only module, so a caller can
/// compute against `&elab.parameters` without holding a `&mut ElaboratedModule`
/// (eliminating the whole-table `parameters.clone()` borrow workarounds).
pub(super) struct RegisteredArray {
    full_name: String,
    shape: Vec<(i64, i64)>,
    width: u32,
    fields: Option<Vec<(String, u32, u32)>>,
    whole: Value,
    values: Vec<(String, Value)>,
    var_decl_type: Option<DataType>,
}

/// Read-only phase of `register`: derive every value / shape / width a
/// registered unpacked-array parameter materializes. The caller may pass
/// `params` (and `init_params`) as `&elab.parameters` directly — the only
/// borrows are immutable.
pub(super) fn compute(
    elab: &ElaboratedModule,
    prefix: &str,
    name: &str,
    dims: &[UnpackedDimension],
    init: Option<&Expression>,
    override_val: Option<&Value>,
    data_type: &DataType,
    params: &dyn ParamLookup,
    init_params: &dyn ParamLookup,
) -> Option<RegisteredArray> {
    let overlay;
    let params: &dyn ParamLookup = if needs_elab_fallback(elab, dims, params) {
        overlay = ArrayShapeEnv {
            base: &elab.parameters,
            top: params,
        };
        &overlay
    } else {
        params
    };
    remember_default(&format!("{prefix}{name}"), data_type, params, elab);
    let values = elements(
        elab,
        name,
        dims,
        init,
        override_val,
        data_type,
        params,
        init_params,
    )?;
    let dims = normalize_unpacked_dims_env(dims, params, &elab.typedef_types);
    let shape = declared_unpacked_dims_env(&dims, params)?;
    let width = resolve_type_width_env(data_type, Some(&params), Some(&elab.typedefs)).max(1);
    let full_name = format!("{prefix}{name}");
    let fields = super::packed_struct_field_layout_env(
        data_type,
        params,
        &elab.typedefs,
        &elab.typedef_types,
    );
    if let Some(fields) = &fields {
        // §7.2.2: `array[i].field.subfield` slices the element Value. The
        // layout has to be on the array name; a scalar struct parameter
        // already records it, an unpacked array of that struct did not.
        super::tls_register_struct_layout(&full_name, fields);
    }
    // §6.20.2: aggregate parameter elements use whole Value storage.
    // An unpacked variable type would route their member reads to separate
    // field signals, which this constant representation does not allocate.
    let var_decl_type = (!matches!(resolve_typedef_chain(data_type, &elab.typedef_types),
        DataType::Struct(s) if !s.packed))
        .then(|| data_type.clone());
    Some(RegisteredArray {
        full_name,
        shape,
        width,
        fields,
        whole: packed(&values),
        values,
        var_decl_type,
    })
}

impl RegisteredArray {
    pub(super) fn bind_local(&self, name: &str, params: &mut HashMap<String, Value>) {
        params.insert(name.to_owned(), self.whole.clone());
        params.extend(self.values.iter().cloned());
        if let Some(fields) = &self.fields {
            super::tls_register_struct_layout(name, fields);
        }
    }

    /// Write-only phase: apply the data computed by `compute` into an
    /// `ElaboratedModule`. Takes the `prefix` separately (not threaded through
    /// the struct) so the same computed value can back several prefixes.
    pub(super) fn apply(self, elab: &mut ElaboratedModule, prefix: &str) {
        let RegisteredArray {
            full_name,
            shape,
            width,
            fields,
            whole,
            values,
            var_decl_type,
        } = self;
        if let Some(fields) = fields {
            elab.packed_struct_fields
                .entry(full_name.clone())
                .or_insert(fields);
        }
        register_shape(elab, &full_name, &shape, width);
        elab.set_param(line!(), full_name.clone(), whole);
        if let Some(dt) = var_decl_type {
            elab.var_decl_types.insert(full_name, dt);
        }
        for (name, value) in values {
            let name = format!("{prefix}{name}");
            elab.set_param(line!(), name.clone(), value.clone());
            signals_insert_traced(
                &mut elab.signals,
                line!(),
                name.clone(),
                Signal {
                    is_const: true,
                    name: name.into(),
                    width,
                    is_signed: value.is_signed,
                    is_real: value.is_real,
                    direction: None,
                    value,
                    type_name: None,
                },
            );
        }
    }
}

pub(super) fn register(
    elab: &mut ElaboratedModule,
    prefix: &str,
    name: &str,
    dims: &[UnpackedDimension],
    init: Option<&Expression>,
    override_val: Option<&Value>,
    data_type: &DataType,
    params: &dyn ParamLookup,
    init_params: &dyn ParamLookup,
) -> bool {
    let Some(registered) = compute(
        &*elab,
        prefix,
        name,
        dims,
        init,
        override_val,
        data_type,
        params,
        init_params,
    ) else {
        return false;
    };
    registered.apply(elab, prefix);
    true
}

fn register_shape(elab: &mut ElaboratedModule, name: &str, shape: &[(i64, i64)], width: u32) {
    let Some(&(left, right)) = shape.first() else {
        return;
    };
    elab.unpacked_decl_dims
        .insert(name.to_string(), shape.to_vec());
    if left > right {
        elab.descending_arrays.insert(name.to_string());
    }
    match shape {
        [first] => {
            elab.arrays.insert(
                name.to_string(),
                (first.0.min(first.1), first.0.max(first.1), width),
            );
        }
        [first, second] => {
            elab.arrays_2d
                .insert(name.to_string(), (*first, *second, width));
        }
        _ => {
            elab.arrays_nd
                .insert(name.to_string(), (shape.to_vec(), width));
        }
    }
    if shape.len() > 1 {
        for index in left.min(right)..=left.max(right) {
            register_shape(elab, &format!("{name}[{index}]"), &shape[1..], width);
        }
    }
}

/// Is a nested array's `default:` value a row literal? A pattern or a
/// concatenation is a row — except for a struct element, where a pattern
/// whose items are scalars is the struct's own literal and reaches every
/// leaf (§10.9.1); a row of struct literals has patterns as items.
fn default_is_row(d: &Expression, struct_elem: bool) -> bool {
    match &super::peel_unpacked_typed_pattern(d).kind {
        ExprKind::Concatenation(_) => true,
        ExprKind::AssignmentPattern(items) => {
            !struct_elem
                || items.iter().any(|it| {
                    matches!(
                        it.expr().kind,
                        ExprKind::AssignmentPattern(_) | ExprKind::Concatenation(_)
                    )
                })
        }
        _ => false,
    }
}
