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
    params: &HashMap<String, Value>,
    elab: &ElaboratedModule,
) {
    let width = resolve_type_width(data_type, Some(params), Some(&elab.typedefs)).max(1);
    let mut value = if is_type_two_state_resolved(data_type, &elab.typedef_types) {
        Value::zero(width)
    } else {
        Value::new(width)
    };
    value.is_signed = is_type_signed_resolved(data_type, &elab.typedef_types);
    DEFAULTS.with(|values| values.borrow_mut().insert(name.to_string(), value));
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
    params: &HashMap<String, Value>,
    init_params: &HashMap<String, Value>,
) -> Option<Vec<(String, Value)>> {
    remember_default(name, data_type, params, elab);
    let dims = normalize_unpacked_dims(dims, params, &elab.typedef_types);
    let shape = declared_unpacked_dims(&dims, params)?;
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
    let items: Option<Vec<&Expression>> = init.and_then(|e| match &e.kind {
        ExprKind::Concatenation(v) => Some(v.iter().collect()),
        ExprKind::AssignmentPattern(v) => Some(v.iter().map(|v| v.expr()).collect()),
        _ => None,
    });
    let elem_w = resolve_type_width(data_type, Some(params), Some(&elab.typedefs)).max(1);
    let row_count = dims[1..].iter().try_fold(1usize, |n, d| {
        n.checked_mul(const_dim_indices(std::slice::from_ref(d), params)?.len())
    })?;
    let row_w = row_count.checked_mul(elem_w as usize)?;
    if let Some(v) = override_val {
        if (v.width as usize) < row_w.checked_mul(outer.len())? {
            return None;
        }
    } else if items.as_ref()?.len() != outer.len() {
        return None;
    }
    let mut out = Vec::new();
    for (position, index) in outer.iter().enumerate() {
        let key = format!("{name}[{index}]");
        let item = items.as_ref().and_then(|v| v.get(position)).copied();
        let packed = override_val.map(|v| {
            let low = (outer.len() - 1 - position) * row_w;
            v.range_select(low + row_w - 1, low)
        });
        if dims.len() > 1 {
            out.extend(elements(
                elab,
                &key,
                &dims[1..],
                item,
                packed.as_ref(),
                data_type,
                params,
                init_params,
            )?);
            continue;
        }
        let mut value = if let Some(v) = packed {
            v
        } else {
            let item = item?;
            pack_struct_const_value(
                data_type,
                item,
                init_params,
                &elab.typedefs,
                &elab.typedef_types,
            )
            .or_else(|| {
                pack_packed_vector_pattern(data_type, item, init_params, &elab.typedef_types)
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

pub(super) fn register(
    elab: &mut ElaboratedModule,
    prefix: &str,
    name: &str,
    dims: &[UnpackedDimension],
    init: Option<&Expression>,
    override_val: Option<&Value>,
    data_type: &DataType,
    params: &HashMap<String, Value>,
    init_params: &HashMap<String, Value>,
) -> bool {
    remember_default(&format!("{prefix}{name}"), data_type, params, elab);
    let Some(values) = elements(
        elab,
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
    let dims = normalize_unpacked_dims(dims, params, &elab.typedef_types);
    let Some(shape) = declared_unpacked_dims(&dims, params) else {
        return false;
    };
    let width = resolve_type_width(data_type, Some(params), Some(&elab.typedefs)).max(1);
    let full_name = format!("{prefix}{name}");
    if let Some(fields) = super::packed_struct_field_layout(
        data_type,
        params,
        &elab.typedefs,
        &elab.typedef_types,
    ) {
        // §7.2.2: `array[i].field.subfield` slices the element Value. The
        // layout has to be on the array name; a scalar struct parameter
        // already records it, an unpacked array of that struct did not.
        super::tls_register_struct_layout(&full_name, &fields);
        elab.packed_struct_fields
            .entry(full_name.clone())
            .or_insert(fields);
    }
    register_shape(elab, &full_name, &shape, width);
    // §6.20.2: aggregate parameter elements use whole Value storage.
    // An unpacked variable type would route their member reads to separate
    // field signals, which this constant representation does not allocate.
    if !matches!(resolve_typedef_chain(data_type, &elab.typedef_types),
        DataType::Struct(s) if !s.packed)
    {
        elab.var_decl_types.insert(full_name, data_type.clone());
    }
    for (name, value) in values {
        let name = format!("{prefix}{name}");
        params_insert_traced(&mut elab.parameters, line!(), name.clone(), value.clone());
        signals_insert_traced(
            &mut elab.signals,
            line!(),
            name.clone(),
            Signal {
                is_const: true,
                name,
                width,
                is_signed: value.is_signed,
                is_real: value.is_real,
                direction: None,
                value,
                type_name: None,
            },
        );
    }
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
