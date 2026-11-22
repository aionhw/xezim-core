use super::*;

/// Register members of an anonymous enum attached to a variable declaration
/// (`enum logic { A, B } var_name;`) into `elab.parameters` and `elab.signals`.
/// `typedef enum {...}` already does this via `process_typedef`; this is the
/// missing path for the bare-variable form. Used by every `DataDeclaration`
/// arm in the elaborator (top-level, submodule, generate-scope, etc.).
/// §6.19.1: expand one enum member into its concrete (name, value) entries,
/// honoring a `[lo:hi]` element range (already normalized from the `[N]` count
/// form by the parser). An `init` seeds the FIRST expanded name; the rest
/// auto-increment. Returns the expanded entries and the next auto value.
/// §6.19: an enum member may carry an X/Z-bearing value (`XX = 'bx`,
/// `XZ = 32'h1x2z3xxz`). The u64 pipeline masks those bits away, so the
/// registered CONSTANT must be rebuilt as a 4-state Value from the raw
/// initializer. Only single (non-ranged) members can carry one legally.
pub(super) fn enum_member_4state(
    member: &crate::ast::types::EnumMember,
    fallback: u64,
    width: u32,
    params: &crate::hasher::HashMap<String, Value>,
) -> Value {
    if member.range.is_none() {
        if let Some(init) = &member.init {
            let v = eval_const_expr_val(init, params);
            if v.has_xz() && !v.is_real {
                return v.resize(width.max(1));
            }
        }
    }
    Value::from_u64(fallback, width)
}

pub(super) fn expand_enum_member(
    member: &crate::ast::types::EnumMember,
    next_val: u64,
    params: &crate::hasher::HashMap<String, Value>,
) -> (Vec<(String, u64)>, u64) {
    let mut out = Vec::new();
    let mut val = if let Some(init) = &member.init {
        eval_const_expr(init, params)
    } else {
        next_val
    };
    match &member.range {
        None => {
            out.push((member.name.name.clone(), val));
            val = val.wrapping_add(1);
        }
        Some((lo_e, hi_e)) => {
            let lo = const_eval_i64_with_params(lo_e, Some(params)).unwrap_or(0);
            let hi = const_eval_i64_with_params(hi_e, Some(params)).unwrap_or(lo);
            let idxs: Vec<i64> = if lo <= hi {
                (lo..=hi).collect()
            } else {
                (hi..=lo).rev().collect()
            };
            for i in idxs {
                out.push((format!("{}{}", member.name.name, i), val));
                val = val.wrapping_add(1);
            }
        }
    }
    (out, val)
}

/// §6.19 Value-domain twin of `expand_enum_member`, for bases WIDER than 64
/// bits: the u64 pipeline truncates every member to its low 64 bits — and
/// runs the auto-increment chain there, so even an unspecified member
/// carried only the low half of its predecessor. Same name expansion; the
/// values and the increment chain are carried at full width.
fn expand_enum_member_wide(
    member: &crate::ast::types::EnumMember,
    next_val: &Value,
    width: u32,
    params: &crate::hasher::HashMap<String, Value>,
) -> (Vec<(String, Value)>, Value) {
    let one = Value::from_u64(1, width);
    let mut val = if let Some(init) = &member.init {
        let v = eval_const_expr_val(init, params);
        if v.is_real {
            Value::from_u64(eval_const_expr(init, params), width)
        } else {
            v.resize(width)
        }
    } else {
        next_val.clone()
    };
    let mut out = Vec::new();
    match &member.range {
        None => {
            out.push((member.name.name.clone(), val.clone()));
            val = val.add(&one).resize(width);
        }
        Some((lo_e, hi_e)) => {
            let lo = const_eval_i64_with_params(lo_e, Some(params)).unwrap_or(0);
            let hi = const_eval_i64_with_params(hi_e, Some(params)).unwrap_or(lo);
            let idxs: Vec<i64> = if lo <= hi {
                (lo..=hi).collect()
            } else {
                (hi..=lo).rev().collect()
            };
            for i in idxs {
                out.push((format!("{}{}", member.name.name, i), val.clone()));
                val = val.add(&one).resize(width);
            }
        }
    }
    (out, val)
}

/// Full-width member values of an enum whose base exceeds 64 bits, keyed by
/// member name — the override map the registration sites consult so the u64
/// tables (`enum_members`, iteration order) keep their shape while the
/// CONSTANTS the design reads carry every bit.
pub fn wide_enum_value_map(
    et: &crate::ast::types::EnumType,
    width: u32,
    params: &crate::hasher::HashMap<String, Value>,
) -> crate::hasher::HashMap<String, Value> {
    let mut map: crate::hasher::HashMap<String, Value> = crate::hasher::HashMap::default();
    let mut next = Value::from_u64(0, width);
    for member in &et.members {
        let (entries, nv) = expand_enum_member_wide(member, &next, width, params);
        next = nv;
        for (nm, v) in entries {
            map.insert(nm, v);
        }
    }
    map
}

/// Compute an anonymous enum's members in declaration order (which is the LRM
/// §6.19.6 iteration order for first/last/next/prev/num). Mirrors the value
/// expansion in `register_anonymous_enum_members`.
pub fn anon_enum_members_ordered(
    dt: &DataType,
    params: &crate::hasher::HashMap<String, Value>,
) -> Option<Vec<(String, u64)>> {
    if let DataType::Enum(et) = dt {
        let mut next_val: u64 = 0;
        let mut ordered: Vec<(String, u64)> = Vec::new();
        for member in &et.members {
            let (entries, nv) = expand_enum_member(member, next_val, params);
            next_val = nv;
            for (nm, val) in entries {
                ordered.push((nm, val));
            }
        }
        Some(ordered)
    } else {
        None
    }
}

pub fn register_anonymous_enum_members(dt: &DataType, elab: &mut ElaboratedModule) {
    // §6.19: an enum declared INSIDE a struct member's type installs its
    // members in the scope enclosing the STRUCT — `struct packed { enum
    // integer { A } e; } s;` makes `A` visible in the module. Recurse.
    if let DataType::Struct(su) = dt {
        for m in &su.members {
            register_anonymous_enum_members(&m.data_type, elab);
        }
        return;
    }
    if let DataType::Enum(et) = dt {
        let base_width = et
            .base_type
            .as_ref()
            .map(|bt| resolve_type_width(bt, Some(&elab.parameters), Some(&elab.typedefs)))
            .unwrap_or(32);
        let mut next_val: u64 = 0;
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
                elab.parameters
                    .entry(nm.clone())
                    .or_insert_with(|| v.clone());
                elab.signals.entry(nm.clone()).or_insert_with(|| Signal {
                    is_const: false,
                    name: nm.clone().into(),
                    width: base_width,
                    is_signed: false,
                    is_real: false,
                    direction: None,
                    value: v,
                    type_name: None,
                });
            }
        }
    }
}

/// Register a class's CLASS-LOCAL typedefs. Two responsibilities:
///  * `typedef enum {...}` members become resolvable bare-name constants
///    (like module/package enums), so `req.request = SEQ_TYPE_REQ` doesn't
///    store X.
///  * ALL class-local typedefs get their full registration via `process_typedef`
///    — type, width, unpacked dimensions, and (for enums) member values. This
///    is required so that (a) a `ref edges_t` formal is detected as an
///    associative array — UVM's `typedef bit edges_t[uvm_phase]` lives INSIDE
///    class uvm_phase and was invisible to `port_is_assoc_array`; and (b)
///    config_db / type-handle equality resolves the class-local type.
///    Without it the phase-DAG successor writeback was silently lost and every
///    such test stalled at t=0.
pub fn register_class_enum_members(c: &ClassDeclaration, elab: &mut ElaboratedModule) {
    for item in &c.items {
        if let ClassItem::Typedef(td) = item {
            register_anonymous_enum_members(&td.data_type, elab);
            // A class-local typedef must not STOMP an existing package/$unit
            // type of the same name in the global bare table: classes are
            // registered during the design-wide hoist, whose HashMap order is
            // arbitrary, so `typedef logic [63:0] wdata_t` inside some class
            // could transiently own the bare slot while a TOP-module
            // declaration of the package's 146-bit `wdata_t` was being sized —
            // carving the signal at the wrong width even though every later
            // probe of the table read the healed value. Register fully (the
            // class body still needs absent names resolvable — UVM's
            // `typedef bit edges_t[uvm_phase]`), then restore any pre-existing
            // bare entry: on a collision the package type keeps the slot.
            let prev_w = elab.typedefs.get(&td.name.name).copied();
            let prev_t = elab.typedef_types.get(&td.name.name).cloned();
            process_typedef(td, elab);
            // §8.23: a struct member sized by the class's own constant
            // (`m[Q]`) — `process_typedef` only sees the enclosing scope.
            if class_binds_values(c)
                && !class_has_value_params(c)
                && let Some(dt @ DataType::Struct(_)) = elab.typedef_types.get(&td.name.name)
            {
                let scope = class_const_scope(c, Some(&elab.parameters));
                if let Some(sized) = size_struct_member_dims(dt, &scope, &elab.typedef_types, true)
                {
                    let w = resolve_type_width(&sized, Some(&scope), Some(&elab.typedefs));
                    typedefs_insert_traced(
                        &mut elab.typedefs,
                        "insert:class_local_struct_dims",
                        td.name.name.clone(),
                        w,
                    );
                    elab.typedef_types.insert(td.name.name.clone(), sized);
                    sync_typedefs_tls(&elab.typedefs);
                }
            }
            if let Some(w) = prev_w {
                typedefs_insert_traced(
                    &mut elab.typedefs,
                    "restore:class_local_typedef",
                    td.name.name.clone(),
                    w,
                );
                if let Some(t) = prev_t {
                    elab.typedef_types.insert(td.name.name.clone(), t);
                }
                sync_typedefs_tls(&elab.typedefs);
            }
        }
    }
    register_nested_qualified_typedefs(c, elab);
}
