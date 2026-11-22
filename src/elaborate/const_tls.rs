use super::*;

// §13.4.3 — thread-local FUNCTION table consulted by
// `const_eval_i64_with_params` when a RANGE DIMENSION calls a user sizing
// function directly (`reg [log2(DEPTH)-1:0] a;` with no parameter in
// between). Same shape as TYPEDEFS_TLS: refreshed by `set_funcs_tls`
// wherever function declarations are (pre-)registered, so dimension
// resolution sees them without threading `&elab` through 47 call sites.
thread_local! {
    pub(super) static FUNCS_TLS: std::cell::RefCell<Option<std::rc::Rc<HashMap<String, FunctionDeclaration>>>>
        = const { std::cell::RefCell::new(None) };
}

thread_local! {
    /// The table `FUNCS_TLS` currently mirrors (identity, change-log
    /// position), like `TYPEDEFS_TLS_MIRROR`; None after `funcs_tls_add`
    /// merged in declarations of its own.
    static FUNCS_TLS_MIRROR: std::cell::Cell<Option<(u64, usize)>> =
        const { std::cell::Cell::new(None) };
}

/// Make `FUNCS_TLS` hold exactly the contents of `funcs` (see
/// `sync_typedefs_tls`).
pub(super) fn set_funcs_tls(funcs: &FuncTable) {
    let mirror = FUNCS_TLS_MIRROR.with(|m| m.get());
    FUNCS_TLS.with(|cell| {
        let mut slot = cell.borrow_mut();
        match (slot.as_mut(), mirror) {
            (Some(rc), Some((id, seen))) if id == funcs.ident.0 && seen <= funcs.log.len() => {
                if seen < funcs.log.len() {
                    funcs.replay_into(std::rc::Rc::make_mut(rc), seen);
                }
            }
            _ => *slot = Some(std::rc::Rc::new((*funcs.map).clone())),
        }
    });
    FUNCS_TLS_MIRROR.with(|m| m.set(Some((funcs.ident.0, funcs.log.len()))));
}

/// Incremental FUNCS_TLS refresh for the per-instance inlining path. The full
/// `set_funcs_tls` deep-clones the ENTIRE accumulated function map — which
/// grows with every inlined instance — so calling it per instantiation was
/// O(instances²) in AST clones and dominated big-design elaboration (a 2200-
/// instance design spent ~95% of its 23s compile there). The const-eval
/// consumer only ever looks up BARE names (`h.path.last()`), so it needs just
/// the sub-module's own function declarations merged in, first-wins like the
/// `entry().or_insert` registration it mirrors.
pub(super) fn funcs_tls_add<'a>(
    funcs: &HashMap<String, FunctionDeclaration>,
    names: impl Iterator<Item = &'a String>,
) {
    FUNCS_TLS_MIRROR.with(|m| m.set(None));
    FUNCS_TLS.with(|cell| {
        let mut b = cell.borrow_mut();
        let rc = b.get_or_insert_with(|| std::rc::Rc::new(HashMap::default()));
        let map = std::rc::Rc::make_mut(rc);
        for n in names {
            if !map.contains_key(n) {
                if let Some(fd) = funcs.get(n) {
                    map.insert(n.clone(), fd.clone());
                }
            }
        }
    });
}

// LRM §20.7 — thread-local typedef table consulted by const-eval `$bits`
// when the operand is a typedef-name ident. Avoids changing the signature
// of `const_eval_i64_with_params` at all 47 call sites. Callers that
// have a typedef table in scope wrap their const-eval with
// `with_typedefs(td, || const_eval_…)`; the table is restored on exit.
thread_local! {
    /// The table `TYPEDEFS_TLS` currently mirrors — its identity and how much
    /// of its change log the snapshot already reflects — or None when the
    /// snapshot holds anything else. Every writer of `TYPEDEFS_TLS` keeps
    /// this in step.
    pub(super) static TYPEDEFS_TLS_MIRROR: std::cell::Cell<Option<(u64, usize)>> =
        const { std::cell::Cell::new(None) };
}

/// Make `TYPEDEFS_TLS` hold exactly the contents of `table`: replay the
/// changes since the snapshot was taken when it mirrors this table, copy the
/// whole table otherwise.
pub(super) fn sync_typedefs_tls(table: &TypedefTable) {
    let mirror = TYPEDEFS_TLS_MIRROR.with(|m| m.get());
    TYPEDEFS_TLS.with(|cell| {
        let mut slot = cell.borrow_mut();
        match (slot.as_mut(), mirror) {
            (Some(snap), Some((id, seen))) if id == table.ident.0 && seen <= table.log.len() => {
                table.replay_into(snap, seen)
            }
            _ => *slot = Some((*table.map).clone()),
        }
    });
    TYPEDEFS_TLS_MIRROR.with(|m| m.set(Some((table.ident.0, table.log.len()))));
}

thread_local! {
    pub(super) static TYPEDEFS_TLS: std::cell::RefCell<Option<HashMap<String, u32>>>
        = const { std::cell::RefCell::new(None) };
    /// §6.20.3 / §20.6.2 — the packed widths of the TYPE PARAMETERS of the
    /// instance whose behavioral items are currently being materialized, so
    /// `rewrite_expr_impl` can fold `$bits(T)` to a literal. The binding only
    /// exists during inlining (the `saved_type_binds` rail restores the
    /// bare typedef slot afterwards), so at run time `$bits(T)` found no `T`
    /// and read 1 — wrong in every expression position (cont-assign,
    /// procedural, loop bound) while a `localparam NB = $bits(T)` folded
    /// correctly during elaboration. Same pattern as TYPEDEFS_TLS.
    pub(super) static TYPE_BIND_WIDTHS_TLS: std::cell::RefCell<Option<Rc<HashMap<String, u32>>>>
        = const { std::cell::RefCell::new(None) };
    /// §20.7 — the same instance's type parameters as array-query operands:
    /// `$left(T)` / `$size(T)` / … fold from these. At run time `T` is not a
    /// signal and the queries read 0.
    pub(super) static TYPE_BIND_QUERIES_TLS: std::cell::RefCell<Option<Rc<HashMap<String, TypeQueryDims>>>>
        = const { std::cell::RefCell::new(None) };
    /// §10.9: the same instance's type parameters as types, for a typed
    /// pattern `T'{...}`; `T` resolves only while the instance is inlined.
    pub(super) static TYPE_BIND_TYPES_TLS: std::cell::RefCell<Option<Rc<HashMap<String, DataType>>>>
        = const { std::cell::RefCell::new(None) };
    /// LRM §20.7 — thread-local array-range table for const-eval of
    /// `$size`/`$left`/`$right`/`$high`/`$low`/`$dimensions` on an
    /// array-name ident. Same pattern as TYPEDEFS_TLS to avoid touching
    /// every call site. Maps `name → (lo, hi, ndim)`.
    pub(super) static ARRAYS_TLS: std::cell::RefCell<Option<HashMap<String, (i64, i64, u32)>>>
        = const { std::cell::RefCell::new(None) };
    /// Const-eval support for struct-member select `s.field` (IEEE 1800-2017
    /// §7.2.1): packed-struct field layout `name → [(field, lsb_offset, width)]`,
    /// mirroring `ElaboratedModule.packed_struct_fields`. Lets `eval_const_expr_val`
    /// slice a field out of a struct-typed parameter Value (black-parrot's
    /// `proc_param_lp.icache_sets`). Updated incrementally as struct params/
    /// localparams register their layout, so a later localparam that selects from
    /// an earlier one resolves.
    pub(super) static STRUCT_FIELDS_TLS: std::cell::RefCell<HashMap<String, Vec<(String, u32, u32)>>>
        = std::cell::RefCell::new(HashMap::default());
    /// Const-eval support for packed-array element select `a[i]` on an
    /// array-of-structs parameter: `name → element bit-width`. Lets
    /// `eval_const_expr_val` slice element `i` (`[i*elem_w +: elem_w]`) out of a
    /// packed-array parameter Value (black-parrot's `all_cfgs_gp[bp_params_p]`).
    pub(super) static PACKED_ELEM_W_TLS: std::cell::RefCell<HashMap<String, u32>>
        = std::cell::RefCell::new(HashMap::default());
    /// Packed arrays declared `[0:N]` keep index 0 in the MS bits. The width
    /// map alone numbers index 0 from the LSB, which is `[N-1:0]`.
    pub(super) static PACKED_ELEM_MSB0_TLS: std::cell::RefCell<HashSet<String>>
        = std::cell::RefCell::new(HashSet::default());
    /// The lowest index of a packed array's outermost range when it is not
    /// 0 (`s_t [1:3]`, `s_t [3:1]`): an index counts from it (§7.4.1).
    pub(super) static PACKED_ELEM_LOW_TLS: std::cell::RefCell<HashMap<String, i64>>
        = std::cell::RefCell::new(HashMap::default());
    /// The packed dimensions below the outermost one of a multi-dimensional
    /// packed parameter, outermost first: (element width, ascending, lowest
    /// index) of each, for the second and later selects of `M[i][j]`.
    static PACKED_ELEM_INNER_TLS: std::cell::RefCell<HashMap<String, Vec<(u32, bool, i64)>>>
        = std::cell::RefCell::new(HashMap::default());
    /// Names of STRING-typed parameters, so const-eval knows a concatenation
    /// involving them is TEXT concatenation (§6.16) rather than a bit-vector
    /// concatenation — `localparam string CAT = {PFX, NAME}` produced only the
    /// last operand's text otherwise.
    static STRING_PARAMS_TLS: std::cell::RefCell<HashSet<String>>
        = std::cell::RefCell::new(HashSet::default());
    /// Globally-visible parameter fallback for const-eval: package/$unit params
    /// (snapshot taken after package elaboration, before module inlining). When a
    /// const-eval `Ident` misses the scoped param map — e.g. a sub-module
    /// header localparam `sc = all_cfgs_gp[SEL]` evaluated in the instance-merge
    /// context, which holds only the sub-instance's own params — fall back here so
    /// the imported package parameter still resolves.
    static PARAM_FALLBACK_TLS: std::cell::RefCell<HashMap<String, Value>>
        = std::cell::RefCell::new(HashMap::default());
    /// §26.3: the `import` items of each inlined definition, by definition
    /// name: `(package, Some(item))` for `import p::x`, `(package, None)` for
    /// `import p::*`. Read by `imported_array_element`.
    pub(super) static DEF_IMPORTS_TLS: std::cell::RefCell<HashMap<String, Rc<[(String, Option<String>)]>>>
        = std::cell::RefCell::new(HashMap::default());
    /// §26.3: the definitions whose items are being read, innermost last,
    /// each with the address of its parent's own parameter map
    /// (`ImportScope`).
    static IMPORT_SCOPE_TLS: std::cell::RefCell<Vec<(String, usize)>>
        = const { std::cell::RefCell::new(Vec::new()) };
    /// Typedef bodies for `const_eval_user_call`. That path builds an empty
    /// module shell, so a generate-if that calls a package function could not
    /// see `typedef unit_type_t [0:4] fmt_unit_types_t` and indexed the formal
    /// as bits. Snapshot taken once the package typedefs are complete; it
    /// shares the elaboration's table until either is written, and every
    /// shell shares it, so a call no longer copies every typedef (#721).
    pub(super) static TYPEDEF_TYPES_TLS: std::cell::RefCell<Option<SharedMap<DataType>>>
        = const { std::cell::RefCell::new(None) };
    /// Matching widths. A miss in `resolve_type_width` is 32 bits, which
    /// zero-extends a 10-bit packed array and moves ascending element 0 off
    /// the bits that hold the value. Shared the same way.
    pub(super) static TYPEDEF_WIDTHS_TLS: std::cell::RefCell<Option<Rc<HashMap<String, u32>>>>
        = const { std::cell::RefCell::new(None) };
}

/// Clear the package/$unit parameter and typedef snapshots the constant
/// evaluator falls back to, at the start of an elaboration: they are
/// thread-locals installed part-way through, so an elaboration read the
/// previous one's until it installed its own (#739).
pub(crate) fn reset_const_eval_snapshots() {
    PARAM_FALLBACK_TLS.with(|c| c.borrow_mut().clear());
    DEF_IMPORTS_TLS.with(|c| c.borrow_mut().clear());
    TYPEDEF_TYPES_TLS.with(|c| *c.borrow_mut() = None);
    TYPEDEF_WIDTHS_TLS.with(|c| *c.borrow_mut() = None);
}

/// Install the global package/$unit parameter snapshot consulted by const-eval
/// `Ident` lookups that miss the scoped map. Idempotent overwrite.
pub(super) fn set_param_fallback(params: &HashMap<String, Value>) {
    PARAM_FALLBACK_TLS.with(|c| *c.borrow_mut() = params.clone());
}

pub(super) fn set_typedef_types_tls(types: &SharedMap<DataType>) {
    TYPEDEF_TYPES_TLS.with(|c| *c.borrow_mut() = Some(types.clone()));
}

pub(super) fn set_typedef_widths_tls(widths: &TypedefTable) {
    TYPEDEF_WIDTHS_TLS.with(|c| *c.borrow_mut() = Some(widths.shared_map()));
}

/// Look up `name` in the global parameter fallback (package/$unit params).
pub(super) fn param_fallback_get(name: &str) -> Option<Value> {
    PARAM_FALLBACK_TLS.with(|c| c.borrow().get(name).cloned())
}

/// §26.3: an instance's items are read with its definition's imports in
/// scope, from where its parent binds them until the instance is inlined.
/// The parent evaluates the expressions it wrote for the instance (its
/// `#(...)` overrides) against its own parameter map, `parent_params`; an
/// expression evaluated against that map is answered by the parent's
/// imports instead.
pub(super) struct ImportScope;

impl ImportScope {
    pub(super) fn enter(def: &str, parent_params: &HashMap<String, Value>) -> Self {
        let parent = parent_params as *const HashMap<String, Value> as usize;
        IMPORT_SCOPE_TLS.with(|s| s.borrow_mut().push((def.to_string(), parent)));
        ImportScope
    }
}

impl Drop for ImportScope {
    fn drop(&mut self) {
        IMPORT_SCOPE_TLS.with(|s| {
            s.borrow_mut().pop();
        });
    }
}

/// §26.3: element `index` of the array `name` (`V`, or a row `V[0]` of it)
/// that the definition being read imports, under its package's qualified key
/// (`p::V[0][index]`). An explicit `import p::V` names the package;
/// otherwise exactly one of the wildcard-imported packages must declare the
/// element. The innermost definition that imports it decides, from the one
/// that wrote the expression outward (`ImportScope`).
pub(super) fn imported_array_element<P: ParamLookup>(
    name: &str,
    index: i64,
    params: &P,
) -> Option<Value> {
    let (root, rows) = name.split_at(name.find('[').unwrap_or(name.len()));
    let read = |pkg: &str| {
        let key = format!("{pkg}::{root}{rows}[{index}]");
        params
            .get(&key)
            .cloned()
            .or_else(|| param_fallback_get(&key))
    };
    let map = params
        .as_hashmap_base()
        .map(|m| m as *const HashMap<String, Value> as usize);
    let scopes = IMPORT_SCOPE_TLS.with(|s| s.borrow().clone());
    // Evaluated against an instance's parent map: the parent (the entry
    // before it, or the top) wrote it.
    let end = scopes
        .iter()
        .rposition(|(_, parent)| map == Some(*parent))
        .unwrap_or(scopes.len());
    for (def, _) in scopes[..end].iter().rev() {
        let Some(imports) = DEF_IMPORTS_TLS.with(|c| c.borrow().get(def).cloned()) else {
            continue;
        };
        if let Some((pkg, _)) = imports
            .iter()
            .find(|(_, item)| item.as_deref() == Some(root))
        {
            return read(pkg);
        }
        let mut found = imports
            .iter()
            .filter(|(_, item)| item.is_none())
            .filter_map(|(pkg, _)| read(pkg));
        if let Some(value) = found.next() {
            return found.next().is_none().then_some(value);
        }
    }
    None
}

/// Fold a bare alias into the global parameter fallback so an inlined
/// submodule's const-eval (`localparam X = PW`, an unpacked `[N]` dimension)
/// can resolve a package parameter its OWN `import P::*` brings in. The
/// fallback snapshot is taken from the top/$unit params before inlining;
/// module-scope imports bind only later (during inlining), so their aliases
/// must be added here to reach the const-eval that reads via
/// `param_fallback_get`.
pub(super) fn param_fallback_set(name: &str, v: &Value) {
    PARAM_FALLBACK_TLS.with(|c| {
        let mut c = c.borrow_mut();
        if !c.contains_key(name) {
            c.insert(name.to_string(), v.clone());
        }
    });
}

/// Record a struct param/localparam's packed field layout for const-eval
/// member selects (`s.field`). Keyed by bare name; later registrations win
/// (matches `packed_struct_fields`).
pub(super) fn tls_register_struct_layout(name: &str, fields: &[(String, u32, u32)]) {
    STRUCT_FIELDS_TLS.with(|c| {
        c.borrow_mut().insert(name.to_string(), fields.to_vec());
    });
}

/// Root parameter and dotted field path of a const select base.
/// An index is the element (`OUTERS[0].rsp` keeps layout `OUTERS`, path `rsp`).
fn const_struct_select_root(expr: &Expression) -> Option<(String, String)> {
    // Package and instance prefixes are part of the array's registered key.
    // Resolve that key before interpreting a suffix as a struct member.
    let mut keys = Vec::new();
    const_index_base_keys::<HashMap<String, Value>>(expr, None, &mut keys);
    if let Some(root) = STRUCT_FIELDS_TLS.with(|c| {
        let map = c.borrow();
        keys.into_iter().find(|key| map.contains_key(key))
    }) {
        return Some((root, String::new()));
    }
    match &expr.kind {
        ExprKind::Paren(inner) => const_struct_select_root(inner),
        ExprKind::Index { expr, .. } => const_struct_select_root(expr),
        ExprKind::Ident(h) => {
            let root = h.path.first()?.name.name.clone();
            let prefix = h.path[1..]
                .iter()
                .map(|s| s.name.name.as_str())
                .collect::<Vec<_>>()
                .join(".");
            Some((root, prefix))
        }
        ExprKind::MemberAccess { expr, member } => {
            let (root, prefix) = const_struct_select_root(expr)?;
            let path = if prefix.is_empty() {
                member.name.clone()
            } else {
                format!("{prefix}.{}", member.name)
            };
            Some((root, path))
        }
        _ => None,
    }
}

/// `(offset within the evaluated base, width)` of `member` (§7.2.2).
/// Nested paths are stored on the root (`rsp.accept`); the offset is relative
/// to the prefix already sliced into the base value.
pub(super) fn const_struct_field_in_base(base: &Expression, member: &str) -> Option<(u32, u32)> {
    if let ExprKind::Ident(h) = &base.kind
        && h.path.len() == 1
        && h.path[0].selects.is_empty()
    {
        return STRUCT_FIELDS_TLS.with(|c| {
            c.borrow().get(&h.path[0].name.name).and_then(|fields| {
                fields
                    .iter()
                    .find(|(name, _, _)| name == member)
                    .map(|(_, offset, width)| (*offset, *width))
            })
        });
    }
    let (root, prefix) = const_struct_select_root(base)?;
    let full = if prefix.is_empty() {
        member.to_string()
    } else {
        format!("{prefix}.{member}")
    };
    STRUCT_FIELDS_TLS.with(|c| {
        let map = c.borrow();
        let layout = map.get(&root)?;
        let (abs, w) = layout
            .iter()
            .find(|(f, _, _)| f == &full)
            .map(|(_, o, w)| (*o, *w))?;
        if prefix.is_empty() {
            return Some((abs, w));
        }
        let poff = layout
            .iter()
            .find(|(f, _, _)| f == &prefix)
            .map(|(_, o, _)| *o)?;
        abs.checked_sub(poff).map(|rel| (rel, w))
    })
}

/// Record a packed-array parameter's element width for const-eval index selects
/// (`a[i]`).
pub(super) fn tls_register_string_param(name: &str) {
    STRING_PARAMS_TLS.with(|c| {
        c.borrow_mut().insert(name.to_string());
    });
}

pub(super) fn tls_is_string_param(name: &str) -> bool {
    STRING_PARAMS_TLS.with(|c| c.borrow().contains(name))
}

pub(super) fn tls_register_elem_w(name: &str, elem_w: u32) {
    if elem_w == 0 {
        return;
    }
    PACKED_ELEM_W_TLS.with(|c| {
        c.borrow_mut().insert(name.to_string(), elem_w);
    });
}

pub(super) fn tls_register_elem_msb0(name: &str) {
    PACKED_ELEM_MSB0_TLS.with(|c| {
        c.borrow_mut().insert(name.to_string());
    });
}

/// Record (or, for 0, forget) the lowest index of `name`'s outermost packed
/// range; returns the previous entry.
pub(super) fn tls_register_elem_low(name: &str, low: i64) -> Option<i64> {
    PACKED_ELEM_LOW_TLS.with(|c| {
        let mut map = c.borrow_mut();
        if low != 0 {
            map.insert(name.to_string(), low)
        } else {
            map.remove(name)
        }
    })
}

/// Record the packed dimensions of `dt` below its outermost one for `name`
/// (see `PACKED_ELEM_INNER_TLS`); a type with one packed dimension clears it.
pub(super) fn tls_register_elem_inner(
    name: &str,
    dt: &DataType,
    params: &dyn ParamLookup,
    typedef_types: &HashMap<String, DataType>,
) {
    let shape = packed_struct_array_info_env(dt, params, typedef_types)
        .and_then(|(dims, elem)| {
            let leaf = typedefs_snapshot(|td| resolve_type_width_env(&elem, Some(&params), td));
            (leaf > 0).then_some((dims, leaf))
        })
        .or_else(|| {
            let (dims, leaf) = packed_pattern_shape(dt, params, typedef_types)?;
            let mut out = Vec::with_capacity(dims.len());
            for d in &dims {
                let PackedDimension::Range { left, right, .. } = d else {
                    return None;
                };
                out.push((
                    const_eval_i64_with_params_env(left, Some(&params))?,
                    const_eval_i64_with_params_env(right, Some(&params))?,
                ));
            }
            Some((out, leaf.max(1)))
        });
    let mut inner = Vec::new();
    if let Some((dims, leaf)) = shape {
        let mut ew = leaf;
        for (l, r) in dims.iter().skip(1).rev() {
            inner.push((ew, l < r, *l.min(r)));
            ew = ew.saturating_mul(((l - r).unsigned_abs() + 1) as u32);
        }
        inner.reverse();
    }
    PACKED_ELEM_INNER_TLS.with(|c| {
        let mut map = c.borrow_mut();
        if inner.is_empty() {
            map.remove(name);
        } else {
            map.insert(name.to_string(), inner);
        }
    });
}

/// Bit offset of element `idx` in a `width`-bit packed array whose elements
/// are `ew` bits: the left bound of the range is the most significant
/// element (§7.4.1), and `low` is the range's lowest index. `None` when the
/// index is outside the range.
pub(super) fn packed_elem_slot_lo(
    width: u32,
    ew: u32,
    msb0: bool,
    low: i64,
    idx: i64,
) -> Option<u32> {
    if ew == 0 || width < ew {
        return None;
    }
    let n = (width / ew) as i64;
    let rel = idx.checked_sub(low)?;
    if rel < 0 || rel >= n {
        return None;
    }
    let slot = if msb0 { n - 1 - rel } else { rel };
    Some(slot as u32 * ew)
}

/// Outermost element of a packed array: its width, and whether index 0 sits
/// in the MS bits (`[0:N]`, not `[N:0]`). A plain bit vector (element width
/// 1) is left to the bit-select path.
pub(super) fn packed_outer_elem(
    dt: &DataType,
    params: &dyn ParamLookup,
    typedef_types: &HashMap<String, DataType>,
) -> Option<(u32, bool, i64)> {
    // §7.4.1: a packed array of packed structures or unions; its element is
    // the whole structure.
    if let Some((dims, elem)) = packed_struct_array_info_env(dt, params, typedef_types) {
        let mut ew = typedefs_snapshot(|td| resolve_type_width_env(&elem, Some(&params), td));
        if ew == 0 {
            return None;
        }
        for (l, r) in dims.iter().skip(1) {
            ew = ew.checked_mul(((l - r).unsigned_abs() + 1) as u32)?;
        }
        let (l, r) = *dims.first()?;
        return Some((ew, l < r, l.min(r)));
    }
    let (dims, leaf) = packed_pattern_shape(dt, params, typedef_types)?;
    let outer = dims.first()?;
    let bounds = |d: &PackedDimension| -> Option<(i64, i64)> {
        let PackedDimension::Range { left, right, .. } = d else {
            return None;
        };
        Some((
            const_eval_i64_with_params_env(left, Some(&params))?,
            const_eval_i64_with_params_env(right, Some(&params))?,
        ))
    };
    let mut ew = leaf.max(1);
    for d in dims.iter().skip(1) {
        let (l, r) = bounds(d)?;
        ew = ew.checked_mul(((l - r).unsigned_abs() + 1) as u32)?;
    }
    let (l, r) = bounds(outer)?;
    if ew <= 1 {
        // A one-bit element is a bit-select. `[N-1:0]` already numbers bit 0
        // from the LSB. `[0:N]` numbers bit 0 from the MSB — fpnew's format
        // masks are declared that way, and reading bit 0 turned FP32 off.
        if l < r {
            return Some((1, true, l));
        }
        return None;
    }
    Some((ew, l < r, l.min(r)))
}

/// `P.Field[i]` on a packed-array member. The field select yields the array
/// value; the index has to take one element, not one bit, and `[0:N]` keeps
/// element 0 at the top of that value.
pub(super) fn register_struct_member_elem_widths(
    param: &str,
    dt: &DataType,
    params: &HashMap<String, Value>,
    typedef_types: &HashMap<String, DataType>,
) {
    let resolved = resolve_typedef_chain(dt, typedef_types).clone();
    let DataType::Struct(su) = resolved else {
        return;
    };
    for member in &su.members {
        let Some((ew, msb0, low)) = packed_outer_elem(&member.data_type, params, typedef_types)
        else {
            continue;
        };
        for decl in &member.declarators {
            let key = format!("{param}.{}", decl.name.name);
            tls_register_elem_w(&key, ew);
            tls_register_elem_low(&key, low);
            tls_register_elem_inner(&key, &member.data_type, params, typedef_types);
            if msb0 {
                tls_register_elem_msb0(&key);
            }
        }
    }
}

/// Element `idx` of a packed-array value whose element width was registered
/// for `base` (`Implementation.UnitTypes[opgrp]`). `[0:N]` keeps element 0 in
/// the MS bits; `[N:0]` keeps it at the LSB.
pub(super) fn const_packed_array_elem<P: ParamLookup>(
    base: &Expression,
    base_val: &Value,
    idx: i64,
    params: &P,
) -> Option<Value> {
    // §7.4.1: `M[i][j]` — `base` is itself an element select of a
    // multi-dimensional packed parameter; this select takes one element of
    // the next dimension out of the value the selects before it produced.
    let mut root = base;
    let mut depth = 0usize;
    loop {
        match &root.kind {
            ExprKind::Paren(inner) => root = inner,
            ExprKind::Index { expr, .. } => {
                depth += 1;
                root = expr;
            }
            _ => break,
        }
    }
    if depth > 0 {
        let mut keys = Vec::new();
        if let Some(path) = const_parameter_path(root, Some(params)) {
            keys.push(path);
        }
        const_index_base_keys(root, Some(params), &mut keys);
        let level = PACKED_ELEM_INNER_TLS.with(|c| {
            let map = c.borrow();
            keys.iter()
                .find_map(|k| map.get(k))
                .and_then(|levels| levels.get(depth - 1).copied())
        });
        if let Some((ew, msb0, low)) = level {
            let lo = packed_elem_slot_lo(base_val.width, ew, msb0, low, idx)?;
            return Some(base_val.range_select((lo + ew - 1) as usize, lo as usize));
        }
    }
    let mut keys = Vec::new();
    if let Some(path) = const_parameter_path(base, Some(params)) {
        keys.push(path);
    }
    const_index_base_keys(base, Some(params), &mut keys);
    let (ew, msb0, low) = PACKED_ELEM_W_TLS.with(|widths| {
        let widths = widths.borrow();
        PACKED_ELEM_MSB0_TLS.with(|msb| {
            let msb = msb.borrow();
            keys.into_iter().find_map(|k| {
                let ew = *widths.get(&k)?;
                let low = PACKED_ELEM_LOW_TLS.with(|c| c.borrow().get(&k).copied());
                Some((ew, msb.contains(&k), low.unwrap_or(0)))
            })
        })
    })?;
    if ew == 0 || base_val.width < ew {
        return None;
    }
    let lo = packed_elem_slot_lo(base_val.width, ew, msb0, low, idx)?;
    Some(base_val.range_select((lo + ew - 1) as usize, lo as usize))
}

/// §7.4.1, §7.2: the packed shape of a port of the module being elaborated,
/// as a variable declaration records it: the element width and dimensions of
/// a packed multi-D or typedef'd array, and the field layout of a packed
/// structure (and of a packed array of one). The packed dims may live on the
/// TYPEDEF (`typedef b_t [0:3] w_t; output w_t o;`): one step of a bare
/// reference, as the DataDeclaration arm takes. A TYPEDEF'd element with
/// declared dims (`output u8_t [0:7] o;`) chains them with the typedef's;
/// unrecorded, the ascending `[0:7]` fell back to [7:0] element order.
pub(super) fn register_port_packed_shape(
    elab: &mut ElaboratedModule,
    name: &str,
    data_type: &DataType,
) {
    if let Some(ew) =
        packed_inner_elem_width(data_type, &elab.parameters, &elab.typedefs).or_else(|| {
            let one = bare_typedef_step(data_type, &elab.typedef_types)?;
            packed_inner_elem_width(&one, &elab.parameters, &elab.typedefs)
        })
    {
        elab.packed_signal_elem_widths
            .entry(name.to_string())
            .or_insert(ew);
    }
    if let Some(fd) = packed_full_dims_of(data_type, &elab.parameters).or_else(|| {
        packed_full_dims_chained(data_type, &elab.parameters, &elab.typedef_types)
    }) {
        elab.packed_full_dims.entry(name.to_string()).or_insert(fd);
    }
    if let Some(fields) = packed_struct_field_layout(
        data_type,
        &elab.parameters,
        &elab.typedefs,
        &elab.typedef_types,
    ) && !fields.is_empty()
    {
        // §7.4.1: a packed ARRAY of the struct (`output s_t [0:3] o;`): its
        // dims, the struct the innermost.
        let struct_w = fields.iter().map(|(_, o, w)| o + w).max().unwrap_or(0);
        if let Some(fd) = packed_typedef_array_dims(data_type, struct_w, &elab.parameters) {
            elab.packed_full_dims.entry(name.to_string()).or_insert(fd);
        }
        tls_register_struct_layout(name, &fields);
        elab.packed_struct_fields
            .entry(name.to_string())
            .or_insert(fields);
        // §7.2, §7.4.1: and its members' packed shapes. Unrecorded,
        // `arg.vec[1]` of a `logic [3:0][7:0] vec` member was a one-bit select.
        register_member_packed_meta(elab, name, data_type, None);
    }
}

/// §6.12: `name` is a `shortreal` variable or net, declared directly or
/// through a typedef.
pub(super) fn signal_is_shortreal(elab: &ElaboratedModule, name: &str) -> bool {
    let Some(sig) = elab.signals.get(name).filter(|s| s.is_real) else {
        return false;
    };
    if sig.type_name.as_deref() == Some("shortreal") {
        return true;
    }
    elab.var_decl_types
        .get(name)
        .or_else(|| sig.type_name.as_ref().and_then(|ty| elab.typedef_types.get(ty)))
        .is_some_and(|dt| {
            matches!(
                resolve_typedef_chain(dt, &elab.typedef_types),
                DataType::Real {
                    kind: crate::ast::types::RealType::ShortReal,
                    ..
                }
            )
        })
}

/// Runtime twin of `register_packed_array_elem_w`. Const-eval already slices
/// `FP_ENCODINGS[fmt]` via the TLS tables; a function call with a variable
/// index (`fpnew_pkg::bias(src_fmt_q)`, `exp_bits(dst_fmt_q)`) goes through
/// the simulator, which bit-selects unless the parameter is in
/// `packed_signal_elem_widths`. An ascending `[0:N]` array also needs its
/// declared bounds, or index 0 reads the last element.
pub(super) fn register_packed_param_index(
    elab: &mut ElaboratedModule,
    key: &str,
    data_type: &DataType,
    params: Option<&HashMap<String, Value>>,
) {
    let ew = {
        let params = params.unwrap_or(&elab.parameters);
        packed_inner_elem_width(data_type, params, &elab.typedefs).or_else(|| {
            packed_outer_elem(data_type, params, &elab.typedef_types)
                .map(|(ew, _, _)| ew)
                .filter(|ew| *ew > 1)
        })
    };
    let fdims = {
        let params = params.unwrap_or(&elab.parameters);
        packed_struct_array_info(data_type, params, &elab.typedef_types)
            .map(|(dims, _)| dims)
            .or_else(|| packed_full_dims_chained(data_type, params, &elab.typedef_types))
            .or_else(|| packed_full_dims_of(data_type, params))
            .or_else(|| {
                // A typedef'd enum or mask (`unit_type_t [0:4]`, `logic [0:4]`)
                // keeps its range on the typedef. A lone normalized `[N-1:0]`
                // stays unrecorded; `packed_full_dims_of` already declined it.
                let (dims, _) = packed_pattern_shape(data_type, params, &elab.typedef_types)?;
                let mut out = Vec::with_capacity(dims.len());
                for d in &dims {
                    let PackedDimension::Range { left, right, .. } = d else {
                        return None;
                    };
                    out.push((
                        const_eval_i64_with_params(left, Some(params))?,
                        const_eval_i64_with_params(right, Some(params))?,
                    ));
                }
                if out.len() == 1 {
                    let (l, r) = out[0];
                    if r == 0 && l >= 0 {
                        return None;
                    }
                }
                Some(out)
            })
    };
    if let Some(ew) = ew.filter(|ew| *ew > 0) {
        elab.packed_signal_elem_widths.insert(key.to_string(), ew);
    }
    if let Some(fdims) = fdims {
        elab.packed_full_dims.insert(key.to_string(), fdims);
    }
}

/// If `dt` is a packed array of a named type (`T [hi:lo]…`, e.g. black-parrot's
/// `bp_proc_param_s [max_cfgs-1:0] all_cfgs_gp`), register the element width
/// `$bits(T)` so const-eval `name[i]` can slice one element. No-op otherwise.
pub(super) fn register_packed_array_elem_w(
    name: &str,
    dt: &DataType,
    typedefs: &HashMap<String, u32>,
    params: &HashMap<String, Value>,
) {
    if let DataType::TypeReference {
        name: tn,
        dimensions,
        ..
    } = dt
    {
        if !dimensions.is_empty() {
            let ew = typedefs
                .get(&tn.name.name)
                .copied()
                .filter(|w| *w > 1)
                .or_else(|| {
                    let mut elem = dt.clone();
                    if let DataType::TypeReference { dimensions, .. } = &mut elem {
                        dimensions.clear();
                    }
                    let w = resolve_type_width(&elem, Some(params), Some(typedefs));
                    (w > 1).then_some(w)
                });
            if let Some(ew) = ew {
                tls_register_elem_w(name, ew);
            }
            // `[0:N]` keeps element 0 in the MS bits. The width registration
            // above sliced from the LSB, so `FP_ENCODINGS[FP32]` read the
            // last encoding (16) instead of `{8,23}` (32).
            if let Some(PackedDimension::Range { left, right, .. }) = dimensions.first()
                && let Some(l) = const_eval_i64_with_params(left, Some(params))
                && let Some(r) = const_eval_i64_with_params(right, Some(params))
            {
                tls_register_elem_low(name, l.min(r));
                if l < r {
                    tls_register_elem_msb0(name);
                }
            }
        }
    }
}

/// Collect `name → declared DataType` for a module's ANSI ports and its
/// body variable/net declarations. Used to size `$bits(<port>.<member>)` in a
/// SUB-module's own body localparam, where the elaborated signal table does not
/// yet hold the sub-module's names — the width has to come from the
/// declarations themselves.
/// `elem_out` receives declarators that carry UNPACKED dimensions, mapped to
/// their ELEMENT type — `logic [3:0] arr [4]` gives `arr → logic [3:0]`, which
/// is what `$bits(arr[1])` needs. Those are kept apart from `out` because
/// `$bits(arr)` is the whole array, not one element.
pub(super) fn collect_declared_types(
    ports: &PortList,
    items: &[ModuleItem],
    out: &mut HashMap<String, DataType>,
    elem_out: &mut HashMap<String, DataType>,
) {
    if let PortList::Ansi(ps) = ports {
        for p in ps {
            if let Some(dt) = &p.data_type {
                let target = if p.dimensions.is_empty() {
                    &mut *out
                } else {
                    &mut *elem_out
                };
                target
                    .entry(p.name.name.clone())
                    .or_insert_with(|| dt.clone());
            }
        }
    }
    for item in items {
        if let ModuleItem::DataDeclaration(vd) = item {
            for d in &vd.declarators {
                let target = if d.dimensions.is_empty() {
                    &mut *out
                } else {
                    &mut *elem_out
                };
                target
                    .entry(d.name.name.clone())
                    .or_insert_with(|| vd.data_type.clone());
            }
        }
    }
}

/// `$bits(<expr>)` sized purely from DECLARED types (no signal table). Mirrors
/// `bits_of_signal_expr` for the sub-module-body case.
fn bits_from_declared_types(
    arg: &Expression,
    decls: &HashMap<String, DataType>,
    elem_decls: &HashMap<String, DataType>,
    params: &HashMap<String, Value>,
    typedefs: &HashMap<String, u32>,
    typedef_types: &HashMap<String, DataType>,
) -> Option<u32> {
    if let ExprKind::SystemCall { name, args } = &arg.kind {
        if (name == "$unsigned" || name == "$signed") && args.len() == 1 {
            return bits_from_declared_types(
                &args[0],
                decls,
                elem_decls,
                params,
                typedefs,
                typedef_types,
            );
        }
        return None;
    }
    // `arr[i]` / `arr[i].member` on an unpacked array — size from the ELEMENT
    // type. A bit-select of a packed vector is handled by the signal-table
    // path, which knows the declaration is not an array.
    if let ExprKind::Index { expr, .. } = &arg.kind {
        let (base, path) = flatten_member_chain(expr)?;
        if params.contains_key(&base) {
            return None;
        }
        let dt = elem_decls.get(&base)?;
        return member_path_width(dt, &path, params, typedefs, typedef_types, 0);
    }
    let (base, path) = flatten_member_chain(arg)?;
    if params.contains_key(&base) || typedefs.contains_key(&base) {
        return None;
    }
    let dt = decls.get(&base)?;
    member_path_width(dt, &path, params, typedefs, typedef_types, 0)
}

/// Rewrite every `$bits(<decl-rooted expr>)` in `e` to a literal, using
/// declared types only.
pub(super) fn prebind_bits_from_declared_types(
    e: &Expression,
    decls: &HashMap<String, DataType>,
    elem_decls: &HashMap<String, DataType>,
    params: &HashMap<String, Value>,
    typedefs: &HashMap<String, u32>,
    typedef_types: &HashMap<String, DataType>,
) -> Expression {
    let mut out = e.clone();
    if let ExprKind::SystemCall { name, args } = &e.kind {
        if name == "$bits" && args.len() == 1 {
            // §20.6.2: the installed declared shapes know a type parameter's
            // instance binding and every unpacked dimension.
            let from_shape = decl_var_query("$bits", args, Some(params))
                // §7.4.5: an element or slice of a declared variable has the
                // width its selects leave (`pk[2]` of `logic [3:0][1:0]`);
                // the declared-type walk below sized it as one bit.
                .or_else(|| decl_select_bits(&args[0], Some(params)))
                .and_then(|b| u32::try_from(b).ok())
                .filter(|w| *w > 0);
            if let Some(w) = from_shape.or_else(|| {
                bits_from_declared_types(
                    &args[0],
                    decls,
                    elem_decls,
                    params,
                    typedefs,
                    typedef_types,
                )
            }) {
                out.kind = ExprKind::Number(NumberLiteral::Integer {
                    size: None,
                    signed: false,
                    base: crate::ast::expr::NumberBase::Decimal,
                    value: w.to_string(),
                    cached_val: crate::ast::cache::LiteralCache::new(None),
                });
            }
            return out;
        }
    }
    macro_rules! rb {
        ($x:expr_2021) => {
            prebind_bits_from_declared_types($x, decls, elem_decls, params, typedefs, typedef_types)
        };
    }
    match &mut out.kind {
        ExprKind::Binary { left, right, .. } => {
            **left = rb!(left);
            **right = rb!(right);
        }
        ExprKind::Unary { operand, .. } => {
            **operand = rb!(operand);
        }
        ExprKind::Paren(inner) => {
            **inner = rb!(inner);
        }
        ExprKind::SystemCall { args, .. } => {
            for a in args.iter_mut() {
                *a = rb!(a);
            }
        }
        _ => {}
    }
    out
}

/// Does this expression mention `$bits` anywhere? Cheap guard so the prebind
/// walk (which clones) only runs for the expressions that need it.
pub(super) fn expr_mentions_bits(e: &Expression) -> bool {
    match &e.kind {
        ExprKind::SystemCall { name, args } => {
            name == "$bits" || args.iter().any(expr_mentions_bits)
        }
        ExprKind::Binary { left, right, .. } => {
            expr_mentions_bits(left) || expr_mentions_bits(right)
        }
        ExprKind::Unary { operand, .. } => expr_mentions_bits(operand),
        ExprKind::Paren(inner) => expr_mentions_bits(inner),
        _ => false,
    }
}

/// Bit width of a struct/union member PATH (`.w0`, `.w0.a`) starting from the
/// declared type `dt`. A named type is resolved through `typedef_types` so a
/// nested `hidden_field_t` inside a `prebuf_sync_t` can be walked; anonymous
/// inline structs and unions work directly. Returns None the moment the walk
/// cannot be completed, so callers keep whatever behaviour they had.
fn member_path_width(
    dt: &DataType,
    path: &[String],
    params: &HashMap<String, Value>,
    typedefs: &HashMap<String, u32>,
    typedef_types: &HashMap<String, DataType>,
    depth: u32,
) -> Option<u32> {
    if path.is_empty() {
        // §7.4.2: a packed dimension on the member multiplies its width, which
        // `resolve_type_width` already accounts for.
        return Some(resolve_type_width(dt, Some(params), Some(typedefs))).filter(|w| *w > 0);
    }
    if depth > 8 {
        return None;
    }
    let resolved: DataType;
    let su = match dt {
        DataType::Struct(su) => su,
        DataType::TypeReference { name, .. } => {
            resolved = typedef_types.get(&name.name.name)?.clone();
            match &resolved {
                DataType::Struct(su) => su,
                _ => return None,
            }
        }
        _ => return None,
    };
    for m in &su.members {
        for d in &m.declarators {
            if d.name.name == path[0] {
                // An unpacked dimension on the declarator would make `$bits`
                // the whole array; not modelled here, so decline rather than
                // report the element width.
                if !d.dimensions.is_empty() {
                    return None;
                }
                return member_path_width(
                    &m.data_type,
                    &path[1..],
                    params,
                    typedefs,
                    typedef_types,
                    depth + 1,
                );
            }
        }
    }
    None
}

/// Flatten `a.b.c` into its base identifier and the member names after it.
/// A `::` scope resolution lowers to the same `MemberAccess` node, so callers
/// must confirm the base actually names a signal before trusting the result.
fn flatten_member_chain(e: &Expression) -> Option<(String, Vec<String>)> {
    match &e.kind {
        ExprKind::Ident(h) => Some((h.path.last()?.name.name.clone(), Vec::new())),
        ExprKind::MemberAccess { expr, member } => {
            let (base, mut path) = flatten_member_chain(expr)?;
            path.push(member.name.clone());
            Some((base, path))
        }
        _ => None,
    }
}

/// Rewrite `$bits(<expr>)` to a literal when `<expr>` is rooted at a SIGNAL in
/// the enclosing scope. Const-eval resolves `$bits` of a parameter or a type
/// NAME, but has no signal table, so `$bits` of a plain variable, a port, a
/// struct-member select, a part-select or an element select all fell through to
/// 0 — silently. `#(.W($bits(some_signal)))` then elaborated a port declared
/// `[W-1:0]` as `[-1:0]`, and `localparam L = $bits(port.member)` came back 0,
/// which sized a whole synchronizer bus to nothing and left its output x.
///
/// Parameters and type names are left untouched: `$bits` resolves those itself,
/// and a `pkg::type_t` lowers to the same `MemberAccess` node as a member
/// select, so only a base that really names a signal is rewritten here.
pub(super) fn prebind_bits_of_signals(
    e: &Expression,
    signals: &SharedNameMap<Signal>,
    params: &HashMap<String, Value>,
    prefix: &str,
    typedefs: &HashMap<String, u32>,
    typedef_types: &HashMap<String, DataType>,
    struct_fields: &HashMap<String, Vec<(String, u32, u32)>>,
    arrays: &HashMap<String, (i64, i64, u32)>,
) -> Expression {
    let mut out = e.clone();
    if let ExprKind::SystemCall { name, args } = &e.kind {
        if name == "$bits" && args.len() == 1 {
            // A typedef may be visible only in this generate scope. Freeze its
            // width before the elaborator's type context is discarded (§20.6.2).
            let from_type = flatten_member_chain(&args[0]).and_then(|(base, path)| {
                let mut parts = vec![base];
                parts.extend(path);
                let dotted = parts.join(".");
                if signals.contains_key(&dotted) || params.contains_key(&dotted) {
                    return None;
                }
                // §20.6.2: the width table holds an unpacked typedef's
                // element width; $bits includes all of its dimensions.
                typedef_unpacked_bits(&dotted, Some(params))
                    .or_else(|| typedef_unpacked_bits(&parts.join("::"), Some(params)))
                    .and_then(|w| u32::try_from(w).ok())
                    .or_else(|| {
                        typedefs
                            .get(&dotted)
                            .or_else(|| typedefs.get(&parts.join("::")))
                            .copied()
                    })
            });
            // §7.4.5: an element or slice of a declared variable (see
            // `decl_select_bits`) before the signal table's element width.
            let from_shape = decl_select_bits(&args[0], Some(params))
                .and_then(|b| u32::try_from(b).ok())
                .filter(|w| *w > 0);
            if let Some(w) = from_shape.or(from_type).or_else(|| {
                bits_of_signal_expr(
                    &args[0],
                    signals,
                    params,
                    prefix,
                    typedefs,
                    typedef_types,
                    struct_fields,
                    arrays,
                )
            }) {
                out.kind = ExprKind::Number(NumberLiteral::Integer {
                    size: None,
                    signed: false,
                    base: crate::ast::expr::NumberBase::Decimal,
                    value: w.to_string(),
                    cached_val: crate::ast::cache::LiteralCache::new(None),
                });
            }
            return out;
        }
    }
    // Recurse into the common composite forms so `$bits(sig)-1` works.
    macro_rules! rb {
        ($x:expr_2021) => {
            prebind_bits_of_signals(
                $x,
                signals,
                params,
                prefix,
                typedefs,
                typedef_types,
                struct_fields,
                arrays,
            )
        };
    }
    match &mut out.kind {
        ExprKind::Binary { left, right, .. } => {
            **left = rb!(left);
            **right = rb!(right);
        }
        ExprKind::Unary { operand, .. } => {
            **operand = rb!(operand);
        }
        ExprKind::Paren(inner) => {
            **inner = rb!(inner);
        }
        ExprKind::SystemCall { args, .. } => {
            for a in args.iter_mut() {
                *a = rb!(a);
            }
        }
        _ => {}
    }
    out
}

/// `$bits(arg)` where `arg` is rooted at a declared signal, or None when it is
/// not (a parameter, a type name, or anything this cannot size confidently).
#[allow(clippy::too_many_arguments)]
fn bits_of_signal_expr(
    arg: &Expression,
    signals: &SharedNameMap<Signal>,
    params: &HashMap<String, Value>,
    prefix: &str,
    typedefs: &HashMap<String, u32>,
    typedef_types: &HashMap<String, DataType>,
    struct_fields: &HashMap<String, Vec<(String, u32, u32)>>,
    arrays: &HashMap<String, (i64, i64, u32)>,
) -> Option<u32> {
    // `$signed`/`$unsigned` are width-preserving wrappers.
    if let ExprKind::SystemCall { name, args } = &arg.kind {
        if (name == "$unsigned" || name == "$signed") && args.len() == 1 {
            return bits_of_signal_expr(
                &args[0],
                signals,
                params,
                prefix,
                typedefs,
                typedef_types,
                struct_fields,
                arrays,
            );
        }
        return None;
    }
    // §20.6.2 `$bits(<typedef> [dims])` — `$bits(pkg::t [0:0][1:0])`. A scoped
    // or plain TYPE NAME is not a data-type keyword, so the parser cannot emit
    // a TypeLiteral and produces a RangeSelect chain over the type name
    // instead. It looks exactly like a part-select, and the arm below sized it
    // by its own bounds: `$bits(t [0:0][1:0])` came back 2 rather than
    // `$bits(t) * 1 * 2`. A flattened pipeline stage declared
    // `logic [DATA_BITS-1:0]` then held two bits instead of 292 and dropped
    // every payload. Must be tried BEFORE the part-select arm, and only when
    // the base names a type that is NOT also a signal — a real part-select of
    // a signal keeps its ordinary meaning.
    {
        let mut dims: Vec<(i64, i64)> = Vec::new();
        let mut cur: &Expression = arg;
        while let ExprKind::RangeSelect {
            kind,
            left,
            right,
            expr,
        } = &cur.kind
        {
            if !matches!(kind, RangeKind::Constant) {
                break;
            }
            let (Some(l), Some(r)) = (
                const_eval_i64_with_params(left, Some(params)),
                const_eval_i64_with_params(right, Some(params)),
            ) else {
                break;
            };
            dims.push((l, r));
            cur = expr.as_ref();
        }
        if !dims.is_empty() {
            let tname = match &cur.kind {
                // `pkg::t` lowers to the same MemberAccess node as a struct
                // member select.
                ExprKind::MemberAccess { member, .. } => Some(member.name.clone()),
                ExprKind::Ident(h) => h.path.last().map(|sg| sg.name.name.clone()),
                _ => None,
            };
            if let Some(tname) = tname {
                let is_signal =
                    signals.contains_key(&tname) || signals.contains_key(&cat2(&prefix, &tname));
                if !is_signal && let Some(&base_w) = typedefs.get(&tname) {
                    let mut total = base_w as i64;
                    for (l, r) in dims {
                        total = total.checked_mul((l - r).abs() + 1)?;
                    }
                    return u32::try_from(total).ok().filter(|w| *w > 0);
                }
            }
        }
    }
    // A part-select is sized by its own bounds, whatever the base is.
    if let ExprKind::RangeSelect {
        kind, left, right, ..
    } = &arg.kind
    {
        let l = const_eval_i64_with_params(left, Some(params))?;
        let r = const_eval_i64_with_params(right, Some(params))?;
        let w = match kind {
            RangeKind::Constant => (l - r).abs() + 1,
            // §7.4.6 `[base +: n]` / `[base -: n]` — the width is the operand.
            RangeKind::IndexedUp | RangeKind::IndexedDown => r,
        };
        return u32::try_from(w).ok().filter(|w| *w > 0);
    }
    // An element select: an unpacked-array element keeps the declared width, a
    // bit-select of a packed vector is one bit.
    if let ExprKind::Index { expr, .. } = &arg.kind {
        let (base, path) = flatten_member_chain(expr)?;
        if params.contains_key(&base) || !path.is_empty() {
            return None;
        }
        let scoped = cat2(&prefix, &base);
        let is_unpacked = arrays.contains_key(&scoped) || arrays.contains_key(&base);
        if is_unpacked {
            // An unpacked array's ELEMENTS are the signals; the declaration
            // name may not be one at all, so take the width from an element.
            let w = signals
                .get(&scoped)
                .or_else(|| signals.get(&base))
                .map(|s| s.width)
                .or_else(|| {
                    let (lo, hi, _) = *arrays.get(&scoped).or_else(|| arrays.get(&base))?;
                    signals
                        .get(&format!("{}[{}]", scoped, lo))
                        .or_else(|| signals.get(&format!("{}[{}]", base, lo)))
                        .or_else(|| signals.get(&format!("{}[{}]", scoped, hi)))
                        .or_else(|| signals.get(&format!("{}[{}]", base, hi)))
                        .map(|s| s.width)
                })?;
            return Some(w).filter(|w| *w > 0);
        }
        let sig = signals.get(&scoped).or_else(|| signals.get(&base))?;
        return Some(1).filter(|_| sig.width > 0);
    }

    let (base, path) = flatten_member_chain(arg)?;
    // A parameter or type name resolves inside `$bits` itself — leave it.
    if params.contains_key(&base) || typedefs.contains_key(&base) {
        return None;
    }
    // §20.6.2: a declared variable is sized from its declared type — every
    // unpacked dimension included, a typedef's too (`arr_t ta;`). Its signal
    // only records one element.
    if path.is_empty()
        && decl_has_unpacked_dims(arg)
        && let Some(b) = decl_var_query("$bits", std::slice::from_ref(arg), Some(params))
    {
        return u32::try_from(b).ok().filter(|w| *w > 0);
    }
    let scoped = cat2(&prefix, &base);
    let sig = signals.get(&scoped).or_else(|| signals.get(&base))?;
    if path.is_empty() {
        return Some(sig.width).filter(|w| *w > 0);
    }
    // One level of member select also works for an ANONYMOUS inline struct,
    // which has no type name to walk — the packed field layout is recorded
    // under the signal's own name.
    if path.len() == 1 {
        if let Some(fields) = struct_fields
            .get(&scoped)
            .or_else(|| struct_fields.get(&base))
        {
            if let Some((_, _, w)) = fields.iter().find(|(f, _, _)| *f == path[0]) {
                if *w > 0 {
                    return Some(*w);
                }
            }
        }
    }
    // Otherwise walk the declared type, which handles nesting.
    let tn = sig.type_name.as_deref()?;
    let dt = typedef_types.get(tn)?;
    member_path_width(dt, &path, params, typedefs, typedef_types, 0)
}

/// Run `f` with `typedefs` installed as the thread-local typedef table
/// consulted by const-eval `$bits(typedef_name)`. The previous binding
/// is restored on exit so nested calls compose correctly.
pub fn with_typedefs<R>(typedefs: &HashMap<String, u32>, f: impl FnOnce() -> R) -> R {
    with_typedefs_owned(typedefs.clone(), f)
}

/// `with_typedefs` taking the table by value (no copy of a table the caller
/// built just for this call).
pub(super) fn with_typedefs_owned<R>(typedefs: HashMap<String, u32>, f: impl FnOnce() -> R) -> R {
    type_trace_tls_refresh("with_typedefs", &typedefs);
    let prev = TYPEDEFS_TLS.with(|td| (*td.borrow_mut()).replace(typedefs));
    let prev_mirror = TYPEDEFS_TLS_MIRROR.with(|m| m.replace(None));
    let r = f();
    TYPEDEFS_TLS.with(|td| *td.borrow_mut() = prev);
    TYPEDEFS_TLS_MIRROR.with(|m| m.set(prev_mirror));
    r
}

/// LRM §20.7 — install the array-range table for the duration of `f`.
/// Restored on exit so nested calls compose.
pub fn with_arrays<R>(arrays: &HashMap<String, (i64, i64, u32)>, f: impl FnOnce() -> R) -> R {
    let snapshot = arrays.clone();
    let prev = ARRAYS_TLS.with(|ar| (*ar.borrow_mut()).replace(snapshot));
    let r = f();
    ARRAYS_TLS.with(|ar| *ar.borrow_mut() = prev);
    r
}
