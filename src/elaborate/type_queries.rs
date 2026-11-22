use super::*;

/// IEEE 1800-2017 §20.7 — what a TYPE operand exposes to the array query
/// functions (`$left(int)`, `$size(my_vec_t)`, `$dimensions(bit [3:0][7:0])`).
#[derive(Debug, Clone, Default, serde::Serialize)]
pub struct TypeQueryDims {
    /// The queryable dimensions, unpacked first then packed (§7.4.5 numbers
    /// them in that order), each as the DECLARED `(left, right)` bounds:
    /// `int` -> `[(31, 0)]`, `logic [15:4]` -> `[(15, 4)]`,
    /// `bit [3:0][7:0]` -> `[(3, 0), (7, 0)]`, `byte t [0:2]` ->
    /// `[(0, 2), (7, 0)]`. Empty for a type with no dimension of its own.
    pub dims: Vec<(i64, i64)>,
    /// How many leading `dims` entries are UNPACKED ($unpacked_dimensions).
    pub unpacked: usize,
    /// Range the BOUND queries answer over when `dims` is empty: an integral
    /// type whose width is not written as a dimension (an enum, a packed
    /// struct) still reports `$left`/`$size` over its whole `[w-1:0]` extent
    /// while `$dimensions` stays 0. `None` for a scalar `logic`/`bit` and for
    /// the non-integral types, which have no dimension at all and answer `x`.
    pub whole: Option<(i64, i64)>,
}

/// Is `name` a built-in data-type keyword? Such a word can never also name a
/// variable, so an array query over it is unambiguously a §20.7 type query.
pub fn is_builtin_type_keyword(name: &str) -> bool {
    atom_keyword_width(name).is_some()
        || matches!(
            name,
            "bit"
                | "logic"
                | "reg"
                | "real"
                | "shortreal"
                | "realtime"
                | "string"
                | "chandle"
                | "event"
        )
}

/// Bit width of an integer ATOM type keyword (§6.11.1); None if `name` is not
/// one. Atom types carry one implicit packed dimension `[w-1:0]`.
pub(super) fn atom_keyword_width(name: &str) -> Option<u32> {
    Some(match name {
        "byte" => 8,
        "shortint" => 16,
        "int" | "integer" => 32,
        "longint" | "time" => 64,
        _ => return None,
    })
}

/// §20.6.2 + §6.24.1: `$bits` of a cast is the width of the cast's target,
/// whatever the operand (`$bits(int'(45))` is 32, `$bits(5'(45))` is 5).
/// None when the target width is not known here.
pub(super) fn const_cast_bits<P: ParamLookup>(e: &Expression, params: &P) -> Option<u32> {
    let ExprKind::SystemCall { name, args } = &e.kind else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let w = match name.as_str() {
        "$__xz_size_cast" => {
            u32::try_from(const_eval_i64_with_params_env(&args[0], Some(params))?).ok()?
        }
        "$__xz_type_cast" | "$__xz_named_cast" => match &args[0].kind {
            ExprKind::TypeLiteral(dt) => {
                typedefs_snapshot(|td| resolve_type_width_env(dt, Some(params), td))
            }
            // `N'(e)` with a constant `N` lowers to a named cast too.
            ExprKind::Ident(h) if h.path.len() == 1 => {
                let n = h.path[0].name.name.as_str();
                match params.get(n).and_then(|v| v.to_u64()) {
                    Some(v) => u32::try_from(v).ok()?,
                    None => TYPEDEFS_TLS
                        .with(|td| td.borrow().as_ref().and_then(|m| m.get(n).copied()))?,
                }
            }
            ExprKind::MemberAccess { expr: base, member } => {
                let ExprKind::Ident(h) = &base.kind else {
                    return None;
                };
                let scoped = format!("{}::{}", h.path.last()?.name.name, member.name);
                TYPEDEFS_TLS.with(|td| {
                    let b = td.borrow();
                    let m = b.as_ref()?;
                    m.get(&scoped)
                        .or_else(|| m.get(member.name.as_str()))
                        .copied()
                })?
            }
            _ => return None,
        },
        _ => return None,
    };
    (w > 0).then_some(w)
}

/// §20.6.2/§11.6.1: the self-determined width of a compound `$bits` operand
/// in a constant expression: `$bits(q_t'(1) + 1)`, `$bits({q_t'(1), 8'd2})`,
/// `$bits(c ? a : b)`, `$bits(f(1))`. A leaf (an identifier, member or
/// select) is answered by the `$bits` evaluator itself, a cast by its
/// target. None when a width is not known here.
pub(super) fn const_self_width<P: ParamLookup>(e: &Expression, params: &P) -> Option<u32> {
    use crate::ast::expr::{BinaryOp as B, UnaryOp as U};
    let leaf = |x: &Expression| -> Option<u32> {
        let call = Expression::new(
            ExprKind::SystemCall {
                name: "$bits".to_string(),
                args: vec![x.clone()],
            },
            x.span,
        );
        let w = const_eval_i64_with_params_env(&call, Some(params))
            .filter(|&w| w > 0)
            .or_else(|| eval_const_expr_val_inner(&call, params, &mut const_context::Types::default()).to_i64())?;
        u32::try_from(w).ok().filter(|&w| w > 0)
    };
    match &e.kind {
        ExprKind::Number(NumberLiteral::Integer { size: Some(s), .. }) => Some(*s),
        ExprKind::Number(n @ NumberLiteral::Integer { size: None, .. }) => {
            Some(number_literal_width(n))
        }
        ExprKind::Number(NumberLiteral::UnbasedUnsized(_)) => Some(1),
        ExprKind::Number(NumberLiteral::Real(_)) => Some(64),
        ExprKind::StringLiteral(t) => Some(8 * t.len().max(1) as u32),
        ExprKind::Paren(i) => const_self_width(i, params),
        ExprKind::SystemCall { name, .. } if is_cast_call(name) => const_cast_bits(e, params),
        // `$signed`/`$unsigned` keep the width (§11.7).
        ExprKind::SystemCall { name, args }
            if (name == "$signed" || name == "$unsigned") && args.len() == 1 =>
        {
            const_self_width(&args[0], params)
        }
        ExprKind::Concatenation(parts) => parts
            .iter()
            .try_fold(0u32, |t, x| t.checked_add(const_self_width(x, params)?)),
        ExprKind::Replication { count, exprs } => {
            let n = u32::try_from(const_eval_i64_with_params_env(count, Some(params))?).ok()?;
            exprs
                .iter()
                .try_fold(0u32, |t, x| t.checked_add(const_self_width(x, params)?))?
                .checked_mul(n)
        }
        ExprKind::Unary { op, operand } => match op {
            U::LogNot | U::BitAnd | U::BitNand | U::BitOr | U::BitNor | U::BitXor | U::BitXnor => {
                Some(1)
            }
            U::Plus | U::Minus | U::BitNot => const_self_width(operand, params),
            _ => None,
        },
        ExprKind::Binary { op, left, right } => match op {
            B::Eq
            | B::Neq
            | B::CaseEq
            | B::CaseNeq
            | B::WildcardEq
            | B::WildcardNeq
            | B::LogAnd
            | B::LogOr
            | B::LogImplies
            | B::LogEquiv
            | B::Lt
            | B::Leq
            | B::Gt
            | B::Geq => Some(1),
            B::ShiftLeft | B::ShiftRight | B::ArithShiftLeft | B::ArithShiftRight | B::Power => {
                const_self_width(left, params)
            }
            B::Add
            | B::Sub
            | B::Mul
            | B::Div
            | B::Mod
            | B::BitAnd
            | B::BitOr
            | B::BitXor
            | B::BitXnor => {
                Some(const_self_width(left, params)?.max(const_self_width(right, params)?))
            }
            _ => None,
        },
        ExprKind::Conditional {
            then_expr,
            else_expr,
            ..
        } => Some(const_self_width(then_expr, params)?.max(const_self_width(else_expr, params)?)),
        // §13.4.1: a function call has the width of its declared return type.
        ExprKind::Call { func, .. } => {
            let ExprKind::Ident(h) = &func.kind else {
                return None;
            };
            let name = h.path.last()?.name.name.as_str();
            let rt = FUNCS_TLS.with(|f| {
                let f = f.borrow();
                f.as_ref()?.get(name).map(|fd| fd.return_type.clone())
            })?;
            typedefs_snapshot(|td| Some(resolve_type_width_env(&rt, Some(params), td))).filter(|&w| w > 0)
        }
        ExprKind::Ident(_)
        | ExprKind::MemberAccess { .. }
        | ExprKind::Index { .. }
        | ExprKind::RangeSelect { .. } => leaf(e),
        _ => None,
    }
}

/// The constant-evaluator lowerings of a cast (§6.24.1).
pub(super) fn is_cast_call(name: &str) -> bool {
    matches!(
        name,
        "$__xz_size_cast" | "$__xz_type_cast" | "$__xz_named_cast"
    )
}

/// Append a type's packed dimensions, declared order preserved. Stops at the
/// first non-constant / unsized dimension.
fn push_packed_query_dims<P: ParamLookup>(
    dimensions: &[PackedDimension],
    params: Option<&P>,
    out: &mut Vec<(i64, i64)>,
) {
    for d in dimensions {
        let PackedDimension::Range { left, right, .. } = d else {
            return;
        };
        let (Some(l), Some(r)) = (
            const_eval_i64_with_params_env(left, params),
            const_eval_i64_with_params_env(right, params),
        ) else {
            return;
        };
        out.push((l, r));
    }
}

/// §20.7 over an explicit type — the packed shape of `dt`, following any
/// typedef chain. See `type_query_dims_by_name` for the name-keyed form.
pub fn type_query_dims_of<P: ParamLookup>(
    dt: &DataType,
    params: Option<&P>,
    typedefs: Option<&HashMap<String, u32>>,
    typedef_types: Option<&HashMap<String, DataType>>,
) -> TypeQueryDims {
    let mut q = TypeQueryDims::default();
    let mut cur = Some(dt.clone());
    for _ in 0..32 {
        let Some(t) = cur.take() else { break };
        match t {
            DataType::TypeReference {
                ref name,
                ref dimensions,
                ..
            } => {
                push_packed_query_dims(dimensions, params, &mut q.dims);
                cur = typedef_types.and_then(|m| m.get(&name.name.name).cloned());
                if cur.is_none() {
                    // The chain bottoms out on a typedef known only by width
                    // (an enum, or one whose definition was never registered).
                    let w = resolve_type_width_env(&t, params, typedefs);
                    if w > 0 && dimensions.is_empty() {
                        q.whole = Some((w as i64 - 1, 0));
                    }
                    break;
                }
            }
            DataType::IntegerVector { ref dimensions, .. }
            | DataType::Implicit { ref dimensions, .. } => {
                push_packed_query_dims(dimensions, params, &mut q.dims);
                break;
            }
            DataType::IntegerAtom { .. } => {
                let w = resolve_type_width_env(&t, params, typedefs).max(1);
                q.dims.push((w as i64 - 1, 0));
                break;
            }
            DataType::Enum(_) | DataType::Struct(_) => {
                // Neither an enum nor a packed struct/union has an array
                // dimension of its own, so `$dimensions` is 0 — but the bound
                // queries still describe its whole packed extent.
                let w = resolve_type_width_env(&t, params, typedefs);
                if w > 0 {
                    q.whole = Some((w as i64 - 1, 0));
                }
                break;
            }
            // real / string / chandle / event: no dimension to report.
            _ => break,
        }
    }
    q
}

/// §20.7 — resolve a type NAME used as an array-query operand (a built-in
/// type keyword or a typedef) into the dimensions it exposes. None when the
/// name does not denote a type.
///
/// `typedef_types` is optional so const-eval, which carries only the
/// name->width typedef table, can still answer: without it a typedef is
/// described by its width alone (`whole`), which gets the bound queries right
/// for every zero-based type but cannot report `$dimensions`.
pub fn type_query_dims_by_name<P: ParamLookup>(
    name: &str,
    params: Option<&P>,
    typedefs: Option<&HashMap<String, u32>>,
    typedef_types: Option<&HashMap<String, DataType>>,
    typedef_unpacked_dims: Option<&HashMap<String, Vec<UnpackedDimension>>>,
) -> Option<TypeQueryDims> {
    if let Some(w) = atom_keyword_width(name) {
        return Some(TypeQueryDims {
            dims: vec![(w as i64 - 1, 0)],
            unpacked: 0,
            whole: None,
        });
    }
    // A scalar `bit`/`logic`/`reg` has no packed dimension, and the
    // non-integral types have none either: every bound query answers `x`.
    if is_builtin_type_keyword(name) {
        return Some(TypeQueryDims::default());
    }
    let dt = typedef_types.and_then(|m| m.get(name));
    let width = typedefs.and_then(|m| m.get(name).copied());
    if dt.is_none() && width.is_none() {
        return None;
    }
    // §7.4.5: unpacked dimensions are numbered BEFORE the packed ones.
    let mut q = TypeQueryDims::default();
    if let Some(uds) = typedef_unpacked_dims.and_then(|m| m.get(name)) {
        for d in uds {
            match d {
                UnpackedDimension::Range { left, right, .. } => {
                    let (Some(l), Some(r)) = (
                        const_eval_i64_with_params_env(left, params),
                        const_eval_i64_with_params_env(right, params),
                    ) else {
                        break;
                    };
                    q.dims.push((l, r));
                }
                UnpackedDimension::Expression { expr, .. } => {
                    match const_eval_i64_with_params_env(expr, params) {
                        Some(n) if n > 0 => q.dims.push((0, n - 1)),
                        _ => break,
                    }
                }
                // A queue / dynamic / associative dimension has no static
                // bounds; §20.7 rejects such a type as a query operand.
                _ => break,
            }
            q.unpacked += 1;
        }
    }
    match dt {
        Some(dt) => {
            let inner = type_query_dims_of(dt, params, typedefs, typedef_types);
            q.dims.extend(inner.dims);
            q.whole = inner.whole;
        }
        // Known only by width (an enum typedef): its extent answers the bound
        // queries, and it contributes no dimension.
        None => {
            if let Some(w) = width.filter(|&w| w > 0) {
                q.whole = Some((w as i64 - 1, 0));
            }
        }
    }
    Some(q)
}

/// §20.7 — one array query over a resolved TYPE operand; `dim` is the 1-based
/// dimension number. None when that dimension does not exist, which §20.7
/// answers with `x`.
pub fn type_query_bound(sn: &str, q: &TypeQueryDims, dim: usize) -> Option<i64> {
    match sn {
        "$dimensions" => return Some(q.dims.len() as i64),
        "$unpacked_dimensions" => return Some(q.unpacked as i64),
        _ => {}
    }
    let (l, r) = match q.dims.get(dim.wrapping_sub(1)) {
        Some(&d) => d,
        None if dim == 1 && q.dims.is_empty() => q.whole?,
        None => return None,
    };
    let (lo, hi) = (l.min(r), l.max(r));
    Some(match sn {
        "$left" => l,
        "$right" => r,
        "$high" => hi,
        "$low" => lo,
        "$size" => hi - lo + 1,
        // §20.7: 1 for a descending range, -1 for an ascending one.
        "$increment" => {
            if l >= r {
                1
            } else {
                -1
            }
        }
        _ => return None,
    })
}

/// Full packed dimension bounds (outermost first) of a multi-dimensional
/// packed IntegerVector type — `logic [1:0][15:0][7:0]` returns
/// `Some([(1,0),(15,0),(7,0)])`. Single-dim / non-constant shapes return
/// None. Companion to `packed_inner_elem_width`; lets nested selects
/// (`a[i][j]`) resolve to correct flat bit slices per LRM §7.4.1.
pub fn packed_full_dims_of(
    dt: &DataType,
    params: &HashMap<String, Value>,
) -> Option<Vec<(i64, i64)>> {
    let dims = match dt {
        DataType::IntegerVector { dimensions, .. } => dimensions,
        // A declaration with packed ranges but NO type keyword — the common
        // `wire [1:0][7:0] w;` net form — parses as an IMPLICIT data type
        // (implicitly 4-state logic, §6.10). Its packed dimensions must be
        // recorded exactly like an explicit `logic [1:0][7:0]`, otherwise
        // element selects degrade to bit-selects and element continuous
        // assigns cannot resolve to a slice.
        DataType::Implicit { dimensions, .. } => dimensions,
        // §7.4.2 inline packed array of packed structs: the dims written after
        // the body are the element dims (each element is one struct); the
        // slot flatten only consumes leading dims, so these plug in directly.
        // Absent this arm a two-index select on such a local had no shape,
        // and the element read collapsed to one bit.
        DataType::Struct(su) if !su.dimensions.is_empty() => &su.dimensions,
        _ => return None,
    };
    if dims.is_empty() {
        return None;
    }
    let mut out = Vec::with_capacity(dims.len());
    for d in dims {
        if let PackedDimension::Range { left, right, .. } = d {
            let l = const_eval_i64_with_params(left, Some(params))?;
            let r = const_eval_i64_with_params(right, Some(params))?;
            out.push((l, r));
        } else {
            return None;
        }
    }
    // A single [w-1:0] dimension is the normalized default the query
    // functions already assume — recording it would be pure overhead. A
    // single NON-normalized dimension ([15:8], ascending [0:7]) must be
    // recorded so §20.7 array queries report the DECLARED bounds.
    if out.len() == 1 {
        let (l, r) = out[0];
        if r == 0 && l >= 0 {
            return None;
        }
    }
    Some(out)
}

/// §7.4.2: detect a PACKED ARRAY of packed struct — `row_entry_t [1:0] x;`
/// (TypeReference with packed dims whose typedef chain lands on a packed
/// struct) or `struct packed {...} [1:0] x;` (body-suffix dims). Walks the
/// typedef chain accumulating packed dims outermost-first and returns
/// `(dims, element_struct_type)` when at least one array dim was found.
pub fn packed_struct_array_info(
    dt: &DataType,
    params: &HashMap<String, Value>,
    typedef_types: &HashMap<String, DataType>,
) -> Option<(Vec<(i64, i64)>, DataType)> {
    packed_struct_array_info_env(dt, params, typedef_types)
}

pub(super) fn packed_struct_array_info_env(
    dt: &DataType,
    params: &dyn ParamLookup,
    typedef_types: &HashMap<String, DataType>,
) -> Option<(Vec<(i64, i64)>, DataType)> {
    let mut dims: Vec<(i64, i64)> = Vec::new();
    let mut cur: DataType = dt.clone();
    for _ in 0..64 {
        match cur {
            DataType::TypeReference {
                ref name,
                ref dimensions,
                ..
            } => {
                for d in dimensions {
                    if let PackedDimension::Range { left, right, .. } = d {
                        let l = const_eval_i64_with_params_env(left, Some(&params))?;
                        let r = const_eval_i64_with_params_env(right, Some(&params))?;
                        dims.push((l, r));
                    } else {
                        return None;
                    }
                }
                let next = typedef_types.get(&name.name.name)?.clone();
                cur = next;
            }
            DataType::Struct(ref su) => {
                if !su.packed {
                    return None;
                }
                for d in &su.dimensions {
                    if let PackedDimension::Range { left, right, .. } = d {
                        let l = const_eval_i64_with_params_env(left, Some(&params))?;
                        let r = const_eval_i64_with_params_env(right, Some(&params))?;
                        dims.push((l, r));
                    } else {
                        return None;
                    }
                }
                if dims.is_empty() {
                    return None;
                }
                let mut elem = su.clone();
                elem.dimensions.clear();
                return Some((dims, DataType::Struct(elem)));
            }
            _ => return None,
        }
    }
    None
}

/// Bit offset (from the LSB of the whole packed array) of the element at
/// `idx` (one index per dim, outermost first), given the array `dims` and
/// per-element width. The LEFT bound of each dim labels the most-significant
/// element (§7.4.1). Returns None when any index is out of bounds.
pub fn packed_elem_lsb_offset(dims: &[(i64, i64)], idx: &[i64], elem_w: u32) -> Option<u32> {
    let counts: Vec<u64> = dims
        .iter()
        .map(|(l, r)| (l - r).unsigned_abs() + 1)
        .collect();
    let total: u64 = counts.iter().product::<u64>() * elem_w as u64;
    let mut msb_off: u64 = 0;
    for (j, &i) in idx.iter().enumerate() {
        let (l, r) = dims[j];
        let (lo_b, hi_b) = if l <= r { (l, r) } else { (r, l) };
        if i < lo_b || i > hi_b {
            return None;
        }
        let slot = if l >= r {
            (l - i) as u64
        } else {
            (i - l) as u64
        };
        let w_j: u64 = counts[j + 1..].iter().product::<u64>() * elem_w as u64;
        msb_off += slot * w_j;
    }
    Some((total - msb_off - elem_w as u64) as u32)
}

/// §7.4.2 — packed dimensions applied to a STRUCT/TYPEDEF base
/// (`some_t [0:0][1:0] arr;`). `packed_full_dims_of` and
/// `packed_inner_elem_width` only understand `IntegerVector`/`Implicit`, so a
/// typedef base registered nothing and `arr[i]` degraded to a 1-BIT select
/// (`$bits(arr[0])` came back 1 instead of the struct width). Model the struct
/// as one extra trailing `[base_w-1:0]` dimension: the ordinary element-select
/// machinery then applies unchanged, so `arr[i]` strips the outer dimension and
/// keeps the rest (`arr2[0]` = the whole `[1:0]` sub-array, `arr2[0][0]` = one
/// struct).
pub(super) fn packed_typedef_array_dims(
    dt: &DataType,
    base_w: u32,
    params: &HashMap<String, Value>,
) -> Option<Vec<(i64, i64)>> {
    let DataType::TypeReference { dimensions, .. } = dt else {
        return None;
    };
    if dimensions.is_empty() || base_w == 0 {
        return None;
    }
    let mut out: Vec<(i64, i64)> = Vec::with_capacity(dimensions.len() + 1);
    for d in dimensions {
        let PackedDimension::Range { left, right, .. } = d else {
            return None;
        };
        let l = const_eval_i64_with_params(left, Some(params))?;
        let r = const_eval_i64_with_params(right, Some(params))?;
        out.push((l, r));
    }
    out.push((base_w as i64 - 1, 0));
    Some(out)
}

pub fn packed_inner_elem_width(
    dt: &DataType,
    params: &HashMap<String, Value>,
    typedefs: &HashMap<String, u32>,
) -> Option<u32> {
    // §7.4.1 packed array whose ELEMENT type is a typedef (`u32_t [4:0] x`).
    // The element width is the typedef's own width — it is not visible in the
    // declaration's dimensions, which carry only the array index range. This
    // used to return None ("callers resolve via their own context"), but no
    // caller did, so the element width defaulted to one bit and `x[i] <= v`
    // wrote a single BIT: `u32_t [4:0] SEC; SEC[0] <= 32'hDEAD_BEEF` stored 1.
    // The equivalent inline form (`logic [4:0][31:0]`) was always correct,
    // which is what made this look like a struct-member problem — a packed
    // array member of a packed struct is simply the commonest way to hit it.
    let resolved: &DataType = if let DataType::TypeReference {
        name, dimensions, ..
    } = dt
    {
        // No array dims => not an element select at all (`u32_t x; x[i]` is a
        // bit select of the typedef's own vector).
        if dimensions.is_empty() {
            return None;
        }
        let base = typedefs.get(&name.name.name).copied().filter(|w| *w > 0)?;
        // Same rule as below: total = base * every dim, element = total / outer.
        // With several dims (`u32_t [1:0][3:0] y`) an element of the outermost
        // is the whole remaining sub-array.
        let mut total = base;
        for d in dimensions {
            let PackedDimension::Range { left, right, .. } = d else {
                return None;
            };
            let l = const_eval_i64_with_params(left, Some(params))?;
            let r = const_eval_i64_with_params(right, Some(params))?;
            total = total.checked_mul(((l - r).abs() + 1) as u32)?;
        }
        let PackedDimension::Range { left, right, .. } = dimensions.first()? else {
            return None;
        };
        let l = const_eval_i64_with_params(left, Some(params))?;
        let r = const_eval_i64_with_params(right, Some(params))?;
        let outer = ((l - r).abs() + 1) as u32;
        if outer == 0 {
            return None;
        }
        return Some(total / outer);
    } else {
        dt
    };
    // §7.4.2 packed array of packed STRUCTS written inline
    // (`struct packed {…} [1:0] a`): the element is one struct; the outer
    // dims after the body count elements. Absent this arm the element width
    // fell to one bit — `a[1] = '{…}` stored a single bit and `a[0].m` read x —
    // and a typedef'd form folded into this shape by the submodule-local
    // typedef substitution broke the same way.
    if let DataType::Struct(su) = resolved {
        if su.dimensions.is_empty() {
            return None;
        }
        let mut no_dims = su.clone();
        no_dims.dimensions.clear();
        let elem = resolve_type_width(&DataType::Struct(no_dims), Some(params), Some(typedefs));
        if elem == 0 {
            return None;
        }
        // Several outer dims: an element of the outermost is the remaining
        // sub-array, same rule as the vector case below.
        let mut inner = elem;
        for d in su.dimensions.iter().skip(1) {
            let PackedDimension::Range { left, right, .. } = d else {
                return None;
            };
            let l = const_eval_i64_with_params(left, Some(params))?;
            let r = const_eval_i64_with_params(right, Some(params))?;
            inner = inner.checked_mul(((l - r).abs() + 1) as u32)?;
        }
        return Some(inner);
    }
    if let DataType::IntegerVector { dimensions, .. } | DataType::Implicit { dimensions, .. } =
        resolved
    {
        if dimensions.len() < 2 {
            return None;
        }
        // Total width = product of all dims
        let mut total = 1u32;
        for d in dimensions {
            if let PackedDimension::Range { left, right, .. } = d {
                let lv = const_eval_i64_with_params(left, Some(params));
                let rv = const_eval_i64_with_params(right, Some(params));
                if let (Some(l), Some(r)) = (lv, rv) {
                    total *= ((l - r).abs() + 1) as u32;
                } else {
                    return None;
                }
            } else {
                return None;
            }
        }
        // Outermost (leftmost) dim is the element-array index; element width
        // is total / outer_count per LRM §7.4.1.
        if let Some(PackedDimension::Range { left, right, .. }) = dimensions.first() {
            let lv = const_eval_i64_with_params(left, Some(params));
            let rv = const_eval_i64_with_params(right, Some(params));
            if let (Some(l), Some(r)) = (lv, rv) {
                let outer = ((l - r).abs() + 1) as u32;
                if outer == 0 {
                    return None;
                }
                return Some(total / outer);
            }
        }
    }
    None
}

/// §7.2, §7.4.1: record `packed_member_meta` of every member of the packed
/// struct `dt` under `<sig>.<member>`, keeping what is already there.
/// `params` is the declaring scope's (the module's own when None).
pub(super) fn register_member_packed_meta(
    elab: &mut ElaboratedModule,
    sig: &str,
    dt: &DataType,
    params: Option<&HashMap<String, Value>>,
) {
    let DataType::Struct(su) = resolve_typedef_chain(dt, &elab.typedef_types) else {
        return;
    };
    let params = params.unwrap_or(&elab.parameters);
    let mut metas = Vec::new();
    for m in &su.members {
        let (ew, fd) =
            packed_member_meta(&m.data_type, params, &elab.typedefs, &elab.typedef_types);
        for mdecl in &m.declarators {
            metas.push((format!("{sig}.{}", mdecl.name.name), ew, fd.clone()));
        }
    }
    for (key, ew, fd) in metas {
        if let Some(ew) = ew {
            elab.packed_signal_elem_widths
                .entry(key.clone())
                .or_insert(ew);
        }
        if let Some(fd) = fd {
            elab.packed_full_dims.entry(key).or_insert(fd);
        }
    }
}

/// §7.2, §7.4.1: the packed-array shape of a struct MEMBER declared with
/// `dt`, as the runtime keys it under `<signal>.<member>`: the element width
/// of its outermost dimension and every packed dimension (outermost first,
/// the element's own bit range innermost). A member whose element type is a
/// typedef (`t3_t [1:0][3:0][7:0] f0`) or whose dimensions live inside the
/// typedef (`t3d_t f0`) has them only through the typedef chain;
/// `packed_full_dims_of` sees the declaration alone, so with it only the
/// first index of `s.f0[i][j]` selected an element and every later one was a
/// one-bit select of the row.
pub fn packed_member_meta(
    dt: &DataType,
    params: &HashMap<String, Value>,
    typedefs: &HashMap<String, u32>,
    typedef_types: &HashMap<String, DataType>,
) -> (Option<u32>, Option<Vec<(i64, i64)>>) {
    let fd = packed_full_dims_of(dt, params)
        .or_else(|| packed_full_dims_chained(dt, params, typedef_types))
        .or_else(|| {
            // §7.4.1: dimensions following a struct/enum body select whole
            // aggregate elements. Add the element's bit range after them.
            let mut dims = Vec::new();
            let mut cur = dt;
            for _ in 0..64 {
                let base = match cur {
                    DataType::TypeReference { name, dimensions, .. } => {
                        dims.extend(dimensions.iter().cloned());
                        cur = lookup_scoped_type(name, typedef_types)?;
                        continue;
                    }
                    DataType::Struct(su) if su.packed => {
                        dims.extend(su.dimensions.iter().cloned());
                        let mut su = su.clone();
                        su.dimensions.clear();
                        DataType::Struct(su)
                    }
                    DataType::Enum(en) => {
                        dims.extend(en.dimensions.iter().cloned());
                        let mut en = en.clone();
                        en.dimensions.clear();
                        DataType::Enum(en)
                    }
                    _ => return None,
                };
                if dims.is_empty() { return None; }
                let w = resolve_type_width(&base, Some(params), Some(typedefs)).max(1);
                let mut bounds = Vec::new();
                for d in &dims {
                    let PackedDimension::Range { left, right, .. } = d else { return None; };
                    bounds.push((const_eval_i64_with_params(left, Some(params))?,
                                 const_eval_i64_with_params(right, Some(params))?));
                }
                bounds.push((i64::from(w) - 1, 0));
                return Some(bounds);
            }
            None
        });
    let ew = packed_inner_elem_width(dt, params, typedefs).or_else(|| {
        // An element of the outermost dimension spans all the others.
        let dims = fd.as_ref().filter(|d| d.len() >= 2)?;
        dims[1..].iter().try_fold(1u32, |w, (l, r)| {
            w.checked_mul(u32::try_from((l - r).unsigned_abs() + 1).ok()?)
        })
    });
    (ew, fd)
}

/// §5.9: a string literal is 8 bits per character, and an empty one still
/// occupies a byte, so `parameter P = "untyped"` keeps all its text.
pub(super) fn string_literal_width(init: &Expression) -> Option<u32> {
    match &init.kind {
        ExprKind::StringLiteral(s) => Some(Value::from_string(s).width.max(8)),
        _ => None,
    }
}

/// §6.20.2: a parameter with no type and no range takes the type of its
/// final value — the SELF-DETERMINED width (§11.6.1, Table 11-21) of its
/// initializer. Known for literals (sized, unsized at least 32, string 8 per
/// character), other parameters in `params`, and the operators whose result
/// width follows from their operands'. `None` when an operand's width is not
/// known here (a function call, an element select, a cast), which keeps the
/// 32-bit default. Only sized literals were handled, so `localparam C =
/// {8'h1, 8'h2}` was 32 bits where the reference simulator gives 16.
pub fn untyped_param_width(e: &Expression, params: &HashMap<String, Value>) -> Option<u32> {
    let w = |x: &Expression| untyped_param_width(x, params);
    match &e.kind {
        ExprKind::Number(NumberLiteral::Integer {
            size,
            signed,
            base,
            value,
            ..
        }) => {
            let radix = match base {
                NumberBase::Binary => 2,
                NumberBase::Octal => 8,
                NumberBase::Hex => 16,
                NumberBase::Decimal => 10,
            };
            Some(size.unwrap_or_else(|| Value::unsized_integer_width(value, radix, *signed)))
        }
        ExprKind::StringLiteral(t) if !t.is_empty() && !t.contains('\\') => {
            Some(8 * t.len() as u32)
        }
        ExprKind::Ident(h) if h.root.is_none() && h.path.len() == 1 => {
            if !h.path[0].selects.is_empty() {
                return None;
            }
            let raw = h.path[0].name.name.as_str();
            let name = crate::sv_parser::strip_unit_scope_name(raw).unwrap_or(raw);
            params
                .get(raw)
                .or_else(|| params.get(name))
                .filter(|v| !v.is_real)
                .map(|v| v.width)
        }
        // `pkg::P`
        ExprKind::MemberAccess { expr, member } => match &expr.kind {
            ExprKind::Ident(h) if h.root.is_none() && h.path.len() == 1 => params
                .get(&format!("{}::{}", h.path[0].name.name, member.name))
                .filter(|v| !v.is_real)
                .map(|v| v.width),
            _ => None,
        },
        ExprKind::Paren(inner) => w(inner),
        // §11.4.3: unary +/- keeps the operand's size, so `localparam P =
        // -4'sd1` is 4 bits (ivtest localparam_type2 nnvm1/snvm1).
        ExprKind::Unary { op, operand } => match op {
            UnaryOp::Plus | UnaryOp::Minus | UnaryOp::BitNot => w(operand),
            UnaryOp::LogNot
            | UnaryOp::BitAnd
            | UnaryOp::BitNand
            | UnaryOp::BitOr
            | UnaryOp::BitNor
            | UnaryOp::BitXor
            | UnaryOp::BitXnor => Some(1),
            _ => None,
        },
        ExprKind::Binary { op, left, right } => match op {
            BinaryOp::Add
            | BinaryOp::Sub
            | BinaryOp::Mul
            | BinaryOp::Div
            | BinaryOp::Mod
            | BinaryOp::BitAnd
            | BinaryOp::BitOr
            | BinaryOp::BitXor
            | BinaryOp::BitXnor => Some(w(left)?.max(w(right)?)),
            BinaryOp::Eq
            | BinaryOp::Neq
            | BinaryOp::CaseEq
            | BinaryOp::CaseNeq
            | BinaryOp::WildcardEq
            | BinaryOp::WildcardNeq
            | BinaryOp::Lt
            | BinaryOp::Leq
            | BinaryOp::Gt
            | BinaryOp::Geq
            | BinaryOp::LogAnd
            | BinaryOp::LogOr
            | BinaryOp::LogImplies
            | BinaryOp::LogEquiv => Some(1),
            BinaryOp::ShiftLeft
            | BinaryOp::ShiftRight
            | BinaryOp::ArithShiftLeft
            | BinaryOp::ArithShiftRight
            | BinaryOp::Power => w(left),
            _ => None,
        },
        ExprKind::Conditional {
            then_expr,
            else_expr,
            ..
        } => Some(w(then_expr)?.max(w(else_expr)?)),
        ExprKind::Concatenation(parts) => parts.iter().map(w).sum(),
        ExprKind::Replication { count, exprs } => {
            let n = const_eval_i64_with_params(count, Some(params))?;
            let inner: u32 = exprs.iter().map(w).sum::<Option<u32>>()?;
            u32::try_from(n).ok()?.checked_mul(inner).filter(|&t| t > 0)
        }
        ExprKind::RangeSelect {
            kind, left, right, ..
        } => match kind {
            RangeKind::Constant => {
                let l = const_eval_i64_with_params(left, Some(params))?;
                let r = const_eval_i64_with_params(right, Some(params))?;
                u32::try_from((l - r).abs() + 1).ok()
            }
            RangeKind::IndexedUp | RangeKind::IndexedDown => {
                u32::try_from(const_eval_i64_with_params(right, Some(params))?).ok()
            }
        },
        ExprKind::SystemCall { name, args } => match name.as_str() {
            "$signed" | "$unsigned" => w(args.first()?),
            "$clog2" | "$bits" | "$size" | "$countones" => Some(32),
            _ => None,
        },
        // §11.4.13: `inside` is one bit.
        ExprKind::Inside { .. } => Some(1),
        // §6.20.2, §13.4.1: a call has its function's declared return type.
        ExprKind::Call { func, .. } => const_context::function_type_resolved(func, params)
            .filter(|t| t.integral)
            .map(|t| t.width),
        _ => None,
    }
}
