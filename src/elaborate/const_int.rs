use super::*;

/// The first UNPACKED dimension of a declarator as inclusive `(lo, hi)` bounds,
/// when both ends const-evaluate. `[N]` is `0..N-1`; `[l:r]` is normalized
/// ascending so the result matches `ElaboratedClass::array_properties`, which
/// stores `(l.min(r), l.max(r), width)`.
pub(super) fn const_unpacked_bounds(
    dims: &[UnpackedDimension],
    params: Option<&HashMap<String, Value>>,
) -> Option<(i64, i64)> {
    let (left, right) = const_unpacked_decl_bounds(dims, params)?;
    Some((left.min(right), left.max(right)))
}

/// §7.4.2 / §10.9.1: retain the left bound for positional array initializers.
pub(super) fn const_unpacked_decl_bounds(
    dims: &[UnpackedDimension],
    params: Option<&HashMap<String, Value>>,
) -> Option<(i64, i64)> {
    match dims.first()? {
        UnpackedDimension::Expression { expr, .. } => {
            match const_eval_i64_with_params(expr, params) {
                Some(n) if n > 0 => Some((0, n - 1)),
                _ => None,
            }
        }
        UnpackedDimension::Range { left, right, .. } => {
            let l = const_eval_i64_with_params(left, params)?;
            let r = const_eval_i64_with_params(right, params)?;
            Some((l, r))
        }
        // `[N]` with a bare identifier is grammatically ambiguous: a TYPE name
        // makes it associative, a CONSTANT makes it a size. The parser cannot
        // decide and always yields `Associative`. Inside a `localparam` array
        // the name is a size whenever it evaluates in the class constant scope
        // — an associative localparam has no meaning, since it could not be
        // positionally initialized by the `'{...}` it is required to carry.
        UnpackedDimension::Associative {
            data_type: Some(dt),
            ..
        } => {
            if let Some(UnpackedDimension::Expression { expr, .. }) =
                params.and_then(|p| scoped_const_dim(&dims[0], p))
            {
                let n = const_eval_i64_with_params(&expr, params)?;
                return (n > 0).then(|| (0, n - 1));
            }
            let nm = get_type_name(dt)?;
            let n = params?.get(&nm)?.to_u64()? as i64;
            if n > 0 { Some((0, n - 1)) } else { None }
        }
        _ => None,
    }
}

/// §13.4.3: interpret a user constant-function call against FUNCS_TLS and
/// return its result at the function's DECLARED return type (width and
/// signedness, or real). None when the call's shape, the function or any
/// argument cannot be resolved — callers keep their prior fallback.
pub(super) fn const_eval_user_call(
    expr: &Expression,
    params: Option<&HashMap<String, Value>>,
) -> Option<Value> {
    let ExprKind::Call { func, args } = &expr.kind else {
        return None;
    };
    // A SCOPED call (`p::LOG2(64)`) reaches here as either a 2-segment Ident
    // or MemberAccess{Ident(p), LOG2} — resolve the qualified registration
    // first so the right package's fn wins.
    let (fname, scoped_key) = match &func.kind {
        ExprKind::Ident(h) => {
            let leaf = h.path.last().map(|s| s.name.name.clone())?;
            let sk = (h.path.len() >= 2)
                .then(|| format!("{}::{}", h.path[h.path.len() - 2].name.name, leaf));
            (leaf, sk)
        }
        ExprKind::MemberAccess { expr: base, member } => {
            let sk = match &base.kind {
                ExprKind::Ident(bh) if bh.path.len() == 1 => {
                    Some(format!("{}::{}", bh.path[0].name.name, member.name))
                }
                _ => None,
            };
            (member.name.clone(), sk)
        }
        _ => return None,
    };
    let funcs = FUNCS_TLS.with(|cell| {
        cell.borrow()
            .as_ref()
            .filter(|m| {
                scoped_key.as_deref().is_some_and(|k| m.contains_key(k)) || m.contains_key(&fname)
            })
            .cloned()
    })?;
    let fd = scoped_key
        .as_deref()
        .and_then(|k| funcs.get(k))
        .or_else(|| funcs.get(&fname))
        .cloned()?;
    let mut shell = ElaboratedModule::new(String::new());
    if let Some(p) = params {
        shell.parameters = p.clone();
    }
    shell.functions = FuncTable::from_shared(Rc::clone(&funcs));
    // Generate-if conditions reach this shell with no typedef table. A formal
    // `fmt_unit_types_t` then has no element width, so `types[i] == MERGED`
    // reads a bit and the merged opgroup is not generated. The localparam
    // path uses the module elaboration, which already has the types.
    if let Some(types) = TYPEDEF_TYPES_TLS.with(|c| c.borrow().clone()) {
        shell.typedef_types = types;
    }
    // Widths too: a missing entry makes `resolve_type_width` answer 32, and
    // the actual is zero-extended. An ascending `[0:N]` index then reads the
    // top of that 32-bit word (zeros) instead of element 0.
    if let Some(widths) = TYPEDEF_WIDTHS_TLS.with(|c| c.borrow().clone()) {
        shell.typedefs = TypedefTable::from_shared(widths);
    }
    let mut argv = Vec::with_capacity(args.len());
    for a in args {
        // A pattern actual of a packed-struct formal (#680), as in a constant.
        if let Some(v) =
            const_fn_struct_pattern_actual(fd.ports.get(argv.len()), a, Some(&shell.parameters), &shell)
        {
            argv.push(v);
            continue;
        }
        let folded = substitute_const_fn_calls(a,Some(&shell.parameters), &shell, 0)?;
        if expr_has_call(&folded) || !is_const_expr(&folded, &shell.parameters) {
            return None;
        }
        // §13.4.3: actuals retain width, signedness, realness and X/Z until
        // conversion to the formal; an i64/32-bit bridge loses those values.
        argv.push(const_function_actual(
            fd.ports.get(argv.len()),
            &folded,
            Some(&shell.parameters),
            &shell,
        ));
    }
    // §13.4.3/§6.24.1: the function casts to the typedefs of the scope
    // that declares it: its package (registered as `pkg::f` with this
    // body), else, called from an instance that does not declare it, `$unit`.
    let owner = match scoped_key.as_deref().and_then(|k| k.split_once("::")) {
        Some((pkg, _)) => Some(pkg.to_string()),
        None => funcs
            .iter()
            .filter(|(k, f)| {
                f.span == fd.span && k.split_once("::").is_some_and(|(_, leaf)| leaf == fname)
            })
            .map(|(k, _)| {
                k.split_once("::")
                    .map_or(k.as_str(), |(pkg, _)| pkg)
                    .to_string()
            })
            .min(),
    };
    let foreign = owner.is_none()
        && CONST_FN_LOCAL_FUNCS
            .with(|c| c.borrow().as_ref().is_some_and(|own| !own.contains(&fname)));
    let prev_in_unit = CONST_FN_IN_UNIT.with(|c| c.replace(foreign));
    let prev_owner = CONST_FN_PACKAGE.with(|c| c.replace(owner));
    let v = eval_const_user_function(&fd, &argv, Some(&shell.parameters), &shell, 0);
    CONST_FN_PACKAGE.with(|c| *c.borrow_mut() = prev_owner);
    CONST_FN_IN_UNIT.with(|c| c.set(prev_in_unit));
    v
}


/// Candidate ENV KEYS for the base of a constant `base[index]` element
/// select. `register_array_param` stores each element of an unpacked-array
/// parameter under `base[idx]`: bare (`LIM[i]`) at module scope, scoped
/// (`pkg::LIM[i]`, the `alias_pkg_param` spelling) for package parameters,
/// dotted (`u.mod.A[i]`) for inlined instances. A scoped reference parses
/// either as a multi-segment Ident or as a MemberAccess, so enumerate the
/// `::` and `.` spellings (bare leaf last, matching the existing bare-leaf
/// fallback for Ident bases).
pub(crate) fn const_index_base_keys<P: ParamLookup>(
    e: &Expression,
    params: Option<&P>,
    out: &mut Vec<String>,
) {
    match &e.kind {
        ExprKind::Ident(h) if h.path.iter().all(|s| s.selects.is_empty()) => {
            let segs: Vec<&str> = h.path.iter().map(|s| s.name.name.as_str()).collect();
            if segs.len() > 1 {
                out.push(segs.join("::"));
                out.push(segs.join("."));
            }
            if segs.len() == 1
                && let Some(last) = segs.last()
            {
                out.push((*last).to_string());
            }
        }
        ExprKind::MemberAccess { expr, member } => {
            let mut subs = Vec::new();
            const_index_base_keys(expr, params, &mut subs);
            for s in subs {
                out.push(format!("{}::{}", s, member.name));
                out.push(format!("{}.{}", s, member.name));
            }
        }
        ExprKind::Index { expr, index } => {
            if let Some(index) = const_eval_i64_with_params_env(index, params) {
                let mut bases = Vec::new();
                const_index_base_keys(expr, params, &mut bases);
                out.extend(bases.into_iter().map(|base| format!("{base}[{index}]")));
            }
        }
        ExprKind::Paren(inner) => const_index_base_keys(inner, params, out),
        _ => {}
    }
}

/// Full spelling of a hierarchical path with constant selects, for parameter
/// lookup and member-wise storage. Retain every selected instance or element.
pub(super) fn const_parameter_path<P: ParamLookup>(
    expr: &Expression,
    params: Option<&P>,
) -> Option<String> {
    match &expr.kind {
        ExprKind::Ident(h) => {
            let mut path = String::new();
            for (i, segment) in h.path.iter().enumerate() {
                if i > 0 {
                    path.push('.');
                }
                path.push_str(&segment.name.name);
                for select in &segment.selects {
                    let index = const_eval_i64_with_params_env(select, params)?;
                    path.push_str(&format!("[{index}]"));
                }
            }
            Some(path)
        }
        ExprKind::MemberAccess { expr, member } => Some(format!(
            "{}.{}",
            const_parameter_path(expr, params)?,
            member.name
        )),
        ExprKind::Index { expr, index } => Some(format!(
            "{}[{}]",
            const_parameter_path(expr, params)?,
            const_eval_i64_with_params_env(index, params)?
        )),
        ExprKind::Paren(inner) => const_parameter_path(inner, params),
        _ => None,
    }
}

/// §5.7.1, §11.6.1, §11.8.2: fold literal-only pattern keys with their
/// widths and signedness. Other expressions retain the scalar evaluator.
/// Bounds only guard admission; they do not supply an expression context.
pub fn const_eval_pattern_index(
    expr: &Expression,
    params: Option<&HashMap<String, Value>>,
    bounds: (i64, i64),
) -> Option<i64> {
    let p_dyn = params.map(|p| p as &dyn ParamLookup);
    const_eval_pattern_index_env(expr, p_dyn.as_ref(), bounds)
}

pub(super) fn const_eval_pattern_index_env<P: ParamLookup>(
    expr: &Expression,
    params: Option<&P>,
    bounds: (i64, i64),
) -> Option<i64> {
    const_eval_typed_pattern_index_env(expr, params, bounds)
        .or_else(|| const_eval_i64_with_params_env(expr, params))
}

/// The typed part of pattern-index evaluation; callers keep their own fallback.
pub fn const_eval_literal_pattern_index(expr: &Expression, bounds: (i64, i64)) -> Option<i64> {
    const_eval_typed_pattern_index_env::<HashMap<String, Value>>(expr, None, bounds)
}

/// [`const_eval_literal_pattern_index`] whose leaves may also be integral
/// parameters bound in `params` (bare, or `pkg::NAME`): a parameter has its
/// declared width and sign (§6.20.2), so `'{(F + 4'd1): v}` over a 4-bit `F`
/// of 15 keys element 0 (§11.6.1).
pub fn const_eval_typed_pattern_index(
    expr: &Expression,
    params: Option<&HashMap<String, Value>>,
    bounds: (i64, i64),
) -> Option<i64> {
    const_eval_typed_pattern_index_env(expr, params, bounds)
}

fn const_eval_typed_pattern_index_env<P: ParamLookup>(
    expr: &Expression,
    params: Option<&P>,
    bounds: (i64, i64),
) -> Option<i64> {
    fn literals<P: ParamLookup>(
        e: &Expression,
        params: Option<&P>,
        max_width: u32,
    ) -> Option<()> {
        let literals = |e: &Expression, max_width: u32| literals(e, params, max_width);
        match &e.kind {
            // §6.20, §26.3: a parameter operand has its declared type.
            ExprKind::Ident(h)
                if h.root.is_none()
                    && (1..=2).contains(&h.path.len())
                    && h.path.iter().all(|s| s.selects.is_empty()) =>
            {
                let name = &h.path.last()?.name.name;
                let key = match h.path.len() {
                    1 => name.clone(),
                    _ => format!("{}::{}", h.path[0].name.name, name),
                };
                let v = params?.get(&key)?;
                (!v.is_real
                    && !v.has_xz()
                    && !tls_is_string_param(name)
                    && v.width > 0
                    && v.width <= max_width)
                    .then_some(())
            }
            // `pkg::NAME` parses as a member access of the package name.
            ExprKind::MemberAccess { expr: base, member } => {
                let ExprKind::Ident(h) = &base.kind else {
                    return None;
                };
                if h.root.is_some() || h.path.len() != 1 || !h.path[0].selects.is_empty() {
                    return None;
                }
                let v = params?.get(&format!("{}::{}", h.path[0].name.name, member.name))?;
                (!v.is_real
                    && !v.has_xz()
                    && !tls_is_string_param(&member.name)
                    && v.width > 0
                    && v.width <= max_width)
                    .then_some(())
            }
            // §11.7: the sign casts keep their operand's width.
            ExprKind::SystemCall { name, args }
                if matches!(name.as_str(), "$signed" | "$unsigned") && args.len() == 1 =>
            {
                literals(&args[0], max_width)
            }
            ExprKind::Number(NumberLiteral::Integer {
                size, signed, base, value, ..
            }) => {
                let radix = match base {
                    NumberBase::Binary => 2,
                    NumberBase::Octal => 8,
                    NumberBase::Decimal => 10,
                    NumberBase::Hex => 16,
                };
                let digits = value.replace('_', "");
                let digits = u64::from_str_radix(&digits, radix)
                    .or_else(|_| i64::from_str_radix(&digits, radix).map(|v| v as u64))
                    .ok()?;
                let width = size.unwrap_or(32);
                // Keep large unsized values on the general evaluator so
                // this scalar folding path cannot truncate their magnitude.
                let unsized_max = if *signed && matches!(base, NumberBase::Decimal) {
                    i32::MAX as u64
                } else {
                    u32::MAX as u64
                };
                (width > 0 && width <= max_width && (size.is_some() || digits <= unsized_max))
                    .then_some(())
            }
            ExprKind::Paren(inner) => literals(inner, max_width),
            ExprKind::Unary {
                op: UnaryOp::Plus | UnaryOp::Minus | UnaryOp::BitNot | UnaryOp::LogNot,
                operand,
            } => literals(operand, max_width),
            ExprKind::Binary { op, left, right }
                if matches!(
                    op,
                    BinaryOp::Add
                        | BinaryOp::Sub
                        | BinaryOp::Mul
                        | BinaryOp::Div
                        | BinaryOp::Mod
                        | BinaryOp::BitAnd
                        | BinaryOp::BitOr
                        | BinaryOp::BitXor
                        | BinaryOp::BitXnor
                        | BinaryOp::ShiftLeft
                        | BinaryOp::ShiftRight
                        | BinaryOp::ArithShiftLeft
                        | BinaryOp::ArithShiftRight
                        | BinaryOp::Eq
                        | BinaryOp::Neq
                        | BinaryOp::CaseEq
                        | BinaryOp::CaseNeq
                        | BinaryOp::Lt
                        | BinaryOp::Leq
                        | BinaryOp::Gt
                        | BinaryOp::Geq
                ) =>
            {
                literals(left, max_width)?;
                // §11.4.10: counts are unsigned and self-determined. The
                // typed evaluator narrows them to u32; retain the old path
                // when the count's tree can have more than 32 bits.
                let shift = matches!(
                    op,
                    BinaryOp::ShiftLeft
                        | BinaryOp::ShiftRight
                        | BinaryOp::ArithShiftLeft
                        | BinaryOp::ArithShiftRight
                );
                literals(right, if shift { 32 } else { max_width })
            }
            ExprKind::Conditional {
                condition,
                then_expr,
                else_expr,
            } => {
                literals(condition, max_width)?;
                literals(then_expr, max_width)?;
                literals(else_expr, max_width)
            }
            _ => None,
        }
    }
    if literals(expr, params, 64).is_some() {
        let empty = HashMap::default();
        let value = match params {
            Some(p) => eval_const_expr_val_inner(expr, p, &mut const_context::Types::default()),
            None => eval_const_expr_val(expr, &empty),
        };
        // Preserve the old index conversion for unsigned high-bit 32-bit
        // keys, and the old fallback for unresolved or out-of-range keys.
        let unsigned_max = if value.width == 32 {
            i32::MAX as u64
        } else {
            i64::MAX as u64
        };
        if (value.is_signed || value.to_u64().is_some_and(|v| v <= unsigned_max))
            && let Some(index) = value.to_index()
            && (bounds.0.min(bounds.1)..=bounds.0.max(bounds.1)).contains(&index)
        {
            return Some(index);
        }
    }
    None
}

pub fn const_eval_i64_with_params_env<P: ParamLookup>(
    expr: &Expression,
    params: Option<&P>,
) -> Option<i64> {
    if matches!(&expr.kind, ExprKind::Ident(h) if h.path.len() > 1)
        || matches!(&expr.kind, ExprKind::MemberAccess { .. })
    {
        if let Some(value) = params.and_then(|p| p.get(&const_parameter_path(expr, params)?)) {
            return value.to_i64();
        }
    }
    // §25.5 interface-port parameter (`c.DEPTH`) — dotted key seeded at
    // child inlining; parses as MemberAccess. Resolve once without building
    // format! strings in a match guard.
    if let ExprKind::MemberAccess { expr: base, member } = &expr.kind
        && let ExprKind::Ident(h) = &base.kind
        && h.path.len() == 1
        && h.path[0].selects.is_empty()
        && let Some(p) = params
    {
        let base_name = &h.path[0].name.name;
        if let Some(v) = p
            .get(&format!("{base_name}.{}", member.name))
            .or_else(|| p.get(&format!("{base_name}::{}", member.name)))
        {
            return v.to_i64();
        }
    }
    match &expr.kind {
        // §6.20.2/§26.3: element of an UNPACKED-ARRAY parameter in a
        // constant context — `pkg::LIM[3]`, `LIM[1]`, `u.mod.A[2]`.
        // `register_array_param` stores each element under `base[idx]`
        // (scoped `pkg::LIM[i]` for package arrays, bare `LIM[i]` at module
        // scope, dotted for inlined instances), but this i64 evaluator had
        // no Index arm at all: a dimension sized by an array element
        // (`int mem [pkg::LIM[3]]`) evaluated 0 and the array silently
        // vanished. Try the qualified spellings of the base first, then the
        // Value evaluator's packed bit-/element-select for bases that
        // actually resolve.
        ExprKind::Index { expr: base, index } => {
            // §6.20.2/§26.3: element of an UNPACKED-ARRAY parameter —
            // `pkg::LIM[3]`, `LIM[1]`, `u.mod.A[2]`. register_array_param
            // stores each element under `base[idx]` (scoped `pkg::LIM[i]`
            // for package arrays, bare `LIM[i]` at module scope, dotted for
            // inlined instances). Try those env keys first; everything else
            // keeps the former `Index | MemberAccess` tail below (delegate
            // to the full value evaluator).
            if let Some(idx) = const_eval_i64_with_params_env(index, params) {
                let mut keys = Vec::new();
                const_index_base_keys(base, params, &mut keys);
                for k in &keys {
                    if let Some(v) = params.and_then(|p| p.get(&format!("{}[{}]", k, idx))) {
                        return v.to_i64();
                    }
                }
            }
            let p = params?;
            eval_const_expr_val_inner(expr, p, &mut const_context::Types::default()).to_i64()
        }
        ExprKind::Number(NumberLiteral::Integer { value, base, .. }) => {
            let r = match base {
                NumberBase::Binary => 2,
                NumberBase::Octal => 8,
                NumberBase::Hex => 16,
                NumberBase::Decimal => 10,
            };
            i64::from_str_radix(&value.replace('_', ""), r).ok()
        }
        ExprKind::Number(NumberLiteral::UnbasedUnsized('0')) => Some(0),
        ExprKind::Number(NumberLiteral::UnbasedUnsized('1')) => Some(1),
        // Time literal magnitude in tick units (1 ns).
        ExprKind::Number(NumberLiteral::Time(s)) => Some((*s * 1e9) as i64),
        ExprKind::Ident(hier) => {
            let name = hier.path.last().map(|s| s.name.name.as_str()).unwrap_or("");
            // §26.3: a SCOPED `P::x` resolves against THAT package's parameter
            // alias (`alias_pkg_param` registers every package parameter under
            // `pkg::name`). Taking only the leaf dropped the qualifier, so a
            // cross-package reference (`$clog2(cfg_pkg::DEPTH) - 6`) read the
            // bare slot — absent unless someone imported it — and evaluated 0,
            // driving every dependent range negative.
            let scoped = (hier.path.len() >= 2)
                .then(|| format!("{}::{}", hier.path[hier.path.len() - 2].name.name, name));
            // §25.5: interface-port parameter (`c.DEPTH`) — seeded under its
            // dotted spelling at child inlining; try it before the bare name.
            let dotted = (hier.path.len() >= 2)
                .then(|| const_parameter_path(expr, params))
                .flatten();
            scoped
                .as_deref()
                .and_then(|k| params.and_then(|p| p.get(k)))
                .or_else(|| {
                    dotted
                        .as_deref()
                        .and_then(|k| params.and_then(|p| p.get(k)))
                })
                .or_else(|| params.and_then(|p| p.get(name)))
                .and_then(|v| v.to_i64())
                // A package function's own parameter (`N` in `unit_type_t [0:N-1]`)
                // sizes the formal while the generate-if shell is evaluating the
                // call. The value lives under `pkg::N`; the instance map does not
                // re-import it. Same lookup as `eval_const_expr_val`.
                .or_else(|| {
                    CONST_FN_PACKAGE.with(|c| {
                        c.borrow().clone().and_then(|pkg| {
                            let qual = format!("{pkg}::{name}");
                            let dotted = format!("{pkg}.{name}");
                            params
                                .and_then(|p| p.get(&qual).or_else(|| p.get(&dotted)).cloned())
                                .or_else(|| param_fallback_get(&qual))
                                .or_else(|| param_fallback_get(&dotted))
                                .and_then(|v| v.to_i64())
                        })
                    })
                })
                // Fall back to the global package/$unit param snapshot so that a
                // dimension like `[paddr_width_p - page_offset_width_gp - 1:0]`
                // (where the global `page_offset_width_gp` is absent from the
                // scoped instance-merge param map) resolves instead of dropping
                // the whole dimension — which otherwise mis-sized black-parrot's
                // bp_pte_leaf_s and wrapped r_entry_high_bits_lp.
                .or_else(|| param_fallback_get(name).and_then(|v| v.to_i64()))
                // XEZIM_TRACE_PARAM: a name the const evaluator cannot
                // resolve is what most callers silently turn into 0 — the
                // classic seed of a `[N-1:0]` underflow (`LOG_X - 6` with
                // `LOG_X` unresolved → −6). Loud only when traced.
                .or_else(|| {
                    param_trace(
                        "const-eval:MISS",
                        name,
                        "unresolved identifier (callers default it to 0)",
                    );
                    None
                })
        }
        ExprKind::Binary { op, left, right } => {
            // LRM §11.4 — full operator set, evaluated in i64 context.
            // Short-circuit logical/conditional handled separately to avoid
            // unnecessary right-side eval (and to match LRM §11.4.7 logical
            // short-circuit semantics).
            match op {
                BinaryOp::LogAnd => {
                    let l = const_eval_i64_with_params_env(left, params)?;
                    if l == 0 {
                        return Some(0);
                    }
                    let r = const_eval_i64_with_params_env(right, params)?;
                    Some(if r != 0 { 1 } else { 0 })
                }
                BinaryOp::LogOr => {
                    let l = const_eval_i64_with_params_env(left, params)?;
                    if l != 0 {
                        return Some(1);
                    }
                    let r = const_eval_i64_with_params_env(right, params)?;
                    Some(if r != 0 { 1 } else { 0 })
                }
                _ => {
                    let l = const_eval_i64_with_params_env(left, params)?;
                    let r = const_eval_i64_with_params_env(right, params)?;
                    match op {
                        BinaryOp::Add => l.checked_add(r),
                        BinaryOp::Sub => l.checked_sub(r),
                        BinaryOp::Mul => l.checked_mul(r),
                        BinaryOp::Div => {
                            if r != 0 {
                                Some(l / r)
                            } else {
                                None
                            }
                        }
                        BinaryOp::Mod => {
                            if r != 0 {
                                Some(l % r)
                            } else {
                                None
                            }
                        }
                        // LRM §11.4.3 power.
                        BinaryOp::Power => {
                            if r < 0 {
                                return None;
                            }
                            let e = u32::try_from(r).ok()?;
                            l.checked_pow(e)
                        }
                        BinaryOp::ShiftLeft | BinaryOp::ArithShiftLeft => {
                            Some(l.wrapping_shl(r as u32))
                        }
                        BinaryOp::ShiftRight => Some((l as u64).wrapping_shr(r as u32) as i64),
                        BinaryOp::ArithShiftRight => Some(l.wrapping_shr(r as u32)),
                        BinaryOp::BitAnd => Some(l & r),
                        BinaryOp::BitOr => Some(l | r),
                        BinaryOp::BitXor => Some(l ^ r),
                        BinaryOp::BitXnor => Some(!(l ^ r)),
                        // LRM §11.4.4 equality / §11.4.5 case equality.
                        BinaryOp::Eq | BinaryOp::CaseEq => Some(if l == r { 1 } else { 0 }),
                        BinaryOp::Neq | BinaryOp::CaseNeq => Some(if l != r { 1 } else { 0 }),
                        // LRM §11.4.6 relational.
                        BinaryOp::Lt => Some(if l < r { 1 } else { 0 }),
                        BinaryOp::Leq => Some(if l <= r { 1 } else { 0 }),
                        BinaryOp::Gt => Some(if l > r { 1 } else { 0 }),
                        BinaryOp::Geq => Some(if l >= r { 1 } else { 0 }),
                        _ => None,
                    }
                }
            }
        }
        ExprKind::Unary { op, operand } => {
            let scalar = const_eval_i64_with_params_env(operand, params);
            // §11.4.9: reduction operands are self-determined. Reduce before
            // narrowing to i64: high bits, narrow signed operands and literals
            // too wide for i64 must all retain their declared width. Do not
            // let the Value evaluator's unresolved-name default turn an
            // incomplete parameter binding into a resolved range.
            if matches!(
                op,
                UnaryOp::BitAnd
                    | UnaryOp::BitNand
                    | UnaryOp::BitOr
                    | UnaryOp::BitNor
                    | UnaryOp::BitXor
                    | UnaryOp::BitXnor
            ) {
                let empty = HashMap::default();
                match params {
                    Some(env) if scalar.is_some() || is_const_expr(operand, env) => {
                        let val = eval_const_expr_val_inner(
                            operand,
                            env,
                            &mut const_context::Types::default(),
                        );
                        if !val.is_real {
                            let reduced = match op {
                                UnaryOp::BitAnd => val.reduce_and(),
                                UnaryOp::BitNand => val.reduce_and().logic_not(),
                                UnaryOp::BitOr => val.reduce_or(),
                                UnaryOp::BitNor => val.reduce_or().logic_not(),
                                UnaryOp::BitXor => val.reduce_xor(),
                                _ => val.reduce_xor().logic_not(),
                            };
                            return reduced.to_index();
                        }
                    }
                    None if scalar.is_some() || is_const_expr(operand, &empty) => {
                        let val = eval_const_expr_val(operand, &empty);
                        if !val.is_real {
                            let reduced = match op {
                                UnaryOp::BitAnd => val.reduce_and(),
                                UnaryOp::BitNand => val.reduce_and().logic_not(),
                                UnaryOp::BitOr => val.reduce_or(),
                                UnaryOp::BitNor => val.reduce_or().logic_not(),
                                UnaryOp::BitXor => val.reduce_xor(),
                                _ => val.reduce_xor().logic_not(),
                            };
                            return reduced.to_index();
                        }
                    }
                    _ => {}
                }
            }
            let v = scalar?;
            match op {
                UnaryOp::Plus => Some(v),
                UnaryOp::Minus => Some(v.wrapping_neg()),
                UnaryOp::LogNot => Some(if v == 0 { 1 } else { 0 }),
                UnaryOp::BitNot => Some(!v),
                UnaryOp::BitAnd => Some(if v == -1 { 1 } else { 0 }), // reduction & on all-ones i64
                UnaryOp::BitNand => Some(if v == -1 { 0 } else { 1 }),
                UnaryOp::BitOr => Some(if v != 0 { 1 } else { 0 }),
                UnaryOp::BitNor => Some(if v != 0 { 0 } else { 1 }),
                UnaryOp::BitXor => Some((v.count_ones() & 1) as i64),
                UnaryOp::BitXnor => Some(((!v.count_ones()) & 1) as i64),
                _ => None,
            }
        }
        // LRM §11.4.11 conditional ?: — both branches optional to evaluate
        // depending on cond, but const-eval requires the chosen branch.
        ExprKind::Conditional {
            condition,
            then_expr,
            else_expr,
        } => {
            let c = const_eval_i64_with_params_env(condition, params)?;
            if c != 0 {
                const_eval_i64_with_params_env(then_expr, params)
            } else {
                const_eval_i64_with_params_env(else_expr, params)
            }
        }
        ExprKind::Paren(e) => const_eval_i64_with_params_env(e, params),
        // LRM §20.8 / §20.9 — constant integer system functions commonly used
        // in array bounds: $clog2, $unsigned, $signed are size-preserving;
        // $min/$max take two args. Real math reaches integer dimensions
        // through $rtoi, retaining each operand's packed width (§20.5).
        ExprKind::SystemCall { name, args } => match name.as_str() {
            "$rtoi" if args.len() == 1 && const_fn_expr_supported(&args[0]) => {
                let empty = HashMap::default();
                match params {
                    Some(p) => eval_const_expr_val_inner(expr, p, &mut const_context::Types::default())
                        .to_i64(),
                    None => eval_const_expr_val(expr, &empty).to_i64(),
                }
            }
            "$clog2" => {
                let val = const_eval_i64_with_params_env(args.first()?, params)?;
                if val <= 1 {
                    Some(0)
                } else {
                    let mut res = 0;
                    let mut tmp = val - 1;
                    while tmp > 0 {
                        tmp >>= 1;
                        res += 1;
                    }
                    Some(res)
                }
            }
            "$unsigned" | "$signed" => const_eval_i64_with_params_env(args.first()?, params),
            // §6.24.1 casts (`int'(e)`, `N'(e)`, `T'(e)`) — the value
            // evaluator applies the cast width as the operand's context. A
            // cast in a dimension (`logic [int'(A + B) - 1:0]`) left the range
            // unresolved.
            "$__xz_size_cast" | "$__xz_type_cast" | "$__xz_named_cast" => {
                let v = eval_const_expr_val_inner(expr, params?, &mut const_context::Types::default());
                if v.is_real || v.has_xz() {
                    return None;
                }
                v.to_i64()
            }
            // LRM §20.9 bit-introspection system functions.
            // `$countones(x)` — Hamming weight (count of 1 bits).
            // `$onehot(x)` — 1 iff exactly one bit set.
            // `$onehot0(x)` — 1 iff at most one bit set.
            // `$isunknown(x)` — 1 iff any bit is X or Z.
            // For const-eval we operate on the const-evaluated i64 value
            // (X/Z bits aren't preserved, so $isunknown is 0 here).
            "$countones" => {
                let v = const_eval_i64_with_params_env(args.first()?, params)?;
                Some((v as u64).count_ones() as i64)
            }
            "$onehot" => {
                let v = const_eval_i64_with_params_env(args.first()?, params)?;
                let v = v as u64;
                Some(if v != 0 && v & (v - 1) == 0 { 1 } else { 0 })
            }
            "$onehot0" => {
                let v = const_eval_i64_with_params_env(args.first()?, params)?;
                let v = v as u64;
                Some(if v == 0 || v & (v - 1) == 0 { 1 } else { 0 })
            }
            "$isunknown" => {
                // const_eval flattens X/Z to 0 — so const-eval always
                // returns 0 here. The runtime path is the correct
                // place to check x/z; this just keeps parameter
                // expressions like `parameter int K = $isunknown(N);`
                // from falling through to a generic 0.
                let _ = const_eval_i64_with_params_env(args.first()?, params)?;
                Some(0)
            }
            "$countbits" => {
                // `$countbits(x, ctl1[, ctl2 …])` — count bits matching
                // any of the control values (0/1/X/Z encoded as 2'b
                // const). For const-eval we only count 0/1 controls
                // since X/Z are stripped.
                let v = const_eval_i64_with_params_env(args.first()?, params)? as u64;
                let mut want_zero = false;
                let mut want_one = false;
                for ctl in &args[1..] {
                    if let Some(c) = const_eval_i64_with_params_env(ctl, params) {
                        match c {
                            0 => want_zero = true,
                            1 => want_one = true,
                            _ => {}
                        }
                    }
                }
                if !want_zero && !want_one {
                    return Some(0);
                }
                // Width of x: take the largest set bit + 1, capped at 64.
                let w = 64 - v.leading_zeros() as u64;
                let mut count = 0u32;
                if want_one {
                    count += v.count_ones();
                }
                if want_zero {
                    let mask = if w == 64 { u64::MAX } else { (1u64 << w) - 1 };
                    count += (!v & mask).count_ones();
                }
                Some(count as i64)
            }
            // LRM §20.7 — `$bits(x)` returns the bit width. We handle the
            // cases reachable without a typedef table: a parameter ident
            // (uses its Value width), a sized number literal (uses the
            // declared size), or an `$unsigned`/`$signed` wrapper.
            // `$bits(typedef_name)` requires typedef threading and falls
            // through to None — runtime path still resolves it.
            "$bits" => {
                let arg = args.first()?;
                let inner = if let ExprKind::SystemCall { name, args: a2 } = &arg.kind {
                    if name == "$unsigned" || name == "$signed" {
                        a2.first()?
                    } else {
                        arg
                    }
                } else {
                    arg
                };
                match &inner.kind {
                    // §7.4.5/§20.6.2: an element or slice of a declared
                    // variable (`pk[2]` of `logic [3:0][1:0] pk`) has the
                    // width of the dimensions its index selects leave.
                    ExprKind::Index { .. } | ExprKind::RangeSelect { .. }
                        if decl_select_bits(inner, params).is_some() =>
                    {
                        decl_select_bits(inner, params)
                    }
                    ExprKind::Ident(hier) => {
                        let name = hier.path.last().map(|s| s.name.name.as_str()).unwrap_or("");
                        // First try parameter ident → its Value width.
                        params
                            .and_then(|p| p.get(name))
                            .map(|v| v.width as i64)
                            // §20.6.2: a declared variable of this scope, sized
                            // from its declared type (every unpacked dimension
                            // included), then a typedef with unpacked dimensions.
                            .or_else(|| {
                                decl_var_query("$bits", std::slice::from_ref(inner), params)
                            })
                            .or_else(|| typedef_unpacked_bits(name, params))
                            // Then fall through to the thread-local typedef
                            // table (set by callers that have one available).
                            .or_else(|| {
                                TYPEDEFS_TLS.with(|td| {
                                    td.borrow()
                                        .as_ref()
                                        .and_then(|m| m.get(name).copied())
                                        .map(|w| w as i64)
                                })
                            })
                            // §20.6.2 over a BUILT-IN integer atom type.
                            // `$bits(int)` parses to a bare Ident (the operand
                            // is not a typedef and not a parameter), so both
                            // lookups above miss and the call answered 0 — a
                            // `localparam W = $bits(int)` used as a vector
                            // width then declared a degenerate vector.
                            .or_else(|| atom_keyword_width(name).map(|w| w as i64))
                            // §20.7: the non-atom builtins too (real family,
                            // string container, 1-bit scalars, void).
                            .or_else(|| match name {
                                "real" => Some(64),
                                "shortreal" => Some(32),
                                "realtime" => Some(64),
                                "string" => Some(1024),
                                "bit" | "logic" | "reg" => Some(1),
                                "void" => Some(0),
                                _ => None,
                            })
                    }
                    // §8.23: `$bits(pkg::cls::td)` — a `::`-chained scope
                    // NESTS member accesses; the one-level arm below only
                    // sees `pkg::td`. Resolve the FULL chain key against
                    // the typedef table (class-scope registration keys it);
                    // a miss falls through to the expression-width arms
                    // exactly as before.
                    ExprKind::MemberAccess { expr: base, .. }
                        if matches!(base.kind, ExprKind::MemberAccess { .. }) =>
                    {
                        member_access_chain_as_scopes(inner)
                            .and_then(|(scopes, leaf)| {
                                let mut key = String::new();
                                for l in &scopes {
                                    key.push_str(&l.name.name);
                                    key.push_str("::");
                                }
                                key.push_str(&leaf.name);
                                TYPEDEFS_TLS.with(|td| {
                                    td.borrow()
                                        .as_ref()
                                        .and_then(|m| m.get(&key).copied())
                                        .map(|w| w as i64)
                                })
                            })
                            .or_else(|| {
                                if let ExprKind::MemberAccess { expr: base, member } = &inner.kind {
                                    const_struct_field_in_base(base, &member.name)
                                        .map(|(_, w)| w as i64)
                                } else {
                                    None
                                }
                            })
                    }
                    // §7.2.2: `a[i].field.subfield` — the base is not a bare ident.
                    ExprKind::MemberAccess { expr: base, member }
                        if !matches!(base.kind, ExprKind::Ident(_)) =>
                    {
                        const_struct_field_in_base(base, &member.name).map(|(_, w)| w as i64)
                    }
                    // §26.3 package- (or class-) scoped type: `$bits(pkg::t)`.
                    // `::` lowers to the SAME `MemberAccess` node as a struct
                    // member select, so accept the leaf name and let the typedef
                    // table arbitrate — a real type name hits it, a member select
                    // misses and yields None exactly as before. Without this the
                    // whole arm fell through to `_ => None`, so a port declared
                    // `[$bits(some_pkg::some_t)-1:0]` elaborated to ONE BIT and
                    // silently truncated the bus. A struct MEMBER select
                    // (`$bits(CDEF.b)`) answers from the base's registered
                    // field layout.
                    ExprKind::MemberAccess { expr: base, member }
                        if matches!(base.kind, ExprKind::Ident(_)) =>
                    {
                        let from_layout =
                            const_struct_field_in_base(base, &member.name).map(|(_, w)| w as i64);
                        // §26.3: `P::T` must reach THAT package's typedef —
                        // the bare name is one global slot a same-named typedef
                        // in another package can own.
                        let scoped = if let ExprKind::Ident(h) = &base.kind {
                            h.path
                                .last()
                                .map(|s| format!("{}::{}", s.name.name, member.name))
                        } else {
                            None
                        };
                        from_layout.or_else(|| {
                            TYPEDEFS_TLS.with(|td| {
                                let b = td.borrow();
                                let m = b.as_ref()?;
                                scoped
                                    .as_deref()
                                    .and_then(|k| m.get(k).copied())
                                    .or_else(|| m.get(member.name.as_str()).copied())
                                    .map(|w| w as i64)
                            })
                        })
                    }
                    ExprKind::Number(NumberLiteral::Integer { size: Some(s), .. }) => {
                        Some(*s as i64)
                    }
                    ExprKind::Number(n @ NumberLiteral::Integer { size: None, .. }) => {
                        Some(i64::from(number_literal_width(n)))
                    }
                    ExprKind::Number(NumberLiteral::UnbasedUnsized(_)) => Some(1),
                    ExprKind::SystemCall { name: cn, .. } if is_cast_call(cn) => params
                        .and_then(|p| const_cast_bits(inner, p))
                        .map(i64::from),
                    // §20.6.2/§11.6.1: an operator, conditional or call
                    // operand has its self-determined width.
                    ExprKind::Binary { .. }
                    | ExprKind::Unary { .. }
                    | ExprKind::Conditional { .. }
                    | ExprKind::Call { .. } => params
                        .and_then(|p| const_self_width(inner, p))
                        .map(i64::from),
                    // §20.6.2 over an EXPRESSION operand: compute the
                    // self-determined width structurally. A port declared
                    // `[$bits({{A{1'b0}}, {(A*B){1'b0}}})-1:0]` elaborated to
                    // ONE BIT without this and silently truncated the bus.
                    ExprKind::Concatenation(_)
                    | ExprKind::Replication { .. }
                    | ExprKind::Paren(_) => {
                        fn expr_bits<P: ParamLookup>(
                            e: &Expression,
                            params: Option<&P>,
                        ) -> Option<i64> {
                            match &e.kind {
                                ExprKind::Number(NumberLiteral::Integer {
                                    size: Some(s), ..
                                }) => Some(*s as i64),
                                ExprKind::Number(n @ NumberLiteral::Integer { size: None, .. }) => {
                                    Some(number_literal_width(n) as i64)
                                }
                                ExprKind::Number(NumberLiteral::UnbasedUnsized(_)) => Some(1),
                                ExprKind::Paren(i) => expr_bits(i, params),
                                ExprKind::Concatenation(parts) => {
                                    let mut t = 0i64;
                                    for p in parts {
                                        t = t.checked_add(expr_bits(p, params)?)?;
                                    }
                                    Some(t)
                                }
                                ExprKind::Replication { count, exprs } => {
                                    let c = const_eval_i64_with_params_env(count, params)?;
                                    if c < 0 {
                                        return None;
                                    }
                                    let mut t = 0i64;
                                    for p in exprs {
                                        t = t.checked_add(expr_bits(p, params)?)?;
                                    }
                                    t.checked_mul(c)
                                }
                                ExprKind::Ident(hier) => {
                                    let n = hier
                                        .path
                                        .last()
                                        .map(|s| s.name.name.as_str())
                                        .unwrap_or("");
                                    // §26.3: prefer the qualified `P::T` key —
                                    // the bare name is a single global slot a
                                    // same-named typedef elsewhere can own.
                                    let scoped = (hier.path.len() >= 2).then(|| {
                                        format!(
                                            "{}::{}",
                                            hier.path[hier.path.len() - 2].name.name,
                                            n
                                        )
                                    });
                                    params
                                        .and_then(|m| m.get(n).map(|v| v.width as i64))
                                        .or_else(|| {
                                            TYPEDEFS_TLS.with(|td| {
                                                let b = td.borrow();
                                                let m = b.as_ref()?;
                                                scoped
                                                    .as_deref()
                                                    .and_then(|k| m.get(k).copied())
                                                    .or_else(|| m.get(n).copied())
                                                    .map(|w| w as i64)
                                            })
                                        })
                                        // A signal (`{sig, arr[1]}`): its
                                        // declared width, as `$bits(sig)`.
                                        .or_else(|| {
                                            params
                                                .and_then(|p| const_self_width(e, p))
                                                .map(i64::from)
                                        })
                                }
                                // A cast, operator, conditional or call inside
                                // the concatenation (`{q_t'(1), 2'b0}`).
                                _ => params.and_then(|p| const_self_width(e, p)).map(i64::from),
                            }
                        }
                        expr_bits(inner, params)
                    }
                    // §20.6.2 `$bits(<data_type>)`. `logic [0:0][1:0][1:0]`
                    // parses to a TypeLiteral (a data-type KEYWORD starts it),
                    // but nothing evaluated that node, so the whole call fell
                    // through to None and the enclosing localparam became 0 —
                    // `logic [VLD_W-1:0]` then declared a degenerate vector and
                    // half the bits silently vanished.
                    ExprKind::TypeLiteral(dt) => {
                        typedefs_snapshot(|td| Some(resolve_type_width_env(dt, params, td) as i64))
                    }
                    // §20.6.2 over a TYPEDEF with packed dimensions —
                    // `$bits(pkg::t [0:0][1:0])`. A scoped type name is not a
                    // data-type keyword, so the parser cannot take the
                    // TypeLiteral path and produces a RangeSelect chain over a
                    // MemberAccess instead. Evaluated as an expression that is
                    // a 2-bit part-select; it is really the typedef's width
                    // times every dimension. Getting 2 instead of 292 truncated
                    // a flattened pipeline stage to two bits.
                    ExprKind::RangeSelect { .. } => {
                        let mut dims: Vec<(i64, i64)> = Vec::new();
                        let mut cur: &Expression = inner;
                        while let ExprKind::RangeSelect {
                            expr,
                            kind,
                            left,
                            right,
                        } = &cur.kind
                        {
                            if !matches!(kind, crate::ast::expr::RangeKind::Constant) {
                                return None;
                            }
                            let l = const_eval_i64_with_params_env(left, params)?;
                            let r = const_eval_i64_with_params_env(right, params)?;
                            dims.push((l, r));
                            cur = expr.as_ref();
                        }
                        // The base must name a TYPE, not a signal — a signal
                        // part-select keeps its existing meaning.
                        let tname = match &cur.kind {
                            ExprKind::MemberAccess { member, .. } => member.name.clone(),
                            ExprKind::Ident(h) => h
                                .path
                                .last()
                                .map(|s| s.name.name.clone())
                                .unwrap_or_default(),
                            _ => return None,
                        };
                        let base_w = TYPEDEFS_TLS
                            .with(|td| td.borrow().as_ref().and_then(|m| m.get(&tname).copied()))?
                            as i64;
                        let mut total = base_w;
                        for (l, r) in dims {
                            total = total.checked_mul((l - r).abs() + 1)?;
                        }
                        Some(total)
                    }
                    _ => None,
                }
            }
            // LRM §20.7 array-introspection system functions over an array
            // name: each consults ARRAYS_TLS for `(lo, hi)` and returns
            // the appropriate bound. Falls through to None when the
            // table is empty or the name is not registered.
            "$size"
            | "$left"
            | "$right"
            | "$high"
            | "$low"
            | "$increment"
            | "$dimensions"
            | "$unpacked_dimensions" => {
                let arg = args.first()?;
                // §20.7: a declared fixed-size variable answers from its
                // declared type — every dimension, in declared order.
                if let Some(v) = decl_var_query(name, args, params) {
                    return Some(v);
                }
                if let ExprKind::TypeLiteral(dt) = &arg.kind {
                    return type_literal_query(name, dt, args, params);
                }
                let arr_name = match &arg.kind {
                    ExprKind::Ident(hier) => hier.path.last().map(|s| s.name.name.clone())?,
                    _ => return None,
                };
                ARRAYS_TLS
                    .with(|ar| ar.borrow().as_ref().and_then(|m| m.get(&arr_name).copied()))
                    .and_then(|(lo, hi, _ndim)| {
                        Some(match name.as_str() {
                            "$size" => hi - lo + 1,
                            "$left" => lo,
                            "$right" => hi,
                            "$high" => hi.max(lo),
                            "$low" => lo.min(hi),
                            "$dimensions" => 1,
                            // $increment and $unpacked_dimensions over an array need
                            // the DECLARED order / full dimension list, which this
                            // (lo, hi, ndim) table has already normalized away — leave
                            // them to the runtime rather than answer wrongly.
                            _ => return None,
                        })
                    })
                    // §20.7 also accepts a TYPE as the operand — `$size(int)` is
                    // 32, `$left(byte)` 7. The name parses as a plain Ident (see
                    // `parse_call_args`), so a `localparam W = $size(int)` used as
                    // a vector width const-folded to nothing and the vector
                    // elaborated one bit wide.
                    .or_else(|| {
                        // The full typedef definitions (TYPEDEF_SHAPES_TLS)
                        // count an unpacked typedef's dimensions too.
                        let q = TYPEDEFS_TLS.with(|td| {
                            TYPEDEF_SHAPES_TLS.with(|sh| {
                                let sh = sh.borrow();
                                type_query_dims_by_name(
                                    &arr_name,
                                    params,
                                    td.borrow().as_ref(),
                                    Some(&sh.0),
                                    Some(&sh.1),
                                )
                            })
                        })?;
                        // Width-only typedef knowledge cannot count dimensions;
                        // leave those to the runtime rather than answer wrongly.
                        if q.dims.is_empty()
                            && matches!(name.as_str(), "$dimensions" | "$unpacked_dimensions")
                        {
                            return None;
                        }
                        let dim = match args.get(1) {
                            Some(d) => const_eval_i64_with_params_env(d, params)? as usize,
                            None => 1,
                        };
                        type_query_bound(name, &q, dim)
                    })
            }
            _ => None,
        },
        // Packed-array element select / struct member select in an integer
        // const context — e.g. a dimension `[all_cfgs_gp[idx].icache_sets-1:0]`
        // or `[proc_param_lp.field-1:0]`. Delegate to the full value evaluator
        // (which carries the array-elem / struct-layout / package-param TLS
        // context) and reduce to i64. Without this, such a dimension underflows
        // to ~u32::MAX (black-parrot config widths used directly in a range).
        // (`Index` moved to the dedicated arm above, which tries the
        // unpacked-array element env keys first.)
        // §26.3, §6.20.2: a signed value keeps its sign (`pk::LO` of -1 is
        // -1, not 4294967295).
        ExprKind::MemberAccess { .. } => {
            let p = params?;
            eval_const_expr_val_inner(expr, p, &mut const_context::Types::default()).to_i64()
        }
        // §11.4.12: a constant concatenation or replication, such as the
        // `{Width{1'b1}}` bound of a covergroup bin range.
        ExprKind::Concatenation(_) | ExprKind::Replication { .. } => {
            const_concat_bits(expr, params).and_then(|(v, w)| (w > 0).then_some(v as i64))
        }
        // §13.4.3: a user sizing function called directly in a dimension.
        // Interpret its REAL body (FUNCS_TLS) — the name-based ceil-log2
        // fallback below only fires when the declaration isn't visible, and
        // silently assumes $clog2 semantics (wrong for floor-log2 variants).
        ExprKind::Call { func, args } => {
            if let Some(v) = const_eval_user_call(expr, params.map(ParamLookup::to_hashmap).as_deref()) {
                return v.to_i64();
            }
            let fname = match &func.kind {
                ExprKind::Ident(h) => h.path.last().map(|s| s.name.name.as_str())?,
                ExprKind::MemberAccess { member, .. } => member.name.as_str(),
                _ => return None,
            };
            // Name-based ceil-log2 fallback (HardFloat `clog2` == $clog2).
            if fname == "clog2" {
                let n = const_eval_i64_with_params_env(args.first()?, params)? as u64;
                return Some(ceil_log2(n) as i64);
            }
            None
        }
        _ => None,
    }
}

/// Const-evaluate `expr` against a plain parameter table (`None` = empty).
/// The generic core [`const_eval_i64_with_params_env`] additionally accepts a
/// [`ParamLookup`] overlay for constant-function bodies.
pub fn const_eval_i64_with_params(
    expr: &Expression,
    params: Option<&HashMap<String, Value>>,
) -> Option<i64> {
    const_eval_i64_with_params_env(expr, params)
}

/// Value and width of a constant concatenation operand (§11.4.12), when
/// every operand is a sized literal, a parameter, or a nested concatenation
/// or replication, and the whole fits in 64 bits. A zero replication has
/// width 0 (§11.4.12.1); 65 copies of a nonzero width are already too wide.
fn const_concat_bits<P: ParamLookup>(
    e: &Expression,
    params: Option<&P>,
) -> Option<(u64, u32)> {
    let mask = |v: u64, w: u32| if w >= 64 { v } else { v & ((1u64 << w) - 1) };
    let (v, w) = match &e.kind {
        ExprKind::Paren(x) => return const_concat_bits(x, params),
        ExprKind::Number(NumberLiteral::Integer { size: Some(s), .. }) => {
            let empty = HashMap::default();
            let lit = match params {
                Some(p) => eval_const_expr_val_inner(e, p, &mut const_context::Types::default()),
                None => eval_const_expr_val(e, &empty),
            };
            (lit.to_u64().filter(|_| !lit.has_xz())?, *s)
        }
        ExprKind::Ident(h) if h.path.len() == 1 && h.path[0].selects.is_empty() => {
            let p = params?.get(&h.path[0].name.name)?;
            if p.has_xz() || p.is_real {
                return None;
            }
            (p.to_u64()?, p.width)
        }
        ExprKind::Concatenation(parts) => {
            let (mut v, mut w) = (0u64, 0u32);
            for part in parts {
                let (pv, pw) = const_concat_bits(part, params)?;
                w = w.checked_add(pw).filter(|&w| w <= 64)?;
                v = v.checked_shl(pw).unwrap_or(0) | pv;
            }
            (v, w)
        }
        ExprKind::Replication { count, exprs } => {
            let n = u32::try_from(const_eval_i64_with_params_env(count, params)?).ok()?;
            let mut inner = Vec::with_capacity(exprs.len());
            for x in exprs {
                inner.push(const_concat_bits(x, params)?);
            }
            let (mut v, mut w) = (0u64, 0u32);
            for _ in 0..n.min(65) {
                for &(pv, pw) in &inner {
                    w = w.checked_add(pw).filter(|&w| w <= 64)?;
                    v = v.checked_shl(pw).unwrap_or(0) | pv;
                }
            }
            (v, w)
        }
        _ => return None,
    };
    (w <= 64).then(|| (mask(v, w), w))
}
