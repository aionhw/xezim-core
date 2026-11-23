use super::*;

// §11.8.2: a real destination converts the completed integral RHS;
// its 64-bit representation is not an integral operand width.
pub(super) fn eval_init_for_target(
    expr: &Expression,
    params: &dyn ParamLookup,
    width: u32,
    real: bool,
) -> Value {
    if real {
        Value::from_f64(eval_const_expr_val_env(expr, &params).to_f64())
    } else {
        // §6.12.1: a real initializer of an integral variable converts to
        // it, rounded to the nearest integer. `resize_for_assign` leaves a
        // real as it is for a 64-bit target (a `real` is 64 bits wide too),
        // so `time t = 9200s;` and `longint l = 3e9;` kept the double and a
        // shift read its IEEE 754 bits.
        let v = eval_init_for_width(expr, params, width);
        if v.is_real {
            Value::from_real_wrapped(v.to_f64(), width)
        } else {
            v
        }
    }
}

pub(super) fn eval_init_for_width(
    expr: &Expression,
    params: &dyn ParamLookup,
    width: u32,
) -> Value {
    if let ExprKind::Number(NumberLiteral::UnbasedUnsized(c)) = &expr.kind {
        return match c {
            '0' => Value::zero(width),
            '1' => Value::ones(width),
            'x' | 'X' => Value::new(width),
            'z' | 'Z' => Value::all_z(width),
            _ => Value::new(width),
        };
    }
    // §10.7 assignment resize: a signed source with an X/Z MSB widens with X/Z
    // (resize_for_assign), matching a procedural assignment to the same target.
    eval_const_expr_val_with_ctx(
        expr,
        &params,
        Some(width),
        &mut const_context::Types::default(),
    )
    .resize_for_assign(width)
}

/// §6.11.3, §6.11.2: a package variable's initial value takes the DECLARED
/// type's signedness, not the initializer's, and a 2-state type maps x/z to
/// 0, as a module variable's declaration initializer does.
pub(super) fn package_var_init_value(
    mut v: Value,
    dt: &DataType,
    typedef_types: &HashMap<String, DataType>,
) -> Value {
    v.is_signed = is_type_signed_resolved(dt, typedef_types);
    if is_type_two_state_resolved(dt, typedef_types) {
        v = v.to_two_state();
    }
    v
}

/// §5.7.1: self-determined literal width, shared by elaboration queries.
pub fn number_literal_width(num: &NumberLiteral) -> u32 {
    match num {
        NumberLiteral::Integer {
            size,
            signed,
            base,
            value,
            ..
        } => {
            let radix = match base {
                NumberBase::Binary => 2,
                NumberBase::Octal => 8,
                NumberBase::Hex => 16,
                NumberBase::Decimal => 10,
            };
            size.unwrap_or_else(|| Value::unsized_integer_width(value, radix, *signed))
        }
        NumberLiteral::UnbasedUnsized(_) => 1,
        _ => 64,
    }
}

/// Evaluate a constant expression, returning a full Value (preserving width/sign).
/// §11.8.2: a constant integral operand that takes REAL type from its context
/// (the other side of a relational operator, the other arm of `?:`). The real
/// type reaches its top operator, whose own operands are self-determined and
/// converted; anything else is converted whole (§6.12.2).
fn const_eval_in_real_context<P: ParamLookup>(e: &Expression, params: &P) -> Value {
    let real = |e: &Expression| {
        let v = eval_const_expr_val_inner(e, params, &mut const_context::Types::default());
        if v.is_real {
            v
        } else {
            Value::from_f64(v.to_f64())
        }
    };
    match &e.kind {
        ExprKind::Paren(x) => const_eval_in_real_context(x, params),
        ExprKind::Binary { op, left, right }
            if matches!(
                op,
                BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Power
            ) =>
        {
            let (l, r) = (real(left), real(right));
            match op {
                BinaryOp::Add => l.add(&r),
                BinaryOp::Sub => l.sub(&r),
                BinaryOp::Mul => l.mul(&r),
                BinaryOp::Div => l.div(&r),
                _ => l.power(&r),
            }
        }
        ExprKind::Unary {
            op: UnaryOp::Minus,
            operand,
        } => real(operand).negate(),
        ExprKind::Unary {
            op: UnaryOp::Plus,
            operand,
        } => real(operand),
        _ => real(e),
    }
}

/// §20.8.2, Table 20-4: real math functions are also constant system
/// functions (§11.2.1). Keep arity shared with the constant-function guard.
pub(super) fn const_real_math_arity(name: &str) -> Option<usize> {
    match name {
        "$ln" | "$log10" | "$log2" | "$exp" | "$sqrt" | "$floor" | "$ceil" | "$sin" | "$cos"
        | "$tan" | "$asin" | "$acos" | "$atan" | "$sinh" | "$cosh" | "$tanh" | "$asinh"
        | "$acosh" | "$atanh" => Some(1),
        "$pow" | "$atan2" | "$hypot" => Some(2),
        _ => None,
    }
}

pub fn eval_const_expr_val_env<P: ParamLookup>(expr: &Expression, params: &P) -> Value {
    eval_const_expr_val_with_ctx(expr, params, None, &mut const_context::Types::default())
}

pub(super) fn eval_const_expr_val(expr: &Expression, params: &HashMap<String, Value>) -> Value {
    eval_const_expr_val_with_ctx(expr, params, None, &mut const_context::Types::default())
}

#[inline]
pub(super) fn eval_const_expr_val_inner<P: ParamLookup>(
    expr: &Expression,
    params: &P,
    types: &mut const_context::Types,
) -> Value {
    eval_const_expr_val_with_ctx(expr, params, None, types)
}

pub(super) fn eval_const_expr_val_with_ctx<P: ParamLookup>(
    expr: &Expression,
    params: &P,
    ctx_w: Option<u32>,
    types: &mut const_context::Types,
) -> Value {
    if ctx_w.is_none() {
        if let Some(value) = types.take_value(expr) {
            return value;
        }
    }
    if is_context_operator(expr) {
        let ty = const_context::infer(expr, params, types);
        if ty.integral {
            let width = ctx_w.map_or(ty.width, |w| w.max(ty.width));
            if let Some(value) = const_ctx_fold(expr, params, width, ty.signed, types) {
                return value;
            }
        }
    }
    // §25.5: a parameter reached through an interface PORT formal
    // (`c.DEPTH`) parses as MemberAccess; the child's param map carries
    // it under the dotted spelling (seeded at inlining). Resolve the two
    // spellings once (a single `format!` pair), returning early only when
    // the key exists so an unbound member falls through to the general
    // struct/field handler below.
    if let ExprKind::MemberAccess { expr: base, member } = &expr.kind
        && let ExprKind::Ident(h) = &base.kind
        && h.path.len() == 1
        && h.path[0].selects.is_empty()
    {
        let name = &h.path[0].name.name;
        let dotted = format!("{}.{}", name, member.name);
        let doubledash = format!("{}::{}", name, member.name);
        if let Some(v) = params.get(&dotted).or_else(|| params.get(&doubledash)) {
            return v.clone();
        }
    }
    let mut res = match &expr.kind {
        // §3.14.3: an elaborated `1step` delay is one tick.
        ExprKind::SystemCall { name, .. } if name == ONE_STEP_DELAY => Value::from_u64(1, 64),
        ExprKind::Number(num) => {
            match num {
                NumberLiteral::Integer {
                    size,
                    signed,
                    base,
                    value,
                    ..
                } => {
                    let r = match base {
                        NumberBase::Binary => 2,
                        NumberBase::Octal => 8,
                        NumberBase::Hex => 16,
                        NumberBase::Decimal => 10,
                    };
                    let w = size.unwrap_or_else(|| Value::unsized_integer_width(value, r, *signed));
                    // A NEGATIVE genvar substituted into a generate body
                    // (`genvar_const_expr`, §27.4) spells its value `-2`; the
                    // radix parse has no sign and read it as x.
                    let mut v = match value.strip_prefix('-').map(|m| m.parse::<u64>()) {
                        Some(Ok(m)) if matches!(base, NumberBase::Decimal) && w <= 64 => {
                            Value::from_u64(m.wrapping_neg(), w)
                        }
                        _ => Value::from_str_radix(&value.replace('_', ""), r, w),
                    };
                    v.is_signed = *signed;
                    v
                }
                NumberLiteral::Real(f) => Value::from_f64(*f),
                // A time literal in a value context evaluates to its magnitude in
                // the simulation tick unit (1 ns), preserving the prior behaviour
                // where `10ns` const-folded to 10.
                NumberLiteral::Time(s) => Value::from_f64(*s * 1e9),
                // §5.7.1 fill literal — flagged so downstream resize/ops
                // replicate to the consuming width.
                NumberLiteral::UnbasedUnsized(c) => Value::fill_of(*c),
            }
        }
        ExprKind::StringLiteral(s) => Value::from_string(s),
        ExprKind::Ident(hier) => {
            // Multi-segment hierarchical ident: `pt.FIELD` (a struct parameter's
            // field, parsed as a path rather than MemberAccess). Slice the field
            // from the struct param via its registered layout. Field path joins
            // path[1..] with '.' to match nested flatten keys (`pt.a.b`).
            if hier.path.len() > 1 {
                let base = hier.path[0].name.name.as_str();
                if let Some(base_val) = params.get(base).cloned() {
                    let field_path = hier.path[1..]
                        .iter()
                        .map(|s| s.name.name.as_str())
                        .collect::<Vec<_>>()
                        .join(".");
                    if let Some((off, w)) = STRUCT_FIELDS_TLS.with(|c| {
                        c.borrow().get(base).and_then(|layout| {
                            layout
                                .iter()
                                .find(|(f, _, _)| f == &field_path)
                                .map(|&(_, o, w)| (o, w))
                        })
                    }) {
                        if w > 0 && off + w <= base_val.width {
                            return base_val.range_select((off + w - 1) as usize, off as usize);
                        }
                    }
                }
            }
            let name = hier.path.last().map(|s| s.name.name.as_str()).unwrap_or("");
            // §26.3: prefer the `P::x` alias for a scoped reference — see the
            // matching arm in `const_eval_i64_with_params`.
            let scoped = (hier.path.len() >= 2)
                .then(|| format!("{}::{}", hier.path[hier.path.len() - 2].name.name, name));
            // §25.5: a parameter reached through an interface PORT formal
            // (`c.DEPTH`) is seeded into the child's param map under its
            // dotted spelling — try that before the bare-name fallback.
            let dotted = (hier.path.len() >= 2)
                .then(|| const_parameter_path(expr, Some(params)))
                .flatten();
            {
                let resolved = scoped
                    .as_deref()
                    .and_then(|k| params.get(k).cloned())
                    .or_else(|| dotted.as_deref().and_then(|k| params.get(k).cloned()))
                    .or_else(|| params.get(name).cloned())
                    // A package function body names the package's own parameters
                    // bare (`ENC[fmt]`). After package elaboration those values
                    // live under `pkg::ENC`; the caller's map does not re-import
                    // them. Without this, `fp_width` at module scope summed two
                    // missing fields and returned 1.
                    .or_else(|| {
                        CONST_FN_PACKAGE.with(|c| {
                            let pkg = c.borrow().clone();
                            pkg.and_then(|pkg| {
                                let qual = format!("{pkg}::{name}");
                                let dotted = format!("{pkg}.{name}");
                                params
                                    .get(&qual)
                                    .or_else(|| params.get(&dotted))
                                    .cloned()
                                    .or_else(|| param_fallback_get(&qual))
                                    .or_else(|| param_fallback_get(&dotted))
                            })
                        })
                    })
                    .or_else(|| param_fallback_get(name));
                resolved.unwrap_or_else(|| {
                    // XEZIM_TRACE_PARAM: this silent zero-default is the
                    // classic seed of a `[N-1:0]` underflow (`LOG_X - 6`
                    // with `LOG_X` unresolved → −6). Loud only when traced.
                    param_trace(
                        "const-eval:MISS",
                        name,
                        "unresolved identifier, defaulting to 0",
                    );
                    Value::zero(32)
                })
            }
        }
        ExprKind::Binary { op, left, right } => {
            // §11.8.2: comparison operands share width/sign before any
            // nested arithmetic, while the comparison result stays one bit.
            let common = if const_context::is_comparison(*op)
                && (is_context_operator(left) || is_context_operator(right))
            {
                let l = const_context::infer(left, params, types);
                let r = const_context::infer(right, params, types);
                (l.integral && r.integral).then_some((l.width.max(r.width), l.signed && r.signed))
            } else {
                None
            };
            let (mut l, mut r) = match common {
                Some((w, signed)) => (
                    const_ctx_fold(left, params, w, signed, types)
                        .unwrap_or_else(|| eval_const_expr_val_inner(left, params, types)),
                    const_ctx_fold(right, params, w, signed, types)
                        .unwrap_or_else(|| eval_const_expr_val_inner(right, params, types)),
                ),
                None => (
                    eval_const_expr_val_inner(left, params, types),
                    eval_const_expr_val_inner(right, params, types),
                ),
            };
            if const_context::is_comparison(*op) && common.is_none() && !l.is_real && !r.is_real {
                let w = l.width.max(r.width);
                let signed = l.is_signed && r.is_signed;
                l.is_signed = signed;
                r.is_signed = signed;
                if l.width != w || l.is_fill {
                    l = l.resize_for_assign(w);
                }
                if r.width != w || r.is_fill {
                    r = r.resize_for_assign(w);
                }
            }
            match op {
                BinaryOp::Add => l.add(&r),
                BinaryOp::Sub => l.sub(&r),
                BinaryOp::Mul => l.mul(&r),
                BinaryOp::Div => l.div(&r),
                BinaryOp::Mod => l.modulo(&r),
                BinaryOp::Power => l.power(&r),
                BinaryOp::Eq => l.is_equal(&r),
                BinaryOp::Neq => l.is_not_equal(&r),
                // §11.4.6: wildcard equality in a CONSTANT expression —
                // `parameter W = 2'b01 ==? 2'b0x;` evaluated to 0 because
                // these ops had no const-eval arm at all.
                BinaryOp::CaseEq => l.case_eq(&r),
                BinaryOp::CaseNeq => l.case_eq(&r).logic_not(),
                BinaryOp::WildcardEq => l.wildcard_eq(&r),
                BinaryOp::WildcardNeq => l.wildcard_ne(&r),
                BinaryOp::Lt => l.less_than(&r),
                BinaryOp::Leq => l.less_equal(&r),
                BinaryOp::Gt => l.greater_than(&r),
                BinaryOp::Geq => l.greater_equal(&r),
                BinaryOp::ShiftLeft | BinaryOp::ArithShiftLeft => l.shift_left(&r),
                BinaryOp::ShiftRight => l.shift_right(&r),
                BinaryOp::BitOr => l.bitwise_or(&r),
                BinaryOp::BitAnd => l.bitwise_and(&r),
                BinaryOp::BitXor => l.bitwise_xor(&r),
                BinaryOp::BitXnor => l.bitwise_xor(&r).bitwise_not(),
                BinaryOp::LogOr => l.logic_or(&r),
                BinaryOp::LogAnd => l.logic_and(&r),
                // §11.4.7 logical implication / equivalence in constant exprs.
                BinaryOp::LogImplies => l.logic_impl(&r),
                BinaryOp::LogEquiv => l.logic_equiv(&r),
                BinaryOp::ArithShiftRight => l.arith_shift_right(&r),
                _ => Value::zero(32),
            }
        }
        ExprKind::Unary { op, operand } => {
            let v = eval_const_expr_val_inner(operand, params, types);
            // LRM §11.4.9 — reduction operators collapse the vector to 1 bit.
            // Prior to this audit the catch-all silently returned `v` unchanged,
            // so `|MASK` / `&ALL_ONES` etc. produced a same-width value instead
            // of the 1-bit reduction result.
            match op {
                UnaryOp::Plus => v,
                UnaryOp::Minus => v.negate(),
                UnaryOp::BitNot => v.bitwise_not(),
                UnaryOp::LogNot => v.logic_not(),
                UnaryOp::BitAnd => v.reduce_and(),
                UnaryOp::BitNand => v.reduce_and().bitwise_not(),
                UnaryOp::BitOr => v.reduce_or(),
                UnaryOp::BitNor => v.reduce_or().bitwise_not(),
                UnaryOp::BitXor => v.reduce_xor(),
                UnaryOp::BitXnor => v.reduce_xor().bitwise_not(),
                _ => v,
            }
        }
        ExprKind::Dollar => Value::from_u64(u32::MAX as u64, 32),
        ExprKind::Paren(inner) => eval_const_expr_val_inner(inner, params, types),
        ExprKind::SystemCall { name, args } if name == "$clog2" => {
            if let Some(arg) = args.first() {
                let v = eval_const_expr_val_inner(arg, params, types);
                let val = v.to_u64().unwrap_or(0);
                if val <= 1 {
                    Value::from_u64(0, 32)
                } else {
                    let mut res = 0;
                    let mut tmp = val - 1;
                    while tmp > 0 {
                        tmp >>= 1;
                        res += 1;
                    }
                    Value::from_u64(res, 32)
                }
            } else {
                Value::zero(32)
            }
        }
        // LRM §20.7 — `$bits(x)` in const-eval position. We handle the
        // cases reachable without a typedef table (parameter ident → its
        // Value's width; sized literal → declared size; `'0`/`'1` → 1).
        // `$bits(<typedef_name>)` requires typedef threading and returns 0
        // here — the runtime path still resolves it.
        ExprKind::SystemCall { name, args } if name == "$bits" => {
            let Some(arg) = args.first() else {
                return Value::zero(32);
            };
            let inner = if let ExprKind::SystemCall { name, args: a2 } = &arg.kind {
                if name == "$unsigned" || name == "$signed" {
                    a2.first().unwrap_or(arg)
                } else {
                    arg
                }
            } else {
                arg
            };
            let w: u32 = match &inner.kind {
                // §7.4.5/§20.6.2: an element or slice of a declared variable
                // — see the matching arm in `const_eval_i64_with_params`.
                ExprKind::Index { .. } | ExprKind::RangeSelect { .. }
                    if decl_select_bits(inner, Some(params)).is_some() =>
                {
                    decl_select_bits(inner, Some(params)).map_or(0, |b| b as u32)
                }
                ExprKind::Ident(hier) => {
                    let n = hier.path.last().map(|s| s.name.name.as_str()).unwrap_or("");
                    // §26.3: prefer the qualified `P::T` key — the bare name is
                    // one global slot a same-named typedef elsewhere can own.
                    let scoped = (hier.path.len() >= 2)
                        .then(|| format!("{}::{}", hier.path[hier.path.len() - 2].name.name, n));
                    params
                        .get(n)
                        .map(|v| v.width)
                        // §20.6.2: a declared variable of this scope, then a
                        // typedef with unpacked dimensions — see the matching
                        // arm in `const_eval_i64_with_params`.
                        .or_else(|| {
                            decl_var_query("$bits", std::slice::from_ref(inner), Some(params))
                                .or_else(|| {
                                    (hier.path.len() == 1)
                                        .then(|| typedef_unpacked_bits(n, Some(params)))
                                        .flatten()
                                })
                                .and_then(|b| u32::try_from(b).ok())
                        })
                        .or_else(|| {
                            TYPEDEFS_TLS.with(|td| {
                                let b = td.borrow();
                                let m = b.as_ref()?;
                                scoped
                                    .as_deref()
                                    .and_then(|k| m.get(k).copied())
                                    .or_else(|| m.get(n).copied())
                            })
                        })
                        // §20.6.2 over a BUILT-IN integer atom type — see the
                        // matching arm in `const_eval_i64_with_params`.
                        .or_else(|| atom_keyword_width(n))
                        .unwrap_or(0)
                }
                // §7.2.2: `a[i].field.subfield` — the base is not a bare ident.
                ExprKind::MemberAccess { expr: base, member }
                    if !matches!(base.kind, ExprKind::Ident(_)) =>
                {
                    const_struct_field_in_base(base, &member.name)
                        .map(|(_, w)| w)
                        .unwrap_or(0)
                }
                // §26.3 package-/class-scoped type — see the matching arm in
                // `const_eval_i64_with_params`. A struct MEMBER select
                // (`$bits(CDEF.b)`) answers from the base's field layout.
                ExprKind::MemberAccess { expr: base, member }
                    if matches!(base.kind, ExprKind::Ident(_)) =>
                {
                    let from_layout =
                        const_struct_field_in_base(base, &member.name).map(|(_, w)| w);
                    // §26.3: `P::T` must reach THAT package's typedef. Package
                    // typedefs also occupy one global bare-name table, so a
                    // same-named typedef in another package can own the bare
                    // key — answering from it reported the wrong type's width.
                    let scoped = if let ExprKind::Ident(h) = &base.kind {
                        h.path
                            .last()
                            .map(|s| format!("{}::{}", s.name.name, member.name))
                    } else {
                        None
                    };
                    from_layout
                        .or_else(|| {
                            TYPEDEFS_TLS.with(|td| {
                                let b = td.borrow();
                                let m = b.as_ref()?;
                                scoped
                                    .as_deref()
                                    .and_then(|k| m.get(k).copied())
                                    .or_else(|| m.get(member.name.as_str()).copied())
                            })
                        })
                        .unwrap_or(0)
                }
                ExprKind::Number(NumberLiteral::Integer { size: Some(s), .. }) => *s,
                ExprKind::Number(n @ NumberLiteral::Integer { size: None, .. }) => {
                    number_literal_width(n)
                }
                ExprKind::Number(NumberLiteral::UnbasedUnsized(_)) => 1,
                ExprKind::SystemCall { name: cn, .. } if is_cast_call(cn) => {
                    const_cast_bits(inner, params).unwrap_or(0)
                }
                // §20.6.2/§11.6.1: a concatenation, replication, operator,
                // conditional or call operand has its self-determined width.
                ExprKind::Concatenation(_)
                | ExprKind::Replication { .. }
                | ExprKind::Paren(_)
                | ExprKind::Binary { .. }
                | ExprKind::Unary { .. }
                | ExprKind::Conditional { .. }
                | ExprKind::Call { .. } => const_self_width(inner, params).unwrap_or(0),
                // §20.6.2 `$bits(<data_type>)`. `logic [0:0][1:0][1:0]` parses
                // to a TypeLiteral, which no arm evaluated, so the `_ => 0`
                // default made the enclosing localparam 0 — and
                // `logic [W-1:0]` then declared a degenerate vector.
                ExprKind::TypeLiteral(dt) => {
                    typedefs_snapshot(|td| resolve_type_width_env(dt, Some(params), td))
                }
                // §20.6.2 over a TYPEDEF carrying packed dimensions —
                // `$bits(pkg::t [0:0][1:0])`. A scoped type name is not a
                // data-type keyword, so the parser cannot produce a
                // TypeLiteral and emits a RangeSelect chain over the
                // MemberAccess instead; evaluated as an expression that is a
                // 2-bit part-select. It is really the typedef's width times
                // every dimension — 2 instead of 292 truncated a flattened
                // pipeline stage to two bits.
                ExprKind::RangeSelect { .. } => {
                    let mut dims: Vec<(i64, i64)> = Vec::new();
                    let mut cur: &Expression = inner;
                    let mut ok = true;
                    while let ExprKind::RangeSelect {
                        expr,
                        kind,
                        left,
                        right,
                    } = &cur.kind
                    {
                        if !matches!(kind, crate::ast::expr::RangeKind::Constant) {
                            ok = false;
                            break;
                        }
                        match (
                            const_eval_i64_with_params_env(left, Some(params)),
                            const_eval_i64_with_params_env(right, Some(params)),
                        ) {
                            (Some(l), Some(r)) => dims.push((l, r)),
                            _ => {
                                ok = false;
                                break;
                            }
                        }
                        cur = expr.as_ref();
                    }
                    // The base must name a TYPE — a signal part-select keeps
                    // its ordinary meaning and is left to the arms above.
                    let tname = match &cur.kind {
                        ExprKind::MemberAccess { member, .. } => Some(member.name.clone()),
                        ExprKind::Ident(h) => h.path.last().map(|sg| sg.name.name.clone()),
                        _ => None,
                    };
                    let base_w = tname.filter(|_| ok).and_then(|n| {
                        TYPEDEFS_TLS
                            .with(|td| td.borrow().as_ref().and_then(|m| m.get(&n).copied()))
                    });
                    match base_w {
                        Some(bw) => {
                            let mut total = bw as i64;
                            for (l, r) in dims {
                                total = total.saturating_mul((l - r).abs() + 1);
                            }
                            total as u32
                        }
                        None => 0,
                    }
                }
                _ => 0,
            };
            Value::from_u64(w as u64, 32)
        }
        // `$unsigned`/`$signed` in const-eval — width-preserving identity.
        // §6.24.1 casts in CONSTANT context — the parser lowers `5'(x)`,
        // `int'(x)` and `T'(x)` to intrinsics that had no const-eval arms, so
        // `localparam int RI = int'(RP * 4.0)` silently became 0.
        // §20.5 real↔integer conversions and rounding in CONSTANT context.
        // None had const-eval arms, so `localparam int PI_I = $rtoi(PI*100.0)`
        // evaluated to 0.
        // §11.4.13: a tolerance range bound.
        ExprKind::SystemCall { name, args }
            if name == crate::ast::expr::TOLERANCE_BOUND_FN && args.len() == 3 =>
        {
            let a = eval_const_expr_val_inner(&args[0], params, types);
            let b = eval_const_expr_val_inner(&args[1], params, types);
            let mode = eval_const_expr_val_inner(&args[2], params, types)
                .to_u64()
                .unwrap_or(0);
            Value::tolerance_bound(&a, &b, mode & 2 != 0, mode & 1 != 0)
        }
        ExprKind::SystemCall { name, args }
            if matches!(
                name.as_str(),
                "$rtoi"
                    | "$itor"
                    | "$realtobits"
                    | "$bitstoreal"
                    | "$shortrealtobits"
                    | "$bitstoshortreal"
            ) && args.len() == 1 =>
        {
            let v = eval_const_expr_val_inner(&args[0], params, types);
            let f = v.to_f64();
            match name.as_str() {
                // $rtoi TRUNCATES toward zero (unlike an assignment to int,
                // which rounds).
                "$rtoi" => Value::rtoi(f),
                "$itor" => Value::from_f64(f),
                "$realtobits" => Value::from_u64(f.to_bits(), 64),
                "$bitstoreal" => Value::from_f64(f64::from_bits(v.to_u64().unwrap_or(0))),
                "$shortrealtobits" => Value::from_u64((f as f32).to_bits() as u64, 32),
                _ => Value::from_f64(f32::from_bits(v.to_u64().unwrap_or(0) as u32) as f64),
            }
        }
        ExprKind::SystemCall { name, args } if const_real_math_arity(name) == Some(args.len()) => {
            let a = eval_const_expr_val_inner(&args[0], params, types).to_f64();
            let mut b = || eval_const_expr_val_inner(&args[1], params, types).to_f64();
            let result = match name.as_str() {
                "$ln" => a.ln(),
                "$log10" => a.log10(),
                "$log2" => a.log2(),
                "$exp" => a.exp(),
                "$sqrt" => a.sqrt(),
                "$floor" => a.floor(),
                "$ceil" => a.ceil(),
                "$pow" => a.powf(b()),
                "$sin" => a.sin(),
                "$cos" => a.cos(),
                "$tan" => a.tan(),
                "$asin" => a.asin(),
                "$acos" => a.acos(),
                "$atan" => a.atan(),
                "$atan2" => a.atan2(b()),
                "$hypot" => a.hypot(b()),
                "$sinh" => a.sinh(),
                "$cosh" => a.cosh(),
                "$tanh" => a.tanh(),
                "$asinh" => a.asinh(),
                "$acosh" => a.acosh(),
                _ => a.atanh(),
            };
            Value::from_f64(result)
        }
        ExprKind::SystemCall { name, args } if name == "$__xz_size_cast" && args.len() == 2 => {
            let n = eval_const_expr_val_inner(&args[0], params, types)
                .to_u64()
                .unwrap_or(32)
                .max(1) as u32;
            // §6.24.1: the cast width is the operand's evaluation CONTEXT —
            // `5'(3'd7 + 3'd6)` is 13, not the 3-bit-wrapped 5.
            let v = eval_const_expr_val_with_ctx(&args[1], params, Some(n), types);
            if v.is_real {
                let f = v.to_f64();
                let r = if f >= 0.0 {
                    (f + 0.5).floor()
                } else {
                    (f - 0.5).ceil()
                };
                Value::from_u64((r as i64) as u64, 64).resize(n)
            } else {
                v.resize(n)
            }
        }
        ExprKind::SystemCall { name, args } if name == "$__xz_named_cast" && args.len() == 2 => {
            // §6.24.1: `id'(v)` where `id` resolves to a CONSTANT — a size
            // cast at that width (`localparam [AW-1:0] TOP = AW'(6);` read 0
            // because this intrinsic had no const arm at all).
            // A package-scoped target (`pkg::T'(v)`) prefers its qualified
            // `pkg::T` registration.
            let (nm, scoped) = match &args[0].kind {
                ExprKind::Ident(h) if h.path.len() == 1 => {
                    (Some(h.path[0].name.name.clone()), None)
                }
                ExprKind::MemberAccess { expr: base, member } => match &base.kind {
                    ExprKind::Ident(h) if h.path.len() == 1 => (
                        Some(member.name.clone()),
                        Some(format!("{}::{}", h.path[0].name.name, member.name)),
                    ),
                    _ => (None, None),
                },
                _ => (None, None),
            };
            if let Some(nm) = nm {
                if let Some(w) = scoped
                    .as_ref()
                    .and_then(|k| params.get(k))
                    .or_else(|| params.get(&nm))
                    .and_then(|v| v.to_u64())
                    .or_else(|| param_fallback_get(&nm).and_then(|v| v.to_u64()))
                {
                    let w = (w.max(1)) as u32;
                    let mut out =
                        eval_const_expr_val_with_ctx(&args[1], params, Some(w), types).resize(w);
                    out.is_signed = false;
                    return out;
                }
                // §6.24.1 TYPE cast to an integral typedef: the value takes the
                // typedef's width and signing, and the target is the operand's
                // context, as for a keyword type cast below.
                if let Some((w, signed)) = const_typedef_cast_target(&nm, scoped.as_deref(), params)
                {
                    let v = eval_const_expr_val_with_ctx(&args[1], params, Some(w), types);
                    if !v.is_real {
                        let mut out = v.resize(w);
                        out.is_signed = signed;
                        return out;
                    }
                }
                // A typedef whose declared type is not known here: only an
                // operator expression can observe a context, and the width
                // table cannot tell an integral typedef from a string one, so
                // a bare operand keeps its pass-through.
                let td = TYPEDEFS_TLS.with(|c| {
                    c.borrow().as_ref().and_then(|m| {
                        scoped
                            .as_ref()
                            .and_then(|k| m.get(k))
                            .or_else(|| m.get(&nm))
                            .copied()
                    })
                });
                if let Some(w) = td.filter(|&w| w > 0 && is_context_operator(&args[1])) {
                    let v = eval_const_expr_val_with_ctx(&args[1], params, Some(w), types);
                    if !v.is_real {
                        return v.resize(w);
                    }
                }
            }
            eval_const_expr_val_inner(&args[1], params, types)
        }
        ExprKind::SystemCall { name, args } if name == "$__xz_type_cast" && args.len() == 2 => {
            if let ExprKind::TypeLiteral(dt) = &args[0].kind {
                if is_type_real(dt) {
                    let f = eval_const_expr_val_inner(&args[1], params, types).to_f64();
                    return Value::from_f64(if matches!(dt.as_ref(), DataType::Real {
                        kind: crate::ast::types::RealType::ShortReal, ..
                    }) { f as f32 as f64 } else { f });
                }
                let w = TYPEDEFS_TLS
                    .with(|c| {
                        let b = c.borrow();
                        resolve_type_width_env(dt, Some(params), b.as_ref())
                    })
                    .max(1);
                // §6.24.1: an integral target is the operand's context width.
                let integral = matches!(
                    dt.as_ref(),
                    DataType::IntegerAtom { .. } | DataType::IntegerVector { .. }
                );
                let v = if integral {
                    eval_const_expr_val_with_ctx(&args[1], params, Some(w), types)
                } else {
                    eval_const_expr_val_inner(&args[1], params, types)
                };
                let mut out = if v.is_real {
                    // §6.24.1: real-to-int conversion ROUNDS (away from zero).
                    let f = v.to_f64();
                    let r = if f >= 0.0 {
                        (f + 0.5).floor()
                    } else {
                        (f - 0.5).ceil()
                    };
                    Value::from_u64((r as i64) as u64, 64).resize(w)
                } else {
                    v.resize(w)
                };
                out.is_signed = is_type_signed(dt);
                out
            } else {
                eval_const_expr_val_inner(&args[1], params, types)
            }
        }
        ExprKind::SystemCall { name, args } if name == "$unsigned" || name == "$signed" => {
            let mut v = args
                .first()
                .map(|a| eval_const_expr_val_inner(a, params, types))
                .unwrap_or_else(|| Value::zero(32));
            // §20.5: `$signed(x)` reinterprets x as signed so a later width
            // extension sign-extends the MSB (`$signed(1'b1)` -> 2'b11), and
            // `$unsigned(x)` forces zero-extension.
            v.is_fill = false;
            v.is_signed = name == "$signed";
            v
        }
        // LRM §20.9 bit-introspection system functions in
        // value-producing const-eval position. Mirror the i64
        // const-eval implementations in `const_eval_i64_with_params`.
        ExprKind::SystemCall { name, args }
            if matches!(
                name.as_str(),
                "$countones" | "$onehot" | "$onehot0" | "$isunknown" | "$countbits"
            ) =>
        {
            let Some(arg) = args.first() else {
                return Value::zero(32);
            };
            // §20.9: count over every bit of the operand, x and z included;
            // a 64-bit integer view loses the high bits and reads x/z as 0.
            use crate::value::LogicBit;
            let v = eval_const_expr_val_inner(arg, params, types);
            let count = |want: &[LogicBit]| {
                (0..v.width as usize)
                    .filter(|&i| want.contains(&v.get_bit(i)))
                    .count() as u64
            };
            let result: u64 = match name.as_str() {
                "$countones" => count(&[LogicBit::One]),
                "$onehot" => (count(&[LogicBit::One]) == 1) as u64,
                "$onehot0" => (count(&[LogicBit::One]) <= 1) as u64,
                "$isunknown" => (count(&[LogicBit::X, LogicBit::Z]) != 0) as u64,
                "$countbits" => {
                    // A control bit is 1-bit logic; only its LSB counts.
                    let mut want = Vec::new();
                    for ctl in &args[1..] {
                        let bit = eval_const_expr_val_inner(ctl, params, types).get_bit(0);
                        if !want.contains(&bit) {
                            want.push(bit);
                        }
                    }
                    count(&want)
                }
                _ => 0,
            };
            // §20.9: `$onehot`/`$onehot0`/`$isunknown` return `bit`; the
            // count functions return `int`.
            let w = if matches!(name.as_str(), "$onehot" | "$onehot0" | "$isunknown") {
                1
            } else {
                32
            };
            Value::from_u64(result, w)
        }
        // §20.7 over an explicit type (`$size(logic [7:0])`).
        ExprKind::SystemCall { name, args }
            if matches!(
                name.as_str(),
                "$size"
                    | "$left"
                    | "$right"
                    | "$high"
                    | "$low"
                    | "$increment"
                    | "$dimensions"
                    | "$unpacked_dimensions"
            ) && matches!(
                args.first().map(|a| &a.kind),
                Some(ExprKind::TypeLiteral(_))
            ) =>
        {
            let Some(ExprKind::TypeLiteral(dt)) = args.first().map(|a| &a.kind) else {
                unreachable!()
            };
            match type_literal_query(name, dt, args, Some(params)) {
                Some(v) => {
                    let mut out = Value::from_u64((v as u64) & 0xFFFF_FFFF, 32);
                    out.is_signed = true;
                    out
                }
                None => Value::new(32),
            }
        }
        // §20.7, §23.6: a query over a generate block's variable by path
        // (`g[0].arr`) answers from the block's declared shape.
        ExprKind::SystemCall { name, args }
            if args
                .first()
                .is_some_and(|a| matches!(a.kind, ExprKind::MemberAccess { .. }))
                && decl_var_query(name, args, Some(params)).is_some() =>
        {
            let v = decl_var_query(name, args, Some(params)).unwrap_or_default();
            let mut out = Value::from_u64((v as u64) & 0xFFFF_FFFF, 32);
            out.is_signed = true;
            out
        }
        // LRM §20.7 array-introspection on an array-name ident: consults
        // ARRAYS_TLS (populated at end of elaborate_module_with_defs and
        // via runtime path before deferred-param eval).
        ExprKind::SystemCall { name, args }
            if matches!(
                name.as_str(),
                "$size"
                    | "$left"
                    | "$right"
                    | "$high"
                    | "$low"
                    | "$increment"
                    | "$dimensions"
                    | "$unpacked_dimensions"
            ) && args
                .first()
                .map(|a| matches!(a.kind, ExprKind::Ident(_)))
                .unwrap_or(false) =>
        {
            // §20.7: a declared fixed-size variable answers from its declared
            // type (see `decl_var_query`); the result is an `integer`.
            if let Some(v) = decl_var_query(name, args, Some(params)) {
                let mut out = Value::from_u64((v as u64) & 0xFFFF_FFFF, 32);
                out.is_signed = true;
                return out;
            }
            let arg = args.first().unwrap();
            let arr_name = if let ExprKind::Ident(hier) = &arg.kind {
                hier.path
                    .last()
                    .map(|s| s.name.name.clone())
                    .unwrap_or_default()
            } else {
                String::new()
            };
            let res =
                ARRAYS_TLS.with(|ar| ar.borrow().as_ref().and_then(|m| m.get(&arr_name).copied()));
            if let Some((lo, hi, _ndim)) = res {
                let v: i64 = match name.as_str() {
                    "$size" => hi - lo + 1,
                    "$left" => lo,
                    "$right" => hi,
                    "$high" => hi.max(lo),
                    "$low" => lo.min(hi),
                    "$dimensions" => 1,
                    _ => 0,
                };
                Value::from_u64(v as u64, 32)
            } else if let Some(v) = TYPEDEFS_TLS
                .with(|td| {
                    TYPEDEF_SHAPES_TLS.with(|sh| {
                        let sh = sh.borrow();
                        type_query_dims_by_name(
                            &arr_name,
                            Some(params),
                            td.borrow().as_ref(),
                            Some(&sh.0),
                            Some(&sh.1),
                        )
                    })
                })
                .and_then(|q| {
                    // §20.7 accepts a TYPE as the operand: `$size(int)` is 32,
                    // `$left(byte)` 7. The name parses as a plain Ident (see
                    // `parse_call_args`), so a `localparam W = $size(int)`
                    // const-folded to ZERO here and every vector sized `[W-1:0]`
                    // elaborated to `[-1:0]` — two bits.
                    let dim = args
                        .get(1)
                        .and_then(|d| const_eval_i64_with_params_env(d, Some(params)))
                        .unwrap_or(1) as usize;
                    type_query_bound(name, &q, dim)
                })
            {
                let mut out = Value::from_u64((v as u64) & 0xFFFF_FFFF, 32);
                out.is_signed = true;
                out
            } else {
                Value::zero(32)
            }
        }
        ExprKind::Conditional {
            condition,
            then_expr,
            else_expr,
        } => {
            let c = eval_const_expr_val_inner(condition, params, types);
            let (taken, other) = if c.is_true() {
                (then_expr, else_expr)
            } else {
                (else_expr, then_expr)
            };
            let v = eval_const_expr_val_inner(taken, params, types);
            if v.is_real && c.is_nonzero().is_some() {
                return v;
            }
            let other_real = const_context::infer(other, params, types).real;
            let v = if !v.is_real && other_real {
                const_eval_in_real_context(taken, params)
            } else {
                v
            };
            if v.is_real && c.is_nonzero().is_none() {
                let other = if other_real {
                    eval_const_expr_val_inner(other, params, types)
                } else {
                    const_eval_in_real_context(other, params)
                };
                v.merge_unknown(&other)
            } else {
                v
            }
        }
        ExprKind::Concatenation(parts) => {
            // §6.16: a concatenation involving a STRING operand is TEXT
            // concatenation. Bit-concatenating instead produced only the last
            // operand's text (`localparam string CAT = {PFX, NAME}` = "widget"),
            // because a string Value is padded to its placeholder width.
            let is_text = parts.iter().any(|p| match &p.kind {
                ExprKind::StringLiteral(_) => true,
                ExprKind::Ident(h) => h
                    .path
                    .last()
                    .is_some_and(|seg| tls_is_string_param(&seg.name.name)),
                _ => false,
            });
            if is_text {
                let mut text: Vec<u8> = Vec::new();
                for p in parts {
                    text.extend_from_slice(
                        &eval_const_expr_val_inner(p, params, types).sv_string_bytes(),
                    );
                }
                return Value::from_string(&String::from_utf8_lossy(&text));
            }
            let mut r = Value::zero(0);
            for p in parts.iter().rev() {
                r = eval_const_expr_val_inner(p, params, types).concat_with(&r);
            }
            r
        }
        ExprKind::Replication { count, exprs } => {
            // §11.4.12.1: the count is a non-negative constant. A signed
            // count is read as signed, so `{$bits(T) - 1{1'b1}}` with an
            // unresolved `T` replicates nothing instead of wrapping to
            // ~4 G copies (built one concatenation at a time, it never
            // finished elaborating).
            let cv = eval_const_expr_val_inner(count, params, types);
            let n = if cv.has_xz() {
                0
            } else if cv.is_signed {
                cv.to_i64().unwrap_or(0).max(0) as usize
            } else {
                cv.to_u64().unwrap_or(1) as usize
            };
            let mut inner = Value::zero(0);
            for p in exprs.iter().rev() {
                inner = eval_const_expr_val_inner(p, params, types).concat_with(&inner);
            }
            inner.replicate(n)
        }
        // SystemVerilog `for (j = 0; j < N; j = j+1)` parses the increment
        // as an `AssignExpr { lvalue: j, rvalue: j+1 }`. As a const-eval
        // result, the value of `j = j+1` is the rvalue's value (the
        // assigned-after value). Without this case the increment falls to
        // `Value::zero(32)` and the generate-for loop never terminates
        // until the 10000-iter safety cap fires — observed on E902
        // `cr_clic_sel` where the inner `for (j=0; j<DATA_WIDTH; j=j+1)`
        // ran ~313× over budget and consumed ~1.4 GB elaborating phantom
        // assigns.
        ExprKind::AssignExpr { rvalue, .. } => eval_const_expr_val_inner(rvalue, params, types),
        // User-defined ceil-log2 helper used as a constant function — most
        // notably HardFloat's `clog2` (`for (clog2=0; fa>0; …) fa>>=1;` over
        // `a-1`), which is exactly `$clog2`. Without const-eval it returned 0, so
        // `alignDistWidth = clog2(sigWidth)` was 0 and `inWidth = alignDistWidth-2`
        // wrapped to ~u32::MAX. Recognise a 1-arg call named `clog2` and fold it.
        ExprKind::Call { func, args }
            if matches!(&func.kind, ExprKind::Ident(h)
                if h.path.last().map(|s| s.name.name.as_str()) == Some("clog2")) =>
        {
            let n = args
                .first()
                .map(|a| {
                    eval_const_expr_val_inner(a, params, types)
                        .to_u64()
                        .unwrap_or(0)
                })
                .unwrap_or(0);
            Value::from_u64(ceil_log2(n), 32)
        }
        // §7.2.1 struct member select in const context: `s.field`. Slice the
        // field out of the struct-typed parameter Value using its registered
        // packed layout. Enables black-parrot's
        // `localparam icache_sets_p = proc_param_lp.icache_sets`.
        ExprKind::MemberAccess { expr: base, member } => {
            // A whole parameter (`pkg::C`, `u.P`). An indexed field
            // (`ENC[i].exp_bits`) must be sliced from the element; a stored
            // `ENC[0].exp_bits` from an earlier, still-zero pack was winning
            // and `fp_width` stayed 1 after the array value was corrected.
            // Only a PACKED array base is sliced; an indexed path into an
            // interface or instance array (`b[0].W` of `bus_if b[0:1]`) is
            // registered under that path and read from it.
            if let Some(path) = const_parameter_path(expr, Some(params))
                && (!path.contains('[')
                    || !PACKED_ELEM_W_TLS.with(|c| {
                        c.borrow()
                            .contains_key(path.split('[').next().unwrap_or(&path))
                    }))
                && let Some(value) = params.get(&path)
            {
                return value.clone();
            }
            // §8.23 / §8.25.1: a class-scoped constant (`cls::N`,
            // `pkg::cls::N`, `cls#(4)::N`).
            if let Some(v) = class_scoped_const(base, &member.name, params) {
                return v;
            }
            let base_val = eval_const_expr_val_inner(base, params, types);
            if let ExprKind::Ident(h) = &base.kind {
                let nm = h.path.last().map(|s| s.name.name.as_str()).unwrap_or("");
                // Package-scoped constant `pkg::CONST` (parsed as MemberAccess):
                // when the base names no struct value, resolve the member as an
                // imported package constant / enum member (held by bare name).
                let base_is_struct = STRUCT_FIELDS_TLS.with(|c| c.borrow().contains_key(nm));
                if !base_is_struct && !params.contains_key(nm) {
                    // §26.3: the EXACT scoped alias first (`alias_pkg_param`
                    // registers every package parameter as `pkg::name`).
                    // Resolving by bare member name alone meant a package
                    // constant referenced scoped-but-never-imported
                    // (`$clog2(cfg_pkg::DEPTH) - 6`) read whatever the bare
                    // slot held — usually nothing — and evaluated 0, driving
                    // the dependent parameter negative.
                    if let Some(v) = params.get(&format!("{}::{}", nm, member.name)) {
                        return v.clone();
                    }
                    if let Some(v) = params.get(&member.name) {
                        return v.clone();
                    }
                    // A package constant referenced from a scope whose local
                    // env doesn't carry it (an instance header default
                    // `parameter cs_t C = cfg_pkg::CDEF`): same global
                    // fallback the bare-Ident arm uses.
                    if let Some(v) = param_fallback_get(&member.name) {
                        return v;
                    }
                }
                if let Some(found) = STRUCT_FIELDS_TLS.with(|c| {
                    c.borrow().get(nm).and_then(|layout| {
                        layout
                            .iter()
                            .find(|(f, _, _)| f == &member.name)
                            .map(|&(_, off, w)| (off, w))
                    })
                }) {
                    let (off, w) = found;
                    if w > 0 && off + w <= base_val.width {
                        return base_val.range_select((off + w - 1) as usize, off as usize);
                    }
                }
            }
            // §7.2.2: `array[i].field.subfield`. The base is itself a select,
            // so the layout key is the root parameter (`rsp.accept` on
            // `OUTERS`), and the offset is relative to that base value.
            if let Some((off, w)) = const_struct_field_in_base(base, &member.name) {
                if w > 0 && off + w <= base_val.width {
                    return base_val.range_select((off + w - 1) as usize, off as usize);
                }
            }
            Value::zero(32)
        }
        // Packed-array element select in const context: `a[i]`. For an
        // array-of-structs parameter with a registered element width, slice
        // element `i` (`[i*elem_w +: elem_w]`). Enables black-parrot's
        // `localparam bp_proc_param_s proc_param_lp = all_cfgs_gp[bp_params_p]`.
        // Falls back to a single-bit select for plain vectors.
        ExprKind::Index { expr: base, index } => {
            let base_val = eval_const_expr_val_inner(base, params, types);
            let index_value = eval_const_expr_val_inner(index, params, types);
            let signed_index = index_value.to_i64();
            let idx = index_value.to_u64().unwrap_or(0);
            // §26.3: a SCOPED base (`pkg::LIM[3]`, `inst.mod.A[2]`) —
            // `register_array_param` stores package array elements under
            // the qualified `pkg::LIM[i]` key. Try the qualified spellings
            // before the bare-leaf lookup below.
            {
                let mut keys = Vec::new();
                const_index_base_keys(base, Some(params), &mut keys);
                for k in &keys {
                    if let Some(ev) =
                        signed_index.and_then(|i| params.get(&format!("{}[{}]", k, i)))
                    {
                        return ev.clone();
                    }
                    // §26.3: an element of a PACKAGE array parameter read in
                    // an instance's scope (`p::V[k]`, or `V[k]` after
                    // `import p::*` or `import p::V`). The scope's map need not
                    // hold it: a scoped name is in the package/$unit snapshot,
                    // as its scalars are for the Ident arm, and a bare name is
                    // read under the package that this definition imports it
                    // from. An array of the scope's own (any row of it) takes
                    // precedence. `keys()` collects every row of the lookup,
                    // so scan them only once the package does hold this
                    // element.
                    let root = &k[..k.find('[').unwrap_or(k.len())];
                    if !params.contains_key(root)
                        && let Some(i) = signed_index
                        && let Some(ev) = if root.contains("::") || root.contains('.') {
                            param_fallback_get(&format!("{k}[{i}]"))
                        } else {
                            imported_array_element(k, i, params)
                        }
                        && !params.keys().iter().any(|name| {
                            name.strip_prefix(root).is_some_and(|rest| rest.starts_with('['))
                        })
                    {
                        return ev;
                    }
                    // §7.4.6: an invalid array index reads the element's
                    // default; it must not select an unrelated bare name.
                    if let Some(value) = array_params::default_value(k) {
                        // A packed array (`enc_t [0:4] ENC`) also has an
                        // element width. Its index slices the aggregate;
                        // the unpacked default is 0 and was winning whenever
                        // the bare name was absent from this map (`p::ENC`
                        // only), so `ENC[0].exp_bits` folded to 0.
                        let packed =
                            PACKED_ELEM_W_TLS.with(|c| c.borrow().contains_key(k));
                        // A scalar homonym in another instance must keep
                        // its packed-select semantics. Array overrides may
                        // retain a packed aggregate alongside their elements.
                        let prefix = format!("{k}[");
                        if !packed
                            && (k.contains("::")
                                || !params.contains_key(k)
                                || params.keys().iter().any(|name| name.starts_with(&prefix)))
                        {
                            return value;
                        }
                    }
                }
            }
            if let ExprKind::Ident(h) = &base.kind {
                let nm = h.path.last().map(|s| s.name.name.as_str()).unwrap_or("");
                // §6.20.2: element of an unpacked-array parameter — stored in
                // the env under "name[idx]" by register_array_param.
                if h.path.len() == 1
                    && let Some(ev) =
                        signed_index.and_then(|i| params.get(&format!("{}[{}]", nm, i)))
                {
                    return ev.clone();
                }
            }
            if let Some(elem) = const_packed_array_elem(
                base,
                &base_val,
                signed_index.unwrap_or(idx as i64),
                params,
            ) {
                return elem;
            }
            let i = idx as usize;
            if (i as u32) < base_val.width {
                base_val.range_select(i, i)
            } else {
                Value::zero(1)
            }
        }
        // §11.5.1 part-select in CONSTANT context: `P[11:4]`, `P[7-:8]`,
        // `P[4+:8]` on a parameter. There was no arm, so every range form
        // fell to the zero fallback and a localparam sliced from another
        // parameter silently became 0 (bit-selects worked). Bit numbering is
        // the value's own [width-1:0]; parameters declared with a non-zero
        // LSB keep their raw bit positions (matching the Index arm above).
        ExprKind::RangeSelect {
            expr: base,
            left,
            right,
            kind,
        } => {
            let base_val = eval_const_expr_val_inner(base, params, types);
            let l = eval_const_expr_val_inner(left, params, types)
                .to_i64()
                .unwrap_or(0);
            let r = eval_const_expr_val_inner(right, params, types)
                .to_i64()
                .unwrap_or(0);
            let (hi, lo) = match kind {
                crate::ast::expr::RangeKind::Constant => (l.max(r), l.min(r)),
                crate::ast::expr::RangeKind::IndexedUp => (l + r - 1, l),
                crate::ast::expr::RangeKind::IndexedDown => (l, l - r + 1),
            };
            if lo >= 0 && hi >= lo && (hi as u32) < base_val.width {
                base_val.range_select(hi as usize, lo as usize)
            } else {
                Value::zero(((hi - lo + 1).max(1)) as u32)
            }
        }
        // §13.4.3: a user constant-function call in a value context — e.g. a
        // struct assignment-pattern field `'{x: x_bits_t'(router_x(r)), ...}`
        // in a generate-for body, which otherwise packed as 0. The result
        // keeps the function's declared return type.
        ExprKind::Call { .. } => {
            const_eval_user_call(expr, Some(&params.to_hashmap()))
                .unwrap_or_else(|| Value::zero(32))
        }
        // §10.9: a typed pattern has its type's value, packed against the
        // typedef snapshot.
        ExprKind::TypedPattern { ty, pattern } => {
            TYPEDEF_TYPES_TLS.with(|types| {
                TYPEDEF_WIDTHS_TLS.with(|widths| {
                    let (types, widths) = (types.borrow(), widths.borrow());
                    pack_typed_pattern(ty, pattern, params, widths.as_ref()?, types.as_ref()?)
                })
            })
            .unwrap_or_else(|| Value::zero(32))
        }
        _ => Value::zero(32),
    };
    // §20.6.2, §20.7, §20.8.1, §20.9: the size, array query, `$clog2` and
    // bit-count functions return `integer` or `int`, which are signed, so
    // `(~2'sb10) + $clog2(8)` is a signed expression (§11.8.1).
    if let ExprKind::SystemCall { name, .. } = &expr.kind
        && !res.is_real
        && matches!(
            name.as_str(),
            "$bits"
                | "$clog2"
                | "$countones"
                | "$countbits"
                | "$size"
                | "$left"
                | "$right"
                | "$low"
                | "$high"
                | "$increment"
                | "$dimensions"
                | "$unpacked_dimensions"
        )
    {
        res.is_signed = true;
    }
    res
}

/// §11.6.1 / §6.24.1: evaluate a constant expression in an ASSIGNMENT-LIKE
/// context of `ctx_w` bits — the operand of a cast. Context-determined
/// operands (arithmetic and bitwise operators, unary `-`/`~`, the `?:` arms,
/// a shift's or power's left operand) are extended to max(`ctx_w`, the
/// expression's own width) BEFORE the operator applies, zero- or
/// sign-extended per the expression's signedness (§11.8.1). So `int'(A + B)`
/// over 8-bit parameters is 300, not the 8-bit-wrapped 44, and in
/// `4'((A + B) / 3)` the sum is taken at the 32 bits the literal brings.
pub(super) fn eval_const_expr_val_ctx(
    expr: &Expression,
    params: &HashMap<String, Value>,
    ctx_w: u32,
) -> Value {
    eval_const_expr_val_with_ctx(
        expr,
        params,
        Some(ctx_w),
        &mut const_context::Types::default(),
    )
}

/// Width and signing of the integral typedef a cast target `nm` (`scoped`
/// when written `pkg::nm`) names, for `nm'(v)` in a constant expression.
/// The instance's own types (`CONST_FN_LOCAL_TYPES`) come first, then the
/// full typedef definitions (`TYPEDEF_SHAPES_TLS`); typedefs of typedefs are
/// followed. The width of an instance's own type comes from its definition
/// (the width table can still hold a type parameter's default); any other
/// comes from the current scope's width table when it has the name. `None` for a name with no known definition, or a string,
/// real or unpacked type: the caller keeps its pass-through.
fn const_typedef_cast_target<P: ParamLookup>(
    nm: &str,
    scoped: Option<&str>,
    params: &P,
) -> Option<(u32, bool)> {
    let local = |n: &str| CONST_FN_LOCAL_TYPES.with(|c| c.borrow().as_ref()?.get(n).cloned());
    let dt = TYPEDEF_SHAPES_TLS.with(|sh| {
        let sh = sh.borrow();
        let mut cur = match scoped {
            Some(k) => sh.0.get(k).or_else(|| sh.0.get(nm))?.clone(),
            None => match local(nm) {
                Some(dt) => dt,
                None if sh.1.contains_key(nm) => return None,
                None => sh.0.get(nm)?.clone(),
            },
        };
        for _ in 0..16 {
            let DataType::TypeReference {
                name, dimensions, ..
            } = &cur
            else {
                break;
            };
            if !dimensions.is_empty() {
                return None;
            }
            let next = name
                .scopes
                .is_empty()
                .then(|| local(&name.name.name))
                .flatten()
                .or_else(|| lookup_scoped_type(name, &sh.0).cloned())?;
            cur = next;
        }
        Some(cur)
    })?;
    let integral = match &dt {
        DataType::IntegerAtom { .. } | DataType::IntegerVector { .. } | DataType::Enum(_) => true,
        DataType::Struct(s) => s.packed,
        _ => false,
    };
    if !integral {
        return None;
    }
    let own = scoped.is_none() && local(nm).is_some();
    let w = TYPEDEFS_TLS
        .with(|c| {
            let b = c.borrow();
            let m = b.as_ref().filter(|_| !own)?;
            scoped.and_then(|k| m.get(k)).or_else(|| m.get(nm)).copied()
        })
        .filter(|&w| w > 0)
        .unwrap_or_else(|| {
            TYPEDEFS_TLS.with(|c| resolve_type_width_env(&dt, Some(params), c.borrow().as_ref()))
        });
    (w > 0).then(|| (w, is_type_signed(&dt)))
}

/// True for an expression whose operands a surrounding context widens — an
/// arithmetic, bitwise, shift or power operator, unary `-`/`~`, or `?:`.
pub(super) fn is_context_operator(expr: &Expression) -> bool {
    match &expr.kind {
        ExprKind::Paren(inner) => is_context_operator(inner),
        ExprKind::Binary { op, .. } => matches!(
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
                | BinaryOp::ArithShiftLeft
                | BinaryOp::ShiftRight
                | BinaryOp::ArithShiftRight
                | BinaryOp::Power
        ),
        ExprKind::Unary { op, .. } => {
            matches!(op, UnaryOp::Plus | UnaryOp::Minus | UnaryOp::BitNot)
        }
        ExprKind::Conditional { .. } => true,
        _ => false,
    }
}

/// The context fold behind `eval_const_expr_val_ctx`: `None` when a
/// sub-expression cannot take part (for example a real leaf),
/// and the caller keeps the self-determined value.
pub(super) fn const_ctx_fold<P: ParamLookup>(
    expr: &Expression,
    params: &P,
    w: u32,
    signed: bool,
    types: &mut const_context::Types,
) -> Option<Value> {
    let mut value = match &expr.kind {
        ExprKind::Paren(inner) => const_ctx_fold(inner, params, w, signed, types)?,
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
            ) =>
        {
            let l = const_ctx_fold(left, params, w, signed, types)?;
            let r = const_ctx_fold(right, params, w, signed, types)?;
            match op {
                BinaryOp::Add => l.add(&r),
                BinaryOp::Sub => l.sub(&r),
                BinaryOp::Mul => l.mul(&r),
                BinaryOp::Div => l.div(&r),
                BinaryOp::Mod => l.modulo(&r),
                BinaryOp::BitAnd => l.bitwise_and(&r),
                BinaryOp::BitOr => l.bitwise_or(&r),
                BinaryOp::BitXor => l.bitwise_xor(&r),
                _ => l.bitwise_xor(&r).bitwise_not(),
            }
        }
        // The shift amount and the exponent stay self-determined.
        ExprKind::Binary { op, left, right }
            if matches!(
                op,
                BinaryOp::ShiftLeft
                    | BinaryOp::ArithShiftLeft
                    | BinaryOp::ShiftRight
                    | BinaryOp::ArithShiftRight
                    | BinaryOp::Power
            ) =>
        {
            let l = const_ctx_fold(left, params, w, signed, types)?;
            let r = eval_const_expr_val_inner(right, params, types);
            match op {
                BinaryOp::ShiftLeft | BinaryOp::ArithShiftLeft => l.shift_left(&r),
                BinaryOp::ShiftRight => l.shift_right(&r),
                BinaryOp::ArithShiftRight => l.arith_shift_right(&r),
                _ => l.power(&r),
            }
        }
        ExprKind::Unary {
            op: op @ (UnaryOp::Plus | UnaryOp::Minus | UnaryOp::BitNot),
            operand,
        } => {
            let v = const_ctx_fold(operand, params, w, signed, types)?;
            match op {
                UnaryOp::Minus => v.negate(),
                UnaryOp::BitNot => v.bitwise_not(),
                _ => v,
            }
        }
        ExprKind::Conditional {
            condition,
            then_expr,
            else_expr,
        } => {
            // §11.4.11: a condition with a known 1 bit is true even when
            // other bits are x or z; only an ambiguous one merges the arms.
            let c = eval_const_expr_val_inner(condition, params, types);
            let Some(taken) = c.is_nonzero() else {
                let left = const_ctx_fold(then_expr, params, w, signed, types)?;
                let right = const_ctx_fold(else_expr, params, w, signed, types)?;
                return Some(left.merge_unknown(&right));
            };
            let arm = if taken { then_expr } else { else_expr };
            const_ctx_fold(arm, params, w, signed, types)?
        }
        // Self-determined leaf: extend it into the context.
        _ => {
            let mut v = eval_const_expr_val_inner(expr, params, types);
            if v.is_real {
                return None;
            }
            if !signed {
                v.is_signed = false;
            }
            if v.width == w && w != 0 && !v.is_fill {
                v
            } else {
                v.resize_for_assign(w)
            }
        }
    };
    // Arithmetic with X/Z may produce an unsigned Value; its expression
    // type still controls later arithmetic shifts and extension (§11.8.1).
    value.is_signed = signed;
    Some(value)
}

#[cfg(test)]
mod constant_overlay_tests {
    use super::*;
    #[test]
    fn overlay_values_reach_constant_call_arguments() {
        let parsed = crate::parse("module m; function automatic int f(input int x); return x; endfunction localparam X=f(P); endmodule");
        assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
        let crate::ast::Description::Module(m) = &parsed.source.descriptions[0] else { panic!() };
        let ModuleItem::FunctionDeclaration(fd) = &m.items[0] else { panic!() };
        let ModuleItem::LocalparamDeclaration(pd) = &m.items[1] else { panic!() };
        let ParameterKind::Data { assignments, .. } = &pd.kind else { panic!() };
        let expr = assignments[0].init.as_ref().unwrap();
        let old = FUNCS_TLS.with(|c| c.replace(Some(Rc::new(HashMap::from_iter([("f".into(),fd.clone())])))));
        let base = HashMap::from_iter([("P".into(),Value::from_u64(3,32))]);
        let top = HashMap::from_iter([("P".into(),Value::from_u64(9,32))]);
        let env = ParamEnv::Overlay { base: &base, top: &top };
        let upper = HashMap::from_iter([("P".into(), Value::from_u64(11, 32))]);
        let stacked = StackedParamEnv { base: &env, top: &upper };
        let actual = eval_const_expr_val_env(expr, &env).to_u64();
        let nested = eval_const_expr_val_env(expr, &stacked).to_u64();
        let integer = const_eval_i64_with_params_env(expr, Some(&env));
        FUNCS_TLS.with(|c| c.replace(old));
        assert_eq!(actual, Some(9));
        assert_eq!(nested, Some(11));
        assert_eq!(integer, Some(9));
    }
}
