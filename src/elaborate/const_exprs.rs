use super::*;

pub(super) fn expr_has_call(expr: &Expression) -> bool {
    use crate::ast::expr::ExprKind;
    match &expr.kind {
        ExprKind::Call { .. } => true,
        // LRM §20.7 array-introspection system funcs over an array
        // identifier need the runtime path: elaboration's const-eval may
        // not yet have the array registered when the parameter init is
        // walked (order-dependent). Deferring guarantees `elab.arrays`
        // is fully populated and the runtime $size/$left/etc handler
        // resolves correctly.
        // …but a TYPE operand (`$size(int)`, `$left(my_vec_t)`) needs no array
        // table at all, so deferring it only left the parameter 0 for the rest
        // of elaboration — long enough for every `logic [W-1:0]` sized from it
        // to come out as `[-1:0]`, i.e. two bits.
        // A DECLARED fixed-size variable of the scope being elaborated is
        // answered from its declared type (§20.7), so it need not wait either.
        ExprKind::SystemCall { name, args }
            if matches!(
                name.as_str(),
                "$size"
                    | "$left"
                    | "$right"
                    | "$high"
                    | "$low"
                    | "$dimensions"
                    | "$unpacked_dimensions"
                    | "$increment"
            ) =>
        {
            !args
                .first()
                .is_some_and(|a| array_query_operand_is_type(a) || is_decl_shape_operand(a))
        }
        ExprKind::Binary { left, right, .. } => expr_has_call(left) || expr_has_call(right),
        ExprKind::Unary { operand, .. } => expr_has_call(operand),
        ExprKind::Paren(e) => expr_has_call(e),
        ExprKind::Conditional {
            condition,
            then_expr,
            else_expr,
        } => expr_has_call(condition) || expr_has_call(then_expr) || expr_has_call(else_expr),
        _ => false,
    }
}

/// §20.7: does this array-query operand name a TYPE (a built-in keyword or a
/// registered typedef) rather than an array? Such a query is answerable from
/// the type alone, so it need not wait for `elab.arrays`. A name the array
/// table already knows stays an array — a variable never shares its scope with
/// a type of the same name, so only a cross-module coincidence could collide.
fn array_query_operand_is_type(arg: &Expression) -> bool {
    use crate::ast::expr::ExprKind;
    let name = match &arg.kind {
        ExprKind::TypeLiteral(_) => return true,
        ExprKind::Ident(h) => match h.path.last() {
            Some(seg) if seg.selects.is_empty() => seg.name.name.as_str(),
            _ => return false,
        },
        _ => return false,
    };
    if is_builtin_type_keyword(name) {
        return true;
    }
    if ARRAYS_TLS.with(|ar| ar.borrow().as_ref().is_some_and(|m| m.contains_key(name))) {
        return false;
    }
    TYPEDEFS_TLS.with(|td| td.borrow().as_ref().is_some_and(|m| m.contains_key(name)))
}

/// A constant `Value` as a literal expression (sized, with x/z digits), for
/// substituting an elaboration-time constant into another scope's expression.
pub(super) fn const_value_literal(v: &Value, span: Span) -> Option<Expression> {
    if v.is_real {
        return Some(Expression::new(
            ExprKind::Number(NumberLiteral::Real(v.to_f64())),
            span,
        ));
    }
    if v.width == 0 {
        return None;
    }
    Some(Expression::new(
        ExprKind::Number(NumberLiteral::Integer {
            size: Some(v.width),
            signed: v.is_signed,
            base: crate::ast::expr::NumberBase::Binary,
            value: v.to_bin(),
            cached_val: crate::ast::cache::LiteralCache::new(None),
        }),
        span,
    ))
}

pub(super) fn is_const_expr<P: ParamLookup>(expr: &Expression, params: &P) -> bool {
    match &expr.kind {
        ExprKind::Number(_) | ExprKind::StringLiteral(_) => true,
        ExprKind::Ident(hier) => {
            // §11.2.1: a select on a constant is constant only when its index
            // is too. Rewritten generate conditions store indices directly on
            // path segments instead of passing through the Index arm below.
            if !hier.path.iter().flat_map(|s| &s.selects).all(|s| is_const_expr(s, params)) {
                return false;
            }
            let last = hier.path.last().map(|s| s.name.name.as_str()).unwrap_or("");
            // Const if the leaf is a param/enum const (`X`, `pkg::C`), or — for a
            // hierarchical `pt.FIELD` — the BASE is a const struct param.
            let base = hier
                .path
                .first()
                .map(|s| s.name.name.as_str())
                .unwrap_or("");
            params.contains_key(last)
                || (hier.path.len() > 1 && params.contains_key(base))
                // §26.3: `p::Info[k].variant` reaches here folded into the
                // path `p.Info[k].variant` (generate bodies are rewritten
                // that way); the package parameter is under `p::Info`.
                || (hier.root.is_none()
                    && hier.path.first().is_some_and(|s| s.selects.is_empty())
                    && hier.path.get(1).is_some_and(|second| {
                        params.contains_key(&format!("{base}::{}", second.name.name))
                    }))
        }
        ExprKind::Unary { operand, .. } => is_const_expr(operand, params),
        ExprKind::Binary { left, right, .. } => {
            is_const_expr(left, params) && is_const_expr(right, params)
        }
        ExprKind::Conditional {
            condition,
            then_expr,
            else_expr,
        } => {
            is_const_expr(condition, params)
                && is_const_expr(then_expr, params)
                && is_const_expr(else_expr, params)
        }
        ExprKind::Concatenation(parts) => parts.iter().all(|p| is_const_expr(p, params)),
        ExprKind::Paren(inner) => is_const_expr(inner, params),
        // Struct member / packed-array element select on a constant base — e.g.
        // a generate-if on a config-struct parameter field `CVA6Cfg.RVF` (ariane)
        // or `all_cfgs_gp[idx]`. eval_const_expr_val resolves these via the
        // struct-layout / elem-width TLS context (see the Index/MemberAccess arms).
        ExprKind::MemberAccess { expr, member } => {
            // `s.field` (const struct base) OR `pkg::CONST` (the scoped member is
            // an imported package constant / enum value, resolved by bare name).
            is_const_expr(expr, params)
                || params.contains_key(&member.name)
                // §26.3, §6.20: a package parameter named with its package
                // (`p::Info`, then `p::Info[k].variant`) is a constant
                // whether or not this scope imports it; its value is under
                // the scoped key.
                || matches!(&expr.kind, ExprKind::Ident(h)
                    if h.root.is_none()
                        && h.path.len() == 1
                        && h.path[0].selects.is_empty()
                        && params.contains_key(&format!("{}::{}", h.path[0].name.name, member.name)))
                // §8.23: a class-scoped constant (`cls::N`, `cls#(4)::N`).
                || class_scoped_const(expr, &member.name, params).is_some()
        }
        ExprKind::Index { expr, index } => {
            is_const_expr(expr, params) && is_const_expr(index, params)
        }
        // §11.2.1: a constant part-select can itself be an index.
        ExprKind::RangeSelect { expr, left, right, .. } => {
            is_const_expr(expr, params) && is_const_expr(left, params) && is_const_expr(right, params)
        }
        // §20.6.2 / §20.7: `$bits` and the array queries are constant over a
        // fixed-size TYPE or a declared fixed-size VARIABLE — the operand
        // itself need not be constant, only its declared type
        // (`if ($size(fx) - 5 < 0)`, §27.5). Any further argument (the
        // dimension number) must be.
        ExprKind::SystemCall { name, args }
            if matches!(
                name.as_str(),
                "$bits"
                    | "$size"
                    | "$left"
                    | "$right"
                    | "$high"
                    | "$low"
                    | "$dimensions"
                    | "$unpacked_dimensions"
                    | "$increment"
            ) && args
                .first()
                .is_some_and(|a| array_query_operand_is_type(a) || is_decl_shape_operand(a)) =>
        {
            args[1..].iter().all(|a| is_const_expr(a, params))
        }
        // §6.24.1: a cast to a type (`int'(e)`, `T'(e)`, `pkg::T'(e)`) is
        // constant when its operand is; the target is a type, not a value.
        ExprKind::SystemCall { name, args }
            if (name == "$__xz_type_cast" || name == "$__xz_named_cast")
                && args.len() == 2
                && cast_target_is_type(&args[0]) =>
        {
            is_const_expr(&args[1], params)
        }
        // System constant functions used in generate conditions ($bits, $clog2…).
        ExprKind::SystemCall { args, .. } => args.iter().all(|a| is_const_expr(a, params)),
        _ => false, // Calls (new()) etc. are not constant
    }
}

/// A cast target that names a type: a type literal, or a typedef or type
/// parameter known to the instance's types or the typedef tables.
fn cast_target_is_type(target: &Expression) -> bool {
    let name = match &target.kind {
        ExprKind::TypeLiteral(_) => return true,
        ExprKind::Ident(h) if h.path.len() == 1 && h.path[0].selects.is_empty() => {
            h.path[0].name.name.clone()
        }
        ExprKind::MemberAccess { expr, member } => match &expr.kind {
            ExprKind::Ident(h) if h.path.len() == 1 && h.path[0].selects.is_empty() => {
                format!("{}::{}", h.path[0].name.name, member.name)
            }
            _ => return false,
        },
        _ => return false,
    };
    let leaf = name.rsplit("::").next().unwrap_or(&name);
    CONST_FN_LOCAL_TYPES.with(|c| c.borrow().as_ref().is_some_and(|m| m.contains_key(leaf)))
        || TYPEDEF_SHAPES_TLS.with(|c| {
            let c = c.borrow();
            c.0.contains_key(&name) || c.0.contains_key(leaf)
        })
        || TYPEDEFS_TLS.with(|c| c.borrow().as_ref().is_some_and(|m| m.contains_key(&name)))
}
