use super::*;

pub(super) fn collect_effective_items(
    items: &[ModuleItem],
    params: &HashMap<String, Value>,
) -> Vec<ModuleItem> {
    let mut result = Vec::new();
    for item in items {
        match item {
            ModuleItem::GenerateRegion(gr) => {
                // A generate region is NOT a scope (§27.3).
                result.extend(collect_effective_items(&gr.items, params));
            }
            ModuleItem::GenerateIf(gi) => {
                let mut matched = false;
                for (bi, (cond, branch_items)) in gi.branches.iter().enumerate() {
                    let take = match cond {
                        Some(cond_expr) => eval_generate_const(cond_expr, params) != 0,
                        None => true, // unconditional else branch
                    };
                    if take {
                        // §27.5: a directly nested branch is not a scope.
                        if gi.branch_direct.get(bi) == Some(&true) {
                            result.extend(collect_effective_items(branch_items, params));
                            break;
                        }
                        // All branches of one if-chain share the construct's
                        // scope name unless the taken branch is labeled.
                        let label = gi.branch_labels.get(bi).and_then(|l| l.as_ref());
                        let scope = gen_scope_name(label, &gi.implicit_name);
                        // The same `g.x` keys as the direct path
                        // (see elaborate_generate_if).
                        let scoped_items = rename_decls_in_iter(branch_items, &scope);
                        let mut inner = collect_effective_items(&scoped_items, params);
                        prefix_gen_scope(&mut inner, &scope, None);
                        result.extend(inner);
                        matched = true;
                        break;
                    }
                }
                let _ = matched;
            }
            ModuleItem::GenerateCase(gc) => {
                let sel = eval_generate_const(&gc.selector, params);
                let mut chosen: Option<&GenerateCaseArm> = None;
                // First pass: try non-default arms.
                for arm in &gc.arms {
                    if arm.values.is_empty() {
                        continue;
                    }
                    if arm
                        .values
                        .iter()
                        .any(|v| eval_generate_const(v, params) == sel)
                    {
                        chosen = Some(arm);
                        break;
                    }
                }
                // Default arm fallback.
                if chosen.is_none() {
                    chosen = gc.arms.iter().find(|arm| arm.values.is_empty());
                }
                // §27.5: a directly nested arm is not a scope.
                if let Some(arm) = chosen.filter(|arm| arm.direct) {
                    result.extend(collect_effective_items(&arm.items, params));
                } else if let Some(arm) = chosen {
                    let scope = gen_scope_name(arm.label.as_ref(), &gc.implicit_name);
                    let arm_items = rename_decls_in_iter(&arm.items, &scope);
                    let mut inner = collect_effective_items(&arm_items, params);
                    prefix_gen_scope(&mut inner, &scope, None);
                    result.extend(inner);
                }
            }
            ModuleItem::GenerateFor(gf) => {
                // Without this expansion, items inside `for genvar` (always
                // blocks, instances, cont assigns) are dropped when the
                // host module is inlined into its parent. ct_fifo's
                // DFIFO_VLD_GEN reset block was being lost this way, leaving
                // fifo_entry_vld stuck at X and the AXI request path
                // permanently stalled — see openc910 hello_world bringup.
                let mut local_params = params.clone();
                let mut i = generate_for_start(gf, &local_params);
                let limit = 10000;
                let mut iters = 0;
                while iters < limit {
                    // §27.4: generated instances use the same signed genvar
                    // value as the direct elaboration path.
                    let mut gv = Value::from_u64(i as u64 as u32 as u64, 32);
                    gv.is_signed = true;
                    local_params.insert(gf.var.clone(), gv);
                    let cond_val = eval_const_expr(&gf.cond, &local_params);
                    if cond_val == 0 {
                        break;
                    }
                    let subst = substitute_genvar_in_items(&gf.items, &gf.var, i);
                    // Rename signals declared inside the for-body so each
                    // iteration gets its own unique copy. Without this, two
                    // iterations both declare `valid_q` and the elaborator
                    // sees a flat duplicate.
                    let scope = format!(
                        "{}[{}]",
                        gen_scope_name(gf.name.as_ref(), &gf.implicit_name),
                        i
                    );
                    let subst = rename_decls_in_iter(&subst, &scope);
                    let mut inner = collect_effective_items(&subst, &local_params);
                    prefix_gen_scope(&mut inner, &scope, Some(i));
                    result.extend(inner);
                    match &gf.incr.kind {
                        ExprKind::Unary {
                            op: UnaryOp::PostIncr,
                            ..
                        }
                        | ExprKind::Unary {
                            op: UnaryOp::PreIncr,
                            ..
                        } => i += 1,
                        ExprKind::Unary {
                            op: UnaryOp::PostDecr,
                            ..
                        }
                        | ExprKind::Unary {
                            op: UnaryOp::PreDecr,
                            ..
                        } => i -= 1,
                        _ => {
                            let new_val = eval_const_expr(&gf.incr, &local_params) as i64;
                            if new_val == i {
                                i += 1;
                            } else {
                                i = new_val;
                            }
                        }
                    }
                    iters += 1;
                }
                local_params.remove(&gf.var);
            }
            other => result.push(other.clone()),
        }
    }
    result
}

pub(super) fn is_interface_type(dt: &DataType, definitions: &HashMap<String, Definition>) -> bool {
    // Only an actual interface definition makes a port an interface port. A
    // `TypeReference` whose name resolves to a struct/enum/typedef (also stored
    // in `definitions`) is an ordinary data port — routing it as an interface
    // stranded its connection (e.g. a `sample_t` output never drove its net).
    match dt {
        DataType::TypeReference { name, .. } => {
            matches!(
                definitions.get(&name.name.name),
                Some(Definition::Interface(_))
            )
        }
        DataType::Interface { name, .. } => {
            // §25.3.2 generic interface port — `module m(interface b);`. The
            // parser records the keyword itself as the name because no
            // interface is named at the port; `interface` is reserved, so it
            // cannot collide with a real one. Without this the port was routed
            // as an ordinary data port and its connection went through the
            // value port map: `b.data` became `<conn>.data`, which resolves to
            // nothing once the connection carries a modport suffix
            // (`g.tx.data`), so every write through the port vanished.
            name.name == "interface"
                || matches!(definitions.get(&name.name), Some(Definition::Interface(_)))
        }
        _ => false,
    }
}

/// §23.3.2 arrayed-instance connection width in the parent scope.
fn ai_conn_expr_width(
    e: &Expression,
    widths: &HashMap<String, u32>,
    params: &HashMap<String, Value>,
) -> Option<u32> {
    use crate::ast::expr::ExprKind as EK;
    match &e.kind {
        EK::Ident(h) => {
            if h.path.iter().any(|s| !s.selects.is_empty()) {
                return None;
            }
            let name = h
                .path
                .iter()
                .map(|s| s.name.name.as_str())
                .collect::<Vec<_>>()
                .join(".");
            widths
                .get(&name)
                .copied()
                .or_else(|| params.get(&name).map(|v| v.width))
        }
        EK::RangeSelect {
            left,
            right,
            kind: crate::ast::expr::RangeKind::Constant,
            ..
        } => {
            let l = const_eval_i64_with_params(left, Some(params))?;
            let r = const_eval_i64_with_params(right, Some(params))?;
            Some(((l - r).unsigned_abs() as u32) + 1)
        }
        EK::Index { .. } => {
            // §27.6: `g[1]` names an indexed SCOPE, `g[1].w` a net inside
            // it. The scope's own declarations are flattened into the same
            // name space, so a scope-indexed net resolves against the
            // scope's declared widths — which is what lets an instance array
            // distribute such an actual (§23.3.3.5).
            if let Some(flat) = scope_indexed_flat_name_params(&e, params) {
                if let Some(w) = widths.get(&flat) {
                    return Some(*w);
                }
            }
            Some(1)
        }
        EK::MemberAccess { .. } => {
            if let Some(flat) = scope_indexed_flat_name_params(&e, params) {
                if let Some(w) = widths.get(&flat) {
                    return Some(*w);
                }
            }
            None
        }
        EK::Number(crate::ast::expr::NumberLiteral::Integer { size: Some(s), .. }) => Some(*s),
        EK::Concatenation(parts) => {
            let mut sum = 0u32;
            for p in parts {
                sum += ai_conn_expr_width(p, widths, params)?;
            }
            Some(sum)
        }
        EK::Number(n @ crate::ast::expr::NumberLiteral::Integer { size: None, .. }) => {
            Some(number_literal_width(n))
        }
        EK::Unary { op, operand } => {
            use crate::ast::expr::UnaryOp as U;
            match op {
                U::LogNot
                | U::BitAnd
                | U::BitNand
                | U::BitOr
                | U::BitNor
                | U::BitXor
                | U::BitXnor => Some(1),
                _ => ai_conn_expr_width(operand, widths, params),
            }
        }
        EK::Binary { op, left, right } => {
            use crate::ast::expr::BinaryOp as B;
            match op {
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
                B::ShiftLeft
                | B::ShiftRight
                | B::ArithShiftLeft
                | B::ArithShiftRight
                | B::Power => ai_conn_expr_width(left, widths, params),
                B::Add
                | B::Sub
                | B::Mul
                | B::Div
                | B::Mod
                | B::BitAnd
                | B::BitOr
                | B::BitXor
                | B::BitXnor => Some(
                    ai_conn_expr_width(left, widths, params)?
                        .max(ai_conn_expr_width(right, widths, params)?),
                ),
                _ => None,
            }
        }
        EK::Conditional {
            then_expr,
            else_expr,
            ..
        } => Some(
            ai_conn_expr_width(then_expr, widths, params)?
                .max(ai_conn_expr_width(else_expr, widths, params)?),
        ),
        EK::Replication { count, exprs } => {
            let count = u32::try_from(const_eval_i64_with_params(count, Some(params))?).ok()?;
            let width = exprs.iter().try_fold(0u32, |sum, e| {
                sum.checked_add(ai_conn_expr_width(e, widths, params)?)
            })?;
            width.checked_mul(count)
        }
        EK::Paren(inner) => ai_conn_expr_width(inner, widths, params),
        _ => None,
    }
}

pub(super) fn fixed_unpacked_shape(
    dims: &[UnpackedDimension],
    params: &HashMap<String, Value>,
) -> Option<Vec<(i64, i64)>> {
    if dims.is_empty() {
        return Some(Vec::new());
    }
    dims.iter()
        .map(|d| match d {
            UnpackedDimension::Range { .. } | UnpackedDimension::Expression { .. } => {
                extract_array_range(std::slice::from_ref(d), params)
            }
            // A parameter-named dimension reaches here as Associative; only a
            // dimension that resolves to a real size is accepted, so a genuine
            // associative array still yields None and stays dynamic.
            UnpackedDimension::Associative { .. } => {
                extract_array_range(std::slice::from_ref(d), params)
            }
            _ => None,
        })
        .collect()
}

pub(super) fn register_fixed_unpacked_array(
    elab: &mut ElaboratedModule,
    name: &str,
    shape: &[(i64, i64)],
    elem_width: u32,
    two_state: bool,
) {
    elab.unpacked_decl_dims
        .entry(name.to_string())
        .or_insert_with(|| shape.to_vec());
    match shape {
        [d0] => {
            elab.arrays
                .insert(name.to_string(), (d0.0, d0.1, elem_width));
        }
        [d0, d1] => {
            elab.arrays_2d
                .insert(name.to_string(), (*d0, *d1, elem_width));
        }
        dims if dims.len() >= 3 => {
            elab.arrays_nd
                .insert(name.to_string(), (dims.to_vec(), elem_width));
        }
        _ => return,
    }
    if two_state {
        elab.two_state_signals.insert(name.to_string());
    }
}

pub(super) fn mark_array_z_init_if_4state(
    elab: &mut ElaboratedModule,
    name: &str,
    data_type: &DataType,
) {
    if !is_type_two_state(data_type) && !is_type_real_resolved(data_type, &elab.typedef_types) {
        elab.z_init_signals.insert(name.to_string());
    }
}

pub(super) fn shape_index_tuples(shape: &[(i64, i64)]) -> Vec<Vec<i64>> {
    let mut out = vec![Vec::new()];
    for &(lo, hi) in shape {
        let mut next = Vec::new();
        for prefix in &out {
            for idx in lo..=hi {
                let mut tuple = prefix.clone();
                tuple.push(idx);
                next.push(tuple);
            }
        }
        out = next;
    }
    out
}

/// §7.6 / §23.3.3: enumerate an unpacked actual left to right, stripping
/// a slice into its element expressions before binding formal positions.
/// An indexed slice (`pw[10 +: 6]`, `pw[k -: 6]`, §7.4.6) is read in the
/// dimension's direction like a constant range; a variable base gives the
/// element indices `base + c`, so the connection follows the base
/// (aionhw/xezim#867).
pub(super) fn unpacked_connection_elements(
    expr: &Expression,
    elab: &ElaboratedModule,
    params: &HashMap<String, Value>,
) -> Option<Vec<Expression>> {
    enum Sel {
        One(Expression),
        Range(crate::ast::expr::RangeKind, Expression, Expression),
    }
    fn split(e: &Expression) -> Option<(String, Vec<Sel>)> {
        match &e.kind {
            ExprKind::Paren(inner) => split(inner),
            ExprKind::Ident(h) if h.path.len() == 1 => Some((
                h.path[0].name.name.clone(),
                h.path[0].selects.iter().cloned().map(Sel::One).collect(),
            )),
            ExprKind::Index { expr, index } => {
                let (name, mut sels) = split(expr)?;
                sels.push(Sel::One((**index).clone()));
                Some((name, sels))
            }
            ExprKind::RangeSelect {
                expr,
                kind,
                left,
                right,
            } => {
                let (name, mut sels) = split(expr)?;
                sels.push(Sel::Range(*kind, (**left).clone(), (**right).clone()));
                Some((name, sels))
            }
            _ => None,
        }
    }
    // §10.9.1 / §10.10: an assignment pattern or an unpacked-array
    // concatenation written as the actual (`.h({pkg::t'{...}})`,
    // `.h('{a, b})`) supplies its elements directly, left to right. Only a
    // positional pattern: a keyed or `default:` pattern needs the formal's
    // shape to place its items and keeps the element-wise fallback.
    match &peel_unpacked_typed_pattern(expr).kind {
        ExprKind::Concatenation(items) if !items.is_empty() => {
            return Some(items.clone());
        }
        ExprKind::AssignmentPattern(items)
            if !items.is_empty()
                && items
                    .iter()
                    .all(|it| matches!(it, AssignmentPatternItem::Ordered(_))) =>
        {
            return Some(items.iter().map(|it| it.expr().clone()).collect());
        }
        _ => {}
    }
    let (name, sels) = split(expr)?;
    let dims = elab.unpacked_decl_dims.get(&name).cloned().or_else(|| {
        if let Some(&(lo, hi, _)) = elab.arrays.get(&name) {
            Some(vec![if elab.descending_arrays.contains(&name) {
                (hi, lo)
            } else {
                (lo, hi)
            }])
        } else if let Some(&(d0, d1, _)) = elab.arrays_2d.get(&name) {
            Some(vec![d0, d1])
        } else {
            elab.arrays_nd.get(&name).map(|(d, _)| d.clone())
        }
    })?;
    if sels.len() > dims.len() {
        return None;
    }
    // Inside an inlined instance the actual's names, its bounds' parameters
    // included, carry the instance prefix (`w.N`), which the scope's own
    // parameter map does not key; the design-wide table does.
    let konst = |e: &Expression| {
        const_eval_i64_with_params(e, Some(params))
            .or_else(|| const_eval_i64_with_params(e, Some(&elab.parameters)))
    };
    // `l` to `r`, one literal index each.
    let range = |l: i64, r: i64| -> Option<Vec<Expression>> {
        let count = l.abs_diff(r).checked_add(1)?;
        (0..count)
            .map(|k| {
                let i = if l <= r {
                    l.checked_add(k as i64)?
                } else {
                    l.checked_sub(k as i64)?
                };
                Some(ai_num_expr(i, expr.span))
            })
            .collect()
    };
    // The indices each dimension contributes, left to right.
    let mut per_dim: Vec<Vec<Expression>> = Vec::with_capacity(dims.len());
    for (d, &(dl, dr)) in dims.iter().enumerate() {
        let idx = match sels.get(d) {
            None => range(dl, dr)?,
            Some(Sel::One(e)) => vec![ai_num_expr(konst(e)?, expr.span)],
            Some(Sel::Range(crate::ast::expr::RangeKind::Constant, l, r)) => {
                range(konst(l)?, konst(r)?)?
            }
            Some(Sel::Range(kind, b, w)) => {
                let w = konst(w)?;
                if w <= 0 || w > 4096 {
                    return None;
                }
                let up = matches!(kind, crate::ast::expr::RangeKind::IndexedUp);
                // `[b +: w]` covers b .. b+w-1 and `[b -: w]` covers
                // b-w+1 .. b, read in the dimension's direction.
                let off = |k: i64| -> i64 {
                    match (up, dl > dr) {
                        (true, true) => w - 1 - k,
                        (true, false) => k,
                        (false, true) => -k,
                        (false, false) => k - (w - 1),
                    }
                };
                match konst(b) {
                    Some(b) => (0..w).map(|k| ai_num_expr(b + off(k), expr.span)).collect(),
                    None => (0..w)
                        .map(|k| match off(k) {
                            0 => b.clone(),
                            o => Expression::new(
                                ExprKind::Binary {
                                    op: if o > 0 { BinaryOp::Add } else { BinaryOp::Sub },
                                    left: Box::new(b.clone()),
                                    right: Box::new(ai_num_expr(o.abs(), b.span)),
                                },
                                b.span,
                            ),
                        })
                        .collect(),
                }
            }
        };
        per_dim.push(idx);
    }
    let mut elements = vec![make_ident_expr(&name)];
    for idx in per_dim {
        let mut next = Vec::with_capacity(elements.len() * idx.len());
        for base in elements {
            for i in &idx {
                let span = base.span;
                next.push(Expression::new(
                    ExprKind::Index {
                        expr: Box::new(base.clone()),
                        index: Box::new(i.clone()),
                    },
                    span,
                ));
            }
        }
        elements = next;
    }
    Some(elements)
}

pub(super) fn ai_append_indices(mut expr: Expression, indices: &[i64]) -> Expression {
    for &idx in indices {
        let span = expr.span;
        expr = Expression::new(
            ExprKind::Index {
                expr: Box::new(expr),
                index: Box::new(ai_num_expr(idx, span)),
            },
            span,
        );
    }
    expr
}

fn ai_num_expr(n: i64, span: crate::ast::Span) -> Expression {
    if n < 0 {
        // §5.7.1: a minus sign is not part of an unsigned decimal token.
        // Encode the signed value explicitly, including i64::MIN.
        return Expression::new(
            ExprKind::Number(crate::ast::expr::NumberLiteral::Integer {
                size: Some(64),
                signed: true,
                base: crate::ast::expr::NumberBase::Hex,
                value: format!("{:x}", n as u64),
                cached_val: crate::ast::cache::LiteralCache::new(None),
            }),
            span,
        );
    }
    Expression::new(
        ExprKind::Number(crate::ast::expr::NumberLiteral::Integer {
            size: None,
            signed: false,
            base: crate::ast::expr::NumberBase::Decimal,
            value: n.to_string(),
            cached_val: crate::ast::cache::LiteralCache::new(None),
        }),
        span,
    )
}

/// §23.3.3.5 / §11.5.1: preserve writable leaves when splitting a
/// concatenation. Selecting the concatenation itself is not an lvalue.
fn ai_slice_expr(
    expr: &Expression,
    offset: u32,
    width: u32,
    widths: &HashMap<String, u32>,
    params: &HashMap<String, Value>,
) -> Expression {
    if let ExprKind::Paren(inner) = &expr.kind {
        return ai_slice_expr(inner, offset, width, widths, params);
    }
    if let ExprKind::Concatenation(parts) = &expr.kind {
        let mut cursor = 0u32;
        let mut selected = Vec::new();
        for part in parts.iter().rev() {
            let part_width = ai_conn_expr_width(part, widths, params).unwrap_or(0);
            let start = offset.max(cursor);
            let end = (offset + width).min(cursor + part_width);
            if start < end {
                selected.push(ai_slice_expr(
                    part,
                    start - cursor,
                    end - start,
                    widths,
                    params,
                ));
            }
            cursor += part_width;
        }
        selected.reverse();
        return if selected.len() == 1 {
            selected.remove(0)
        } else {
            Expression::new(ExprKind::Concatenation(selected), expr.span)
        };
    }
    let mut base = expr;
    let mut low = offset as i64;
    let mut high = low + width as i64 - 1;
    if let ExprKind::RangeSelect {
        expr: inner,
        left,
        right,
        kind: crate::ast::expr::RangeKind::Constant,
    } = &expr.kind
    {
        if let (Some(left), Some(right)) = (
            const_eval_i64_with_params(left, Some(params)),
            const_eval_i64_with_params(right, Some(params)),
        ) {
            base = inner;
            let direction = if left >= right { 1 } else { -1 };
            low = right + direction * offset as i64;
            high = low + direction * (width as i64 - 1);
        }
    }
    let kind = if width == 1 {
        ExprKind::Index {
            expr: Box::new(base.clone()),
            index: Box::new(ai_num_expr(low, expr.span)),
        }
    } else {
        ExprKind::RangeSelect {
            expr: Box::new(base.clone()),
            kind: crate::ast::expr::RangeKind::Constant,
            left: Box::new(ai_num_expr(high, expr.span)),
            right: Box::new(ai_num_expr(low, expr.span)),
        }
    };
    Expression::new(kind, expr.span)
}

fn ai_slice_conn(
    conn: &crate::ast::decl::PortConnection,
    p: u32,
    k: u32,
    n: u32,
    widths: &HashMap<String, u32>,
    port_shape: Option<&[(i64, i64)]>,
    unpacked_shapes: &HashMap<String, Vec<(i64, i64)>>,
    instance_dims: &[(i64, i64)],
    params: &HashMap<String, Value>,
) -> crate::ast::decl::PortConnection {
    use crate::ast::decl::PortConnection as PC;
    let expr = match conn {
        PC::Ordered(Some(e)) => e,
        PC::Named { expr: Some(e), .. } => e,
        _ => return conn.clone(),
    };
    // §23.3.3.5: when an instance array's actual has one more unpacked
    // dimension than the formal, consume that leading dimension across the
    // instances. Example: a formal `A[0:2]`, actual `bus[0:3][0:2]`, and four
    // instances bind instance k to `bus[k]`.
    if let (Some(formal), ExprKind::Ident(h)) = (port_shape, &expr.kind) {
        if h.path.len() == 1 && h.path[0].selects.is_empty() {
            let actual_name = &h.path[0].name.name;
            if let Some(actual) = unpacked_shapes.get(actual_name) {
                let rank = instance_dims.len();
                if actual.len() == formal.len() + rank
                    && actual[rank..] == *formal
                    && actual[..rank]
                        .iter()
                        .zip(instance_dims)
                        .all(|(&(al, ar), &(il, ir))| al.abs_diff(ar) == il.abs_diff(ir))
                {
                    // Unpacked actuals match left-to-left in every instance
                    // dimension, while k counts packed slots from the right.
                    let mut remainder = k;
                    let mut indices = Vec::with_capacity(rank);
                    for &(left, right) in actual[..rank].iter().rev() {
                        let count = (left.abs_diff(right) + 1) as u32;
                        let slot = remainder % count;
                        remainder /= count;
                        let direction = if left <= right { 1 } else { -1 };
                        indices.push(left + direction * (count - 1 - slot) as i64);
                    }
                    indices.reverse();
                    let sliced = ai_append_indices(expr.clone(), &indices);
                    return match conn {
                        PC::Ordered(_) => PC::Ordered(Some(sliced)),
                        PC::Named { name, implicit, .. } => PC::Named {
                            name: name.clone(),
                            expr: Some(sliced),
                            implicit: *implicit,
                        },
                        _ => conn.clone(),
                    };
                }
            }
        }
    }
    let distribute =
        matches!(ai_conn_expr_width(expr, widths, params), Some(w) if w == p * n && w != p);
    if !distribute {
        return conn.clone();
    }
    let sliced = ai_slice_expr(expr, p * k, p, widths, params);
    match conn {
        PC::Ordered(_) => PC::Ordered(Some(sliced)),
        PC::Named { name, implicit, .. } => PC::Named {
            name: name.clone(),
            expr: Some(sliced),
            implicit: *implicit,
        },
        _ => conn.clone(),
    }
}

pub(super) fn ai_expand_instances(
    instances: &[crate::ast::decl::HierarchicalInstance],
    port_widths: &[u32],
    port_shapes: &[Vec<(i64, i64)>],
    port_names: &[String],
    widths: &HashMap<String, u32>,
    unpacked_shapes: &HashMap<String, Vec<(i64, i64)>>,
    params: &HashMap<String, Value>,
) -> Vec<crate::ast::decl::HierarchicalInstance> {
    use crate::ast::decl::HierarchicalInstance as HInst;
    let mut out = Vec::with_capacity(instances.len());
    for hi in instances {
        if hi.dimensions.is_empty() {
            out.push(hi.clone());
            continue;
        }
        let Some(dims) = declared_unpacked_dims(&hi.dimensions, params) else {
            out.push(hi.clone());
            continue;
        };
        let Some(n) = dims
            .iter()
            .try_fold(1u32, |count, (left, right)| {
                count.checked_mul(u32::try_from(left.abs_diff(*right) + 1).ok()?)
            })
            .filter(|n| *n <= 1 << 20)
        else {
            out.push(hi.clone());
            continue;
        };
        // §23.3.3.5: expand every dimension; the rightmost dimension
        // varies first and all right-hand indices take the least-significant slice.
        let normalized: Vec<_> = dims.iter().map(|&(l, r)| (l.min(r), l.max(r))).collect();
        for indices in shape_index_tuples(&normalized) {
            let mut k = 0u32;
            for (&index, &(left, right)) in indices.iter().zip(&dims) {
                let count = (left.abs_diff(right) + 1) as u32;
                let slot = if left >= right {
                    index - right
                } else {
                    right - index
                };
                k = k * count + slot as u32;
            }
            let new_conns = hi
                .connections
                .iter()
                .enumerate()
                .map(|(pi, conn)| {
                    // §23.3.2: bit-distribution needs the FORMAL port's width,
                    // keyed by port index. A positional connection's port index
                    // is its list position; a by-name connection binds by NAME,
                    // so it may be reordered or sparse — look its index up in
                    // the declared port list (falling back to list position for
                    // NonAnsi / unknown ports).
                    let port_idx = match conn {
                        crate::ast::decl::PortConnection::Named { name, .. } => port_names
                            .iter()
                            .position(|pn| pn == &name.name)
                            .unwrap_or(pi),
                        _ => pi,
                    };
                    let p = port_widths.get(port_idx).copied().unwrap_or(1).max(1);
                    ai_slice_conn(
                        conn,
                        p,
                        k,
                        n,
                        widths,
                        port_shapes.get(port_idx).map(Vec::as_slice),
                        unpacked_shapes,
                        &dims,
                        params,
                    )
                })
                .collect();
            let mut ident = hi.name.clone();
            ident.name = hi.name.name.clone();
            for index in &indices {
                use std::fmt::Write as _;
                let _ = write!(ident.name, "[{index}]");
            }
            out.push(HInst {
                decl: hi.decl,
                name: ident,
                dimensions: vec![],
                connections: new_conns,
                gen_indices: hi.gen_indices.clone(),
                span: hi.span,
            });
        }
    }
    out
}

pub(super) fn ai_module_port_widths(
    def: &Definition,
    params: &HashMap<String, Value>,
    typedefs: &HashMap<String, u32>,
) -> Vec<u32> {
    match def.ports() {
        PortList::Ansi(ps) => ps
            .iter()
            .map(|p| {
                p.data_type
                    .as_ref()
                    .map(|dt| resolve_type_width(dt, Some(params), Some(typedefs)))
                    .unwrap_or(1)
                    .max(1)
            })
            .collect(),
        _ => Vec::new(),
    }
}

/// The declared port names of a module, in port-list order (parallel to
/// `ai_module_port_widths`). Used to map by-name instance-array connections
/// to the correct FORMAL port index for bit-distribution (§23.3.2).
pub(super) fn ai_module_port_names(def: &Definition) -> Vec<String> {
    match def.ports() {
        PortList::Ansi(ps) => ps.iter().map(|p| p.name.name.clone()).collect(),
        _ => Vec::new(),
    }
}

pub(super) fn ai_module_port_shapes(
    def: &Definition,
    params: &HashMap<String, Value>,
) -> Vec<Vec<(i64, i64)>> {
    match def.ports() {
        PortList::Ansi(ps) => ps
            .iter()
            .map(|p| declared_unpacked_dims(&p.dimensions, params).unwrap_or_default())
            .collect(),
        _ => Vec::new(),
    }
}

pub(super) fn ai_scan_signal_widths(
    items: &[ModuleItem],
    params: &HashMap<String, Value>,
    typedefs: &HashMap<String, u32>,
) -> HashMap<String, u32> {
    let mut m = HashMap::default();
    for item in items {
        match item {
            ModuleItem::PortDeclaration(pd) => {
                let w = resolve_type_width(&pd.data_type, Some(params), Some(typedefs)).max(1);
                for d in &pd.declarators {
                    m.insert(d.name.name.clone(), w);
                }
            }
            ModuleItem::NetDeclaration(nd) => {
                let w = resolve_type_width(&nd.data_type, Some(params), Some(typedefs)).max(1);
                for d in &nd.declarators {
                    if d.dimensions.is_empty() {
                        m.insert(d.name.name.clone(), w);
                    }
                }
            }
            ModuleItem::DataDeclaration(dd) => {
                let w = resolve_type_width(&dd.data_type, Some(params), Some(typedefs)).max(1);
                for d in &dd.declarators {
                    if d.dimensions.is_empty() {
                        m.insert(d.name.name.clone(), w);
                    }
                }
            }
            _ => {}
        }
    }
    m
}

pub(super) fn ai_scan_unpacked_shapes(
    items: &[ModuleItem],
    params: &HashMap<String, Value>,
) -> HashMap<String, Vec<(i64, i64)>> {
    let mut shapes = HashMap::default();
    for item in items {
        match item {
            ModuleItem::PortDeclaration(pd) => {
                for d in &pd.declarators {
                    if let Some(shape) = declared_unpacked_dims(&d.dimensions, params) {
                        if !shape.is_empty() {
                            shapes.insert(d.name.name.clone(), shape);
                        }
                    }
                }
            }
            ModuleItem::NetDeclaration(nd) => {
                for d in &nd.declarators {
                    if let Some(shape) = declared_unpacked_dims(&d.dimensions, params) {
                        if !shape.is_empty() {
                            shapes.insert(d.name.name.clone(), shape);
                        }
                    }
                }
            }
            ModuleItem::DataDeclaration(dd) => {
                for d in &dd.declarators {
                    if let Some(shape) = declared_unpacked_dims(&d.dimensions, params) {
                        if !shape.is_empty() {
                            shapes.insert(d.name.name.clone(), shape);
                        }
                    }
                }
            }
            _ => {}
        }
    }
    shapes
}

/// LRM §25.4: an interface actual may be written `instance.modport`
/// (`m u(bus.mp)`), selecting a modport VIEW of the instance. The modport
/// segment is not part of the instance path — inlined interface tasks are
/// keyed by the instance name (`bus.put`) and members resolve to `bus.<m>`,
/// so a stray `.mp` left in the interface_map strands both (task dispatch
/// falls through, member reads hit a phantom `bus.mp.<m>` signal). If the
/// last path segment names a modport of ANY interface definition, drop it.
/// §25.3.3: the interface INSTANCE that a port connection names, as the flat
/// path under which that instance is registered.
///
/// Four spellings have to land on the same answer: `b`, `b.mp`, `barr[0]` and
/// `barr[0].mp`. The element index arrives in one of TWO shapes — an `Index`
/// node, or folded into a path segment's `selects` (which is what happens when
/// a `.modport` follows it). Matching only a bare `Ident` and joining only the
/// segment NAMES missed both: an indexed connection inserted no mapping at all
/// and left the child's port unbound, while `barr[0].mp` silently collapsed to
/// `barr`, losing which element was meant.
pub(super) fn iface_conn_path(
    e: &Expression,
    params: &HashMap<String, Value>,
    definitions: &HashMap<String, Definition>,
) -> Option<String> {
    fn walk(e: &Expression, params: &HashMap<String, Value>) -> Option<String> {
        match &e.kind {
            ExprKind::Ident(hier) => {
                let mut out = String::new();
                for (i, seg) in hier.path.iter().enumerate() {
                    if i > 0 {
                        out.push('.');
                    }
                    out.push_str(&seg.name.name);
                    for sel in &seg.selects {
                        let idx = const_eval_i64_with_params(sel, Some(params))?;
                        out.push_str(&format!("[{}]", idx));
                    }
                }
                Some(out)
            }
            ExprKind::RangeSelect {
                expr: base,
                kind: RangeKind::Constant,
                left,
                right,
            } => {
                let b = walk(base, params)?;
                let l = const_eval_i64_with_params(left, Some(params))?;
                let r = const_eval_i64_with_params(right, Some(params))?;
                Some(format!("{}[{}:{}]", b, l, r))
            }
            ExprKind::Index { expr: base, index } => {
                let b = walk(base, params)?;
                let idx = const_eval_i64_with_params(index, Some(params))?;
                Some(format!("{}[{}]", b, idx))
            }
            // `r[0].snk` can also arrive as a MemberAccess over the index
            // rather than as one Ident whose segment carries the select.
            ExprKind::MemberAccess { expr: base, member } => {
                let b = walk(base, params)?;
                Some(format!("{}.{}", b, member.name))
            }
            ExprKind::Paren(inner) => walk(inner, params),
            _ => None,
        }
    }
    walk(e, params).map(|full| strip_modport_suffix(&full, definitions))
}

fn strip_modport_suffix(full_path: &str, definitions: &HashMap<String, Definition>) -> String {
    let Some((head, last)) = full_path.rsplit_once('.') else {
        return full_path.to_string();
    };
    let is_modport = definitions.values().any(|def| {
        if let Definition::Interface(idef) = def {
            idef.items.iter().any(|item| {
                if let ModuleItem::ModportDeclaration(md) = item {
                    md.items.iter().any(|mp| mp.name.name == last)
                } else {
                    false
                }
            })
        } else {
            false
        }
    });
    if is_modport {
        head.to_string()
    } else {
        full_path.to_string()
    }
}

#[cfg(test)]
mod generated_instance_tests {
    use super::*;

    /// §27.4: instance expansion retains negative genvars and terminates
    /// descending loops at zero, just like direct generate elaboration.
    #[test]
    fn signed_genvar_instance_expansion() {
        for (loop_header, expected) in [
            (
                "g=-2;g<1;g++",
                vec!["bank[-2].m", "bank[-1].m", "bank[0].m"],
            ),
            (
                "g=1;g>=-1;g--",
                vec!["bank[1].m", "bank[0].m", "bank[-1].m"],
            ),
        ] {
            let result = sv_parser::parse(&format!(
                "module top; for(genvar {loop_header}) begin: bank mem m(); end endmodule"
            ));
            assert!(result.errors.is_empty(), "{:?}", result.errors);
            let mut descs = result.source.descriptions;
            crate::scope_tree::build_design(&mut descs);
            let crate::ast::Description::Module(module) = &descs[0] else {
                panic!("missing top");
            };
            let items = collect_effective_items(&module.items, &HashMap::default());
            let names: Vec<_> = items
                .iter()
                .flat_map(|item| match item {
                    ModuleItem::ModuleInstantiation(mi) => mi
                        .instances
                        .iter()
                        .map(|i| i.name.name.as_str())
                        .collect::<Vec<_>>(),
                    _ => Vec::new(),
                })
                .collect();
            assert_eq!(names, expected);
        }
    }
}
