use super::*;

/// Best-effort self-determined width of a port-connection actual, reading
/// widths from already-registered parent signals/parameters. Returns None
/// when the width cannot be judged (unknown net, expression form we do not
/// size, or a §5.7.1 fill literal, which legally adapts to any width).
pub(super) fn port_conn_width(e: &Expression, elab: &ElaboratedModule) -> Option<u32> {
    use crate::ast::expr::ExprKind as EK;
    match &e.kind {
        EK::Paren(inner) => port_conn_width(inner, elab),
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
            if let Some(sig) = elab.signals.get(&name) {
                return Some(sig.width);
            }
            // §26.3: a package constant `pk::P` is registered as `pk::P`.
            elab.parameters
                .get(&name)
                .or_else(|| {
                    (h.path.len() == 2)
                        .then(|| {
                            elab.parameters
                                .get(&format!("{}::{}", h.path[0].name.name, h.path[1].name.name))
                        })
                        .flatten()
                })
                .map(|v| v.width)
        }
        EK::Index { expr: base, .. } => {
            // A bit-select of a packed vector is 1 bit; an element-select of
            // an unpacked array or multi-dim packed vector is the ELEMENT
            // width. Skip (None) when the base isn't resolvable.
            if let EK::Ident(h) = &base.kind {
                let name = h
                    .path
                    .iter()
                    .map(|s| s.name.name.as_str())
                    .collect::<Vec<_>>()
                    .join(".");
                if let Some(&(_, _, elem_w)) = elab.arrays.get(&name) {
                    return Some(elem_w);
                }
                if let Some(&ew) = elab.packed_signal_elem_widths.get(&name) {
                    return Some(ew);
                }
                if elab.signals.contains_key(&name) {
                    return Some(1);
                }
            }
            None
        }
        EK::RangeSelect {
            expr: base,
            left,
            right,
            kind,
            ..
        } => {
            let r = const_eval_i64_with_params(right, Some(&elab.parameters))?;
            let count = match kind {
                crate::ast::expr::RangeKind::Constant => {
                    let l = const_eval_i64_with_params(left, Some(&elab.parameters))?;
                    u32::try_from(l.abs_diff(r).checked_add(1)?).ok()?
                }
                // §11.5.1: the starting position may vary, but the width is constant.
                _ => u32::try_from(r).ok().filter(|&n| n > 0)?,
            };
            // §7.4.1: a constant range on a packed MULTI-D base selects
            // ELEMENTS, so the connection carries count × elem_w bits.
            // `.p(arr[1:0])` on a packed array of 128-bit structs is 256
            // bits, and reporting 2 here mis-sized the port cont-assign.
            if let EK::Ident(h) = &base.kind {
                let name = h
                    .path
                    .iter()
                    .map(|s| s.name.name.as_str())
                    .collect::<Vec<_>>()
                    .join(".");
                if let Some(&ew) = elab.packed_signal_elem_widths.get(&name) {
                    if ew > 1 {
                        return count.checked_mul(ew);
                    }
                }
            }
            // §7.4.3, §11.5.1: after an index the range selects elements of
            // the NEXT dimension: `.o(a[2][4:2])` on `logic [3:0][5:0][7:0] a`
            // is three 8-bit elements, 24 bits, not 3.
            if let Some(ew) = chain_range_elem_width(base, elab) {
                return count.checked_mul(ew);
            }
            Some(count)
        }
        EK::Number(crate::ast::expr::NumberLiteral::Integer { size: Some(sz), .. }) => Some(*sz),
        EK::Concatenation(parts) => {
            let mut total = 0u32;
            for p in parts {
                total = total.checked_add(port_conn_width(p, elab)?)?;
            }
            Some(total)
        }
        _ => None,
    }
}

/// §7.4.3: the width of one element of the dimension a part-select on the
/// index chain `base` addresses, when that dimension is not the last: on
/// `logic [3:0][5:0][7:0] a`, after `a[2]` the range counts 8-bit elements.
/// The first indices of an element of an unpacked array, one per unpacked
/// dimension, select the element. None for a select of bits or a layout not
/// on file.
fn chain_range_elem_width(base: &Expression, elab: &ElaboratedModule) -> Option<u32> {
    use crate::ast::expr::ExprKind as EK;
    let mut cur = base;
    let mut layers = 0usize;
    while let EK::Index { expr, .. } = &cur.kind {
        cur = expr;
        layers += 1;
    }
    let EK::Ident(h) = &cur.kind else {
        return None;
    };
    if layers == 0 {
        return None;
    }
    let name = h
        .path
        .iter()
        .map(|s| s.name.name.as_str())
        .collect::<Vec<_>>()
        .join(".");
    let (depth, total) = if let Some(&(_, _, elem_w)) = elab.arrays.get(&name) {
        (1, elem_w)
    } else if let Some(&(_, _, elem_w)) = elab.arrays_2d.get(&name) {
        (2, elem_w)
    } else if let Some((dims, elem_w)) = elab.arrays_nd.get(&name) {
        (dims.len(), *elem_w)
    } else {
        (0, elab.signals.get(&name)?.width)
    };
    let level = layers.checked_sub(depth)?;
    let dims = elab.packed_full_dims.get(&name)?;
    let counts: Vec<u64> = dims.iter().map(|&(l, r)| l.abs_diff(r) + 1).collect();
    if dims.len() <= level + 1 || counts.iter().product::<u64>() != u64::from(total) {
        return None;
    }
    u32::try_from(counts[level + 1..].iter().product::<u64>())
        .ok()
        .filter(|&w| w > 1)
}

/// §23.3.3.8, §10.7: an inlined literal must read like the result of
/// assigning it to the input. Resize with the actual's sign, then give
/// the resulting bits the formal's sign.
pub(super) fn port_literal_for_formal(
    actual: &Expression,
    prefix: &str,
    port: &str,
    elab: &ElaboratedModule,
    resolved_two_state_ports: &HashSet<&str>,
) -> Option<Expression> {
    let mut literal = actual;
    while let ExprKind::Paren(inner) = &literal.kind {
        literal = inner;
    }
    if !matches!(
        literal.kind,
        ExprKind::Number(NumberLiteral::Integer { .. } | NumberLiteral::Real(_))
            | ExprKind::StringLiteral(_)
    ) {
        return None;
    }
    let formal_name = cat2(prefix, port);
    let formal = elab.signals.get(&formal_name)?;
    if formal.width == 0 || elab.string_signals.contains(&formal_name) {
        return None;
    }
    let is_two_state = || {
        resolved_two_state_ports.contains(port)
            || elab.two_state_signals.contains(&formal_name)
            || (!is_net_name(elab, &formal_name) && !formal.value.has_xz())
    };
    let mut value = match &literal.kind {
        ExprKind::Number(NumberLiteral::Integer {
            size: Some(size),
            signed,
            base,
            value,
            cached_val,
        }) if *size == formal.width
            && !formal.is_real
            && !(value.contains(['x', 'X', 'z', 'Z', '?']) && is_two_state()) =>
        {
            if *signed == formal.is_signed {
                return Some(literal.clone());
            }
            // At equal width the cached bits are independent of the sign.
            return Some(Expression::new(
                ExprKind::Number(NumberLiteral::Integer {
                    size: Some(*size),
                    signed: formal.is_signed,
                    base: *base,
                    value: value.clone(),
                    cached_val: cached_val.clone(),
                }),
                literal.span,
            ));
        }
        // An unsized nonnegative decimal has enough bits for its magnitude.
        // Sizing its digits directly is equivalent to extending or truncating
        // that value. This also covers the common .en(1) and .rst(0) tie-offs.
        ExprKind::Number(NumberLiteral::Integer {
            size: None,
            base: NumberBase::Decimal,
            value,
            ..
        }) if !formal.is_real && value.starts_with(|c: char| c.is_ascii_digit()) => {
            return Some(Expression::new(
                ExprKind::Number(NumberLiteral::Integer {
                    size: Some(formal.width),
                    signed: formal.is_signed,
                    base: NumberBase::Decimal,
                    value: value.clone(),
                    cached_val: Default::default(),
                }),
                actual.span,
            ));
        }
        ExprKind::Number(
            num @ NumberLiteral::Integer { size, signed, base, value, .. },
        ) => {
            let width = number_literal_width(num);
            let radix = match base {
                NumberBase::Binary => 2,
                NumberBase::Octal => 8,
                NumberBase::Decimal => 10,
                NumberBase::Hex => 16,
            };
            // §5.7.1: a leading X/Z in an unsized unsigned literal pads
            // to the expression width, even beyond its intrinsic width.
            let width = if size.is_none() && !signed && !formal.is_real {
                width.max(formal.width)
            } else {
                width
            };
            let mut v = Value::from_literal_text(value, radix, width);
            v.is_signed = *signed;
            v
        }
        ExprKind::Number(NumberLiteral::Real(value)) if !formal.is_real => {
            Value::from_real_wrapped(*value, formal.width)
        }
        ExprKind::StringLiteral(value) => Value::from_string(value),
        _ => return None,
    };
    if formal.is_real {
        value = Value::from_f64(value.to_two_state().to_f64());
    } else {
        value = value.resize_for_assign(formal.width);
        value.is_signed = formal.is_signed;
        if value.has_xz() && is_two_state() {
            value = value.to_two_state();
        }
    }
    if value.is_real || value.has_xz() {
        return const_value_literal(&value, actual.span);
    }
    Some(Expression::new(
        ExprKind::Number(NumberLiteral::Integer {
            size: Some(value.width),
            signed: value.is_signed,
            base: NumberBase::Hex,
            value: value.to_hex(),
            cached_val: Default::default(),
        }),
        actual.span,
    ))
}

/// Warn once per (module, port) about a width-mismatched connection. §23.3.3
/// makes the mismatch legal (implicit truncation/extension applies), but it
/// is the classic wiring bug, and commercial tools flag it.
pub(super) fn warn_port_width_mismatch(
    sub_mod_name: &str,
    port: &str,
    formal_w: u32,
    actual_w: u32,
    inst_prefix: &str,
    actual: &Expression,
    elab: &ElaboratedModule,
    parent_def: &str,
) {
    use std::sync::{Mutex, OnceLock};
    static SEEN: OnceLock<Mutex<std::collections::HashSet<(String, String)>>> = OnceLock::new();
    if crate::elab_diags_muted() {
        return;
    }
    let seen = SEEN.get_or_init(|| Mutex::new(std::collections::HashSet::new()));
    let key = (sub_mod_name.to_string(), port.to_string());
    let first = seen.lock().map(|mut g| g.insert(key)).unwrap_or(false);
    if !first {
        return;
    }
    // The connection expression lives in the PARENT module's file — the file
    // of the module being elaborated (the root) would misreport whenever the
    // root file is large enough for the offset to fit it too.
    let where_ = match span_location_of(elab, actual.span, parent_def) {
        Some(loc) => format!("at {}", loc),
        None => format!("at source offset {}", actual.span.start),
    };
    crate::elab_diag(format!(
        "[xezim][warning] port width mismatch: module '{}' port '{}' is {} bit(s) but the \
         connection is {} bit(s) — instance '{}' (connection {}); the value \
         is truncated/extended per IEEE 1800-2017 §23.3.3. Further instances of this \
         (module, port) pair are not reported.{}",
        sub_mod_name,
        port,
        formal_w,
        actual_w,
        inst_prefix.trim_end_matches('.'),
        where_,
        explain_conn_width(actual, elab, parent_def),
    ));
}

/// Explain HOW a port connection reached its width. A bare "the connection is
/// 86 bit(s)" leaves a user with no way to find the under-sized declaration —
/// on a real design the answer is usually one struct whose fields were sized
/// by a parameter that resolved to 0 (each `[P:0]` field collapsing to 1 bit),
/// which is obvious the moment the field widths are printed next to each other.
fn explain_conn_width(actual: &Expression, elab: &ElaboratedModule, parent_def: &str) -> String {
    fn conn_root(expr: &Expression) -> Option<String> {
        match &expr.kind {
            ExprKind::Ident(h) => Some(
                h.path
                    .iter()
                    .map(|s| s.name.name.as_str())
                    .collect::<Vec<_>>()
                    .join("."),
            ),
            ExprKind::MemberAccess { expr, .. } | ExprKind::Index { expr, .. } => conn_root(expr),
            ExprKind::RangeSelect { expr, .. } => conn_root(expr),
            _ => None,
        }
    }
    let mut out = String::new();
    // A concatenation's width is the sum of its parts; name the parts.
    if let ExprKind::Concatenation(parts) = &actual.kind {
        let mut items: Vec<String> = Vec::new();
        for p in parts {
            let w = port_conn_width(p, elab);
            let n = conn_root(p).unwrap_or_else(|| "<expr>".to_string());
            items.push(match w {
                Some(w) => format!("{}:{}", n, w),
                None => format!("{}:?", n),
            });
        }
        if !items.is_empty() {
            out.push_str(&format!(
                "\n  connection is a concatenation of: {}",
                items.join(" ")
            ));
        }
    }
    let Some(name) = conn_root(actual) else {
        return out;
    };
    if let Some(sig) = elab.signals.get(&name) {
        let ty = sig
            .type_name
            .clone()
            .unwrap_or_else(|| "<anonymous>".to_string());
        out.push_str(&format!(
            "\n  connection '{}' is declared as '{}' ({} bit(s))",
            name, ty, sig.width
        ));
        let leaf = name.rsplit('.').next().unwrap_or(&name);
        if let Some(decl) = elab
            .decl_sites
            .get(&name)
            .or_else(|| elab.decl_sites.get(leaf))
        {
            if let Some(loc) = span_location_of(elab, decl.0, parent_def) {
                out.push_str(&format!(", declared at {}", loc));
            }
        }
    }
    // A packed struct's per-field widths are the payload of this diagnostic:
    // a row of 1-bit fields beside a much wider port names the culprit type.
    let mut collapsed = false;
    if let Some(fields) = elab.packed_struct_fields.get(&name) {
        if !fields.is_empty() {
            let mut items: Vec<String> = fields
                .iter()
                .map(|(f, _off, w)| format!("{}:{}", f, w))
                .collect();
            items.reverse(); // stored LSB-first; print in declaration order
            out.push_str(&format!("\n  its packed fields are: {}", items.join(" ")));
            collapsed = fields.iter().any(|(_, _, w)| *w == 1);
        }
    }
    // For every 1-bit field of the connection's struct TYPE, name the
    // identifiers its range expression reads and their resolved values —
    // this is the parameter the user has to trace, printed so they never
    // have to open the typedef. (A field that is genuinely `logic f;` has
    // no range identifiers and prints nothing.)
    let type_name = elab
        .signals
        .get(&name)
        .and_then(|s| s.type_name.clone())
        .or_else(|| elab.var_decl_types.get(&name).and_then(get_type_name));
    if let Some(tn) = type_name {
        let chain_root = elab
            .typedef_types
            .get(&tn)
            .map(|dt| resolve_typedef_chain(dt, &elab.typedef_types));
        // The identifiers each struct field's range reads, from the ORIGINAL
        // (pre-fold) declaration — the folded `typedef_types` collapses
        // `[P:0]` to `[0:0]` and would lose the parameter's name.
        let range_ids = elab.struct_field_range_idents.get(&tn);
        if let Some(DataType::Struct(su)) = chain_root {
            let mut named_any = false;
            for m in &su.members {
                let w =
                    resolve_type_width(&m.data_type, Some(&elab.parameters), Some(&elab.typedefs));
                let mut idents: Vec<String> = Vec::new();
                if let Some(map) = range_ids {
                    for d in &m.declarators {
                        if let Some(ids) = map.get(&d.name.name) {
                            idents.extend(ids.iter().cloned());
                        }
                    }
                }
                idents.dedup();
                if idents.is_empty() {
                    continue;
                }
                // Suspicious = the field collapsed to 1-2 bits, or any
                // identifier in its range resolved to <= 0 (an `[N-1:0]`
                // underflow) or did not resolve at all. A healthy
                // parameter-sized field prints nothing.
                let mut vals: Vec<String> = Vec::new();
                let mut suspicious = w <= 2;
                for id in &idents {
                    match elab
                        .parameters
                        .get(id)
                        .cloned()
                        .or_else(|| param_fallback_get(id))
                        .and_then(|v| v.to_i64())
                    {
                        Some(v) => {
                            if v <= 0 {
                                suspicious = true;
                            }
                            vals.push(format!("{} = {}", id, v));
                        }
                        None => {
                            suspicious = true;
                            vals.push(format!("{} = <UNRESOLVED — evaluates as 0>", id));
                        }
                    }
                }
                if !suspicious {
                    continue;
                }
                for decl in &m.declarators {
                    out.push_str(&format!(
                        "\n  field '{}' resolved to {} bit(s); its range reads: {}",
                        decl.name.name,
                        w,
                        vals.join(", ")
                    ));
                    named_any = true;
                }
            }
            if named_any {
                out.push_str(
                    "\n  trace the parameter above with XEZIM_TRACE_PARAM=<name> --compile \
                     to see every write to it and where the resolution went wrong.",
                );
                collapsed = false; // the specific note supersedes the generic one
            }
        }
    }
    if collapsed {
        out.push_str(
            "\n  NOTE: several fields are 1 bit wide — a `[P:0]`/`[P-1:0]` field whose \
             parameter P resolved to 0 collapses to 1 bit. Re-run with \
             XEZIM_TRACE_PARAM=<param> to see where that parameter was resolved.",
        );
    }
    out
}
