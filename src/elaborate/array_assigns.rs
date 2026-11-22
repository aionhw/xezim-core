use super::*;

/// §10.6.2: a WHOLE-ARRAY continuous assignment between two UNPACKED arrays
/// (`assign dst = src;`). An unpacked array has no single backing signal — its
/// ELEMENTS are the signals — so this was pushed as one scalar assignment that
/// matched no target and silently did nothing: `dst` stayed x for the entire
/// run and never responded to a change in `src`. The per-element spelling
/// (`assign dst[i] = src[i];`) always worked, so expand into that.
///
/// Returns true when it consumed the assignment. Only the plain
/// `<ident> = <ident>` shape between two same-sized unpacked arrays is
/// expanded; anything else keeps its existing path.
/// The per-element assignments a whole-array continuous assign expands to, or
/// None when this is not that shape. Pure so both the eager and the streaming
/// pending-drain can share it.
pub fn whole_array_assign_parts(
    lhs: &Expression,
    rhs: &Expression,
    delay: u64,
    arrays: &HashMap<String, (i64, i64, u32)>,
) -> Option<Vec<ContinuousAssignment>> {
    whole_array_assign_parts_dir(lhs, rhs, delay, arrays, None, None)
}

/// `whole_array_assign_parts`, knowing each array's declared dimensions:
/// `descending` names the 1-D arrays declared `[hi:lo]`, and `decl_dims`
/// gives the declared `(left, right)` of every unpacked dimension. An
/// assignment pattern's first item goes to the LEFT bound (§10.9, §7.4.6).
pub fn whole_array_assign_parts_dir(
    lhs: &Expression,
    rhs: &Expression,
    delay: u64,
    arrays: &HashMap<String, (i64, i64, u32)>,
    descending: Option<&HashSet<String>>,
    decl_dims: Option<&HashMap<String, Vec<(i64, i64)>>>,
) -> Option<Vec<ContinuousAssignment>> {
    whole_array_assign_parts_dir_with_params(lhs, rhs, delay, arrays, descending, decl_dims, None)
}

/// §10.9.1: pattern keys and replication counts use the design's parameter
/// bindings even when expansion happens after loading a compiled artifact.
pub fn whole_array_assign_parts_dir_with_params(
    lhs: &Expression,
    rhs: &Expression,
    delay: u64,
    arrays: &HashMap<String, (i64, i64, u32)>,
    descending: Option<&HashSet<String>>,
    decl_dims: Option<&HashMap<String, Vec<(i64, i64)>>>,
    params: Option<&HashMap<String, Value>>,
) -> Option<Vec<ContinuousAssignment>> {
    let pattern = peel_unpacked_typed_pattern(rhs);
    if let ExprKind::AssignmentPattern(_) = &pattern.kind {
        return pattern_array_assign_parts(
            lhs, pattern, delay, arrays, descending, decl_dims, params, None,
        );
    }
    let (ExprKind::Ident(lh), ExprKind::Ident(rh)) = (&lhs.kind, &rhs.kind) else {
        return None;
    };
    // A hierarchical side (`ifc.arr`, `u.arr`) is registered under its
    // dotted name.
    let dotted = |h: &HierarchicalIdentifier| {
        h.path.iter().all(|s| s.selects.is_empty()).then(|| {
            h.path
                .iter()
                .map(|s| s.name.name.as_str())
                .collect::<Vec<_>>()
                .join(".")
        })
    };
    let ln = &dotted(lh)?;
    let rn = &dotted(rh)?;
    let &(llo, lhi, _) = arrays.get(ln)?;
    let &(rlo, rhi, _) = arrays.get(rn)?;
    // Same element COUNT is what matters; the index ranges may differ.
    if lhi < llo || rhi < rlo || (lhi - llo) != (rhi - rlo) {
        return None;
    }
    let n = lhi - llo;
    if n > 4096 {
        return None; // pathological; leave it alone
    }
    // §7.6: elements pair up left to right, whatever each range's direction.
    let desc = |nm: &str| descending.is_some_and(|d| d.contains(nm));
    let (ld, rd) = (desc(ln), desc(rn));
    Some(
        (0..=n)
            .map(|k| ContinuousAssignment {
                gate_delay_fall: None,
                delay_exprs: None,
                delay_select: None,
                origin: None,
                lhs: index_expr(lhs.clone(), if ld { lhi - k } else { llo + k }),
                rhs: index_expr(rhs.clone(), if rd { rhi - k } else { rlo + k }),
                delay,
                rhs_parent_scoped: false,
                delay_fall: None,
                delay_off: None,
            })
            .collect(),
    )
}

/// §7.4.6 (§7.4.5 in 1800-2023), §7.6, §10.3: a continuous assignment of a
/// SLICE of a one-dimensional unpacked array, or to one: `assign cw =
/// w[58 +: 6];`, `assign a[0 +: 6] = b;`, `assign d[2:7] = w[i -: 6];`.
/// Like a whole array, a slice has no signal of its own, so the assignment
/// drove nothing (aionhw/xezim#867). It becomes one assignment per element,
/// the elements paired left to right. A target slice needs constant bounds
/// (§10.3.1); a source slice may have a variable base, which becomes the
/// element index `base + k`, so each element assignment follows the base.
pub fn slice_array_assign_parts(
    lhs: &Expression,
    rhs: &Expression,
    delay: u64,
    arrays: &HashMap<String, (i64, i64, u32)>,
    descending: Option<&HashSet<String>>,
    decl_dims: Option<&HashMap<String, Vec<(i64, i64)>>>,
    params: &HashMap<String, Value>,
) -> Option<Vec<ContinuousAssignment>> {
    if !matches!(lhs.kind, ExprKind::RangeSelect { .. })
        && !matches!(rhs.kind, ExprKind::RangeSelect { .. })
    {
        return None;
    }
    let lhs_elems = slice_side_elems(lhs, arrays, descending, decl_dims, params, true)?;
    let rhs_elems = slice_side_elems(rhs, arrays, descending, decl_dims, params, false)?;
    if lhs_elems.len() != rhs_elems.len() || lhs_elems.is_empty() || lhs_elems.len() > 4096 {
        return None;
    }
    Some(
        lhs_elems
            .into_iter()
            .zip(rhs_elems)
            .map(|(l, r)| ContinuousAssignment {
                gate_delay_fall: None,
                delay_exprs: None,
                delay_select: None,
                origin: None,
                lhs: l,
                rhs: r,
                delay,
                rhs_parent_scoped: false,
                delay_fall: None,
                delay_off: None,
            })
            .collect(),
    )
}

/// The array tables [`concat_array_assign_parts`] reads.
pub struct UnpackedArrayTables<'a> {
    pub arrays: &'a HashMap<String, (i64, i64, u32)>,
    pub arrays_2d: &'a HashMap<String, ((i64, i64), (i64, i64), u32)>,
    pub arrays_nd: &'a HashMap<String, (Vec<(i64, i64)>, u32)>,
    pub descending: &'a HashSet<String>,
    pub decl_dims: &'a HashMap<String, Vec<(i64, i64)>>,
    pub params: &'a HashMap<String, Value>,
    /// Whether a name is a dynamic array, a queue or an associative array.
    pub other_array: &'a dyn Fn(&str) -> bool,
}

impl ElaboratedModule {
    /// `f` with this module's [`UnpackedArrayTables`].
    pub fn with_unpacked_array_tables<R>(
        &self,
        f: impl FnOnce(&UnpackedArrayTables<'_>) -> R,
    ) -> R {
        let other = |n: &str| {
            self.dynamic_arrays.contains(n)
                || self.queue_vars.contains(n)
                || self.associative_arrays.contains_key(n)
        };
        f(&UnpackedArrayTables {
            arrays: &self.arrays,
            arrays_2d: &self.arrays_2d,
            arrays_nd: &self.arrays_nd,
            descending: &self.descending_arrays,
            decl_dims: &self.unpacked_decl_dims,
            params: &self.parameters,
            other_array: &other,
        })
    }
}

/// §10.3, §10.10: a continuous assignment of an unpacked array concatenation
/// to a whole one-dimensional fixed unpacked array, `assign a = {x, w, m[i],
/// s[0 +: 2]};`. Like a whole array, the concatenation has no signal of its
/// own, so the assignment drove nothing. It becomes one assignment per
/// element, the items' elements paired left to right with the target's: a
/// whole one-dimensional array or a slice of one contributes each of its
/// elements, a row `m[i]` of a two-dimensional array each element of that
/// row (§7.4.4), and any other item one element. `None` for any other shape,
/// or when the counts differ.
pub fn concat_array_assign_parts(
    lhs: &Expression,
    rhs: &Expression,
    delay: u64,
    t: &UnpackedArrayTables<'_>,
) -> Option<Vec<ContinuousAssignment>> {
    let ExprKind::Concatenation(items) = &rhs.kind else {
        return None;
    };
    let ExprKind::Ident(lh) = &lhs.kind else {
        return None;
    };
    let whole_name = |h: &HierarchicalIdentifier| {
        h.path.iter().all(|s| s.selects.is_empty()).then(|| {
            h.path
                .iter()
                .map(|s| s.name.name.as_str())
                .collect::<Vec<_>>()
                .join(".")
        })
    };
    let names_array = |n: &str| {
        t.arrays.contains_key(n)
            || t.arrays_2d.contains_key(n)
            || t.arrays_nd.contains_key(n)
            || (t.other_array)(n)
    };
    let lname = whole_name(lh)?;
    if (t.other_array)(&lname) {
        return None;
    }
    let side = |e: &Expression, target: bool| {
        slice_side_elems(
            e,
            t.arrays,
            Some(t.descending),
            Some(t.decl_dims),
            t.params,
            target,
        )
    };
    let lhs_elems = side(lhs, true)?;
    let mut rhs_elems: Vec<Expression> = Vec::with_capacity(lhs_elems.len());
    for item in items {
        match &item.kind {
            ExprKind::Ident(h) => match whole_name(h) {
                Some(n) if names_array(&n) => rhs_elems.extend(side(item, false)?),
                Some(_) => rhs_elems.push(item.clone()),
                None => return None,
            },
            ExprKind::RangeSelect { expr: base, .. } => match &base.kind {
                ExprKind::Ident(h) if whole_name(h).is_some_and(|n| names_array(&n)) => {
                    rhs_elems.extend(side(item, false)?)
                }
                // A part-select of a packed vector is one element.
                ExprKind::Ident(h) if whole_name(h).is_some() => rhs_elems.push(item.clone()),
                _ => return None,
            },
            ExprKind::Index { .. } => {
                // The selects down to the array (`m[i][j]` has two).
                let mut base = item;
                let mut selects = 0;
                while let ExprKind::Index { expr, .. } = &base.kind {
                    selects += 1;
                    base = expr;
                }
                let ExprKind::Ident(h) = &base.kind else {
                    return None;
                };
                let n = whole_name(h)?;
                if selects > 1 {
                    // An element of a two-dimensional array, or a select
                    // of an element: one element. A sub-array of a deeper
                    // array is not spread here.
                    if t.arrays_nd.contains_key(&n) {
                        return None;
                    }
                    rhs_elems.push(item.clone());
                } else if let Some(&(_, inner, _)) = t.arrays_2d.get(&n) {
                    let (l, r) = match t.decl_dims.get(&n) {
                        Some(d) if d.len() == 2 => d[1],
                        _ => inner,
                    };
                    let idx: Vec<i64> = if l >= r {
                        (r..=l).rev().collect()
                    } else {
                        (l..=r).collect()
                    };
                    rhs_elems.extend(idx.into_iter().map(|j| index_expr(item.clone(), j)));
                } else if t.arrays_nd.contains_key(&n) {
                    return None;
                } else {
                    rhs_elems.push(item.clone());
                }
            }
            ExprKind::Concatenation(_)
            | ExprKind::Replication { .. }
            | ExprKind::AssignmentPattern(_)
            | ExprKind::MemberAccess { .. } => return None,
            _ => rhs_elems.push(item.clone()),
        }
    }
    if rhs_elems.len() != lhs_elems.len() || lhs_elems.is_empty() || lhs_elems.len() > 4096 {
        return None;
    }
    Some(
        lhs_elems
            .into_iter()
            .zip(rhs_elems)
            .map(|(l, r)| ContinuousAssignment {
                delay_exprs: None,
                gate_delay_fall: None,
                delay_select: None,
                origin: None,
                lhs: l,
                rhs: r,
                delay,
                rhs_parent_scoped: false,
                delay_fall: None,
                delay_off: None,
            })
            .collect(),
    )
}

/// The element expressions of one side of `slice_array_assign_parts`, left
/// to right: a whole 1-D unpacked array, or a slice of one. `target` asks for
/// constant bounds.
fn slice_side_elems(
    e: &Expression,
    arrays: &HashMap<String, (i64, i64, u32)>,
    descending: Option<&HashSet<String>>,
    decl_dims: Option<&HashMap<String, Vec<(i64, i64)>>>,
    params: &HashMap<String, Value>,
    target: bool,
) -> Option<Vec<Expression>> {
    let name_of = |h: &HierarchicalIdentifier| {
        h.path.iter().all(|s| s.selects.is_empty()).then(|| {
            h.path
                .iter()
                .map(|s| s.name.name.as_str())
                .collect::<Vec<_>>()
                .join(".")
        })
    };
    // The declared (left, right) of the array's one dimension.
    let bounds = |name: &str| -> Option<(i64, i64)> {
        let &(lo, hi, _) = arrays.get(name)?;
        if hi < lo {
            return None;
        }
        Some(match decl_dims.and_then(|d| d.get(name)) {
            Some(d) if d.len() == 1 => d[0],
            Some(_) => return None,
            None if descending.is_some_and(|d| d.contains(name)) => (hi, lo),
            None => (lo, hi),
        })
    };
    let konst = |x: &Expression| -> Option<i64> {
        if eval_const_expr_val(x, params).has_xz() {
            return None;
        }
        const_eval_i64_with_params(x, Some(params))
    };
    match &e.kind {
        ExprKind::Ident(h) => {
            let name = name_of(h)?;
            let (left, right) = bounds(&name)?;
            let idx: Vec<i64> = if left >= right {
                (right..=left).rev().collect()
            } else {
                (left..=right).collect()
            };
            Some(idx.into_iter().map(|i| index_expr(e.clone(), i)).collect())
        }
        ExprKind::RangeSelect {
            expr: base,
            kind,
            left: sl,
            right: sr,
        } => {
            let ExprKind::Ident(h) = &base.kind else {
                return None;
            };
            let name = name_of(h)?;
            let (left, right) = bounds(&name)?;
            let desc = left >= right;
            let (lo_d, hi_d) = (left.min(right), left.max(right));
            match kind {
                RangeKind::Constant => {
                    let (l, r) = (konst(sl)?, konst(sr)?);
                    if l.min(r) < lo_d || l.max(r) > hi_d {
                        return None;
                    }
                    let idx: Vec<i64> = if l >= r {
                        (r..=l).rev().collect()
                    } else {
                        (l..=r).collect()
                    };
                    Some(
                        idx.into_iter()
                            .map(|i| index_expr((**base).clone(), i))
                            .collect(),
                    )
                }
                RangeKind::IndexedUp | RangeKind::IndexedDown => {
                    let w = konst(sr)?;
                    if w <= 0 || w > 4096 {
                        return None;
                    }
                    let up = matches!(kind, RangeKind::IndexedUp);
                    // The offset from the base of the k-th element, left to
                    // right: `[b +: w]` covers b .. b+w-1 and `[b -: w]`
                    // covers b-w+1 .. b, read in the array's direction.
                    let offset = |k: i64| -> i64 {
                        match (up, desc) {
                            (true, true) => w - 1 - k,
                            (true, false) => k,
                            (false, true) => -k,
                            (false, false) => k - (w - 1),
                        }
                    };
                    match konst(sl) {
                        Some(b) => {
                            let idx: Vec<i64> = (0..w).map(|k| b + offset(k)).collect();
                            if idx.iter().any(|&i| i < lo_d || i > hi_d) {
                                return None;
                            }
                            Some(
                                idx.into_iter()
                                    .map(|i| index_expr((**base).clone(), i))
                                    .collect(),
                            )
                        }
                        // §10.3.1: a continuous assignment's target has
                        // constant selects.
                        None if target => None,
                        None => Some(
                            (0..w)
                                .map(|k| {
                                    let off = offset(k);
                                    let index = if off == 0 {
                                        (**sl).clone()
                                    } else {
                                        Expression::new(
                                            ExprKind::Binary {
                                                op: if off > 0 {
                                                    BinaryOp::Add
                                                } else {
                                                    BinaryOp::Sub
                                                },
                                                left: sl.clone(),
                                                right: Box::new(make_udp_int_expr(off.abs())),
                                            },
                                            sl.span,
                                        )
                                    };
                                    Expression::new(
                                        ExprKind::Index {
                                            expr: base.clone(),
                                            index: Box::new(index),
                                        },
                                        e.span,
                                    )
                                })
                                .collect(),
                        ),
                    }
                }
            }
        }
        _ => None,
    }
}

/// §7.6: `assign dst = src[row];` drives a 1-D unpacked array from one row of
/// a 2-D unpacked array with the same inner count, element by element. Like
/// the 1-D form, it has no single target signal to assign.
#[allow(clippy::too_many_arguments)]
pub fn whole_array_row_assign_parts(
    lhs: &Expression,
    rhs: &Expression,
    delay: u64,
    arrays: &HashMap<String, (i64, i64, u32)>,
    arrays_2d: &HashMap<String, ((i64, i64), (i64, i64), u32)>,
    params: &HashMap<String, Value>,
    descending: Option<&HashSet<String>>,
    decl_dims: Option<&HashMap<String, Vec<(i64, i64)>>>,
) -> Option<Vec<ContinuousAssignment>> {
    let (ExprKind::Ident(lh), ExprKind::Index { expr, index }) = (&lhs.kind, &rhs.kind) else {
        return None;
    };
    let ExprKind::Ident(rh) = &expr.kind else {
        return None;
    };
    let ([l], [r]) = (lh.path.as_slice(), rh.path.as_slice()) else {
        return None;
    };
    if !l.selects.is_empty() || !r.selects.is_empty() {
        return None;
    }
    let (ln, rn) = (&l.name.name, &r.name.name);
    let &(llo, lhi, _) = arrays.get(ln)?;
    let &((olo, ohi), (ilo, ihi), _) = arrays_2d.get(rn)?;
    if lhi < llo || ihi < ilo || (lhi - llo) != (ihi - ilo) {
        return None;
    }
    if eval_const_expr_val(index, params).has_xz() {
        return None;
    }
    let row = const_eval_i64_with_params(index, Some(params))?;
    if row < olo.min(ohi) || row > olo.max(ohi) {
        return None;
    }
    let n = lhi - llo;
    if n > 4096 {
        return None;
    }
    let desc = |nm: &str, dim: usize| match decl_dims.and_then(|d| d.get(nm)?.get(dim)) {
        Some(&(left, right)) => left > right,
        None => dim == 0 && descending.is_some_and(|d| d.contains(nm)),
    };
    let (ld, rd) = (desc(ln, 0), desc(rn, 1));
    Some(
        (0..=n)
            .map(|k| ContinuousAssignment {
                gate_delay_fall: None,
                delay_exprs: None,
                delay_select: None,
                origin: None,
                lhs: make_index_expr(ln, if ld { lhi - k } else { llo + k }),
                rhs: make_multi_index_expr(rn, &[row, if rd { ihi - k } else { ilo + k }]),
                delay,
                rhs_parent_scoped: false,
                delay_fall: None,
                delay_off: None,
            })
            .collect(),
    )
}

impl ElaboratedModule {
    /// §10.9.1: retain the declared packed element type when an inherited
    /// default reaches the leaves of a continuous unpacked-array driver.
    pub fn whole_array_driver_parts(
        &self,
        lhs: &Expression,
        rhs: &Expression,
        delay: u64,
        decl_dims: &HashMap<String, Vec<(i64, i64)>>,
    ) -> Option<Vec<ContinuousAssignment>> {
        let pattern = peel_unpacked_typed_pattern(rhs);
        if matches!(pattern.kind, ExprKind::AssignmentPattern(_)) {
            let name = whole_net_ident_name(lhs)?;
            let element = self.var_decl_types.get(&name).filter(|ty| {
                pattern_slot_is_aggregate(ty, &self.typedef_types) == Some(true)
                    && !matches!(resolve_typedef_chain(ty, &self.typedef_types), DataType::Struct(s) if !s.packed)
            });
            return pattern_array_assign_parts(
                lhs,
                pattern,
                delay,
                &self.arrays,
                Some(&self.descending_arrays),
                Some(decl_dims),
                Some(&self.parameters),
                element,
            );
        }
        whole_array_assign_parts_dir_with_params(
            lhs,
            rhs,
            delay,
            &self.arrays,
            Some(&self.descending_arrays),
            Some(decl_dims),
            Some(&self.parameters),
        )
    }
}

/// §10.3 / §10.9: `assign arr = '{...};` — a continuous assignment of an
/// assignment pattern to a whole unpacked array drives each element with
/// its item: positional (`'{3, 4}`, the first item at the LEFT bound),
/// replicated (`'{2{x}}`), index-keyed and `default:`, nested one pattern
/// per dimension (`'{'{1, 2}, '{3, 4}}`). Other shapes (named or typed
/// keys, an element that is itself an aggregate) are left as they were.
fn pattern_array_assign_parts(
    lhs: &Expression,
    rhs: &Expression,
    delay: u64,
    arrays: &HashMap<String, (i64, i64, u32)>,
    descending: Option<&HashSet<String>>,
    decl_dims: Option<&HashMap<String, Vec<(i64, i64)>>>,
    params: Option<&HashMap<String, Value>>,
    packed_element: Option<&DataType>,
) -> Option<Vec<ContinuousAssignment>> {
    let ExprKind::Ident(lh) = &lhs.kind else {
        return None;
    };
    if lh.path.len() != 1 || !lh.path[0].selects.is_empty() {
        return None;
    }
    let ln = &lh.path[0].name.name;
    let dims: Vec<(i64, i64)> = match decl_dims.and_then(|d| d.get(ln)) {
        Some(d) if !d.is_empty() => d.clone(),
        _ => {
            let &(lo, hi, _) = arrays.get(ln)?;
            if descending.is_some_and(|d| d.contains(ln)) {
                vec![(hi, lo)]
            } else {
                vec![(lo, hi)]
            }
        }
    };
    let total: i64 = dims
        .iter()
        .map(|&(l, r)| (l - r).abs() + 1)
        .try_fold(1i64, |a, n| a.checked_mul(n))?;
    if total > 4096 {
        return None;
    }
    let mut out: Vec<(Vec<i64>, Expression, bool)> = Vec::new();
    pattern_leaves(rhs, &dims, &mut Vec::new(), &mut out, params)?;
    Some(
        out.into_iter()
            .map(|(idx, e, inherited)| ContinuousAssignment {
                gate_delay_fall: None,
                delay_exprs: None,
                delay_select: None,
                origin: None,
                lhs: make_multi_index_expr(ln, &idx),
                rhs: if inherited {
                    packed_default_value(e, packed_element)
                } else {
                    e
                },
                delay,
                rhs_parent_scoped: false,
                delay_fall: None,
                delay_off: None,
            })
            .collect(),
    )
}

/// Put the leaf in a one-element packed array of its own type. Applying
/// `default:` to that element lets the ordinary packed pattern evaluator
/// store a matching value whole or descend into its members (§10.9.1).
fn packed_default_value(value: Expression, element: Option<&DataType>) -> Expression {
    let Some(mut ty) = element.cloned() else {
        return value;
    };
    let dimensions = match &mut ty {
        DataType::IntegerVector { dimensions, .. }
        | DataType::Implicit { dimensions, .. }
        | DataType::TypeReference { dimensions, .. } => dimensions,
        DataType::Struct(s) => &mut s.dimensions,
        DataType::Enum(e) => &mut e.dimensions,
        _ => return value,
    };
    let span = value.span;
    dimensions.insert(
        0,
        PackedDimension::Range {
            left: Box::new(make_udp_int_expr(0)),
            right: Box::new(make_udp_int_expr(0)),
            span,
        },
    );
    Expression::new(
        ExprKind::TypedPattern {
            ty: Box::new(ty),
            pattern: Box::new(Expression::new(
                ExprKind::AssignmentPattern(vec![AssignmentPatternItem::Default(value)]),
                span,
            )),
        },
        span,
    )
}

/// The element assignments of pattern `e` over the dimensions `dims`
/// (declared `(left, right)`, outermost first), below index prefix `idx`.
fn pattern_leaves(
    e: &Expression,
    dims: &[(i64, i64)],
    idx: &mut Vec<i64>,
    out: &mut Vec<(Vec<i64>, Expression, bool)>,
    params: Option<&HashMap<String, Value>>,
) -> Option<()> {
    let Some(&(l, r)) = dims.first() else {
        if matches!(e.kind, ExprKind::AssignmentPattern(_)) {
            return None;
        }
        out.push((idx.clone(), e.clone(), false));
        return Some(());
    };
    let ExprKind::AssignmentPattern(items) = &peel_unpacked_typed_pattern(e).kind else {
        return None;
    };
    if items.is_empty() {
        return None;
    }
    let n = ((l - r).abs() + 1) as usize;
    let index_at = |k: usize| if l > r { l - k as i64 } else { l + k as i64 };
    let mut elems: Vec<Option<&Expression>> = vec![None; n];
    let mut flat: Vec<&Expression> = Vec::new();
    let mut default: Option<&Expression> = None;
    let ordered = items
        .iter()
        .all(|it| matches!(it, AssignmentPatternItem::Ordered(_)));
    if ordered {
        if let [AssignmentPatternItem::Ordered(only)] = items.as_slice()
            && let ExprKind::Replication { count, exprs } = &only.kind
        {
            let c = const_eval_i64_with_params(count, params)?;
            for _ in 0..c.max(0) {
                flat.extend(exprs.iter());
            }
        } else {
            flat.extend(items.iter().map(|it| it.expr()));
        }
        if flat.len() != n {
            return None;
        }
        for (k, x) in flat.into_iter().enumerate() {
            elems[k] = Some(x);
        }
    } else {
        for it in items {
            match it {
                AssignmentPatternItem::Default(x) => default = Some(x),
                AssignmentPatternItem::Keyed(key, x) => {
                    let ix = const_eval_pattern_index(key, params, (l, r))?;
                    if ix < l.min(r) || ix > l.max(r) {
                        return None;
                    }
                    elems[(ix - l).unsigned_abs() as usize] = Some(x);
                }
                _ => return None,
            }
        }
    }
    for (k, x) in elems.into_iter().enumerate() {
        idx.push(index_at(k));
        match (x, default) {
            (Some(x), _) => pattern_leaves(x, &dims[1..], idx, out, params)?,
            // §10.9.1: `default:` reaches every leaf of a missing element.
            (None, Some(d))
                if !matches!(
                    peel_unpacked_typed_pattern(d).kind,
                    ExprKind::AssignmentPattern(_)
                ) =>
            {
                default_leaves(d, &dims[1..], idx, out)
            }
            (None, Some(d)) => pattern_leaves(d, &dims[1..], idx, out, params)?,
            (None, None) => return None,
        }
        idx.pop();
    }
    Some(())
}

/// Every leaf below index prefix `idx` takes the `default:` value `d`.
fn default_leaves(
    d: &Expression,
    dims: &[(i64, i64)],
    idx: &mut Vec<i64>,
    out: &mut Vec<(Vec<i64>, Expression, bool)>,
) {
    let Some(&(l, r)) = dims.first() else {
        out.push((idx.clone(), d.clone(), true));
        return;
    };
    for i in l.min(r)..=l.max(r) {
        idx.push(i);
        default_leaves(d, &dims[1..], idx, out);
        idx.pop();
    }
}

/// `name[i0][i1]...` with constant indices.
fn make_multi_index_expr(name: &str, idx: &[i64]) -> Expression {
    let Some((&first, rest)) = idx.split_first() else {
        return make_ident_expr(name);
    };
    let mut e = make_index_expr(name, first);
    for &i in rest {
        e = Expression::new(
            ExprKind::Index {
                expr: Box::new(e),
                index: Box::new(make_udp_int_expr(i)),
            },
            Span::dummy(),
        );
    }
    e
}

/// Push the expansion of a whole-array continuous assign, returning true when
/// it consumed the assignment.
pub(super) fn expand_whole_array_assign(
    lhs: &Expression,
    rhs: &Expression,
    delay: u64,
    delay_exprs: &Option<DelayExpressions>,
    elab: &mut ElaboratedModule,
) -> bool {
    match elab.whole_array_driver_parts(lhs, rhs, delay, &elab.unpacked_decl_dims)
    .or_else(|| {
        slice_array_assign_parts(
            lhs,
            rhs,
            delay,
            &elab.arrays,
            Some(&elab.descending_arrays),
            Some(&elab.unpacked_decl_dims),
            &elab.parameters,
        )
    })
    .or_else(|| elab.with_unpacked_array_tables(|t| concat_array_assign_parts(lhs, rhs, delay, t)))
    {
        Some(mut parts) => {
            for part in &mut parts { part.delay_exprs = delay_exprs.clone(); }
            elab.continuous_assigns.extend(parts);
            true
        }
        None => false,
    }
}
