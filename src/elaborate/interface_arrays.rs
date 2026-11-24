//! Interface-array port views retain the selected physical instances (§25.3).

use super::*;

fn range_path(path: &str) -> Option<(&str, i64, i64)> {
    let (base, range) = path.strip_suffix(']')?.rsplit_once('[')?;
    let (left, right) = range.split_once(':')?;
    Some((base, left.parse().ok()?, right.parse().ok()?))
}

/// Record element bindings alongside the whole view. The existing parameter
/// seeding then also sees `formal[i].PARAM`, rather than a nonexistent slice
/// instance such as `actual[1:2].PARAM`.
pub(super) fn register_views(
    bindings: &mut HashMap<String, String>,
    shapes: &crate::shared_names::SharedSliceMap<(i64, i64)>,
    ports: &PortList,
    params: &HashMap<String, Value>,
) {
    let PortList::Ansi(ports) = ports else { return };
    for port in ports {
        let formal = &port.name.name;
        let Some(bound) = bindings.get(formal) else { continue };
        let whole_range;
        let range = if let Some(shape) = shapes.get(bound)
            && let [(left, right)] = shape.as_slice()
        {
            whole_range = format!("{bound}[{left}:{right}]");
            &whole_range
        } else {
            bound
        };
        let Some((base, al, ar)) = range_path(range) else { continue };
        let Some(dims) = declared_unpacked_dims(&port.dimensions, params) else {
            continue;
        };
        let [(fl, fr)] = dims.as_slice() else {
            continue;
        };
        let Some(n) = al.abs_diff(ar).checked_add(1) else {
            continue;
        };
        if Some(n) != fl.abs_diff(*fr).checked_add(1) {
            continue;
        }
        let Ok(n) = i64::try_from(n) else { continue };
        let astep = if al <= ar { 1 } else { -1 };
        let fstep = if fl <= fr { 1 } else { -1 };
        let entries: Vec<_> = (0..n)
            .map(|i| {
                (
                    format!("{formal}[{}]", fl + i * fstep),
                    format!("{base}[{}]", al + i * astep),
                )
            })
            .collect();
        if bound != range {
            bindings.insert(formal.clone(), range.clone());
        }
        bindings.extend(entries);
    }
}

pub(super) struct View {
    base: String,
    formal_left: i64,
    formal_right: i64,
    actual_left: i64,
    actual_right: i64,
}

pub(super) fn view(bindings: &HashMap<String, String>, name: &str) -> Option<View> {
    let (base, al, ar) = range_path(bindings.get(name)?)?;
    let formal_index = |actual| {
        let target = format!("{base}[{actual}]");
        let prefix = format!("{name}[");
        bindings.iter().find_map(|(key, value)| {
            (value == &target)
                .then(|| {
                    key.strip_prefix(&prefix)?
                        .strip_suffix(']')?
                        .parse::<i64>()
                        .ok()
                })
                .flatten()
        })
    };
    Some(View {
        base: base.to_string(),
        formal_left: formal_index(al)?,
        formal_right: formal_index(ar)?,
        actual_left: al,
        actual_right: ar,
    })
}

pub(super) fn bare_view(bindings: &HashMap<String, String>, e: &Expression) -> Option<View> {
    match &e.kind {
        ExprKind::Ident(h)
            if h.root.is_none() && h.bound != crate::ast::binding::Bound::NO_TARGET && h.path.len() == 1 && h.path[0].selects.is_empty() =>
        {
            view(bindings, &h.path[0].name.name)
        }
        ExprKind::Paren(inner) => bare_view(bindings, inner),
        _ => None,
    }
}

impl View {
    fn same_direction(&self) -> bool {
        (self.formal_left <= self.formal_right) == (self.actual_left <= self.actual_right)
    }

    fn base_expr(&self, span: Span) -> Expression {
        let mut e = make_ident_expr(&self.base);
        e.span = span;
        e
    }

    pub(super) fn index(&self, index: Expression) -> Expression {
        if self.formal_left == self.formal_right {
            return make_i64_literal(self.actual_left, index.span);
        }
        let sign = if self.same_direction() { 1i128 } else { -1 };
        let offset = self.actual_left as i128 - sign * self.formal_left as i128;
        if let Some(i) = const_eval_i64_with_params(&index, None)
            && let Ok(actual) = i64::try_from(offset + sign * i as i128)
        {
            return make_i64_literal(actual, index.span);
        }
        // Preserve parameter expressions: their values need not be known when
        // the child's body is rewritten. The affine map depends only on bounds.
        let span = index.span;
        let delta = Expression::new(
            ExprKind::Binary {
                op: BinaryOp::Sub,
                left: Box::new(index),
                right: Box::new(make_i64_literal(self.formal_left, span)),
            },
            span,
        );
        Expression::new(
            ExprKind::Binary {
                op: if self.same_direction() {
                    BinaryOp::Add
                } else {
                    BinaryOp::Sub
                },
                left: Box::new(make_i64_literal(self.actual_left, span)),
                right: Box::new(delta),
            },
            span,
        )
    }

    pub(super) fn element(&self, index: Expression, span: Span) -> Expression {
        Expression::new(
            ExprKind::Index {
                expr: Box::new(self.base_expr(span)),
                index: Box::new(self.index(index)),
            },
            span,
        )
    }

    pub(super) fn range(&self, left: Expression, right: Expression, span: Span) -> Expression {
        Expression::new(
            ExprKind::RangeSelect {
                expr: Box::new(self.base_expr(span)),
                kind: RangeKind::Constant,
                left: Box::new(self.index(left)),
                right: Box::new(self.index(right)),
            },
            span,
        )
    }

    pub(super) fn whole(&self, span: Span) -> Expression {
        self.range(
            make_i64_literal(self.formal_left, span),
            make_i64_literal(self.formal_right, span),
            span,
        )
    }

    pub(super) fn rewrite_hier(
        &self,
        hier: &crate::ast::expr::HierarchicalIdentifier,
        span: Span,
    ) -> Expression {
        if hier.path[0].selects.is_empty() {
            let mut e = self.whole(span);
            for seg in &hier.path[1..] {
                e = Expression::new(
                    ExprKind::MemberAccess {
                        expr: Box::new(e),
                        member: seg.name.clone(),
                    },
                    span,
                );
                for index in &seg.selects {
                    e = Expression::new(
                        ExprKind::Index {
                            expr: Box::new(e),
                            index: Box::new(index.clone()),
                        },
                        span,
                    );
                }
            }
            e
        } else {
            let mut h = hier.clone();
            // The resolved actual already contains its instance path. Keep the
            // ordinary interface-member representation used by event controls,
            // aggregate stores and method dispatch.
            h.root = None;
            h.path[0].name.name = self.base.clone();
            h.path[0].selects[0] = self.index(h.path[0].selects[0].clone());
            Expression::new(ExprKind::Ident(h), span)
        }
    }
}
