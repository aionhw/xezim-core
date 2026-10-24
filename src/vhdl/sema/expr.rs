//! Expressions and names (IEEE 1076-2008 §8, §9): overload resolution
//! against the context type (§12.5), name classification (call, index,
//! slice, conversion, field, attribute), aggregates, literals, and static
//! evaluation of locally and globally static expressions.

use super::decl::{expr_to_discrete_range, lit_expr, name_text, to_f64};
use super::hir::*;
use super::predefined::TypeSet;
use super::{Design, RegionId, Sym};
use crate::vhdl::ast::{self, Dir, Literal, NameKind};

/// What a name denotes, before it becomes an expression.
#[derive(Clone, Debug)]
enum Denot {
    Syms(Vec<Sym>),
    Expr(HExpr),
}

impl Design {
    // ---- expressions --------------------------------------------------------------

    /// Analyse `e` in a context expecting `expect` (a type or subtype), or
    /// self-determined (`None`).
    pub fn expr(&mut self, r: RegionId, e: &ast::Expr, expect: Option<TypeId>) -> Option<HExpr> {
        let h = self.expr_inner(r, e, expect)?;
        Some(self.implicit_convert(h, expect))
    }

    /// A universal operand in a context of a specific integer/real type
    /// takes that type (§9.3.6).
    fn implicit_convert(&mut self, h: HExpr, expect: Option<TypeId>) -> HExpr {
        let Some(t) = expect else { return h };
        let hb = self.base(h.ty);
        let tb = self.base(t);
        if hb == tb {
            return h;
        }
        let univ = matches!(
            self.types[hb].kind,
            TypeKind::UniversalInteger | TypeKind::UniversalReal
        );
        if univ
            && (self.is_integer(tb) && self.is_integer(hb) || self.is_real(tb) && self.is_real(hb))
        {
            let loc = h.loc.clone();
            return match h.kind {
                HExprKind::Lit(v) => HExpr {
                    kind: HExprKind::Lit(v),
                    ty: t,
                    loc,
                },
                _ => HExpr {
                    kind: HExprKind::Convert(Box::new(h)),
                    ty: t,
                    loc,
                },
            };
        }
        h
    }

    fn expr_inner(&mut self, r: RegionId, e: &ast::Expr, expect: Option<TypeId>) -> Option<HExpr> {
        let loc = self.loc(e.span.clone());
        match &e.kind {
            ast::ExprKind::Lit(l) => self.literal(r, l, expect, e.span.clone()),
            ast::ExprKind::Paren(x) => self.expr_inner(r, x, expect),
            ast::ExprKind::Name(n) => self.name_expr(r, n, expect),
            ast::ExprKind::Qualified(mark, x) => {
                let t = self.type_mark(r, mark)?;
                let inner = self.expr(r, x, Some(t))?;
                Some(HExpr {
                    kind: HExprKind::Qualified(Box::new(inner)),
                    ty: t,
                    loc,
                })
            }
            ast::ExprKind::Aggregate(assocs) => {
                let Some(t) = expect else {
                    self.error(
                        e.span.clone(),
                        "the type of this aggregate cannot be determined",
                    );
                    return None;
                };
                self.aggregate(r, assocs, t, e.span.clone())
            }
            ast::ExprKind::Binary(op, l, rr) => {
                let key = format!("\"{}\"", op.symbol());
                self.operator(
                    r,
                    &key,
                    op.symbol(),
                    &[l.as_ref(), rr.as_ref()],
                    expect,
                    e.span.clone(),
                )
            }
            ast::ExprKind::Unary(op, x) => {
                let key = format!("\"{}\"", op.symbol());
                self.operator(r, &key, op.symbol(), &[x.as_ref()], expect, e.span.clone())
            }
            ast::ExprKind::Range(_) => {
                self.error(
                    e.span.clone(),
                    "a range cannot be used as an expression here",
                );
                None
            }
            // Allocators (§9.3.7): the context gives the access type.
            ast::ExprKind::New(x) => {
                let loc = self.loc(e.span.clone());
                let Some(at) = expect.filter(|t| self.is_access(*t)) else {
                    self.error(e.span.clone(), "an allocator needs an access type context");
                    return None;
                };
                let des = self.designated(at)?;
                let v = self.expr(r, x, Some(des))?;
                Some(HExpr {
                    kind: HExprKind::New(Some(Box::new(v))),
                    ty: at,
                    loc,
                })
            }
            ast::ExprKind::NewSubtype(ind) => {
                let loc = self.loc(e.span.clone());
                let Some(at) = expect.filter(|t| self.is_access(*t)) else {
                    self.error(e.span.clone(), "an allocator needs an access type context");
                    return None;
                };
                let st = self.subtype_ind(r, ind)?;
                Some(HExpr {
                    kind: HExprKind::NewOf(st),
                    ty: at,
                    loc,
                })
            }
        }
    }

    fn literal(
        &mut self,
        r: RegionId,
        l: &Literal,
        expect: Option<TypeId>,
        span: ast::Span,
    ) -> Option<HExpr> {
        let loc = self.loc(span.clone());
        let ui = self.std.universal_integer;
        let ur = self.std.universal_real;
        match l {
            Literal::Int(v) => {
                let Ok(v) = i64::try_from(*v) else {
                    self.error(span, "integer literal out of range");
                    return None;
                };
                Some(lit_expr(Value::Int(v), ui, loc))
            }
            Literal::Real(v) => Some(lit_expr(Value::Real(*v), ur, loc)),
            Literal::Physical(v, unit) => {
                let (t, mult) = match self.name_sym(r, unit) {
                    Some(Sym::Unit(t, m)) => (t, m),
                    _ => {
                        self.error(
                            unit.span.clone(),
                            format!("unknown unit '{}'", name_text(unit)),
                        );
                        return None;
                    }
                };
                let val = match v.as_ref() {
                    Literal::Int(i) => (*i as i64).checked_mul(mult),
                    Literal::Real(f) => Some((f * mult as f64).round() as i64),
                    _ => None,
                };
                let Some(val) = val else {
                    self.error(span, "physical literal out of range");
                    return None;
                };
                Some(lit_expr(Value::Phys(val), t, loc))
            }
            Literal::Char(c) => {
                let key = format!("'{}'", *c as char);
                let lits: Vec<(TypeId, u32)> = self
                    .lookup(r, &key)
                    .into_iter()
                    .filter_map(|s| match s {
                        Sym::EnumLit(t, p) => Some((t, p)),
                        _ => None,
                    })
                    .collect();
                self.pick_enum_lit(&lits, expect, &key, span)
            }
            Literal::Str(s) | Literal::BitStr(s) => {
                let Some(t) = expect else {
                    self.error(span, "the type of this string literal cannot be determined");
                    return None;
                };
                self.string_literal(s, t, span)
            }
            Literal::Null => {
                let Some(t) = expect.filter(|t| self.is_access(*t)) else {
                    self.error(span, "null needs an access type context");
                    return None;
                };
                Some(lit_expr(Value::Null, t, loc))
            }
        }
    }

    fn pick_enum_lit(
        &mut self,
        lits: &[(TypeId, u32)],
        expect: Option<TypeId>,
        key: &str,
        span: ast::Span,
    ) -> Option<HExpr> {
        let loc = self.loc(span.clone());
        let chosen: Vec<&(TypeId, u32)> = match expect {
            Some(t) => {
                let b = self.base(t);
                lits.iter().filter(|(lt, _)| self.base(*lt) == b).collect()
            }
            None => lits.iter().collect(),
        };
        match chosen.as_slice() {
            [(t, p)] => Some(lit_expr(Value::Enum(*p), *t, loc)),
            [] => {
                self.error(
                    span,
                    format!("no enumeration literal {} of the expected type", key),
                );
                None
            }
            _ => {
                if std::env::var_os("XEZIM_VHDL_DEBUG").is_some() {
                    for (t, p) in &chosen {
                        eprintln!("  candidate {} pos {}", self.types[*t].name, p);
                    }
                }
                self.error(span, format!("ambiguous enumeration literal {}", key));
                None
            }
        }
    }

    /// A string or bit string literal of a one-dimensional array type of
    /// characters (§9.3.2): its bounds come from the subtype when
    /// constrained, else the index subtype's left bound and direction.
    fn string_literal(&mut self, s: &[u8], t: TypeId, span: ast::Span) -> Option<HExpr> {
        let loc = self.loc(span.clone());
        let Some(elem) = self.array1d_elem(t) else {
            self.error(span, "a string literal needs a one-dimensional array type");
            return None;
        };
        let lits = self.enum_lits(elem).cloned().unwrap_or_default();
        let mut elems = Vec::new();
        for c in s {
            match lits
                .iter()
                .position(|l| super::predefined::is_char_lit(l, *c))
            {
                Some(p) => elems.push(Value::Enum(p as u32)),
                None => {
                    self.error(
                        span,
                        format!("'{}' is not a literal of the element type", *c as char),
                    );
                    return None;
                }
            }
        }
        let (left, dir, right) = self.literal_bounds(t, elems.len() as i64)?;
        Some(lit_expr(
            Value::Array(Box::new(ArrayValue {
                left,
                dir,
                right,
                elems,
            })),
            t,
            loc,
        ))
    }

    /// Bounds of a positional array value of `n` elements of type `t`.
    pub fn literal_bounds(&self, t: TypeId, n: i64) -> Option<(i64, Dir, i64)> {
        if let Some(Some(sr)) = self
            .array_index_ranges(t)
            .and_then(|v| v.into_iter().next())
        {
            return Some((sr.left.as_i64()?, sr.dir, sr.right.as_i64()?));
        }
        let TypeKind::Array { index, .. } = &self.types[self.base(t)].kind else {
            return None;
        };
        let isr = self.scalar_range(index[0])?;
        let l = isr.left.as_i64()?;
        Some(match isr.dir {
            Dir::To => (l, Dir::To, l + n - 1),
            Dir::Downto => (l, Dir::Downto, l - n + 1),
        })
    }

    /// The static index ranges of a constrained array subtype (`None` per
    /// unconstrained or non-static dimension; `None` overall when the type is
    /// unconstrained).
    pub fn array_index_ranges(&self, t: TypeId) -> Option<Vec<Option<StaticRange>>> {
        let mut cur = t;
        loop {
            match &self.types[cur].kind {
                TypeKind::Subtype {
                    constraint: Some(HConstraint::Index(ranges, _)),
                    base,
                    ..
                } if !ranges.is_empty() => {
                    let _ = base;
                    return Some(
                        ranges
                            .iter()
                            .map(|r| r.as_ref().and_then(|r| r.static_val.clone()))
                            .collect(),
                    );
                }
                TypeKind::Subtype { base, .. } => cur = *base,
                _ => return None,
            }
        }
    }

    /// The index constraint (as ranges) of a constrained array subtype.
    pub fn array_constraint(&self, t: TypeId) -> Option<Vec<Option<HRange>>> {
        let mut cur = t;
        loop {
            match &self.types[cur].kind {
                TypeKind::Subtype {
                    constraint: Some(HConstraint::Index(ranges, _)),
                    ..
                } if !ranges.is_empty() => return Some(ranges.clone()),
                TypeKind::Subtype { base, .. } => cur = *base,
                _ => return None,
            }
        }
    }

    // ---- aggregates ---------------------------------------------------------------

    fn aggregate(
        &mut self,
        r: RegionId,
        assocs: &[ast::ElemAssoc],
        t: TypeId,
        span: ast::Span,
    ) -> Option<HExpr> {
        let loc = self.loc(span.clone());
        let b = self.base(t);
        match self.types[b].kind.clone() {
            TypeKind::Array { index, elem } => {
                let mut out = Vec::new();
                for a in assocs {
                    let mut choices = Vec::new();
                    for c in &a.choices {
                        choices.push(match c {
                            ast::Choice::Others(_) => HChoice::Others,
                            // `x'range =>` or a subtype name: a range choice.
                            ast::Choice::Expr(e)
                                if self.is_range_actual(
                                    r,
                                    &ast::Assoc {
                                        formal: None,
                                        actual: ast::Actual::Expr(e.clone()),
                                        span: e.span.clone(),
                                    },
                                ) =>
                            {
                                let dr = expr_to_discrete_range(e);
                                HChoice::Range(self.discrete_range(r, &dr, Some(index[0]))?.1)
                            }
                            ast::Choice::Expr(e) => {
                                HChoice::Expr(self.expr(r, e, Some(index[0]))?)
                            }
                            ast::Choice::Range(dr) => {
                                HChoice::Range(self.discrete_range(r, dr, Some(index[0]))?.1)
                            }
                        });
                    }
                    // Multi-dimensional: the element of a dimension is a
                    // sub-aggregate of the remaining dimensions.
                    let elem_t = if index.len() > 1 {
                        self.add_type(
                            "",
                            TypeKind::Array {
                                index: index[1..].to_vec(),
                                elem,
                            },
                            None,
                            None,
                        )
                    } else {
                        elem
                    };
                    // VHDL-2008 §9.3.3.3: an element association may give a
                    // slice (an array of the aggregate's type) positionally.
                    let v = match self.try_expr_quiet(r, &a.value, Some(elem_t)) {
                        Some(v) => v,
                        None => self.expr(r, &a.value, Some(t))?,
                    };
                    out.push((choices, v));
                }
                Some(HExpr {
                    kind: HExprKind::ArrayAgg(out),
                    ty: t,
                    loc,
                })
            }
            TypeKind::Record(fields) => {
                let mut vals: Vec<Option<HExpr>> = vec![None; fields.len()];
                let mut pos = 0;
                for a in assocs {
                    if a.choices.is_empty() {
                        let Some((_, ft)) = fields.get(pos) else {
                            self.error(span, "too many elements in the record aggregate");
                            return None;
                        };
                        vals[pos] = Some(self.expr(r, &a.value, Some(*ft))?);
                        pos += 1;
                        continue;
                    }
                    for c in &a.choices {
                        let idxs: Vec<usize> = match c {
                            ast::Choice::Others(_) => {
                                (0..fields.len()).filter(|i| vals[*i].is_none()).collect()
                            }
                            ast::Choice::Expr(ast::Expr {
                                kind:
                                    ast::ExprKind::Name(ast::Name {
                                        kind: NameKind::Simple(i),
                                        ..
                                    }),
                                ..
                            }) => match fields.iter().position(|(n, _)| *n == i.name) {
                                Some(p) => vec![p],
                                None => {
                                    self.error(
                                        i.span.clone(),
                                        format!("no element '{}' in the record", i.name),
                                    );
                                    return None;
                                }
                            },
                            _ => {
                                self.error(span, "a record aggregate choice names an element");
                                return None;
                            }
                        };
                        for i in idxs {
                            vals[i] = Some(self.expr(r, &a.value, Some(fields[i].1))?);
                        }
                    }
                }
                if vals.iter().any(|v| v.is_none()) {
                    self.error(span, "the record aggregate does not give every element");
                    return None;
                }
                Some(HExpr {
                    kind: HExprKind::RecordAgg(vals.into_iter().flatten().collect()),
                    ty: t,
                    loc,
                })
            }
            _ => {
                self.error(span, "an aggregate needs a composite type");
                None
            }
        }
    }

    /// Analyse without reporting errors (for trying an interpretation).
    pub fn try_expr_quiet(
        &mut self,
        r: RegionId,
        e: &ast::Expr,
        expect: Option<TypeId>,
    ) -> Option<HExpr> {
        let n = self.errors.len();
        let h = self.expr(r, e, expect);
        if self.errors.len() > n {
            self.errors.truncate(n);
            return None;
        }
        // The result must actually have the expected type.
        if let (Some(h), Some(t)) = (&h, expect)
            && self.base(h.ty) != self.base(t)
        {
            return None;
        }
        h
    }

    // ---- possible types (for overload resolution) -------------------------------------

    /// The types `e` could have (§12.5), without reporting errors.
    pub fn possible_types(&mut self, r: RegionId, e: &ast::Expr) -> TypeSet {
        let mut s = TypeSet::default();
        match &e.kind {
            ast::ExprKind::Lit(l) => match l {
                Literal::Int(_) => s.univ_int = true,
                Literal::Real(_) => s.univ_real = true,
                Literal::Physical(_, unit) => {
                    if let Some(Sym::Unit(t, _)) = self.name_sym(r, unit) {
                        s.add(t);
                    }
                }
                Literal::Char(c) => {
                    for sym in self.lookup(r, &format!("'{}'", *c as char)) {
                        if let Sym::EnumLit(t, _) = sym {
                            let b = self.base(t);
                            s.add(b);
                        }
                    }
                }
                Literal::Str(v) | Literal::BitStr(v) => s.string_lit = Some(v.clone()),
                Literal::Null => s.null = true,
            },
            ast::ExprKind::Paren(x) => return self.possible_types(r, x),
            ast::ExprKind::Aggregate(_) => s.aggregate = true,
            ast::ExprKind::Qualified(mark, _) => {
                let n = self.errors.len();
                if let Some(t) = self.type_mark(r, mark) {
                    let b = self.base(t);
                    s.add(b);
                }
                self.errors.truncate(n);
            }
            ast::ExprKind::Binary(op, l, rr) => {
                let sets = [self.possible_types(r, l), self.possible_types(r, rr)];
                self.op_result_types(r, op.symbol(), &sets, &mut s);
            }
            ast::ExprKind::Unary(op, x) => {
                let sets = [self.possible_types(r, x)];
                self.op_result_types(r, op.symbol(), &sets, &mut s);
            }
            ast::ExprKind::Name(n) => {
                let errs = self.errors.len();
                self.name_possible_types(r, n, &mut s);
                self.errors.truncate(errs);
            }
            _ => s.any = true,
        }
        s
    }

    fn op_result_types(&mut self, r: RegionId, op: &str, sets: &[TypeSet], out: &mut TypeSet) {
        for sym in self.lookup(r, &format!("\"{}\"", op)) {
            if let Sym::Sub(id) = sym
                && self.subprograms[id].params.len() == sets.len()
                && let Some(rt) = self.subprograms[id].ret
            {
                let ok = self.subprograms[id]
                    .params
                    .clone()
                    .iter()
                    .zip(sets)
                    .all(|(p, s)| self.compatible(s, self.objects[*p].ty));
                if ok {
                    let b = self.base(rt);
                    out.add(b);
                }
            }
        }
        for id in self.predefined_ops(op, sets, None) {
            let ok = self.subprograms[id]
                .params
                .clone()
                .iter()
                .zip(sets)
                .all(|(p, s)| self.compatible(s, self.objects[*p].ty));
            if ok && let Some(rt) = self.subprograms[id].ret {
                let b = self.base(rt);
                match &self.types[b].kind {
                    TypeKind::UniversalInteger => out.univ_int = true,
                    TypeKind::UniversalReal => out.univ_real = true,
                    _ => out.add(b),
                }
            }
        }
    }

    fn name_possible_types(&mut self, r: RegionId, n: &ast::Name, out: &mut TypeSet) {
        match &n.kind {
            NameKind::Simple(_) | NameKind::Selected(..) | NameKind::Op(_) | NameKind::Char(_) => {
                match self.denote(r, n) {
                    Some(Denot::Syms(syms)) => {
                        for s in syms {
                            match s {
                                Sym::Obj(o) => {
                                    let b = self.base(self.objects[o].ty);
                                    out.add(b);
                                }
                                Sym::EnumLit(t, _) | Sym::Unit(t, _) => {
                                    let b = self.base(t);
                                    out.add(b);
                                }
                                Sym::Sub(id) => {
                                    if let Some(rt) = self.subprograms[id].ret
                                        && self.min_args(id) == 0
                                    {
                                        let b = self.base(rt);
                                        out.add(b);
                                    }
                                }
                                Sym::Alias(a) => {
                                    let b = self.base(self.aliases[a].ty);
                                    out.add(b);
                                }
                                _ => out.any = true,
                            }
                        }
                    }
                    Some(Denot::Expr(h)) => {
                        let b = self.base(h.ty);
                        out.add(b);
                    }
                    None => out.any = true,
                }
            }
            NameKind::Call(prefix, args) => {
                match self.denote(r, prefix) {
                    Some(Denot::Syms(syms)) if syms.iter().any(|s| matches!(s, Sym::Sub(_))) => {
                        // Positional arguments must fit the parameters.
                        let arg_sets: Vec<Option<TypeSet>> = args
                            .iter()
                            .map(|a| match (&a.formal, &a.actual) {
                                (None, ast::Actual::Expr(e)) => Some(self.possible_types(r, e)),
                                _ => None,
                            })
                            .collect();
                        for s in syms {
                            if let Sym::Sub(id) = s
                                && let Some(rt) = self.subprograms[id].ret
                                && self.arity_ok(id, args)
                                && self.subprograms[id]
                                    .params
                                    .clone()
                                    .iter()
                                    .zip(&arg_sets)
                                    .all(|(p, set)| {
                                        set.as_ref().is_none_or(|set| {
                                            self.compatible(set, self.objects[*p].ty)
                                        })
                                    })
                            {
                                let b = self.base(rt);
                                out.add(b);
                            }
                        }
                        // Predefined functions (to_string, minimum, …).
                        if let NameKind::Simple(i) = &prefix.kind {
                            let sets: Vec<TypeSet> = args
                                .iter()
                                .filter_map(|a| match &a.actual {
                                    ast::Actual::Expr(e) => Some(self.possible_types(r, e)),
                                    _ => None,
                                })
                                .collect();
                            for id in self.predefined_funcs(&i.name, &sets) {
                                if let Some(rt) = self.subprograms[id].ret {
                                    let b = self.base(rt);
                                    out.add(b);
                                }
                            }
                        }
                    }
                    Some(Denot::Syms(syms)) => match syms.first() {
                        Some(Sym::Type(t)) => {
                            let b = self.base(*t);
                            out.add(b);
                        }
                        Some(Sym::Obj(_)) | Some(Sym::Alias(_)) => {
                            // Indexing or slicing an object.
                            let ty = match syms.first() {
                                Some(Sym::Obj(o)) => self.objects[*o].ty,
                                Some(Sym::Alias(a)) => self.aliases[*a].ty,
                                _ => unreachable!(),
                            };
                            // Through an access value (§8.3).
                            let ty = self.designated(ty).unwrap_or(ty);
                            let b = self.base(ty);
                            let is_slice = args.len() == 1 && self.is_range_actual(r, &args[0]);
                            match &self.types[b].kind {
                                TypeKind::Array { elem, .. } if !is_slice => {
                                    let e = self.base(*elem);
                                    out.add(e);
                                }
                                _ => out.add(b),
                            }
                        }
                        _ => out.any = true,
                    },
                    Some(Denot::Expr(h)) => {
                        // Index (element type) or slice (same type).
                        let b = self.base(self.designated(h.ty).unwrap_or(h.ty));
                        let is_slice = args.len() == 1 && self.is_range_actual(r, &args[0]);
                        match &self.types[b].kind {
                            TypeKind::Array { elem, .. } if !is_slice => {
                                let e = self.base(*elem);
                                out.add(e);
                            }
                            _ => out.add(b),
                        }
                    }
                    None => {
                        // A predefined function by name.
                        if let NameKind::Simple(i) = &prefix.kind {
                            let sets: Vec<TypeSet> = args
                                .iter()
                                .filter_map(|a| match &a.actual {
                                    ast::Actual::Expr(e) => Some(self.possible_types(r, e)),
                                    _ => None,
                                })
                                .collect();
                            for id in self.predefined_funcs(&i.name, &sets) {
                                if let Some(rt) = self.subprograms[id].ret {
                                    let b = self.base(rt);
                                    out.add(b);
                                }
                            }
                        }
                        if out.is_empty() {
                            out.any = true;
                        }
                    }
                }
            }
            NameKind::Attribute(..) => {
                // Analyse it (attributes are not overloaded).
                if let Some(h) = self.name_expr(r, n, None) {
                    let b = self.base(h.ty);
                    match &self.types[b].kind {
                        TypeKind::UniversalInteger => out.univ_int = true,
                        TypeKind::UniversalReal => out.univ_real = true,
                        _ => out.add(b),
                    }
                } else {
                    out.any = true;
                }
            }
            NameKind::External { .. } => out.any = true,
        }
    }

    // ---- names --------------------------------------------------------------------

    /// What a simple or selected name denotes: the visible named entities,
    /// or an expression (a record element, a dereference).
    fn denote(&mut self, r: RegionId, n: &ast::Name) -> Option<Denot> {
        match &n.kind {
            NameKind::Simple(i) => {
                let syms = self.lookup(r, &i.name);
                if syms.is_empty() {
                    return None;
                }
                Some(Denot::Syms(syms))
            }
            NameKind::Op(o) => {
                let syms = self.lookup(r, &format!("\"{}\"", o.to_ascii_lowercase()));
                Some(Denot::Syms(syms))
            }
            NameKind::Char(c) => Some(Denot::Syms(self.lookup(r, &format!("'{}'", *c as char)))),
            NameKind::Selected(prefix, suffix) => {
                let key = match suffix {
                    ast::Suffix::Ident(i) => i.name.clone(),
                    ast::Suffix::Char(c, _) => format!("'{}'", *c as char),
                    ast::Suffix::Op(o, _) => format!("\"{}\"", o),
                    ast::Suffix::All(_) => String::new(),
                };
                // Library or package prefix.
                if let Some(ps) = self.static_prefix(r, prefix) {
                    return match ps {
                        Sym::Library(lib) => {
                            self.unit_sym(&lib, &key).map(|s| Denot::Syms(vec![s]))
                        }
                        Sym::Package(pkg) => {
                            let syms = self.pkg_syms_pub(&pkg, &key);
                            // `std.standard.rising_edge`: an implicitly
                            // declared function of STANDARD (an empty set
                            // that call resolution fills with predefined ones).
                            if syms.is_empty()
                                && pkg.0 == "std"
                                && pkg.1 == "standard"
                                && is_predefined_func(&key)
                            {
                                return Some(Denot::Syms(Vec::new()));
                            }
                            (!syms.is_empty()).then_some(Denot::Syms(syms))
                        }
                        _ => None,
                    };
                }
                // A record element or `.all`.
                let p = self.name_expr(r, prefix, None)?;
                let pb = self.base(p.ty);
                match (&self.types[pb].kind.clone(), suffix) {
                    (TypeKind::Record(fields), ast::Suffix::Ident(i)) => {
                        let Some(idx) = fields.iter().position(|(f, _)| *f == i.name) else {
                            self.error(
                                i.span.clone(),
                                format!("no element '{}' in the record", i.name),
                            );
                            return None;
                        };
                        let ft = fields[idx].1;
                        let loc = self.loc(n.span.clone());
                        Some(Denot::Expr(HExpr {
                            kind: HExprKind::Field(Box::new(p), idx),
                            ty: ft,
                            loc,
                        }))
                    }
                    (TypeKind::Access(des), suffix) => {
                        let des = *des;
                        let loc = self.loc(n.span.clone());
                        let d = HExpr {
                            kind: HExprKind::Deref(Box::new(p)),
                            ty: des,
                            loc: loc.clone(),
                        };
                        match suffix {
                            ast::Suffix::All(_) => Some(Denot::Expr(d)),
                            // A record element through the access value.
                            ast::Suffix::Ident(i) => {
                                let TypeKind::Record(fields) =
                                    self.types[self.base(des)].kind.clone()
                                else {
                                    self.error(
                                        n.span.clone(),
                                        "this selected name is not supported",
                                    );
                                    return None;
                                };
                                let Some(idx) = fields.iter().position(|(f, _)| *f == i.name)
                                else {
                                    self.error(
                                        i.span.clone(),
                                        format!("no element '{}' in the record", i.name),
                                    );
                                    return None;
                                };
                                Some(Denot::Expr(HExpr {
                                    kind: HExprKind::Field(Box::new(d), idx),
                                    ty: fields[idx].1,
                                    loc,
                                }))
                            }
                            _ => {
                                self.error(n.span.clone(), "this selected name is not supported");
                                None
                            }
                        }
                    }
                    _ => {
                        self.error(n.span.clone(), "this selected name is not supported");
                        None
                    }
                }
            }
            _ => None,
        }
    }

    /// A prefix that denotes a library or package (not an object).
    fn static_prefix(&mut self, r: RegionId, n: &ast::Name) -> Option<Sym> {
        match &n.kind {
            NameKind::Simple(i) => match self.lookup(r, &i.name).into_iter().next()? {
                s @ (Sym::Library(_) | Sym::Package(_)) => Some(s),
                _ => None,
            },
            NameKind::Selected(p, ast::Suffix::Ident(i)) => match self.static_prefix(r, p)? {
                Sym::Library(lib) => match self.unit_sym(&lib, &i.name)? {
                    s @ Sym::Package(_) => Some(s),
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        }
    }

    /// A name used as an expression.
    pub fn name_expr(
        &mut self,
        r: RegionId,
        n: &ast::Name,
        expect: Option<TypeId>,
    ) -> Option<HExpr> {
        let loc = self.loc(n.span.clone());
        match &n.kind {
            NameKind::Simple(_) | NameKind::Selected(..) | NameKind::Op(_) | NameKind::Char(_) => {
                let Some(d) = self.denote(r, n) else {
                    self.error(n.span.clone(), format!("unknown name '{}'", name_text(n)));
                    return None;
                };
                match d {
                    Denot::Expr(h) => Some(h),
                    Denot::Syms(syms) => self.syms_expr(r, syms, &[], expect, n),
                }
            }
            NameKind::Call(prefix, args) => {
                // Predefined functions by simple name, if nothing user-declared
                // matches.
                match self.denote(r, prefix) {
                    Some(Denot::Syms(syms)) => {
                        if let Some(Sym::Type(t)) = syms.first() {
                            return self.conversion(r, *t, args, n);
                        }
                        let is_sub = syms.iter().any(|s| matches!(s, Sym::Sub(_)));
                        if is_sub || syms.is_empty() {
                            return self.syms_expr(r, syms, args, expect, n);
                        }
                        let base = self.syms_expr(r, syms, &[], None, prefix)?;
                        self.index_or_slice(r, base, args, n)
                    }
                    Some(Denot::Expr(h)) => self.index_or_slice(r, h, args, n),
                    None => {
                        if let NameKind::Simple(_) = &prefix.kind {
                            return self.syms_expr(r, Vec::new(), args, expect, n);
                        }
                        // `f(x)(i)`: a call result indexed.
                        let base = self.name_expr(r, prefix, None)?;
                        self.index_or_slice(r, base, args, n)
                    }
                }
            }
            NameKind::Attribute(prefix, attr, param) => {
                self.attribute(r, prefix, attr, param.as_deref(), expect, loc)
            }
            NameKind::External { .. } => {
                self.error(n.span.clone(), "external names are not supported yet");
                None
            }
        }
    }

    /// The expression a set of named entities gives with `args`: an object,
    /// an enumeration literal, or a (possibly parameterless) function call.
    fn syms_expr(
        &mut self,
        r: RegionId,
        syms: Vec<Sym>,
        args: &[ast::Assoc],
        expect: Option<TypeId>,
        n: &ast::Name,
    ) -> Option<HExpr> {
        let loc = self.loc(n.span.clone());
        let subs: Vec<SubId> = syms
            .iter()
            .filter_map(|s| match s {
                Sym::Sub(id) => Some(*id),
                _ => None,
            })
            .collect();
        let lits: Vec<(TypeId, u32)> = syms
            .iter()
            .filter_map(|s| match s {
                Sym::EnumLit(t, p) => Some((*t, *p)),
                _ => None,
            })
            .collect();
        if args.is_empty() && !lits.is_empty() && subs.is_empty() {
            return self.pick_enum_lit(&lits, expect, &name_text(n), n.span.clone());
        }
        if subs.is_empty() && lits.is_empty() {
            match syms.first() {
                Some(Sym::Obj(o)) if args.is_empty() => {
                    return Some(HExpr {
                        kind: HExprKind::Obj(*o),
                        ty: self.objects[*o].ty,
                        loc,
                    });
                }
                Some(Sym::Alias(a)) if args.is_empty() => return Some(self.aliases[*a].clone()),
                Some(Sym::Unit(t, m)) if args.is_empty() => {
                    return Some(lit_expr(Value::Phys(*m), *t, loc));
                }
                Some(Sym::Type(_)) => {
                    self.error(n.span.clone(), "a type name cannot be used as a value");
                    return None;
                }
                Some(_) => {
                    self.error(
                        n.span.clone(),
                        format!("'{}' cannot be used here", name_text(n)),
                    );
                    return None;
                }
                None => {}
            }
        }
        // Overload resolution among functions (and enumeration literals).
        let mut cands = subs;
        if matches!(n.kind, NameKind::Simple(_) | NameKind::Call(..)) {
            let fname = match &n.kind {
                NameKind::Simple(i) => Some(i.name.clone()),
                NameKind::Call(p, _) => match &p.kind {
                    NameKind::Simple(i) => Some(i.name.clone()),
                    NameKind::Selected(_, ast::Suffix::Ident(i)) if is_predefined_func(&i.name) => {
                        Some(i.name.clone())
                    }
                    _ => None,
                },
                _ => None,
            };
            if let Some(fname) = fname {
                let sets: Vec<TypeSet> = args
                    .iter()
                    .filter_map(|a| match &a.actual {
                        ast::Actual::Expr(e) => Some(self.possible_types(r, e)),
                        _ => None,
                    })
                    .collect();
                for id in self.predefined_funcs(&fname, &sets) {
                    if !cands.iter().any(|c| self.same_profile_pub(*c, id)) {
                        cands.push(id);
                    }
                }
            }
        }
        if cands.is_empty() {
            if lits.is_empty() {
                self.error(n.span.clone(), format!("unknown name '{}'", name_text(n)));
                return None;
            }
            return self.pick_enum_lit(&lits, expect, &name_text(n), n.span.clone());
        }
        let picked = self.resolve(r, &cands, args, expect, true, n.span.clone())?;
        if args.is_empty() && !lits.is_empty() {
            // An enumeration literal and a parameterless function of the
            // same name: the literal if it fits.
            if let Some(t) = expect
                && lits.iter().any(|(lt, _)| self.base(*lt) == self.base(t))
            {
                return self.pick_enum_lit(&lits, expect, &name_text(n), n.span.clone());
            }
        }
        self.call_expr(r, picked, args, loc)
    }

    pub fn same_profile_pub(&self, a: SubId, b: SubId) -> bool {
        let (sa, sb) = (&self.subprograms[a], &self.subprograms[b]);
        sa.params.len() == sb.params.len()
            && sa.ret.map(|t| self.base(t)) == sb.ret.map(|t| self.base(t))
            && sa
                .params
                .iter()
                .zip(&sb.params)
                .all(|(x, y)| self.base(self.objects[*x].ty) == self.base(self.objects[*y].ty))
    }

    fn min_args(&self, id: SubId) -> usize {
        self.subprograms[id]
            .params
            .iter()
            .filter(|p| self.objects[**p].init.is_none())
            .count()
    }

    fn arity_ok(&self, id: SubId, args: &[ast::Assoc]) -> bool {
        let n = self.subprograms[id].params.len();
        args.len() <= n && self.min_args(id) <= args.len()
    }

    /// Map associations to formals: positional, then named (§6.5.7).
    /// Returns, per formal, the actual (`None` for a default).
    fn map_args<'a>(
        &self,
        id: SubId,
        args: &'a [ast::Assoc],
    ) -> Option<Vec<Option<&'a ast::Expr>>> {
        let params = &self.subprograms[id].params;
        let mut out: Vec<Option<&ast::Expr>> = vec![None; params.len()];
        let mut set = vec![false; params.len()];
        let mut pos = 0;
        for a in args {
            let ast::Actual::Expr(e) = &a.actual else {
                return None;
            };
            match &a.formal {
                None => {
                    if pos >= params.len() {
                        return None;
                    }
                    out[pos] = Some(e);
                    set[pos] = true;
                    pos += 1;
                }
                Some(f) => {
                    let ast::NameKind::Simple(i) = &f.kind else {
                        return None;
                    };
                    let idx = params
                        .iter()
                        .position(|p| self.objects[*p].name == i.name)?;
                    if set[idx] {
                        return None;
                    }
                    out[idx] = Some(e);
                    set[idx] = true;
                }
            }
        }
        for (i, p) in params.iter().enumerate() {
            if !set[i] && self.objects[*p].init.is_none() {
                return None;
            }
        }
        Some(out)
    }

    /// Choose among subprogram candidates by their parameter and result
    /// types (§12.5).
    fn resolve(
        &mut self,
        r: RegionId,
        cands: &[SubId],
        args: &[ast::Assoc],
        expect: Option<TypeId>,
        function: bool,
        span: ast::Span,
    ) -> Option<SubId> {
        let mut fits = Vec::new();
        let mut exact = Vec::new();
        let sets: Vec<Option<TypeSet>> = args
            .iter()
            .map(|a| match &a.actual {
                ast::Actual::Expr(e) => Some(self.possible_types(r, e)),
                _ => None,
            })
            .collect();
        for &c in cands {
            if self.subprograms[c].is_function != function {
                continue;
            }
            let Some(mapping) = self.map_args(c, args) else {
                if std::env::var_os("XEZIM_VHDL_DEBUG").is_some() {
                    eprintln!("  {}: arguments do not map", self.subprograms[c].name);
                }
                continue;
            };
            let params = self.subprograms[c].params.clone();
            let mut ok = true;
            let mut all_exact = true;
            for (pi, actual) in mapping.iter().enumerate() {
                let Some(actual) = actual else { continue };
                let ai = args
                    .iter()
                    .position(
                        |a| matches!(&a.actual, ast::Actual::Expr(e) if std::ptr::eq(e, *actual)),
                    )
                    .unwrap();
                let set = sets[ai].clone().unwrap_or_default();
                let pt = self.objects[params[pi]].ty;
                if !self.compatible(&set, pt) {
                    if std::env::var_os("XEZIM_VHDL_DEBUG").is_some() {
                        eprintln!(
                            "  {}: arg {} {:?} not compatible with {}",
                            self.subprograms[c].name,
                            pi,
                            set,
                            self.types[self.base(pt)].name
                        );
                    }
                    ok = false;
                    break;
                }
                if !set.types.contains(&self.base(pt)) {
                    all_exact = false;
                }
            }
            if !ok {
                continue;
            }
            if let (Some(t), Some(rt)) = (expect, self.subprograms[c].ret) {
                let (tb, rb) = (self.base(t), self.base(rt));
                let univ_ok = matches!(self.types[rb].kind, TypeKind::UniversalInteger)
                    && self.is_integer(tb)
                    || matches!(self.types[rb].kind, TypeKind::UniversalReal) && self.is_real(tb);
                if tb != rb && !univ_ok {
                    continue;
                }
            }
            fits.push(c);
            if all_exact {
                exact.push(c);
            }
        }
        // Prefer user-declared over predefined, and exact over universal.
        let pick = |d: &Self, v: &[SubId]| -> Option<SubId> {
            if v.len() == 1 {
                return Some(v[0]);
            }
            let user: Vec<SubId> = v
                .iter()
                .copied()
                .filter(|c| {
                    d.subprograms[*c].builtin.is_none()
                        || matches!(
                            d.subprograms[*c].builtin,
                            Some(Builtin::Native(_)) | Some(Builtin::Now)
                        )
                })
                .collect();
            if user.len() == 1 {
                return Some(user[0]);
            }
            None
        };
        if let Some(p) = pick(self, &fits) {
            return Some(p);
        }
        if let Some(p) = pick(self, &exact) {
            return Some(p);
        }
        // Several predefined operators on different types: prefer the one
        // not involving universal types.
        let non_univ: Vec<SubId> = fits
            .iter()
            .copied()
            .filter(|c| {
                self.subprograms[*c].params.iter().all(|p| {
                    !matches!(
                        self.types[self.base(self.objects[*p].ty)].kind,
                        TypeKind::UniversalInteger | TypeKind::UniversalReal
                    )
                })
            })
            .collect();
        if non_univ.len() == 1 && fits.len() > 1 {
            return Some(non_univ[0]);
        }
        if fits.is_empty() {
            let what = cands
                .first()
                .map(|c| self.subprograms[*c].name.clone())
                .unwrap_or_default();
            self.error(
                span,
                format!("no matching subprogram {} for these arguments", what),
            );
        } else {
            let what = self.subprograms[fits[0]].name.clone();
            self.error(span, format!("ambiguous call of {}", what));
        }
        None
    }

    /// The call of a resolved function with its actuals analysed against the
    /// formal types (defaults filled in).
    fn call_expr(
        &mut self,
        r: RegionId,
        id: SubId,
        args: &[ast::Assoc],
        loc: Loc,
    ) -> Option<HExpr> {
        let actuals = self.actuals(r, id, args)?;
        let ret = self.subprograms[id].ret?;
        Some(HExpr {
            kind: HExprKind::Call(id, actuals),
            ty: ret,
            loc,
        })
    }

    pub fn actuals(&mut self, r: RegionId, id: SubId, args: &[ast::Assoc]) -> Option<Vec<HExpr>> {
        let mapping = self.map_args(id, args)?;
        let params = self.subprograms[id].params.clone();
        let mut out = Vec::new();
        for (pi, a) in mapping.into_iter().enumerate() {
            let pt = self.objects[params[pi]].ty;
            match a {
                Some(e) => out.push(self.expr(r, e, Some(pt))?),
                None => out.push(self.objects[params[pi]].init.clone()?),
            }
        }
        Some(out)
    }

    /// A procedure call statement's procedure and actuals.
    pub fn procedure_call(&mut self, r: RegionId, n: &ast::Name) -> Option<(SubId, Vec<HExpr>)> {
        let (prefix, args): (&ast::Name, &[ast::Assoc]) = match &n.kind {
            NameKind::Call(p, a) => (p, a),
            _ => (n, &[]),
        };
        let cands: Vec<SubId> = match self.denote(r, prefix) {
            Some(Denot::Syms(s)) => s
                .into_iter()
                .filter_map(|x| match x {
                    Sym::Sub(id) => Some(id),
                    _ => None,
                })
                .collect(),
            _ => Vec::new(),
        };
        // Predefined procedures (DEALLOCATE, §5.4.3).
        let mut cands = cands;
        if let NameKind::Simple(i) = &prefix.kind
            && i.name == "deallocate"
        {
            let sets: Vec<TypeSet> = args
                .iter()
                .filter_map(|a| match &a.actual {
                    ast::Actual::Expr(e) => Some(self.possible_types(r, e)),
                    _ => None,
                })
                .collect();
            cands.extend(self.predefined_funcs("deallocate", &sets));
        }
        if cands.is_empty() {
            self.error(
                n.span.clone(),
                format!("unknown procedure '{}'", name_text(prefix)),
            );
            return None;
        }
        let id = self.resolve(r, &cands, args, None, false, n.span.clone())?;
        let actuals = self.actuals(r, id, args)?;
        Some((id, actuals))
    }

    fn operator(
        &mut self,
        r: RegionId,
        key: &str,
        sym: &str,
        operands: &[&ast::Expr],
        expect: Option<TypeId>,
        span: ast::Span,
    ) -> Option<HExpr> {
        let mut cands: Vec<SubId> = self
            .lookup(r, key)
            .into_iter()
            .filter_map(|s| match s {
                Sym::Sub(id) if self.subprograms[id].params.len() == operands.len() => Some(id),
                _ => None,
            })
            .collect();
        let sets: Vec<TypeSet> = operands.iter().map(|e| self.possible_types(r, e)).collect();
        for id in self.predefined_ops(sym, &sets, expect) {
            // An explicit declaration hides the predefined homograph.
            if !cands.iter().any(|c| self.same_profile_pub(*c, id)) {
                cands.push(id);
            }
        }
        let args: Vec<ast::Assoc> = operands
            .iter()
            .map(|e| ast::Assoc {
                formal: None,
                actual: ast::Actual::Expr((*e).clone()),
                span: e.span.clone(),
            })
            .collect();
        if cands.is_empty() {
            self.error(span, format!("no operator {} for these operand types", key));
            return None;
        }
        let id = self.resolve(r, &cands, &args, expect, true, span.clone())?;
        let loc = self.loc(span);
        self.call_expr(r, id, &args, loc)
    }

    /// `t(x)`: a type conversion (§9.3.6).
    fn conversion(
        &mut self,
        r: RegionId,
        t: TypeId,
        args: &[ast::Assoc],
        n: &ast::Name,
    ) -> Option<HExpr> {
        let loc = self.loc(n.span.clone());
        let [
            ast::Assoc {
                formal: None,
                actual: ast::Actual::Expr(e),
                ..
            },
        ] = args
        else {
            self.error(n.span.clone(), "a type conversion takes one operand");
            return None;
        };
        let x = self.expr(r, e, None)?;
        Some(HExpr {
            kind: HExprKind::Convert(Box::new(x)),
            ty: t,
            loc,
        })
    }

    /// `a(i, j)` (index) or `a(3 downto 0)` / `a(t'range)` (slice).
    fn index_or_slice(
        &mut self,
        r: RegionId,
        base: HExpr,
        args: &[ast::Assoc],
        n: &ast::Name,
    ) -> Option<HExpr> {
        let loc = self.loc(n.span.clone());
        let base = self.implicit_deref(base);
        let b = self.base(base.ty);
        let TypeKind::Array { index, elem } = self.types[b].kind.clone() else {
            self.error(n.span.clone(), "only arrays can be indexed or sliced");
            return None;
        };
        let slice = args.len() == 1 && self.is_range_actual(r, &args[0]);
        if slice {
            let ast::Actual::Expr(e) = &args[0].actual else {
                unreachable!()
            };
            let dr = expr_to_discrete_range(e);
            let (_, hr) = self.discrete_range(r, &dr, Some(index[0]))?;
            let ty = self.add_type(
                "",
                TypeKind::Subtype {
                    base: b,
                    constraint: Some(HConstraint::Index(vec![Some(hr.clone())], None)),
                    resolution: None,
                },
                None,
                None,
            );
            return Some(HExpr {
                kind: HExprKind::Slice(Box::new(base), hr),
                ty,
                loc,
            });
        }
        if args.len() != index.len() {
            self.error(n.span.clone(), "wrong number of indices");
            return None;
        }
        let mut idx = Vec::new();
        for (a, it) in args.iter().zip(&index) {
            let ast::Actual::Expr(e) = &a.actual else {
                self.error(n.span.clone(), "an index cannot be open");
                return None;
            };
            idx.push(self.expr(r, e, Some(*it))?);
        }
        // The element subtype of the array subtype (element constraints).
        let ety = self.element_subtype(base.ty).unwrap_or(elem);
        Some(HExpr {
            kind: HExprKind::Index(Box::new(base), idx),
            ty: ety,
            loc,
        })
    }

    /// Whether an association actual is a discrete range (a slice), not
    /// an index: `3 downto 0`, `x'range`, a subtype name.
    fn is_range_actual(&mut self, r: RegionId, a: &ast::Assoc) -> bool {
        match &a.actual {
            ast::Actual::Expr(e) => match &e.kind {
                ast::ExprKind::Range(_) => true,
                ast::ExprKind::Name(nm) => match &nm.kind {
                    NameKind::Attribute(_, at, _) => {
                        matches!(at.name.as_str(), "range" | "reverse_range")
                    }
                    NameKind::Simple(_) | NameKind::Selected(..) => {
                        let n = self.errors.len();
                        let d = self.denote(r, nm);
                        self.errors.truncate(n);
                        matches!(d, Some(Denot::Syms(s)) if matches!(s.first(), Some(Sym::Type(_))))
                    }
                    _ => false,
                },
                _ => false,
            },
            _ => false,
        }
    }

    pub fn element_subtype(&self, t: TypeId) -> Option<TypeId> {
        let mut cur = t;
        loop {
            match &self.types[cur].kind {
                TypeKind::Subtype {
                    constraint: Some(HConstraint::Index(_, Some(e))),
                    ..
                } => return Some(*e),
                TypeKind::Subtype { base, .. } => cur = *base,
                TypeKind::Array { elem, .. } => return Some(*elem),
                _ => return None,
            }
        }
    }

    // ---- ranges ---------------------------------------------------------------------

    /// A range expression of type `expect` (or self-determined).
    pub fn range_expr(
        &mut self,
        r: RegionId,
        re: &ast::RangeExpr,
        expect: Option<TypeId>,
    ) -> Option<HRange> {
        match re {
            ast::RangeExpr::Explicit {
                left, dir, right, ..
            } => {
                // The bounds' type: from the context, else from each other.
                let t = match expect {
                    Some(t) => Some(t),
                    None => {
                        let (ls, rs) =
                            (self.possible_types(r, left), self.possible_types(r, right));
                        ls.types.first().or(rs.types.first()).copied()
                    }
                };
                let l = self.expr(r, left, t)?;
                let rr = self.expr(r, right, t.or(Some(l.ty)))?;
                // Both universal: the right one's type follows the left.
                let l = self.implicit_convert(l, Some(rr.ty));
                let static_val = match (self.eval(&l), self.eval(&rr)) {
                    (Some(a), Some(b)) => Some(StaticRange {
                        left: a,
                        dir: *dir,
                        right: b,
                    }),
                    _ => None,
                };
                Some(HRange {
                    left: Box::new(l),
                    dir: *dir,
                    right: Box::new(rr),
                    static_val,
                    of_obj: None,
                })
            }
            ast::RangeExpr::Attr(n) => {
                let ast::NameKind::Attribute(prefix, attr, param) = &n.kind else {
                    // A subtype name used as a range.
                    let t = self.type_mark(r, n)?;
                    return self.type_range(t, n.span.clone());
                };
                if !matches!(attr.name.as_str(), "range" | "reverse_range") {
                    self.error(n.span.clone(), "a range attribute was expected");
                    return None;
                }
                self.range_attr(
                    r,
                    prefix,
                    attr.name == "reverse_range",
                    param.as_deref(),
                    n.span.clone(),
                )
            }
        }
    }

    /// `x'range`, `x'reverse_range` (with an optional dimension).
    fn range_attr(
        &mut self,
        r: RegionId,
        prefix: &ast::Name,
        reverse: bool,
        dim: Option<&ast::Expr>,
        span: ast::Span,
    ) -> Option<HRange> {
        let dim = match dim {
            Some(e) => {
                let h = self.expr(r, e, None)?;
                (self.eval(&h)?.as_i64()? - 1) as usize
            }
            None => 0,
        };
        // A type or an object.
        let pt = match self.denote(r, prefix) {
            Some(Denot::Syms(s)) if matches!(s.first(), Some(Sym::Type(_))) => {
                let Some(Sym::Type(t)) = s.first() else {
                    unreachable!()
                };
                if self.is_scalar(*t) {
                    let hr = self.type_range(*t, span)?;
                    return Some(if reverse { reverse_range(hr) } else { hr });
                }
                (None, *t)
            }
            _ => {
                let h = self.name_expr(r, prefix, None)?;
                let h = self.implicit_deref(h);
                let t = h.ty;
                (Some(h), t)
            }
        };
        let (obj, t) = pt;
        // Static bounds when the (sub)type is constrained.
        if let Some(ranges) = self.array_constraint(t)
            && let Some(Some(hr)) = ranges.get(dim)
        {
            return Some(if reverse {
                reverse_range(hr.clone())
            } else {
                hr.clone()
            });
        }
        // Dynamic: 'left/'right of the object.
        let Some(obj) = obj else {
            self.error(span, "the range of an unconstrained type");
            return None;
        };
        let loc = self.loc(span);
        let TypeKind::Array { index, .. } = self.types[self.base(t)].kind.clone() else {
            self.error(loc.span.clone(), "'range needs an array");
            return None;
        };
        let it = index.get(dim).copied().unwrap_or(self.std.integer);
        let placeholder = Box::new(lit_expr(Value::Int(0), it, loc.clone()));
        Some(HRange {
            left: placeholder.clone(),
            dir: Dir::To,
            right: placeholder,
            static_val: None,
            of_obj: Some((Box::new(obj), dim, reverse)),
        })
    }

    // ---- attributes ------------------------------------------------------------------

    fn attribute(
        &mut self,
        r: RegionId,
        prefix: &ast::Name,
        attr: &ast::Ident,
        param: Option<&ast::Expr>,
        expect: Option<TypeId>,
        loc: Loc,
    ) -> Option<HExpr> {
        let name = attr.name.as_str();
        let ui = self.std.universal_integer;
        let boolean = self.std.boolean;
        let string = self.std.string;
        let time = self.std.time;
        // Type prefix?
        let type_prefix = match self.denote(r, prefix) {
            Some(Denot::Syms(s)) => match s.first() {
                Some(Sym::Type(t)) => Some(*t),
                _ => None,
            },
            _ => None,
        };
        if let Some(t) = type_prefix {
            let p = Box::new(AttrPrefix::Type(t));
            let mk = |d: &mut Self, ty: TypeId, param: Option<HExpr>| -> HExpr {
                let h = HExpr {
                    kind: HExprKind::Attr(name.to_string(), p.clone(), param.map(Box::new)),
                    ty,
                    loc: loc.clone(),
                };
                match d.eval(&h) {
                    Some(v) => lit_expr(v, ty, loc.clone()),
                    None => h,
                }
            };
            return match name {
                "left" | "right" | "high" | "low" if self.is_scalar(t) => Some(mk(self, t, None)),
                "left" | "right" | "high" | "low" => {
                    let it = self.index_type(t, param.map(|_| 0))?;
                    let pe = match param {
                        Some(e) => Some(self.expr(r, e, Some(ui))?),
                        None => None,
                    };
                    Some(mk(self, it, pe))
                }
                "length" => {
                    let pe = match param {
                        Some(e) => Some(self.expr(r, e, Some(ui))?),
                        None => None,
                    };
                    Some(mk(self, ui, pe))
                }
                "ascending" => Some(mk(self, boolean, None)),
                "image" => {
                    let e = param?;
                    let x = self.expr(r, e, Some(t))?;
                    Some(mk(self, string, Some(x)))
                }
                "value" => {
                    let e = param?;
                    let x = self.expr(r, e, Some(string))?;
                    Some(mk(self, t, Some(x)))
                }
                "pos" => {
                    let e = param?;
                    let x = self.expr(r, e, Some(t))?;
                    Some(mk(self, ui, Some(x)))
                }
                "val" => {
                    let e = param?;
                    let x = self.expr(r, e, None)?;
                    Some(mk(self, t, Some(x)))
                }
                "succ" | "pred" | "leftof" | "rightof" => {
                    let e = param?;
                    let x = self.expr(r, e, Some(t))?;
                    Some(mk(self, t, Some(x)))
                }
                "base" => {
                    self.error(
                        attr.span.clone(),
                        "'base is only allowed as the prefix of another attribute",
                    );
                    None
                }
                _ => {
                    self.error(
                        attr.span.clone(),
                        format!("attribute '{} is not supported yet", name),
                    );
                    None
                }
            };
        }
        // Object (or expression) prefix; an access value's array attributes
        // are those of the designated array (§8.3).
        let px = self.name_expr(r, prefix, None)?;
        let px = if self.designated(px.ty).is_some_and(|d| self.is_array(d))
            && matches!(
                name,
                "left" | "right" | "high" | "low" | "length" | "ascending"
            ) {
            self.implicit_deref(px)
        } else {
            px
        };
        let pt = px.ty;
        let mk = |d: &mut Self, ty: TypeId, param: Option<HExpr>, px: HExpr| -> HExpr {
            let h = HExpr {
                kind: HExprKind::Attr(
                    name.to_string(),
                    Box::new(AttrPrefix::Expr(px)),
                    param.map(Box::new),
                ),
                ty,
                loc: loc.clone(),
            };
            match d.eval(&h) {
                Some(v) => lit_expr(v, ty, loc.clone()),
                None => h,
            }
        };
        let is_signal = self.is_signal_expr(&px);
        match name {
            "left" | "right" | "high" | "low" | "length" | "ascending" => {
                let pe = match param {
                    Some(e) => Some(self.expr(r, e, Some(ui))?),
                    None => None,
                };
                let ty = match name {
                    "length" => ui,
                    "ascending" => boolean,
                    _ => self.index_type(pt, None)?,
                };
                Some(mk(self, ty, pe, px))
            }
            "event" | "active" | "stable" | "quiet" if is_signal => {
                let pe = match param {
                    Some(e) => Some(self.expr(r, e, Some(time))?),
                    None => None,
                };
                Some(mk(self, boolean, pe, px))
            }
            "last_value" | "driving_value" if is_signal => Some(mk(self, pt, None, px)),
            "last_event" | "last_active" if is_signal => Some(mk(self, time, None, px)),
            "delayed" if is_signal => {
                let pe = match param {
                    Some(e) => Some(self.expr(r, e, Some(time))?),
                    None => None,
                };
                Some(mk(self, pt, pe, px))
            }
            "driving" if is_signal => Some(mk(self, boolean, None, px)),
            "image" => {
                // VHDL-2019 object'image; GHDL accepts it in 2008 mode too.
                let _ = expect;
                Some(mk(self, string, None, px))
            }
            "simple_name" | "path_name" | "instance_name" => Some(mk(self, string, None, px)),
            _ => {
                self.error(
                    attr.span.clone(),
                    format!("attribute '{} is not supported here", name),
                );
                None
            }
        }
    }

    /// The index subtype of dimension `dim` (0-based) of an array type.
    fn index_type(&mut self, t: TypeId, dim: Option<usize>) -> Option<TypeId> {
        match &self.types[self.base(t)].kind {
            TypeKind::Array { index, .. } => index.get(dim.unwrap_or(0)).copied(),
            _ => None,
        }
    }

    /// An access value used as the object it designates (§8.3).
    pub fn implicit_deref(&self, h: HExpr) -> HExpr {
        match self.designated(h.ty) {
            Some(des) => HExpr {
                loc: h.loc.clone(),
                kind: HExprKind::Deref(Box::new(h)),
                ty: des,
            },
            None => h,
        }
    }

    pub fn is_signal_expr(&self, h: &HExpr) -> bool {
        match &h.kind {
            HExprKind::Obj(o) => matches!(
                self.objects[*o].kind,
                ObjKind::Signal | ObjKind::Port(_) | ObjKind::Param(ast::ObjClass::Signal, _)
            ),
            HExprKind::Index(b, _) | HExprKind::Slice(b, _) | HExprKind::Field(b, _) => {
                self.is_signal_expr(b)
            }
            _ => false,
        }
    }

    // ---- static evaluation -----------------------------------------------------------

    /// The value of a static expression (`None` when not static).
    pub fn eval(&self, h: &HExpr) -> Option<Value> {
        match &h.kind {
            HExprKind::Lit(v) => Some(v.clone()),
            HExprKind::Obj(o) => match self.objects[*o].kind {
                ObjKind::Constant | ObjKind::Generic => self.objects[*o].static_val.clone(),
                _ => None,
            },
            HExprKind::Qualified(x) => self.eval(x),
            HExprKind::Convert(x) => {
                let v = self.eval(x)?;
                let t = self.base(h.ty);
                if self.is_integer(t) {
                    match v {
                        Value::Real(r) => Some(Value::Int(r.round() as i64)),
                        Value::Int(i) => Some(Value::Int(i)),
                        _ => None,
                    }
                } else if self.is_real(t) {
                    Some(Value::Real(to_f64(&v)))
                } else {
                    Some(v)
                }
            }
            HExprKind::Call(id, args) => {
                let s = &self.subprograms[*id];
                let Some(Builtin::Op(op)) = &s.builtin else {
                    return None;
                };
                let vals: Option<Vec<Value>> = args.iter().map(|a| self.eval(a)).collect();
                let vals = vals?;
                self.eval_op(op, &vals, h.ty, args)
            }
            HExprKind::Attr(name, prefix, param) => {
                let p = param.as_ref().and_then(|x| self.eval(x));
                match prefix.as_ref() {
                    AttrPrefix::Type(t) => self.eval_type_attr(name, *t, p),
                    AttrPrefix::Expr(x) => {
                        // Array attributes of a constrained object.
                        let dim = p.and_then(|v| v.as_i64()).unwrap_or(1) as usize - 1;
                        let ranges = self.array_index_ranges(x.ty)?;
                        let sr = ranges.get(dim)?.clone()?;
                        let (l, rr) = (sr.left.as_i64()?, sr.right.as_i64()?);
                        match name.as_str() {
                            "left" => Some(sr.left.clone()),
                            "right" => Some(sr.right.clone()),
                            "high" => Some(if sr.dir == Dir::To {
                                sr.right.clone()
                            } else {
                                sr.left.clone()
                            }),
                            "low" => Some(if sr.dir == Dir::To {
                                sr.left.clone()
                            } else {
                                sr.right.clone()
                            }),
                            "length" => Some(Value::Int(match sr.dir {
                                Dir::To => (rr - l + 1).max(0),
                                Dir::Downto => (l - rr + 1).max(0),
                            })),
                            "ascending" => Some(Value::Enum((sr.dir == Dir::To) as u32)),
                            _ => None,
                        }
                    }
                }
            }
            _ => None,
        }
    }

    fn eval_type_attr(&self, name: &str, t: TypeId, p: Option<Value>) -> Option<Value> {
        if self.is_scalar(t) {
            let sr = self.scalar_range(t)?;
            let asc = sr.dir == Dir::To;
            return match name {
                "left" => Some(sr.left),
                "right" => Some(sr.right),
                "high" => Some(if asc { sr.right } else { sr.left }),
                "low" => Some(if asc { sr.left } else { sr.right }),
                "ascending" => Some(Value::Enum(asc as u32)),
                "pos" => Some(Value::Int(p?.as_i64()?)),
                "val" => {
                    let v = p?.as_i64()?;
                    Some(if self.is_enum(t) {
                        Value::Enum(v as u32)
                    } else if self.is_physical(t) {
                        Value::Phys(v)
                    } else {
                        Value::Int(v)
                    })
                }
                "succ" | "pred" | "leftof" | "rightof" => {
                    let v = p?;
                    let step = match name {
                        "succ" => 1,
                        "pred" => -1,
                        "rightof" => {
                            if asc {
                                1
                            } else {
                                -1
                            }
                        }
                        _ => {
                            if asc {
                                -1
                            } else {
                                1
                            }
                        }
                    };
                    Some(match v {
                        Value::Enum(e) => Value::Enum((e as i64 + step) as u32),
                        Value::Int(i) => Value::Int(i + step),
                        Value::Phys(i) => Value::Phys(i + step),
                        _ => return None,
                    })
                }
                _ => None,
            };
        }
        // Constrained array type attributes.
        let dim = p.and_then(|v| v.as_i64()).unwrap_or(1) as usize - 1;
        let sr = self.array_index_ranges(t)?.get(dim)?.clone()?;
        let (l, r) = (sr.left.as_i64()?, sr.right.as_i64()?);
        match name {
            "left" => Some(sr.left.clone()),
            "right" => Some(sr.right.clone()),
            "high" => Some(if sr.dir == Dir::To { sr.right } else { sr.left }),
            "low" => Some(if sr.dir == Dir::To { sr.left } else { sr.right }),
            "length" => Some(Value::Int(match sr.dir {
                Dir::To => (r - l + 1).max(0),
                Dir::Downto => (l - r + 1).max(0),
            })),
            "ascending" => Some(Value::Enum((sr.dir == Dir::To) as u32)),
            _ => None,
        }
    }

    /// A predefined operator on static values.
    fn eval_op(&self, op: &str, v: &[Value], ty: TypeId, args: &[HExpr]) -> Option<Value> {
        let bool_v = |b: bool| Value::Enum(b as u32);
        match (op, v) {
            ("+", [Value::Int(a), Value::Int(b)]) => a.checked_add(*b).map(Value::Int),
            ("-", [Value::Int(a), Value::Int(b)]) => a.checked_sub(*b).map(Value::Int),
            ("*", [Value::Int(a), Value::Int(b)]) => a.checked_mul(*b).map(Value::Int),
            ("/", [Value::Int(a), Value::Int(b)]) if *b != 0 => Some(Value::Int(a / b)),
            // §9.2.7: `a mod b` has the sign of b.
            ("mod", [Value::Int(a), Value::Int(b)]) if *b != 0 => {
                let m = a % b;
                Some(Value::Int(if m != 0 && (m < 0) != (*b < 0) {
                    m + b
                } else {
                    m
                }))
            }
            ("rem", [Value::Int(a), Value::Int(b)]) if *b != 0 => Some(Value::Int(a % b)),
            ("**", [Value::Int(a), Value::Int(b)]) if *b >= 0 => {
                a.checked_pow(*b as u32).map(Value::Int)
            }
            ("+", [Value::Real(a), Value::Real(b)]) => Some(Value::Real(a + b)),
            ("-", [Value::Real(a), Value::Real(b)]) => Some(Value::Real(a - b)),
            ("*", [Value::Real(a), Value::Real(b)]) => Some(Value::Real(a * b)),
            ("/", [Value::Real(a), Value::Real(b)]) => Some(Value::Real(a / b)),
            ("**", [Value::Real(a), Value::Int(b)]) => Some(Value::Real(a.powi(*b as i32))),
            ("*", [Value::Int(a), Value::Real(b)]) => Some(Value::Real(*a as f64 * b)),
            ("*", [Value::Real(a), Value::Int(b)]) => Some(Value::Real(a * *b as f64)),
            ("/", [Value::Real(a), Value::Int(b)]) => Some(Value::Real(a / *b as f64)),
            ("+", [Value::Phys(a), Value::Phys(b)]) => a.checked_add(*b).map(Value::Phys),
            ("-", [Value::Phys(a), Value::Phys(b)]) => a.checked_sub(*b).map(Value::Phys),
            ("*", [Value::Phys(a), Value::Int(b)]) | ("*", [Value::Int(b), Value::Phys(a)]) => {
                a.checked_mul(*b).map(Value::Phys)
            }
            ("*", [Value::Phys(a), Value::Real(b)]) | ("*", [Value::Real(b), Value::Phys(a)]) => {
                Some(Value::Phys((*a as f64 * b).round() as i64))
            }
            ("/", [Value::Phys(a), Value::Int(b)]) if *b != 0 => Some(Value::Phys(a / b)),
            ("/", [Value::Phys(a), Value::Phys(b)]) if *b != 0 => Some(Value::Int(a / b)),
            ("-", [Value::Int(a)]) => a.checked_neg().map(Value::Int),
            ("-", [Value::Real(a)]) => Some(Value::Real(-a)),
            ("-", [Value::Phys(a)]) => a.checked_neg().map(Value::Phys),
            ("+", [x]) => Some(x.clone()),
            ("abs", [Value::Int(a)]) => Some(Value::Int(a.abs())),
            ("abs", [Value::Real(a)]) => Some(Value::Real(a.abs())),
            ("abs", [Value::Phys(a)]) => Some(Value::Phys(a.abs())),
            ("=", [a, b]) => Some(bool_v(a == b)),
            ("/=", [a, b]) => Some(bool_v(a != b)),
            ("<" | "<=" | ">" | ">=", [a, b]) => {
                let ord = match (a, b) {
                    (Value::Real(x), Value::Real(y)) => x.partial_cmp(y)?,
                    _ => a.as_i64()?.cmp(&b.as_i64()?),
                };
                use std::cmp::Ordering::*;
                Some(bool_v(match op {
                    "<" => ord == Less,
                    "<=" => ord != Greater,
                    ">" => ord == Greater,
                    _ => ord != Less,
                }))
            }
            ("and" | "or" | "xor" | "nand" | "nor" | "xnor", [Value::Enum(a), Value::Enum(b)]) => {
                let (a, b) = (*a != 0, *b != 0);
                Some(bool_v(match op {
                    "and" => a && b,
                    "or" => a || b,
                    "xor" => a ^ b,
                    "nand" => !(a && b),
                    "nor" => !(a || b),
                    _ => a == b,
                }))
            }
            ("not", [Value::Enum(a)]) => Some(bool_v(*a == 0)),
            ("&", [a, b]) => {
                let _ = args;
                let mut elems = Vec::new();
                for x in [a, b] {
                    match x {
                        Value::Array(av) => elems.extend(av.elems.iter().cloned()),
                        e => elems.push(e.clone()),
                    }
                }
                let n = elems.len() as i64;
                let (left, dir, _) = self.literal_bounds(ty, n)?;
                let right = match dir {
                    Dir::To => left + n - 1,
                    Dir::Downto => left - n + 1,
                };
                Some(Value::Array(Box::new(ArrayValue {
                    left,
                    dir,
                    right,
                    elems,
                })))
            }
            _ => None,
        }
    }
}

fn reverse_range(mut hr: HRange) -> HRange {
    std::mem::swap(&mut hr.left, &mut hr.right);
    hr.dir = match hr.dir {
        Dir::To => Dir::Downto,
        Dir::Downto => Dir::To,
    };
    if let Some(sr) = &mut hr.static_val {
        std::mem::swap(&mut sr.left, &mut sr.right);
        sr.dir = hr.dir;
    }
    hr
}

/// Functions every type implicitly declares (§5.2.6, §16.3).
fn is_predefined_func(n: &str) -> bool {
    matches!(
        n,
        "rising_edge" | "falling_edge" | "to_string" | "minimum" | "maximum" | "deallocate"
    )
}
