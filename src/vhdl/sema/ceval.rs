//! Static evaluation (IEEE 1076-2008 §9.4): the value of a static
//! expression, calls of functions included. A function call is evaluated by
//! interpreting the function's body (its statements on values of `hir::Value`),
//! the way elaboration evaluates the generics, constants, generate
//! parameters and ranges that call functions (§14.4.2). Anything the
//! interpreter does not model (a signal, a file, an access value, a
//! procedure call, a failed assertion) makes the expression not static.

use std::collections::HashMap;

use super::Design;
use super::hir::*;
use crate::vhdl::ast::Dir;

/// Statements a static evaluation may run before it gives up (an endless
/// loop in a function is not static).
const BUDGET: u64 = 20_000_000;
/// Nesting of function calls.
const MAX_DEPTH: u32 = 256;

pub(super) struct Interp<'a> {
    d: &'a Design,
    /// Variables and parameters of the functions being evaluated.
    frames: Vec<HashMap<ObjId, Value>>,
    steps: u64,
}

enum Flow {
    Normal,
    Return(Option<Value>),
    Exit(usize),
    Next(usize),
}

impl<'a> Interp<'a> {
    pub(super) fn new(d: &'a Design) -> Self {
        Interp {
            d,
            frames: Vec::new(),
            steps: 0,
        }
    }

    fn var(&self, o: ObjId) -> Option<&Value> {
        self.frames.last()?.get(&o)
    }

    pub(super) fn expr(&mut self, h: &HExpr) -> Option<Value> {
        let d = self.d;
        match &h.kind {
            HExprKind::Lit(v) => Some(v.clone()),
            HExprKind::Obj(o) => {
                if let Some(v) = self.var(*o) {
                    return Some(v.clone());
                }
                match d.objects[*o].kind {
                    ObjKind::Constant | ObjKind::Generic => d.objects[*o].static_val.clone(),
                    _ => None,
                }
            }
            HExprKind::Qualified(x) => self.expr(x),
            // Only the selected value is evaluated (VHDL-2019 §9.1).
            HExprKind::Cond(arms, last) => {
                for (c, v) in arms {
                    if self.expr(c)? == Value::Enum(1) {
                        return self.expr(v);
                    }
                }
                self.expr(last)
            }
            HExprKind::RecordAgg(vals) => Some(Value::Record(
                vals.iter()
                    .map(|v| self.expr(v))
                    .collect::<Option<Vec<_>>>()?,
            )),
            HExprKind::Convert(x) => {
                let v = self.expr(x)?;
                let t = d.base(h.ty);
                if d.is_integer(t) {
                    match v {
                        Value::Real(r) => Some(Value::Int(round_half_away(r))),
                        Value::Int(i) => Some(Value::Int(i)),
                        _ => None,
                    }
                } else if d.is_real(t) {
                    Some(Value::Real(super::decl::to_f64(&v)))
                } else if let Value::Array(a) = v {
                    // An array conversion keeps the elements; a constrained
                    // target gives the bounds (§9.3.6).
                    match self.bounds(h.ty) {
                        Some((l, dir, r)) => Some(Value::Array(Box::new(ArrayValue {
                            left: l,
                            dir,
                            right: r,
                            elems: a.elems,
                        }))),
                        None => Some(Value::Array(a)),
                    }
                } else {
                    Some(v)
                }
            }
            HExprKind::Call(id, args) => {
                let s = &d.subprograms[*id];
                match &s.builtin {
                    Some(Builtin::Op(op)) => {
                        // Short-circuit operators (§9.2.2).
                        if matches!(op.as_str(), "and" | "or") && args.len() == 2 {
                            let a = self.expr(&args[0])?;
                            if let Value::Enum(x) = a
                                && d.base(args[0].ty) == d.std.boolean
                            {
                                let short = if op == "and" { x == 0 } else { x != 0 };
                                if short {
                                    return Some(Value::Enum(x));
                                }
                            }
                            let b = self.expr(&args[1])?;
                            return d.eval_op(op, &[a, b], h.ty, args);
                        }
                        let vals = args
                            .iter()
                            .map(|a| self.expr(a))
                            .collect::<Option<Vec<_>>>()?;
                        d.eval_op(op, &vals, h.ty, args)
                    }
                    Some(Builtin::MinMax(max)) => {
                        let vals = args
                            .iter()
                            .map(|a| self.expr(a))
                            .collect::<Option<Vec<_>>>()?;
                        let (a, b) = match vals.as_slice() {
                            [a, b] => (a.clone(), b.clone()),
                            _ => return None,
                        };
                        let less = match (&a, &b) {
                            (Value::Real(x), Value::Real(y)) => x < y,
                            _ => a.as_i64()? < b.as_i64()?,
                        };
                        Some(if less == *max { b } else { a })
                    }
                    Some(_) => None,
                    None => {
                        let vals = args
                            .iter()
                            .map(|a| self.expr(a))
                            .collect::<Option<Vec<_>>>()?;
                        self.call(*id, vals)
                    }
                }
            }
            HExprKind::Index(b, idx) => {
                let base = self.expr(b)?;
                let Value::Array(a) = base else { return None };
                let i = self.expr(idx.first()?)?.as_i64()?;
                let k = offset(&a, i)?;
                let mut v = a.elems.get(k)?.clone();
                // Further dimensions: arrays of arrays in this value model.
                for x in &idx[1..] {
                    let Value::Array(inner) = v else { return None };
                    let j = self.expr(x)?.as_i64()?;
                    v = inner.elems.get(offset(&inner, j)?)?.clone();
                }
                Some(v)
            }
            HExprKind::Slice(b, r) => {
                let base = self.expr(b)?;
                let Value::Array(a) = base else { return None };
                let (l, dir, rr) = self.range(r)?;
                slice(&a, l, dir, rr)
            }
            HExprKind::Field(b, i) => match self.expr(b)? {
                Value::Record(f) => f.get(*i).cloned(),
                _ => None,
            },
            HExprKind::ArrayAgg(items) => self.aggregate(items, h.ty),
            HExprKind::Attr(name, prefix, param) => {
                let p = match param {
                    Some(x) => Some(self.expr(x)?),
                    None => None,
                };
                match prefix.as_ref() {
                    AttrPrefix::Type(t) => {
                        if name == "image" {
                            return self.image(*t, &p?);
                        }
                        if d.is_scalar(*t) || name == "value" {
                            d.eval_type_attr(name, *t, p)
                        } else {
                            let (l, dir, r) = self.bounds(*t)?;
                            array_attr(name, l, dir, r)
                        }
                    }
                    AttrPrefix::Expr(x) => {
                        let dim = p.and_then(|v| v.as_i64()).unwrap_or(1) as usize;
                        // A constrained subtype gives the bounds; else the
                        // value (an unconstrained parameter).
                        if dim == 1
                            && let Some((l, dir, r)) = self.bounds(x.ty)
                        {
                            return array_attr(name, l, dir, r);
                        }
                        let mut v = self.expr(x)?;
                        for _ in 1..dim {
                            let Value::Array(a) = v else { return None };
                            v = a.elems.first()?.clone();
                        }
                        let Value::Array(a) = v else { return None };
                        array_attr(name, a.left, a.dir, a.right)
                    }
                }
            }
            _ => None,
        }
    }

    /// `T'image(v)` (§16.2.2) for an integer, enumeration or physical
    /// value, as a STRING.
    fn image(&self, t: TypeId, v: &Value) -> Option<Value> {
        let d = self.d;
        let b = d.base(t);
        let text = match (&d.types[b].kind, v) {
            (TypeKind::Integer | TypeKind::UniversalInteger, Value::Int(i)) => i.to_string(),
            (TypeKind::Enum(lits), Value::Enum(k)) => lits.get(*k as usize)?.clone(),
            (TypeKind::Physical(units), Value::Phys(x)) => format!("{} {}", x, units.first()?.0),
            _ => return None,
        };
        let elems: Vec<Value> = text.bytes().map(|c| Value::Enum(c as u32)).collect();
        let n = elems.len() as i64;
        Some(Value::Array(Box::new(ArrayValue {
            left: 1,
            dir: Dir::To,
            right: n,
            elems,
        })))
    }

    /// Call function `f` with argument values.
    fn call(&mut self, f: SubId, args: Vec<Value>) -> Option<Value> {
        let d = self.d;
        let s = &d.subprograms[f];
        if !s.is_function || self.frames.len() as u32 >= MAX_DEPTH {
            return None;
        }
        let body = s.body.as_ref()?;
        let mut frame = HashMap::new();
        for (k, p) in s.params.iter().enumerate() {
            let v = match args.get(k) {
                Some(v) => v.clone(),
                None => return None,
            };
            let v = self.rebound(d.objects[*p].ty, v)?;
            frame.insert(*p, v);
        }
        self.frames.push(frame);
        let mut ok = true;
        for l in &body.locals {
            let info = &d.objects[*l];
            if !matches!(info.kind, ObjKind::Variable | ObjKind::Constant) {
                // A file or an object of a protected type: not static.
                ok = false;
                break;
            }
            let v = match &info.init {
                Some(e) => self.expr(e).and_then(|v| self.rebound(info.ty, v)),
                None => self.default_of(info.ty),
            };
            match v {
                Some(v) => {
                    self.frames.last_mut().unwrap().insert(*l, v);
                }
                None => {
                    ok = false;
                    break;
                }
            }
        }
        let flow = if ok { self.stmts(&body.stmts) } else { None };
        self.frames.pop();
        match flow? {
            Flow::Return(Some(v)) => {
                let rt = s.ret?;
                self.rebound(rt, v)
            }
            _ => None,
        }
    }

    fn stmts(&mut self, ss: &[HStmt]) -> Option<Flow> {
        for s in ss {
            self.steps += 1;
            if self.steps > BUDGET {
                return None;
            }
            match self.stmt(s)? {
                Flow::Normal => {}
                f => return Some(f),
            }
        }
        Some(Flow::Normal)
    }

    fn stmt(&mut self, s: &HStmt) -> Option<Flow> {
        let d = self.d;
        match &s.kind {
            HStmtKind::Null => Some(Flow::Normal),
            HStmtKind::VarAssign { target, value } => {
                let v = self.expr(value)?;
                self.assign(target, v)?;
                Some(Flow::Normal)
            }
            HStmtKind::If(arms, els) => {
                for (c, body) in arms {
                    if self.cond(c)? {
                        return self.stmts(body);
                    }
                }
                match els {
                    Some(b) => self.stmts(b),
                    None => Some(Flow::Normal),
                }
            }
            HStmtKind::Case { expr, alts } => {
                let v = self.expr(expr)?;
                for (choices, body) in alts {
                    for c in choices {
                        let hit = match c {
                            HChoice::Others => true,
                            HChoice::Expr(e) => self.expr(e)? == v,
                            HChoice::Range(r) => {
                                let (l, dir, rr) = self.range(r)?;
                                let x = v.as_i64()?;
                                match dir {
                                    Dir::To => l <= x && x <= rr,
                                    Dir::Downto => rr <= x && x <= l,
                                }
                            }
                        };
                        if hit {
                            return self.stmts(body);
                        }
                    }
                }
                Some(Flow::Normal)
            }
            HStmtKind::Loop {
                label,
                scheme,
                body,
            } => self.run_loop(*label, scheme, body),
            HStmtKind::Next(l, c) => {
                if let Some(c) = c
                    && !self.cond(c)?
                {
                    return Some(Flow::Normal);
                }
                Some(Flow::Next(*l))
            }
            HStmtKind::Exit(l, c) => {
                if let Some(c) = c
                    && !self.cond(c)?
                {
                    return Some(Flow::Normal);
                }
                Some(Flow::Exit(*l))
            }
            HStmtKind::Return(e) => Some(Flow::Return(match e {
                Some(e) => Some(self.expr(e)?),
                None => None,
            })),
            HStmtKind::Assert { cond, severity, .. } => {
                let ok = match cond {
                    Some(c) => self.cond(c)?,
                    None => false,
                };
                if ok {
                    return Some(Flow::Normal);
                }
                // A failing assertion of severity error or failure stops
                // elaboration; a note or a warning does not change values.
                let sev = match severity {
                    Some(e) => self.expr(e)?.as_i64()?,
                    None => 2,
                };
                let _ = d;
                (sev < 2).then_some(Flow::Normal)
            }
            _ => None,
        }
    }

    fn cond(&mut self, c: &HExpr) -> Option<bool> {
        match self.expr(c)? {
            Value::Enum(v) => Some(v != 0),
            _ => None,
        }
    }

    fn run_loop(&mut self, label: usize, scheme: &HLoop, body: &[HStmt]) -> Option<Flow> {
        let iter = |this: &mut Self| -> Option<Option<Flow>> {
            match this.stmts(body)? {
                Flow::Normal => Some(None),
                Flow::Next(l) if l == label => Some(None),
                Flow::Exit(l) if l == label => Some(Some(Flow::Normal)),
                f => Some(Some(f)),
            }
        };
        match scheme {
            HLoop::Plain => loop {
                if let Some(f) = iter(self)? {
                    return Some(f);
                }
            },
            HLoop::While(c) => {
                while self.cond(c)? {
                    if let Some(f) = iter(self)? {
                        return Some(f);
                    }
                }
                Some(Flow::Normal)
            }
            HLoop::For(o, r) => {
                let (l, dir, rr) = self.range(r)?;
                let enum_ty = self.d.is_enum(self.d.objects[*o].ty);
                let mut i = l;
                loop {
                    let inside = match dir {
                        Dir::To => i <= rr,
                        Dir::Downto => i >= rr,
                    };
                    if !inside {
                        return Some(Flow::Normal);
                    }
                    let v = if enum_ty {
                        Value::Enum(i as u32)
                    } else {
                        Value::Int(i)
                    };
                    self.frames.last_mut()?.insert(*o, v);
                    if let Some(f) = iter(self)? {
                        return Some(f);
                    }
                    i = match dir {
                        Dir::To => i + 1,
                        Dir::Downto => i - 1,
                    };
                }
            }
        }
    }

    /// Assign `v` to a variable or a part of one.
    fn assign(&mut self, target: &HExpr, v: Value) -> Option<()> {
        match &target.kind {
            HExprKind::Obj(o) => {
                let old = self.var(*o)?.clone();
                let new = match (&old, v) {
                    // An array variable keeps its bounds (§10.6.2.1).
                    (Value::Array(a), Value::Array(b)) => {
                        if a.elems.len() != b.elems.len() {
                            return None;
                        }
                        Value::Array(Box::new(ArrayValue {
                            left: a.left,
                            dir: a.dir,
                            right: a.right,
                            elems: b.elems,
                        }))
                    }
                    (_, v) => v,
                };
                self.frames.last_mut()?.insert(*o, new);
                Some(())
            }
            HExprKind::Index(b, idx) if idx.len() == 1 => {
                let Value::Array(mut a) = self.expr(b)? else {
                    return None;
                };
                let i = self.expr(&idx[0])?.as_i64()?;
                let k = offset(&a, i)?;
                *a.elems.get_mut(k)? = v;
                self.assign(b, Value::Array(a))
            }
            HExprKind::Slice(b, r) => {
                let Value::Array(mut a) = self.expr(b)? else {
                    return None;
                };
                let (l, dir, rr) = self.range(r)?;
                let Value::Array(src) = v else { return None };
                let n = len(l, dir, rr);
                if n != src.elems.len() as i64 {
                    return None;
                }
                for (j, e) in src.elems.into_iter().enumerate() {
                    let idx = match dir {
                        Dir::To => l + j as i64,
                        Dir::Downto => l - j as i64,
                    };
                    let k = offset(&a, idx)?;
                    *a.elems.get_mut(k)? = e;
                }
                self.assign(b, Value::Array(a))
            }
            HExprKind::Field(b, i) => {
                let Value::Record(mut f) = self.expr(b)? else {
                    return None;
                };
                *f.get_mut(*i)? = v;
                self.assign(b, Value::Record(f))
            }
            _ => None,
        }
    }

    /// The bounds of a discrete range.
    fn range(&mut self, r: &HRange) -> Option<(i64, Dir, i64)> {
        if let Some((x, dim, rev)) = &r.of_obj {
            let mut v = self.expr(x)?;
            for _ in 0..*dim {
                let Value::Array(a) = v else { return None };
                v = a.elems.first()?.clone();
            }
            let Value::Array(a) = v else { return None };
            return Some(if *rev {
                (a.right, flip(a.dir), a.left)
            } else {
                (a.left, a.dir, a.right)
            });
        }
        if let Some(sr) = &r.static_val {
            return Some((sr.left.as_i64()?, sr.dir, sr.right.as_i64()?));
        }
        Some((
            self.expr(&r.left)?.as_i64()?,
            r.dir,
            self.expr(&r.right)?.as_i64()?,
        ))
    }

    /// The bounds of a constrained (one-dimensional) array subtype.
    fn bounds(&mut self, t: TypeId) -> Option<(i64, Dir, i64)> {
        let mut cur = t;
        loop {
            match &self.d.types[cur].kind {
                TypeKind::Subtype {
                    constraint: Some(HConstraint::Index(rs, _)),
                    base,
                    ..
                } => match rs.first() {
                    Some(Some(r)) => {
                        let r = r.clone();
                        return self.range(&r);
                    }
                    _ => cur = *base,
                },
                TypeKind::Subtype { base, .. } => cur = *base,
                _ => return None,
            }
        }
    }

    /// `v` with the bounds of subtype `t` when it is a constrained array
    /// (the same length); otherwise unchanged.
    fn rebound(&mut self, t: TypeId, v: Value) -> Option<Value> {
        let Value::Array(a) = v else { return Some(v) };
        match self.bounds(t) {
            Some((l, dir, r)) => {
                if len(l, dir, r) != a.elems.len() as i64 {
                    return None;
                }
                Some(Value::Array(Box::new(ArrayValue {
                    left: l,
                    dir,
                    right: r,
                    elems: a.elems,
                })))
            }
            None => Some(Value::Array(a)),
        }
    }

    /// The default value of a variable of subtype `t` (§6.4.2.3).
    fn default_of(&mut self, t: TypeId) -> Option<Value> {
        let d = self.d;
        let b = d.base(t);
        match &d.types[b].kind {
            TypeKind::Array { elem, .. } => {
                let (l, dir, r) = self.bounds(t)?;
                let e = self.default_of(*elem)?;
                let n = len(l, dir, r).max(0) as usize;
                Some(Value::Array(Box::new(ArrayValue {
                    left: l,
                    dir,
                    right: r,
                    elems: vec![e; n],
                })))
            }
            TypeKind::Record(fields) => Some(Value::Record(
                fields
                    .iter()
                    .map(|(_, ft)| self.default_of(*ft))
                    .collect::<Option<Vec<_>>>()?,
            )),
            _ => {
                // A scalar: T'left of its subtype (a range constraint that
                // is not static is evaluated here).
                let mut cur = t;
                loop {
                    match &d.types[cur].kind {
                        TypeKind::Subtype {
                            constraint: Some(HConstraint::Range(r)),
                            ..
                        } if r.static_val.is_none() => {
                            let r = r.clone();
                            let l = self.expr(&r.left)?;
                            return Some(l);
                        }
                        TypeKind::Subtype { base, .. } => cur = *base,
                        _ => break,
                    }
                }
                Some(d.scalar_range(t)?.left)
            }
        }
    }

    /// An array aggregate of type `t` (§9.3.3.3).
    fn aggregate(&mut self, items: &[(Vec<HChoice>, HExpr)], t: TypeId) -> Option<Value> {
        let d = self.d;
        let positional = items.iter().all(|(c, _)| c.is_empty());
        let target = self.bounds(t);
        if positional {
            let elems = items
                .iter()
                .map(|(_, e)| self.expr(e))
                .collect::<Option<Vec<_>>>()?;
            let n = elems.len() as i64;
            let (l, dir) = match target {
                Some((l, dir, r)) => {
                    if len(l, dir, r) != n {
                        return None;
                    }
                    (l, dir)
                }
                None => {
                    // The index subtype's left bound and direction.
                    let TypeKind::Array { index, .. } = &d.types[d.base(t)].kind else {
                        return None;
                    };
                    let sr = d.scalar_range(*index.first()?)?;
                    (sr.left.as_i64()?, sr.dir)
                }
            };
            let right = match dir {
                Dir::To => l + n - 1,
                Dir::Downto => l - n + 1,
            };
            return Some(Value::Array(Box::new(ArrayValue {
                left: l,
                dir,
                right,
                elems,
            })));
        }
        // Named associations, maybe with `others`: the bounds are the
        // target's, or those of the choices.
        let mut named: Vec<(i64, i64, Value)> = Vec::new();
        let mut others = None;
        for (choices, e) in items {
            let v = self.expr(e)?;
            for c in choices {
                match c {
                    HChoice::Others => others = Some(v.clone()),
                    HChoice::Expr(x) => {
                        let i = self.expr(x)?.as_i64()?;
                        named.push((i, i, v.clone()));
                    }
                    HChoice::Range(r) => {
                        let (l, dir, rr) = self.range(r)?;
                        let (lo, hi) = match dir {
                            Dir::To => (l, rr),
                            Dir::Downto => (rr, l),
                        };
                        if lo <= hi {
                            named.push((lo, hi, v.clone()));
                        }
                    }
                }
            }
        }
        let (l, dir, r) = match target {
            Some(b) => b,
            None => {
                let lo = named.iter().map(|x| x.0).min()?;
                let hi = named.iter().map(|x| x.1).max()?;
                let TypeKind::Array { index, .. } = &d.types[d.base(t)].kind else {
                    return None;
                };
                let dir = d.scalar_range(*index.first()?)?.dir;
                match dir {
                    Dir::To => (lo, dir, hi),
                    Dir::Downto => (hi, dir, lo),
                }
            }
        };
        let n = len(l, dir, r).max(0) as usize;
        let mut elems: Vec<Option<Value>> = vec![others; n];
        let a = ArrayValue {
            left: l,
            dir,
            right: r,
            elems: Vec::new(),
        };
        for (lo, hi, v) in named {
            for i in lo..=hi {
                let k = offset(&a, i)?;
                *elems.get_mut(k)? = Some(v.clone());
            }
        }
        Some(Value::Array(Box::new(ArrayValue {
            left: l,
            dir,
            right: r,
            elems: elems.into_iter().collect::<Option<Vec<_>>>()?,
        })))
    }
}

fn round_half_away(r: f64) -> i64 {
    r.round() as i64
}

fn flip(d: Dir) -> Dir {
    match d {
        Dir::To => Dir::Downto,
        Dir::Downto => Dir::To,
    }
}

fn len(l: i64, dir: Dir, r: i64) -> i64 {
    match dir {
        Dir::To => r - l + 1,
        Dir::Downto => l - r + 1,
    }
}

/// The position of index `i` in an array value.
fn offset(a: &ArrayValue, i: i64) -> Option<usize> {
    let k = match a.dir {
        Dir::To => i - a.left,
        Dir::Downto => a.left - i,
    };
    (k >= 0 && (k as usize) < a.elems.len().max(len(a.left, a.dir, a.right).max(0) as usize))
        .then_some(k as usize)
}

fn slice(a: &ArrayValue, l: i64, dir: Dir, r: i64) -> Option<Value> {
    let n = len(l, dir, r);
    if n <= 0 {
        return Some(Value::Array(Box::new(ArrayValue {
            left: l,
            dir,
            right: r,
            elems: Vec::new(),
        })));
    }
    if dir != a.dir {
        return None;
    }
    let k = offset(a, l)?;
    let elems = a.elems.get(k..k + n as usize)?.to_vec();
    Some(Value::Array(Box::new(ArrayValue {
        left: l,
        dir,
        right: r,
        elems,
    })))
}

fn array_attr(name: &str, l: i64, dir: Dir, r: i64) -> Option<Value> {
    let asc = dir == Dir::To;
    Some(match name {
        "left" => Value::Int(l),
        "right" => Value::Int(r),
        "high" => Value::Int(if asc { r } else { l }),
        "low" => Value::Int(if asc { l } else { r }),
        "length" => Value::Int(len(l, dir, r).max(0)),
        "ascending" => Value::Enum(asc as u32),
        _ => return None,
    })
}

impl Design {
    /// The value of an expression with the objects of `frame` bound to
    /// values (a specialised subprogram's formals and constants).
    pub fn eval_with(&self, h: &HExpr, frame: HashMap<ObjId, Value>) -> Option<Value> {
        let mut it = Interp::new(self);
        it.frames.push(frame);
        it.expr(h)
    }

    /// The value of a static expression, analysing first the bodies of the
    /// functions it calls (they may be declared in package bodies not yet
    /// analysed, or be library functions analysed on first use).
    pub fn eval_static(&mut self, h: &HExpr) -> Option<Value> {
        let mut calls = Vec::new();
        super::calls_in_expr(h, &mut calls);
        if !calls.is_empty() {
            self.ensure_bodies(calls);
        }
        self.eval(h)
    }

    /// Analyse the bodies of functions `work` and of the functions they
    /// call.
    fn ensure_bodies(&mut self, mut work: Vec<SubId>) {
        let mut seen = std::collections::HashSet::new();
        while let Some(f) = work.pop() {
            if !seen.insert(f) {
                continue;
            }
            let s = &self.subprograms[f];
            if s.builtin.is_some() {
                continue;
            }
            if s.body.is_none() && !self.lazy_bodies.contains_key(&f) {
                // Declared in a package whose body is not analysed yet.
                let mut parts = s.path.splitn(3, '.');
                if let (Some(lib), Some(pkg)) = (parts.next(), parts.next()) {
                    let key = (lib.to_string(), pkg.to_string());
                    // Only once the package declaration is complete.
                    let done = matches!(
                        self.state.get(&(key.0.clone(), key.1.clone(), 0u8)),
                        Some(super::State::Done)
                    );
                    if done && self.packages.contains_key(&key) {
                        self.analyze_package_body(&key.0, &key.1);
                    }
                }
            }
            if let Some(lb) = self.lazy_bodies.remove(&f) {
                let saved = (
                    std::mem::replace(&mut self.cur_lib, lb.lib.clone()),
                    self.cur_file,
                );
                self.cur_file = lb.file;
                self.analyze_body(f, lb.region, &lb.body, &lb.path);
                self.cur_lib = saved.0;
                self.cur_file = saved.1;
            }
            if let Some(b) = &self.subprograms[f].body {
                let mut more = Vec::new();
                super::calls_in_stmts(&b.stmts, &mut more);
                for l in &b.locals {
                    if let Some(e) = &self.objects[*l].init {
                        super::calls_in_expr(e, &mut more);
                    }
                }
                work.extend(more);
            }
        }
    }
}
