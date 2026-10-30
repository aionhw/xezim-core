//! Specialisation of subprograms by the static bounds of their array
//! actuals. A function on unconstrained arrays (`"+"(L, R : UNSIGNED)`)
//! takes and returns structs of dynamic arrays, which the simulator
//! interprets. Where a call passes packed values (`Repr::Pk`, static
//! bounds), a copy of the subprogram is lowered for those bounds: its
//! formals are packed, its local arrays whose bounds follow the formals
//! (`RESULT : UNSIGNED(L'LENGTH - 1 downto 0)`) are packed too, loops over
//! `L'RANGE` have constant bounds, and when every `return` yields one static
//! shape the result is packed as well. Copies are also made for integer
//! actuals that bounds depend on (`RESIZE(ARG, 8)`), when they are static.
//!
//! Folding uses the static evaluator (`ceval`) on a copy of each bound
//! expression in which the array attributes of objects with known bounds
//! are replaced by their values, so no array value is ever made up.

use std::collections::{BTreeSet, HashMap};

use super::packed::{Bounds, bounds_len};
use super::{Lw, Repr, sv_ident};
use crate::vhdl::ast::{Dir, Mode, ObjClass};
use crate::vhdl::sema::hir::*;

/// Nesting of specialisations made while computing the shape of one.
const MAX_DEPTH: usize = 8;
/// Specialisations of one subprogram (per instance).
const MAX_COPIES: usize = 64;

/// The bindings a specialisation is lowered with.
#[derive(Clone, Debug, Default)]
pub(super) struct SpecEnv {
    /// Static bounds of array formals (from the actuals) and of local
    /// arrays whose bounds fold.
    pub bounds: HashMap<ObjId, Bounds>,
    /// Integer formals bound to static actuals.
    pub ints: HashMap<ObjId, Value>,
    /// Local constants whose values fold.
    pub consts: HashMap<ObjId, Value>,
}

/// A specialised copy of a subprogram.
#[derive(Clone, Debug)]
pub(super) struct PSpec {
    pub sub: SubId,
    pub inst: usize,
    pub env: SpecEnv,
    pub name: String,
    /// The representation of each formal.
    pub params: Vec<Repr>,
    /// A function's result representation and, when packed, its bounds.
    pub ret: Option<Repr>,
    pub ret_bounds: Option<Bounds>,
}

/// The objects an expression names.
fn objs_in(h: &HExpr, out: &mut BTreeSet<ObjId>) {
    match &h.kind {
        HExprKind::Obj(o) => {
            out.insert(*o);
        }
        HExprKind::Lit(_) | HExprKind::NewOf(_) => {}
        HExprKind::Call(_, args) | HExprKind::RecordAgg(args) => {
            for a in args {
                objs_in(a, out);
            }
        }
        HExprKind::Cond(arms, last) => {
            for (c, v) in arms {
                objs_in(c, out);
                objs_in(v, out);
            }
            objs_in(last, out);
        }
        HExprKind::Index(b, idx) => {
            objs_in(b, out);
            for i in idx {
                objs_in(i, out);
            }
        }
        HExprKind::Slice(b, r) => {
            objs_in(b, out);
            range_objs(r, out);
        }
        HExprKind::Field(b, _)
        | HExprKind::Convert(b)
        | HExprKind::Qualified(b)
        | HExprKind::Deref(b) => objs_in(b, out),
        HExprKind::New(v) => {
            if let Some(v) = v {
                objs_in(v, out);
            }
        }
        HExprKind::ArrayAgg(items) => {
            for (cs, v) in items {
                for c in cs {
                    match c {
                        HChoice::Expr(e) => objs_in(e, out),
                        HChoice::Range(r) => range_objs(r, out),
                        HChoice::Others => {}
                    }
                }
                objs_in(v, out);
            }
        }
        HExprKind::Attr(_, p, prm) => {
            if let AttrPrefix::Expr(x) = p.as_ref() {
                objs_in(x, out);
            }
            if let Some(x) = prm {
                objs_in(x, out);
            }
        }
    }
}

fn range_objs(r: &HRange, out: &mut BTreeSet<ObjId>) {
    objs_in(&r.left, out);
    objs_in(&r.right, out);
    if let Some((o, _, _)) = &r.of_obj {
        objs_in(o, out);
    }
}

/// The expressions of the non-static bounds of array subtype `t`.
fn bound_exprs(lw: &Lw, t: TypeId, out: &mut Vec<HExpr>) {
    if let Some(cons) = lw.d.array_constraint(t) {
        for r in cons.into_iter().flatten() {
            if r.static_val.is_none() {
                out.push((*r.left).clone());
                out.push((*r.right).clone());
                if let Some((o, _, _)) = &r.of_obj {
                    out.push((**o).clone());
                }
            }
        }
    }
}

impl<'a> Lw<'a> {
    /// The active specialisation's environment.
    pub(super) fn env(&self) -> Option<&SpecEnv> {
        self.spec_env.map(|i| &self.pspecs[i].env)
    }

    /// The static bounds a specialisation gives object `o`.
    pub(super) fn env_bounds(&self, o: ObjId) -> Option<Bounds> {
        self.env()?.bounds.get(&o).copied()
    }

    /// The representation of an object with specialised bounds: packed
    /// when its element packs and the vector fits.
    pub(super) fn env_repr(&mut self, o: ObjId, loc: &Loc) -> Option<Repr> {
        let b = self.env_bounds(o)?;
        let ty = self.d.objects[o].ty;
        let n = bounds_len(b);
        if let Some(e) = self.d.element_subtype(ty)
            && let Some(w) = self.pack_elem(e)
            && n >= 1
            && n * w as i64 <= super::MAX_PK_BITS
        {
            return Some(Repr::Pk(w, n));
        }
        Some(self.fat_repr(ty, loc))
    }

    /// The integer formals of `s` that the bounds of its locals depend on
    /// (through local constants).
    fn shaping_ints(&mut self, s: SubId) -> BTreeSet<ObjId> {
        if let Some(set) = self.shaping.get(&s) {
            return set.clone();
        }
        let info = self.d.subprograms[s].clone();
        let mut set = BTreeSet::new();
        if let Some(body) = &info.body {
            let mut work = Vec::new();
            for l in &body.locals {
                bound_exprs(self, self.d.objects[*l].ty, &mut work);
            }
            if let Some(rt) = info.ret {
                bound_exprs(self, rt, &mut work);
            }
            let mut seen = BTreeSet::new();
            while let Some(e) = work.pop() {
                let mut objs = BTreeSet::new();
                objs_in(&e, &mut objs);
                for o in objs {
                    if !seen.insert(o) {
                        continue;
                    }
                    let oi = &self.d.objects[o];
                    match oi.kind {
                        ObjKind::Param(_, _) if info.params.contains(&o) && self.d.is_integer(oi.ty) => {
                            set.insert(o);
                        }
                        ObjKind::Constant | ObjKind::Variable if body.locals.contains(&o) => {
                            if let Some(i) = &oi.init {
                                work.push(i.clone());
                            }
                            bound_exprs(self, oi.ty, &mut work);
                        }
                        _ => {}
                    }
                }
            }
        }
        self.shaping.insert(s, set.clone());
        set
    }

    /// A copy of `s` for the shapes of `args` (`None`: nothing to
    /// specialise on, or not possible).
    pub(super) fn try_specialise(&mut self, s: SubId, args: &[HExpr]) -> Option<usize> {
        let info = self.d.subprograms[s].clone();
        if info.body.is_none() || info.builtin.is_some() || self.spec_depth >= MAX_DEPTH {
            return None;
        }
        if !info.is_function && self.needs_spec(s) {
            return None;
        }
        let shaping = self.shaping_ints(s);
        let mut env = SpecEnv::default();
        let mut useful = false;
        for (p, a) in info.params.iter().zip(args) {
            let pt = self.d.objects[*p].ty;
            let loc = a.loc.clone();
            if self.ndims(pt) == 1 && self.static_bounds(pt).is_none() {
                if let Repr::Pk(..) = self.erepr(a)
                    && let Some(b) = self.shape(a)
                {
                    env.bounds.insert(*p, b);
                    useful = true;
                }
                let _ = loc;
            } else if shaping.contains(p)
                && let Some(v @ Value::Int(_)) = self.eval_env(a)
            {
                env.ints.insert(*p, v);
                useful = true;
            }
        }
        if !useful {
            return None;
        }
        let inst = if self.in_package(s) { 0 } else { self.inst };
        let mut bk: Vec<_> = env
            .bounds
            .iter()
            .map(|(o, b)| (*o, b.0, b.1 == Dir::Downto, b.2))
            .collect();
        bk.sort();
        let mut ik: Vec<_> = env.ints.iter().map(|(o, v)| (*o, v.as_i64())).collect();
        ik.sort();
        let key = format!("{}|{}|{:?}|{:?}", s, inst, bk, ik);
        if let Some(&k) = self.pspec_keys.get(&key) {
            return Some(k);
        }
        if self.pspecs.iter().filter(|p| p.sub == s && p.inst == inst).count() >= MAX_COPIES {
            return None;
        }
        let k = self.pspecs.len();
        let clean: String = info
            .name
            .chars()
            .filter(|c| c.is_ascii_alphanumeric() || *c == '_')
            .collect();
        let name = format!("vh_f{}_{}_s{}", s, sv_ident(&clean), k);
        self.pspecs.push(PSpec {
            sub: s,
            inst,
            env,
            name,
            params: Vec::new(),
            ret: None,
            ret_bounds: None,
        });
        self.pspec_keys.insert(key, k);
        // Fold the locals' bounds and the result's shape in the copy's
        // environment.
        let saved_env = self.spec_env.replace(k);
        let saved_inst = std::mem::replace(&mut self.inst, inst);
        self.spec_depth += 1;
        let body = info.body.clone().unwrap();
        for l in &body.locals {
            let o = self.d.objects[*l].clone();
            if o.kind == ObjKind::Constant
                && let Some(i) = &o.init
                && let Some(v) = self.eval_env(i)
            {
                self.pspecs[k].env.consts.insert(*l, v);
            }
            if self.ndims(o.ty) == 1
                && self.static_bounds(o.ty).is_none()
                && let Some(cons) = self.d.array_constraint(o.ty)
                && let Some(Some(r)) = cons.first()
                && let Some(b) = self.range_bounds(&r.clone())
            {
                self.pspecs[k].env.bounds.insert(*l, b);
            }
        }
        let loc = info.loc.clone().unwrap_or(Loc { file: 0, span: 0..0 });
        let mut params = Vec::new();
        for p in &info.params {
            params.push(self.obj_repr(*p, &loc));
        }
        let (ret, ret_bounds) = match info.ret {
            None => (None, None),
            Some(rt) => {
                let r = self.repr(rt, &loc);
                if matches!(r, Repr::Arr(..)) && self.ndims(rt) == 1 {
                    match self.ret_shape(&body.stmts) {
                        Some(b) => {
                            let e = self.d.element_subtype(rt);
                            match e.and_then(|e| self.pack_elem(e)) {
                                Some(w) if bounds_len(b) >= 1
                                    && bounds_len(b) * w as i64 <= super::MAX_PK_BITS =>
                                {
                                    (Some(Repr::Pk(w, bounds_len(b))), Some(b))
                                }
                                _ => (Some(r), None),
                            }
                        }
                        None => (Some(r), None),
                    }
                } else {
                    (Some(r), self.static_bounds(rt))
                }
            }
        };
        self.spec_depth -= 1;
        self.inst = saved_inst;
        self.spec_env = saved_env;
        let sp = &mut self.pspecs[k];
        sp.params = params;
        sp.ret = ret;
        sp.ret_bounds = ret_bounds;
        self.pspec_todo.push(k);
        Some(k)
    }

    /// The one static shape every reachable `return` of `stmts` yields.
    fn ret_shape(&mut self, stmts: &[HStmt]) -> Option<Bounds> {
        let mut shapes: Vec<Option<Bounds>> = Vec::new();
        self.collect_returns(stmts, &mut shapes);
        let first = *shapes.first()?;
        let b = first?;
        shapes.iter().all(|s| *s == Some(b)).then_some(b)
    }

    fn collect_returns(&mut self, stmts: &[HStmt], out: &mut Vec<Option<Bounds>>) {
        for s in stmts {
            match &s.kind {
                HStmtKind::Return(Some(x)) => {
                    let b = self.shape(x);
                    out.push(b);
                }
                HStmtKind::If(branches, else_b) => {
                    let mut taken = false;
                    for (c, body) in branches {
                        match self.static_cond(c) {
                            Some(false) => continue,
                            Some(true) => {
                                self.collect_returns(body, out);
                                taken = true;
                                break;
                            }
                            None => self.collect_returns(body, out),
                        }
                    }
                    if !taken && let Some(e) = else_b {
                        self.collect_returns(e, out);
                    }
                }
                HStmtKind::Case { alts, .. } => {
                    for (_, body) in alts {
                        self.collect_returns(body, out);
                    }
                }
                HStmtKind::Loop { body, .. } => self.collect_returns(body, out),
                _ => {}
            }
        }
    }

    /// The value of a BOOLEAN condition when it folds.
    pub(super) fn static_cond(&mut self, c: &HExpr) -> Option<bool> {
        match self.eval_env(c)? {
            Value::Enum(v) if self.d.base(c.ty) == self.d.std.boolean => Some(v != 0),
            _ => None,
        }
    }

    /// The value of a static expression, with the active specialisation's
    /// bindings and the array attributes of objects with known bounds
    /// folded in.
    pub(super) fn eval_env(&mut self, h: &HExpr) -> Option<Value> {
        let h2 = self.subst_attrs(h);
        let mut frame: HashMap<ObjId, Value> = HashMap::new();
        if let Some(env) = self.env() {
            for (o, v) in &env.ints {
                frame.insert(*o, v.clone());
            }
            for (o, v) in &env.consts {
                frame.insert(*o, v.clone());
            }
        }
        self.d.eval_with(&h2, frame)
    }

    /// `h` with the array attributes of expressions with static bounds
    /// replaced by their values (`x'LENGTH` → 4).
    fn subst_attrs(&mut self, h: &HExpr) -> HExpr {
        let kind = match &h.kind {
            HExprKind::Attr(name, p, prm)
                if prm.is_none()
                    && matches!(
                        name.as_str(),
                        "left" | "right" | "high" | "low" | "length" | "ascending"
                    ) =>
            {
                if let AttrPrefix::Expr(x) = p.as_ref()
                    && self.ndims(x.ty) >= 1
                    && let Some((l, dir, r)) = self.shape(x)
                {
                    let asc = dir == Dir::To;
                    let v = match name.as_str() {
                        "left" => Value::Int(l),
                        "right" => Value::Int(r),
                        "high" => Value::Int(if asc { r } else { l }),
                        "low" => Value::Int(if asc { l } else { r }),
                        "length" => Value::Int(bounds_len((l, dir, r))),
                        _ => Value::Enum(asc as u32),
                    };
                    HExprKind::Lit(v)
                } else {
                    h.kind.clone()
                }
            }
            HExprKind::Call(s, args) => {
                HExprKind::Call(*s, args.iter().map(|a| self.subst_attrs(a)).collect())
            }
            HExprKind::Index(b, idx) => HExprKind::Index(
                Box::new(self.subst_attrs(b)),
                idx.iter().map(|a| self.subst_attrs(a)).collect(),
            ),
            HExprKind::Convert(b) => HExprKind::Convert(Box::new(self.subst_attrs(b))),
            HExprKind::Qualified(b) => HExprKind::Qualified(Box::new(self.subst_attrs(b))),
            HExprKind::Field(b, i) => HExprKind::Field(Box::new(self.subst_attrs(b)), *i),
            HExprKind::Cond(arms, last) => HExprKind::Cond(
                arms.iter()
                    .map(|(c, v)| (self.subst_attrs(c), self.subst_attrs(v)))
                    .collect(),
                Box::new(self.subst_attrs(last)),
            ),
            _ => h.kind.clone(),
        };
        HExpr {
            kind,
            ty: h.ty,
            loc: h.loc.clone(),
        }
    }

    /// The SV arguments of a call of specialisation `k`.
    pub(super) fn pspec_args(&mut self, k: usize, args: &[HExpr]) -> Vec<String> {
        let sp = self.pspecs[k].clone();
        let info = self.d.subprograms[sp.sub].clone();
        let mut a = Vec::new();
        for ((p, x), pr) in info.params.iter().zip(args).zip(&sp.params) {
            let declared = self.repr(self.d.objects[*p].ty, &x.loc);
            if *pr != declared {
                a.push(self.ex_as(x, pr));
            } else {
                a.extend(self.arg_values(*p, x));
            }
        }
        a
    }

    /// A call of a procedure's specialisation: `out`/`inout` actuals of
    /// another representation go through temporaries.
    pub(super) fn pspec_proc_call(&mut self, k: usize, args: &[HExpr], ind: usize, loc: &Loc) -> String {
        let pad = " ".repeat(ind);
        let sp = self.pspecs[k].clone();
        let info = self.d.subprograms[sp.sub].clone();
        let mut a = Vec::new();
        let (mut before, mut after) = (String::new(), String::new());
        for ((p, x), pr) in info.params.iter().zip(args).zip(&sp.params) {
            let writes = matches!(
                self.d.objects[*p].kind,
                ObjKind::Param(ObjClass::Variable, Mode::Out | Mode::InOut)
            );
            let ar = self.erepr(x);
            if writes && (matches!(x.kind, HExprKind::Slice(..)) || *pr != ar) {
                self.tmp += 1;
                let t = format!("vh_sa{}", self.tmp);
                self.temps.push((t.clone(), pr.sv()));
                let v = self.ex_as(x, pr);
                let _ = std::fmt::Write::write_fmt(&mut before, format_args!("{}{} = {};\n", pad, t, v));
                let bsv = self.shape(x).map(|b| self.bounds_sv(b));
                let back = self.coerce(t.clone(), pr, &ar, bsv, loc);
                after.push_str(&self.assign_to(x, back, ind));
                a.push(t);
            } else {
                let declared = self.repr(self.d.objects[*p].ty, &x.loc);
                if *pr != declared {
                    a.push(self.ex_as(x, pr));
                } else {
                    a.extend(self.arg_values(*p, x));
                }
            }
        }
        format!("{}{}{}({});\n{}", before, pad, sp.name, a.join(", "), after)
    }
}
