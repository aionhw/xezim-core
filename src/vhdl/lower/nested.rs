//! Up-level references of nested subprograms. A subprogram declared in
//! another subprogram sees that one's parameters, variables and constants
//! (§12.1: a declaration is visible in the declarative regions nested in
//! its own). Each subprogram is lowered to an SV function of its own, whose
//! formals and locals no other function can name, so a nested subprogram
//! takes the objects it reads or writes from the enclosing ones as extra
//! formals of the same names (`captures`), and every call passes them: the
//! enclosing subprogram its own objects, another nested subprogram the
//! formals it took itself. A subprogram that calls one with captures takes
//! them too, unless it declares them.

use std::collections::{BTreeMap, BTreeSet};

use super::Lw;
use crate::vhdl::ast::{Mode, ObjClass};
use crate::vhdl::sema::hir::*;

/// The objects and the called subprograms of a subprogram body.
#[derive(Default)]
struct Uses {
    objs: BTreeSet<ObjId>,
    subs: BTreeSet<SubId>,
}

impl Uses {
    fn expr(&mut self, h: &HExpr) {
        match &h.kind {
            HExprKind::Obj(o) => {
                self.objs.insert(*o);
            }
            HExprKind::Lit(_) | HExprKind::NewOf(_) => {}
            HExprKind::Call(s, args) => {
                self.subs.insert(*s);
                for a in args {
                    self.expr(a);
                }
            }
            HExprKind::RecordAgg(args) => {
                for a in args {
                    self.expr(a);
                }
            }
            HExprKind::Cond(arms, last) => {
                for (c, v) in arms {
                    self.expr(c);
                    self.expr(v);
                }
                self.expr(last);
            }
            HExprKind::Index(b, idx) => {
                self.expr(b);
                for i in idx {
                    self.expr(i);
                }
            }
            HExprKind::Slice(b, r) => {
                self.expr(b);
                self.range(r);
            }
            HExprKind::Field(b, _)
            | HExprKind::Convert(b)
            | HExprKind::Qualified(b)
            | HExprKind::Deref(b) => self.expr(b),
            HExprKind::New(v) => {
                if let Some(v) = v {
                    self.expr(v);
                }
            }
            HExprKind::ArrayAgg(items) => {
                for (cs, v) in items {
                    self.choices(cs);
                    self.expr(v);
                }
            }
            HExprKind::Attr(_, p, prm) => {
                if let AttrPrefix::Expr(x) = p.as_ref() {
                    self.expr(x);
                }
                if let Some(x) = prm {
                    self.expr(x);
                }
            }
        }
    }

    fn range(&mut self, r: &HRange) {
        self.expr(&r.left);
        self.expr(&r.right);
        if let Some((o, _, _)) = &r.of_obj {
            self.expr(o);
        }
    }

    fn choices(&mut self, cs: &[HChoice]) {
        for c in cs {
            match c {
                HChoice::Expr(e) => self.expr(e),
                HChoice::Range(r) => self.range(r),
                HChoice::Others => {}
            }
        }
    }

    fn opt(&mut self, h: &Option<HExpr>) {
        if let Some(h) = h {
            self.expr(h);
        }
    }

    fn stmts(&mut self, stmts: &[HStmt]) {
        for s in stmts {
            match &s.kind {
                HStmtKind::Wait { on, until, timeout } => {
                    for x in on {
                        self.expr(x);
                    }
                    self.opt(until);
                    self.opt(timeout);
                }
                HStmtKind::Assert {
                    cond,
                    report,
                    severity,
                } => {
                    self.opt(cond);
                    self.opt(report);
                    self.opt(severity);
                }
                HStmtKind::SignalAssign {
                    target,
                    delay,
                    waves,
                } => {
                    self.expr(target);
                    if let Some(HDelay::Inertial(Some(x))) = delay {
                        self.expr(x);
                    }
                    for w in waves {
                        self.opt(&w.value);
                        self.opt(&w.after);
                    }
                }
                HStmtKind::VarAssign { target, value } => {
                    self.expr(target);
                    self.expr(value);
                }
                HStmtKind::Force { target, value } => {
                    self.expr(target);
                    self.opt(value);
                }
                HStmtKind::Call(c, args) => {
                    self.subs.insert(*c);
                    for a in args {
                        self.expr(a);
                    }
                }
                HStmtKind::If(arms, last) => {
                    for (c, b) in arms {
                        self.expr(c);
                        self.stmts(b);
                    }
                    if let Some(b) = last {
                        self.stmts(b);
                    }
                }
                HStmtKind::Case { expr, alts } => {
                    self.expr(expr);
                    for (cs, b) in alts {
                        self.choices(cs);
                        self.stmts(b);
                    }
                }
                HStmtKind::Loop { scheme, body, .. } => {
                    match scheme {
                        HLoop::Plain => {}
                        HLoop::While(c) => self.expr(c),
                        HLoop::For(_, r) => self.range(r),
                    }
                    self.stmts(body);
                }
                HStmtKind::Next(_, c) | HStmtKind::Exit(_, c) | HStmtKind::Return(c) => {
                    self.opt(c)
                }
                HStmtKind::Null | HStmtKind::InitObj(_) => {}
            }
        }
    }
}

impl<'a> Lw<'a> {
    /// The objects of enclosing subprograms each subprogram takes as extra
    /// formals, by subprogram; only those that take any.
    fn capture_table(&self) -> BTreeMap<SubId, Vec<ObjId>> {
        let d = self.d;
        // The subprogram that declares each parameter and local.
        let mut owner: BTreeMap<ObjId, SubId> = BTreeMap::new();
        for (s, info) in d.subprograms.iter().enumerate() {
            let Some(body) = &info.body else { continue };
            for o in info.params.iter().chain(&body.locals) {
                owner.insert(*o, s);
            }
        }
        let mut direct: BTreeMap<SubId, BTreeSet<ObjId>> = BTreeMap::new();
        let mut calls: BTreeMap<SubId, BTreeSet<SubId>> = BTreeMap::new();
        for (s, info) in d.subprograms.iter().enumerate() {
            let Some(body) = &info.body else { continue };
            let mut u = Uses::default();
            u.stmts(&body.stmts);
            // The initial values and the bounds of its locals too.
            for l in &body.locals {
                let o = &d.objects[*l];
                u.opt(&o.init);
                let mut bounds = Vec::new();
                super::spec::bound_exprs(self, o.ty, &mut bounds);
                for b in &bounds {
                    u.expr(b);
                }
            }
            let up: BTreeSet<ObjId> = u
                .objs
                .into_iter()
                .filter(|o| owner.get(o).is_some_and(|w| *w != s))
                .collect();
            if !up.is_empty() {
                direct.insert(s, up);
            }
            calls.insert(s, u.subs);
        }
        if direct.is_empty() {
            return BTreeMap::new();
        }
        // A caller takes what its callees take and it does not declare.
        loop {
            let mut changed = false;
            for (s, cs) in &calls {
                let mut add = BTreeSet::new();
                for c in cs {
                    if let Some(up) = direct.get(c) {
                        add.extend(up.iter().copied().filter(|o| owner.get(o) != Some(s)));
                    }
                }
                if add.is_empty() {
                    continue;
                }
                let e = direct.entry(*s).or_default();
                let n = e.len();
                e.extend(add);
                changed |= e.len() != n;
            }
            if !changed {
                break;
            }
        }
        direct
            .into_iter()
            .filter(|(_, v)| !v.is_empty())
            .map(|(s, v)| (s, v.into_iter().collect()))
            .collect()
    }

    /// The objects of enclosing subprograms that `s` takes as extra formals.
    pub(super) fn captures(&mut self, s: SubId) -> Vec<ObjId> {
        if self.captures.is_none() {
            let t = self.capture_table();
            // Neither a subprogram with extra formals nor the one that
            // declares them is specialised: a copy would change the
            // representation of an object both name.
            let mut fixed: BTreeSet<SubId> = t.keys().copied().collect();
            for (s, info) in self.d.subprograms.iter().enumerate() {
                let Some(body) = &info.body else { continue };
                if t.values()
                    .flatten()
                    .any(|o| info.params.contains(o) || body.locals.contains(o))
                {
                    fixed.insert(s);
                }
            }
            self.capture_fixed = fixed;
            self.captures = Some(t);
        }
        self.captures
            .as_ref()
            .and_then(|t| t.get(&s))
            .cloned()
            .unwrap_or_default()
    }

    /// Whether `s` takes objects of enclosing subprograms or declares
    /// objects that a nested one takes.
    pub(super) fn capture_fixed(&mut self, s: SubId) -> bool {
        self.captures(s);
        self.capture_fixed.contains(&s)
    }

    /// The extra SV formals of `s`: `input` for what cannot be written
    /// through it (a constant, a parameter of mode `in`), `inout` otherwise.
    pub(super) fn capture_decls(&mut self, s: SubId, loc: &Loc) -> Vec<String> {
        let mut out = Vec::new();
        for o in self.captures(s) {
            let info = self.d.objects[o].clone();
            let r = self.obj_repr(o, &info.loc);
            let name = self.obj_name(o);
            let dir = match info.kind {
                ObjKind::Param(ObjClass::Signal, _) => {
                    self.err(
                        loc,
                        format!(
                            "a nested subprogram that names signal parameter '{}' of its enclosing subprogram is not supported yet",
                            info.name
                        ),
                    );
                    "input"
                }
                ObjKind::Constant | ObjKind::Generic | ObjKind::Param(_, Mode::In) => "input",
                _ => "inout",
            };
            let ty = match info.kind {
                ObjKind::File | ObjKind::Param(ObjClass::File, _) => "int".to_string(),
                _ => r.sv(),
            };
            out.push(format!("{} {} {}", dir, ty, name));
        }
        out
    }

    /// The extra SV actuals of a call of `s`.
    pub(super) fn capture_args(&mut self, s: SubId) -> Vec<String> {
        self.captures(s)
            .into_iter()
            .map(|o| self.obj_name(o))
            .collect()
    }
}
