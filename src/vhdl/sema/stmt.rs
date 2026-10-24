//! Statements (IEEE 1076-2008 §10, §11): sequential statements, and
//! concurrent statements rewritten as their equivalent processes (§11.3,
//! §11.5–§11.7).

use super::decl::name_text;
use super::hir::*;
use super::{Design, RegionId, Sym};
use crate::vhdl::ast;

/// A formal, its actual (`None`: open or unassociated) and whether it is
/// associated explicitly.
pub type Assoc = (ObjId, Option<HExpr>, bool);

/// The source of a nested scope (block or generate iteration).
struct Nested<'a> {
    label: String,
    /// The statement label, iteration value and alternative label, for
    /// block configurations (§3.4.2).
    cfg_label: &'a str,
    index: Option<Value>,
    alt: Option<&'a str>,
    /// A for-generate parameter: name, type and value.
    param: Option<(&'a ast::Ident, TypeId, Value)>,
    generics: &'a [ast::InterfaceDecl],
    generic_map: &'a [ast::Assoc],
    ports: &'a [ast::InterfaceDecl],
    port_map: &'a [ast::Assoc],
    decls: &'a [ast::Decl],
    stmts: &'a [ast::ConcStmt],
    /// The guard expression of a guarded block (§11.2).
    guard: Option<&'a ast::Expr>,
}

#[derive(Clone)]
pub struct StmtCtx {
    /// In a process (wait and signal assignment allowed).
    pub in_process: bool,
    /// In a process with a sensitivity list: no wait statements (§11.3).
    pub sensitized: bool,
    /// The result type of the enclosing function.
    pub ret: Option<TypeId>,
}

impl Design {
    pub fn seq_stmts(&mut self, r: RegionId, stmts: &[ast::SeqStmt], ctx: &StmtCtx) -> Vec<HStmt> {
        let mut out = Vec::new();
        for s in stmts {
            if let Some(h) = self.seq_stmt(r, s, ctx) {
                out.push(h);
            }
        }
        out
    }

    fn severity(&mut self, r: RegionId, e: &Option<ast::Expr>) -> Option<HExpr> {
        let sl = self.std.severity_level;
        e.as_ref().and_then(|e| self.expr(r, e, Some(sl)))
    }

    fn seq_stmt(&mut self, r: RegionId, s: &ast::SeqStmt, ctx: &StmtCtx) -> Option<HStmt> {
        let loc = self.loc(s.span.clone());
        let boolean = self.std.boolean;
        let string = self.std.string;
        let kind = match &s.kind {
            ast::SeqKind::Wait { on, until, timeout } => {
                if ctx.sensitized {
                    self.error(
                        s.span.clone(),
                        "wait statement not allowed in a sensitized process",
                    );
                    return None;
                }
                if !ctx.in_process && ctx.ret.is_some() {
                    self.error(s.span.clone(), "wait statement not allowed in a function");
                    return None;
                }
                let mut sens = Vec::new();
                for n in on {
                    sens.push(self.name_expr(r, n, None)?);
                }
                let until = match until {
                    Some(c) => Some(self.condition(r, c)?),
                    None => None,
                };
                // §10.2: `wait until c` without `on` waits on c's signals.
                if on.is_empty()
                    && let Some(c) = &until
                {
                    self.signals_read(c, &mut sens);
                }
                let time = self.std.time;
                let timeout = match timeout {
                    Some(t) => Some(self.expr(r, t, Some(time))?),
                    None => None,
                };
                HStmtKind::Wait {
                    on: sens,
                    until,
                    timeout,
                }
            }
            ast::SeqKind::Assert {
                cond,
                report,
                severity,
            } => HStmtKind::Assert {
                cond: Some(self.condition(r, cond)?),
                report: match report {
                    Some(m) => Some(self.expr(r, m, Some(string))?),
                    None => None,
                },
                severity: self.severity(r, severity),
            },
            ast::SeqKind::Report { msg, severity } => HStmtKind::Assert {
                cond: None,
                report: Some(self.expr(r, msg, Some(string))?),
                severity: self.severity(r, severity),
            },
            ast::SeqKind::SignalAssign { target, delay, rhs } => {
                let ast::Target::Name(tn) = target else {
                    self.error(target.span(), "aggregate targets are not supported yet");
                    return None;
                };
                let t = self.name_expr(r, tn, None)?;
                if !self.is_signal_expr(&t) {
                    self.error(
                        tn.span.clone(),
                        format!("'{}' is not a signal", name_text(tn)),
                    );
                    return None;
                }
                let delay = self.delay(r, delay);
                return self.assign_rhs(r, rhs, s.span.clone(), |d, w| {
                    let waves = d.waveform(r, w, t.ty)?;
                    // §10.5.2.2: a null transaction needs a guarded target.
                    if waves.iter().any(|w| w.value.is_none())
                        && !d.sig_root(&t).is_some_and(|o| d.sig_kinds.contains_key(&o))
                    {
                        d.error(
                            tn.span.clone(),
                            "the target of a null waveform element must be a guarded signal",
                        );
                        return None;
                    }
                    Some(HStmtKind::SignalAssign {
                        target: t.clone(),
                        delay: delay.clone(),
                        waves,
                    })
                });
            }
            ast::SeqKind::VarAssign { target, rhs } => {
                let ast::Target::Name(tn) = target else {
                    self.error(target.span(), "aggregate targets are not supported yet");
                    return None;
                };
                let t = self.name_expr(r, tn, None)?;
                return self.assign_rhs(r, rhs, s.span.clone(), |d, e| {
                    let v = d.expr(r, e, Some(t.ty))?;
                    Some(HStmtKind::VarAssign {
                        target: t.clone(),
                        value: v,
                    })
                });
            }
            ast::SeqKind::Force { target, .. } | ast::SeqKind::Release { target, .. } => {
                self.error(target.span(), "force and release are not supported yet");
                return None;
            }
            ast::SeqKind::ProcCall(n) => {
                let (id, actuals) = self.procedure_call(r, n)?;
                HStmtKind::Call(id, actuals)
            }
            ast::SeqKind::If {
                branches,
                else_branch,
            } => {
                let mut bs = Vec::new();
                for (c, body) in branches {
                    let c = self.condition(r, c)?;
                    bs.push((c, self.seq_stmts(r, body, ctx)));
                }
                let eb = else_branch.as_ref().map(|b| self.seq_stmts(r, b, ctx));
                HStmtKind::If(bs, eb)
            }
            ast::SeqKind::Case {
                matching,
                expr,
                alts,
            } => {
                if *matching {
                    self.error(s.span.clone(), "case? is not supported yet");
                    return None;
                }
                let x = self.expr(r, expr, None)?;
                let mut hs = Vec::new();
                for (choices, body) in alts {
                    let mut cs = Vec::new();
                    for c in choices {
                        cs.push(match c {
                            ast::Choice::Others(_) => HChoice::Others,
                            ast::Choice::Expr(e) => HChoice::Expr(self.expr(r, e, Some(x.ty))?),
                            ast::Choice::Range(dr) => {
                                HChoice::Range(self.discrete_range(r, dr, Some(x.ty))?.1)
                            }
                        });
                    }
                    hs.push((cs, self.seq_stmts(r, body, ctx)));
                }
                HStmtKind::Case { expr: x, alts: hs }
            }
            ast::SeqKind::Loop { scheme, body } => {
                let lr = self.new_region(Some(r));
                let label = self.labels.len();
                self.labels
                    .push(s.label.as_ref().map(|l| l.name.clone()).unwrap_or_default());
                // Unlabelled loops are the target of a bare exit/next.
                self.declare(lr, "<loop>", Sym::Label(label));
                if let Some(l) = &s.label {
                    self.declare(lr, &l.name, Sym::Label(label));
                }
                let scheme = match scheme {
                    ast::LoopScheme::Plain => HLoop::Plain,
                    ast::LoopScheme::While(c) => HLoop::While(self.condition(lr, c)?),
                    ast::LoopScheme::For(p, dr) => {
                        let (t, hr) = self.discrete_range(lr, dr, None)?;
                        let o = self.add_obj(ObjInfo {
                            name: p.name.clone(),
                            kind: ObjKind::LoopParam,
                            ty: t,
                            init: None,
                            loc: self.loc(p.span.clone()),
                            static_val: None,
                        });
                        self.declare(lr, &p.name, Sym::Obj(o));
                        HLoop::For(o, hr)
                    }
                };
                let body = self.seq_stmts(lr, body, ctx);
                HStmtKind::Loop {
                    label,
                    scheme,
                    body,
                }
            }
            ast::SeqKind::Next { label, cond } | ast::SeqKind::Exit { label, cond } => {
                let key = label
                    .as_ref()
                    .map(|l| l.name.clone())
                    .unwrap_or_else(|| "<loop>".into());
                let Some(Sym::Label(id)) = self.lookup(r, &key).into_iter().next() else {
                    self.error(
                        s.span.clone(),
                        "exit/next outside a loop (or unknown loop label)",
                    );
                    return None;
                };
                let c = match cond {
                    Some(c) => Some(self.condition(r, c)?),
                    None => None,
                };
                if matches!(s.kind, ast::SeqKind::Next { .. }) {
                    HStmtKind::Next(id, c)
                } else {
                    HStmtKind::Exit(id, c)
                }
            }
            ast::SeqKind::Return(v) => match (v, ctx.ret) {
                (Some(e), Some(t)) => HStmtKind::Return(Some(self.expr(r, e, Some(t))?)),
                (None, None) => HStmtKind::Return(None),
                _ => {
                    self.error(s.span.clone(), "return value does not match the subprogram");
                    return None;
                }
            },
            ast::SeqKind::Null => HStmtKind::Null,
            ast::SeqKind::Unsupported(what) => {
                self.error(s.span.clone(), format!("{} is not supported yet", what));
                return None;
            }
        };
        let _ = boolean;
        Some(HStmt { kind, loc })
    }

    /// A condition: BOOLEAN, or (VHDL-2008 §9.2.9) any type with `??`.
    pub fn condition(&mut self, r: RegionId, c: &ast::Expr) -> Option<HExpr> {
        let boolean = self.std.boolean;
        let set = self.possible_types(r, c);
        if self.compatible(&set, boolean) || set.any {
            return self.expr(r, c, Some(boolean));
        }
        // Implicit `??` (§9.2.9).
        let e = ast::Expr {
            kind: ast::ExprKind::Unary(ast::UnOp::Cond, Box::new(c.clone())),
            span: c.span.clone(),
        };
        self.expr(r, &e, Some(boolean))
    }

    fn delay(&mut self, r: RegionId, d: &Option<ast::DelayMech>) -> Option<HDelay> {
        let time = self.std.time;
        Some(match d.as_ref()? {
            ast::DelayMech::Transport => HDelay::Transport,
            ast::DelayMech::Inertial(rej) => {
                HDelay::Inertial(rej.as_ref().and_then(|e| self.expr(r, e, Some(time))))
            }
        })
    }

    fn waveform(&mut self, r: RegionId, w: &ast::Waveform, ty: TypeId) -> Option<Vec<HWave>> {
        let time = self.std.time;
        match w {
            ast::Waveform::Unaffected(_) => Some(Vec::new()),
            ast::Waveform::Elems(elems) => {
                let mut out = Vec::new();
                for e in elems {
                    let value = match &e.value {
                        Some(v) => Some(self.expr(r, v, Some(ty))?),
                        None => None,
                    };
                    let after = match &e.after {
                        Some(a) => Some(self.expr(r, a, Some(time))?),
                        None => None,
                    };
                    out.push(HWave { value, after });
                }
                Some(out)
            }
        }
    }

    /// Simple, conditional (§10.5.3) or selected (§10.5.4) assignment:
    /// conditional and selected forms become if/case statements.
    fn assign_rhs<T>(
        &mut self,
        r: RegionId,
        rhs: &ast::AssignRhs<T>,
        span: ast::Span,
        mut one: impl FnMut(&mut Self, &T) -> Option<HStmtKind>,
    ) -> Option<HStmt> {
        let loc = self.loc(span.clone());
        let kind = match rhs {
            ast::AssignRhs::Simple(v) => one(self, v)?,
            ast::AssignRhs::Cond(arms) => {
                let mut branches = Vec::new();
                let mut else_b = None;
                for (v, c) in arms {
                    let st = HStmt {
                        kind: one(self, v)?,
                        loc: loc.clone(),
                    };
                    match c {
                        Some(c) => branches.push((self.condition(r, c)?, vec![st])),
                        None => else_b = Some(vec![st]),
                    }
                }
                HStmtKind::If(branches, else_b)
            }
            ast::AssignRhs::Select {
                expr,
                matching,
                items,
            } => {
                if *matching {
                    self.error(span, "select? is not supported yet");
                    return None;
                }
                let x = self.expr(r, expr, None)?;
                let mut alts = Vec::new();
                for (v, choices) in items {
                    let mut cs = Vec::new();
                    for c in choices {
                        cs.push(match c {
                            ast::Choice::Others(_) => HChoice::Others,
                            ast::Choice::Expr(e) => HChoice::Expr(self.expr(r, e, Some(x.ty))?),
                            ast::Choice::Range(dr) => {
                                HChoice::Range(self.discrete_range(r, dr, Some(x.ty))?.1)
                            }
                        });
                    }
                    alts.push((
                        cs,
                        vec![HStmt {
                            kind: one(self, v)?,
                            loc: loc.clone(),
                        }],
                    ));
                }
                HStmtKind::Case { expr: x, alts }
            }
        };
        Some(HStmt { kind, loc })
    }

    /// The signals an expression reads (for the sensitivity of concurrent
    /// statements, §11.3, and of `wait until`): the longest static prefixes.
    pub fn signals_read(&self, h: &HExpr, out: &mut Vec<HExpr>) {
        if self.is_signal_expr(h) && self.static_name(h) {
            if !out.iter().any(|o| same_name(o, h)) {
                out.push(h.clone());
            }
            return;
        }
        match &h.kind {
            HExprKind::Call(_, a) => {
                for x in a {
                    self.signals_read(x, out);
                }
            }
            HExprKind::Index(b, i) => {
                self.signals_read(b, out);
                for x in i {
                    self.signals_read(x, out);
                }
            }
            HExprKind::Slice(b, r) => {
                self.signals_read(b, out);
                self.signals_read(&r.left, out);
                self.signals_read(&r.right, out);
            }
            HExprKind::Field(b, _)
            | HExprKind::Convert(b)
            | HExprKind::Qualified(b)
            | HExprKind::Deref(b) => self.signals_read(b, out),
            HExprKind::ArrayAgg(items) => {
                for (_, v) in items {
                    self.signals_read(v, out);
                }
            }
            HExprKind::RecordAgg(v) => {
                for x in v {
                    self.signals_read(x, out);
                }
            }
            HExprKind::Attr(name, p, _)
                if matches!(
                    name.as_str(),
                    "stable" | "quiet" | "delayed" | "transaction"
                ) && matches!(p.as_ref(), AttrPrefix::Expr(_)) =>
            {
                // An implicit signal (§16.2.4) is read itself.
                out.push(h.clone());
            }
            HExprKind::Attr(name, p, param) => {
                // `s'event` etc. read the prefix signal.
                if let AttrPrefix::Expr(x) = p.as_ref()
                    && !matches!(
                        name.as_str(),
                        "left"
                            | "right"
                            | "high"
                            | "low"
                            | "length"
                            | "ascending"
                            | "range"
                            | "simple_name"
                            | "path_name"
                            | "instance_name"
                    )
                {
                    self.signals_read(x, out);
                }
                if let Some(x) = param {
                    self.signals_read(x, out);
                }
            }
            _ => {}
        }
    }

    /// Whether a name is static (indices are static expressions).
    pub fn static_name(&self, h: &HExpr) -> bool {
        match &h.kind {
            HExprKind::Obj(_) => true,
            HExprKind::Index(b, i) => {
                self.static_name(b) && i.iter().all(|x| self.eval(x).is_some())
            }
            HExprKind::Slice(b, r) => self.static_name(b) && r.static_val.is_some(),
            HExprKind::Field(b, _) => self.static_name(b),
            _ => false,
        }
    }

    // ---- concurrent statements -----------------------------------------------------------

    pub fn conc_stmt(&mut self, r: RegionId, s: &ast::ConcStmt, arch: &mut Architecture) {
        let loc = self.loc(s.span.clone());
        let label = s.label.as_ref().map(|l| l.name.clone()).unwrap_or_default();
        let pctx = StmtCtx {
            in_process: true,
            sensitized: false,
            ret: None,
        };
        match &s.kind {
            ast::ConcKind::Process {
                postponed,
                sens,
                decls,
                stmts,
            } => {
                let pr = self.new_region(Some(r));
                let mut locals = Vec::new();
                let mut subs = Vec::new();
                let path = format!("{}.{}.{}", arch.library, arch.entity, label);
                self.decls(pr, decls, &mut locals, &mut subs, &path);
                let ctx = StmtCtx {
                    sensitized: sens.is_some(),
                    ..pctx.clone()
                };
                let body = self.seq_stmts(pr, stmts, &ctx);
                let sens = match sens {
                    None => None,
                    Some(ast::Sensitivity::List(names)) => {
                        let mut v = Vec::new();
                        for n in names {
                            if let Some(h) = self.name_expr(pr, n, None) {
                                v.push(h);
                            }
                        }
                        Some(v)
                    }
                    Some(ast::Sensitivity::All) => {
                        // §11.3: every signal the process reads.
                        let mut v = Vec::new();
                        self.stmts_signals_read(&body, &mut v);
                        Some(v)
                    }
                };
                arch.processes.push(Process {
                    label,
                    postponed: *postponed,
                    sens,
                    locals,
                    stmts: body,
                    loc,
                });
            }
            ast::ConcKind::SignalAssign {
                postponed,
                guarded,
                target,
                delay,
                rhs,
            } => {
                // §11.6: the equivalent process.
                let st = ast::SeqStmt {
                    label: None,
                    kind: ast::SeqKind::SignalAssign {
                        target: target.clone(),
                        delay: delay.clone(),
                        rhs: rhs.clone(),
                    },
                    span: s.span.clone(),
                };
                let Some(mut h) = self.seq_stmt(r, &st, &pctx) else {
                    return;
                };
                if *guarded {
                    match self.guarded_assign(r, target, delay, h, &loc) {
                        Some(g) => h = g,
                        None => return,
                    }
                }
                let mut sens = Vec::new();
                self.stmts_signals_read(std::slice::from_ref(&h), &mut sens);
                arch.processes.push(Process {
                    label,
                    postponed: *postponed,
                    sens: Some(sens),
                    locals: Vec::new(),
                    stmts: vec![h],
                    loc,
                });
            }
            ast::ConcKind::Assert {
                postponed,
                cond,
                report,
                severity,
            } => {
                let st = ast::SeqStmt {
                    label: None,
                    kind: ast::SeqKind::Assert {
                        cond: cond.clone(),
                        report: report.clone(),
                        severity: severity.clone(),
                    },
                    span: s.span.clone(),
                };
                let Some(h) = self.seq_stmt(r, &st, &pctx) else {
                    return;
                };
                let mut sens = Vec::new();
                self.stmts_signals_read(std::slice::from_ref(&h), &mut sens);
                arch.processes.push(Process {
                    label,
                    postponed: *postponed,
                    sens: Some(sens),
                    locals: Vec::new(),
                    stmts: vec![h],
                    loc,
                });
            }
            ast::ConcKind::ProcCall { postponed, call } => {
                // A component instantiation without maps looks the same.
                let prefix = match &call.kind {
                    ast::NameKind::Call(p, _) => p.as_ref(),
                    _ => call,
                };
                if let ast::NameKind::Simple(i) = &prefix.kind
                    && matches!(self.lookup(r, &i.name).first(), Some(Sym::Component(_)))
                {
                    self.instance(
                        r,
                        &s.label,
                        &ast::InstUnit::Component(prefix.clone()),
                        &[],
                        &[],
                        arch,
                        loc,
                    );
                    return;
                }
                let Some((id, actuals)) = self.procedure_call(r, call) else {
                    return;
                };
                let h = HStmt {
                    kind: HStmtKind::Call(id, actuals.clone()),
                    loc: loc.clone(),
                };
                // §11.4: sensitive to the signals of `in`/`inout` actuals.
                let mut sens = Vec::new();
                for a in &actuals {
                    self.signals_read(a, &mut sens);
                }
                arch.processes.push(Process {
                    label,
                    postponed: *postponed,
                    sens: Some(sens),
                    locals: Vec::new(),
                    stmts: vec![h],
                    loc,
                });
            }
            ast::ConcKind::Instance {
                unit,
                generic_map,
                port_map,
            } => self.instance(r, &s.label, unit, generic_map, port_map, arch, loc),
            ast::ConcKind::Block {
                guard,
                generics,
                generic_map,
                ports,
                port_map,
                decls,
                stmts,
            } => {
                self.nested_scope(
                    r,
                    arch,
                    loc,
                    Nested {
                        label: label.clone(),
                        cfg_label: &label,
                        index: None,
                        alt: None,
                        param: None,
                        generics,
                        generic_map,
                        ports,
                        port_map,
                        decls,
                        stmts,
                        guard: guard.as_ref(),
                    },
                );
            }
            ast::ConcKind::ForGenerate {
                param,
                range,
                decls,
                stmts,
            } => {
                // §14.5.3: one block per value of the (static) range.
                let Some((t, hr)) = self.discrete_range(r, range, None) else {
                    return;
                };
                let vals = hr.static_val.as_ref().and_then(|sr| {
                    let (l, rr) = (sr.left.as_i64()?, sr.right.as_i64()?);
                    Some(match sr.dir {
                        ast::Dir::To => (l..=rr).collect::<Vec<_>>(),
                        ast::Dir::Downto => (rr..=l).rev().collect(),
                    })
                });
                let Some(vals) = vals else {
                    self.error(s.span.clone(), "the range of a for-generate must be static");
                    return;
                };
                let is_enum = matches!(self.types[self.base(t)].kind, TypeKind::Enum(_));
                for v in vals {
                    let val = if is_enum {
                        Value::Enum(v as u32)
                    } else {
                        Value::Int(v)
                    };
                    self.nested_scope(
                        r,
                        arch,
                        loc.clone(),
                        Nested {
                            label: format!("{}({})", label, v),
                            cfg_label: &label,
                            index: Some(val.clone()),
                            alt: None,
                            param: Some((param, t, val)),
                            generics: &[],
                            generic_map: &[],
                            ports: &[],
                            port_map: &[],
                            decls,
                            stmts,
                            guard: None,
                        },
                    );
                }
            }
            ast::ConcKind::IfGenerate(branches) => {
                // §14.5.3: the first branch whose condition is true.
                for b in branches {
                    let take = match &b.cond {
                        None => true,
                        Some(c) => {
                            let Some(h) = self.condition(r, c) else {
                                return;
                            };
                            match self.eval(&h) {
                                Some(v) => v == Value::Enum(1),
                                None => {
                                    self.error(
                                        c.span.clone(),
                                        "a generate condition must be static",
                                    );
                                    return;
                                }
                            }
                        }
                    };
                    if take {
                        self.generate_branch(r, arch, loc, &label, b);
                        return;
                    }
                }
            }
            ast::ConcKind::CaseGenerate { expr, branches } => {
                let Some(x) = self.expr(r, expr, None) else {
                    return;
                };
                let Some(v) = self.eval(&x) else {
                    self.error(
                        expr.span.clone(),
                        "a case-generate expression must be static",
                    );
                    return;
                };
                for b in branches {
                    let mut hit = false;
                    for c in &b.choices {
                        hit |= match c {
                            ast::Choice::Others(_) => true,
                            ast::Choice::Expr(e) => {
                                let Some(h) = self.expr(r, e, Some(x.ty)) else {
                                    return;
                                };
                                self.eval(&h).as_ref() == Some(&v)
                            }
                            ast::Choice::Range(dr) => {
                                let Some((_, hr)) = self.discrete_range(r, dr, Some(x.ty)) else {
                                    return;
                                };
                                match (hr.static_val, v.as_i64()) {
                                    (Some(sr), Some(i)) => {
                                        let (a, z) = (
                                            sr.left.as_i64().unwrap_or(0),
                                            sr.right.as_i64().unwrap_or(0),
                                        );
                                        match sr.dir {
                                            ast::Dir::To => a <= i && i <= z,
                                            ast::Dir::Downto => z <= i && i <= a,
                                        }
                                    }
                                    _ => false,
                                }
                            }
                        };
                    }
                    if hit {
                        self.generate_branch(r, arch, loc, &label, b);
                        return;
                    }
                }
            }
            ast::ConcKind::Unsupported(what) => {
                self.error(s.span.clone(), format!("{} is not supported yet", what))
            }
        }
    }

    /// The chosen branch of an if- or case-generate.
    fn generate_branch(
        &mut self,
        r: RegionId,
        arch: &mut Architecture,
        loc: Loc,
        label: &str,
        b: &ast::GenerateBranch,
    ) {
        let alt = b.alt_label.as_ref().map(|a| a.name.as_str());
        self.nested_scope(
            r,
            arch,
            loc,
            Nested {
                label: match alt {
                    Some(a) => format!("{}({})", label, a),
                    None => label.to_string(),
                },
                cfg_label: label,
                index: None,
                alt,
                param: None,
                generics: &[],
                generic_map: &[],
                ports: &[],
                port_map: &[],
                decls: &b.decls,
                stmts: &b.stmts,
                guard: None,
            },
        );
    }

    /// A block statement or generate iteration: a nested architecture
    /// of its own, instantiated in place of the statement (§14.5.2,
    /// §14.5.3). It sees the enclosing scope's objects.
    /// A guarded assignment (§11.6): `if GUARD then <assignment>`, and for
    /// a guarded target `else <target> <= null after <disconnection time>`.
    fn guarded_assign(
        &mut self,
        r: RegionId,
        target: &ast::Target,
        delay: &Option<ast::DelayMech>,
        h: HStmt,
        loc: &Loc,
    ) -> Option<HStmt> {
        let guard = match self.lookup(r, "guard").first() {
            Some(Sym::Obj(o)) if self.objects[*o].kind == ObjKind::Signal => *o,
            _ => {
                self.error(
                    loc.span.clone(),
                    "a guarded assignment needs a GUARD signal (a guarded block)",
                );
                return None;
            }
        };
        let cond = HExpr {
            kind: HExprKind::Obj(guard),
            ty: self.objects[guard].ty,
            loc: loc.clone(),
        };
        let ast::Target::Name(tn) = target else {
            self.error(target.span(), "aggregate targets are not supported yet");
            return None;
        };
        let t = self.name_expr(r, tn, None)?;
        let disconnect = match self.sig_root(&t) {
            Some(o) if self.sig_kinds.contains_key(&o) => {
                let after = match self.disconnect.get(&o) {
                    Some(d) => d.clone(),
                    None => super::decl::lit_expr(Value::Phys(0), self.std.time, loc.clone()),
                };
                Some(vec![HStmt {
                    kind: HStmtKind::SignalAssign {
                        target: t,
                        delay: self.delay(r, delay),
                        waves: vec![HWave {
                            value: None,
                            after: Some(after),
                        }],
                    },
                    loc: loc.clone(),
                }])
            }
            _ => None,
        };
        Some(HStmt {
            kind: HStmtKind::If(vec![(cond, vec![h])], disconnect),
            loc: loc.clone(),
        })
    }

    /// The signal object a signal name is part of.
    pub fn sig_root(&self, h: &HExpr) -> Option<ObjId> {
        match &h.kind {
            HExprKind::Obj(o) => Some(*o),
            HExprKind::Index(b, _) | HExprKind::Slice(b, _) | HExprKind::Field(b, _) => {
                self.sig_root(b)
            }
            _ => None,
        }
    }

    fn nested_scope(&mut self, r: RegionId, parent: &mut Architecture, loc: Loc, b: Nested<'_>) {
        let nr = self.new_region(Some(r));
        let path = format!("{}.{}.{}", parent.library, parent.entity, b.label);
        let mut constants = Vec::new();
        if let Some((p, t, v)) = b.param {
            let ploc = self.loc(p.span.clone());
            let o = self.add_obj(ObjInfo {
                name: p.name.clone(),
                kind: ObjKind::Constant,
                ty: t,
                init: Some(super::decl::lit_expr(v.clone(), t, ploc.clone())),
                loc: ploc,
                static_val: Some(v),
            });
            self.declare(nr, &p.name, Sym::Obj(o));
            constants.push(o);
        }
        let generics = self.interface_list(nr, b.generics, super::decl::IfaceKind::Generic, &path);
        let generic_map = self.map_formals(r, &generics, b.generic_map, true, &loc);
        // The generic values, for the block's declarations (§14.5.2).
        for (g, a) in &generic_map {
            if let Some(v) = a.as_ref().and_then(|a| self.eval(a)) {
                let o = &mut self.objects[*g];
                o.init = Some(super::decl::lit_expr(v.clone(), o.ty, o.loc.clone()));
                o.static_val = Some(v);
            }
        }
        let ports = self.interface_list(nr, b.ports, super::decl::IfaceKind::Port, &path);
        let (port_map, port_conv) = self.map_ports(r, &ports, b.port_map, parent, &loc);
        let mut objs = Vec::new();
        // A guarded block declares the implicit signal GUARD (§11.2).
        if let Some(g) = b.guard
            && let Some(c) = self.condition(nr, g)
        {
            let gloc = self.loc(g.span.clone());
            let o = self.add_obj(ObjInfo {
                name: "guard".into(),
                kind: ObjKind::Signal,
                ty: self.std.boolean,
                init: None,
                loc: gloc,
                static_val: None,
            });
            self.declare(nr, "guard", Sym::Obj(o));
            self.guards.insert(o, c);
            objs.push(o);
        }
        let mut subs = Vec::new();
        self.decls(nr, b.decls, &mut objs, &mut subs, &path);
        let (signals, consts): (Vec<ObjId>, Vec<ObjId>) = objs
            .into_iter()
            .partition(|&o| self.objects[o].kind == ObjKind::Signal);
        constants.extend(consts);
        let mut arch = Architecture {
            entity: parent.entity.clone(),
            name: b.label.clone(),
            library: parent.library.clone(),
            generics,
            ports,
            signals,
            constants,
            processes: Vec::new(),
            instances: Vec::new(),
            nested: true,
            loc: loc.clone(),
        };
        let sub = self
            .cur_cfg
            .and_then(|c| self.sub_block_cfg(c, b.cfg_label, b.index.as_ref(), b.alt));
        let saved = std::mem::replace(&mut self.cur_cfg, sub);
        for s in b.stmts {
            self.conc_stmt(nr, s, &mut arch);
        }
        self.cur_cfg = saved;
        self.archs.push(arch);
        parent.instances.push(Instance {
            label: b.label,
            library: parent.library.clone(),
            entity: parent.entity.clone(),
            arch: None,
            arch_index: Some(self.archs.len() - 1),
            generic_map: generic_map
                .into_iter()
                .filter_map(|(f, a)| a.map(|a| (f, a)))
                .collect(),
            port_map: port_map.into_iter().map(|(f, a, _)| (f, a)).collect(),
            port_conv,
            config: None,
            loc,
        });
    }

    #[allow(clippy::too_many_arguments)]
    fn instance(
        &mut self,
        r: RegionId,
        label: &Option<ast::Ident>,
        unit: &ast::InstUnit,
        generic_map: &[ast::Assoc],
        port_map: &[ast::Assoc],
        arch: &mut Architecture,
        loc: Loc,
    ) {
        let label_s = label.as_ref().map(|l| l.name.clone()).unwrap_or_default();
        let (lib, ent, archn, config) = match unit {
            ast::InstUnit::Entity(n, a) => {
                let Some((lib, en)) = self.entity_name(r, n) else {
                    return;
                };
                (lib, en, a.as_ref().map(|a| a.name.clone()), None)
            }
            ast::InstUnit::Component(n) => {
                self.component_instance(r, &label_s, n, generic_map, port_map, arch, loc);
                return;
            }
            ast::InstUnit::Configuration(n) => match self.config_unit(r, n) {
                Some(c) => c,
                None => return,
            },
        };
        let Some(info) = self.analyze_entity(&lib, &ent) else {
            self.error(
                loc.span.clone(),
                format!("no entity '{}' in library '{}'", ent, lib),
            );
            return;
        };
        let generic_map = self.map_formals(r, &info.generics, generic_map, true, &loc);
        let (port_map, port_conv) = self.map_ports(r, &info.ports, port_map, arch, &loc);
        let generic_map: Vec<(ObjId, HExpr)> = generic_map
            .into_iter()
            .filter_map(|(f, a)| a.map(|a| (f, a)))
            .collect();
        arch.instances.push(Instance {
            label: label_s,
            library: lib,
            entity: ent,
            arch: archn,
            arch_index: None,
            generic_map,
            port_map: port_map.into_iter().map(|(f, a, _)| (f, a)).collect(),
            port_conv,
            config,
            loc,
        });
    }

    /// Associate actuals with ports (§6.5.7.1): the plain associations
    /// (formal, actual, explicitly associated) and those with a conversion
    /// or a partial formal. A non-static actual expression of an `in` port
    /// is assigned to an implicit signal by an implicit process in `arch`
    /// (§6.5.6.3), which the port is associated with.
    pub fn map_ports(
        &mut self,
        r: RegionId,
        formals: &[ObjId],
        assocs: &[ast::Assoc],
        arch: &mut Architecture,
        loc: &Loc,
    ) -> (Vec<Assoc>, Vec<PortConv>) {
        let mut out: Vec<(ObjId, Option<HExpr>, bool)> =
            formals.iter().map(|f| (*f, None, false)).collect();
        let mut convs = Vec::new();
        // The formals are visible in formal parts.
        let fr = self.new_region(Some(r));
        for f in formals {
            let n = self.objects[*f].name.clone();
            self.declare(fr, &n, Sym::Obj(*f));
        }
        for (i, a) in assocs.iter().enumerate() {
            let (idx, fpart) = match &a.formal {
                None => (i, None),
                Some(f) => match &f.kind {
                    ast::NameKind::Simple(n) => {
                        match formals.iter().position(|o| self.objects[*o].name == n.name) {
                            Some(p) => (p, None),
                            None => {
                                self.error(f.span.clone(), format!("no port named '{}'", n.name));
                                continue;
                            }
                        }
                    }
                    _ => {
                        let fe = ast::Expr {
                            kind: ast::ExprKind::Name(f.clone()),
                            span: f.span.clone(),
                        };
                        let Some(fh) = self.expr(fr, &fe, None) else {
                            continue;
                        };
                        let Some(fo) = formal_root(&fh).filter(|o| formals.contains(o)) else {
                            self.error(f.span.clone(), "a formal part names a port");
                            continue;
                        };
                        let p = formals.iter().position(|o| *o == fo).unwrap();
                        (p, Some(fh))
                    }
                },
            };
            let Some(&f) = formals.get(idx) else {
                self.error(a.span.clone(), "too many associations");
                continue;
            };
            out[idx].2 = true;
            let ast::Actual::Expr(e) = &a.actual else {
                if fpart.is_some() {
                    self.error(
                        a.span.clone(),
                        "a partial or converted formal needs an actual",
                    );
                }
                continue;
            };
            let mode = match self.objects[f].kind {
                ObjKind::Port(m) => m,
                _ => ast::Mode::In,
            };
            let ft = fpart.as_ref().map(|h| h.ty).unwrap_or(self.objects[f].ty);
            let Some(ah) = self.expr(r, e, Some(ft)) else {
                continue;
            };
            let formal_conv = fpart
                .as_ref()
                .is_some_and(|h| matches!(h.kind, HExprKind::Call(..) | HExprKind::Convert(_)));
            match mode {
                ast::Mode::In => {
                    if formal_conv {
                        self.error(
                            a.span.clone(),
                            "a port of mode in cannot have a formal conversion",
                        );
                        continue;
                    }
                    let ah = if self.is_signal_expr(&ah) && self.static_name(&ah) {
                        ah
                    } else if self.conversion_of_signal(&ah) || self.eval(&ah).is_some() {
                        if fpart.is_none() && self.eval(&ah).is_some() {
                            // A static value: the port's own signal with it.
                            out[idx].1 = Some(ah);
                            continue;
                        }
                        convs.push(PortConv {
                            formal: f,
                            mode,
                            target: fpart.unwrap_or_else(|| obj_expr(self, f)),
                            value: ah,
                        });
                        continue;
                    } else {
                        match self.implicit_signal(arch, ah, ft, loc) {
                            Some(h) => h,
                            None => continue,
                        }
                    };
                    match fpart {
                        None => out[idx].1 = Some(ah),
                        Some(fh) => convs.push(PortConv {
                            formal: f,
                            mode,
                            target: fh,
                            value: ah,
                        }),
                    }
                }
                ast::Mode::Out | ast::Mode::Buffer => {
                    if !(self.is_signal_expr(&ah) && self.static_name(&ah)) {
                        self.error(
                            e.span.clone(),
                            "the actual of an out port must be a static signal name here",
                        );
                        continue;
                    }
                    match fpart {
                        None => out[idx].1 = Some(ah),
                        Some(fh) => convs.push(PortConv {
                            formal: f,
                            mode,
                            target: ah,
                            value: fh,
                        }),
                    }
                }
                _ => match fpart {
                    None if self.is_signal_expr(&ah) && self.static_name(&ah) => {
                        out[idx].1 = Some(ah)
                    }
                    None if self.eval(&ah).is_some() => out[idx].1 = Some(ah),
                    _ => self.error(
                        a.span.clone(),
                        "conversions and partial association of inout ports are not supported yet",
                    ),
                },
            }
        }
        (out, convs)
    }

    /// `f(s)` with `f` a function of one parameter, or `T(s)`, of a static
    /// signal name `s`: a conversion of the actual (§6.5.7.1).
    fn conversion_of_signal(&self, h: &HExpr) -> bool {
        match &h.kind {
            HExprKind::Call(f, args) => {
                // A function name, not an operator (§6.5.7.1).
                let sub = &self.subprograms[*f];
                args.len() == 1
                    && sub.params.len() == 1
                    && !sub.name.starts_with('"')
                    && !matches!(sub.builtin, Some(Builtin::Op(_)))
                    && self.is_signal_expr(&args[0])
                    && self.static_name(&args[0])
            }
            HExprKind::Convert(x) => self.is_signal_expr(x) && self.static_name(x),
            _ => false,
        }
    }

    /// The implicit signal of a non-static actual expression, assigned by
    /// an implicit process (§6.5.6.3).
    fn implicit_signal(
        &mut self,
        arch: &mut Architecture,
        value: HExpr,
        formal_ty: TypeId,
        loc: &Loc,
    ) -> Option<HExpr> {
        let ty = if self.constrained(formal_ty) {
            formal_ty
        } else if self.constrained(value.ty) {
            value.ty
        } else {
            self.errors.push((
                value.loc.clone(),
                "this actual needs a constrained port subtype here".into(),
            ));
            return None;
        };
        let o = self.add_obj(ObjInfo {
            name: format!("implicit_{}", self.objects.len()),
            kind: ObjKind::Signal,
            ty,
            init: None,
            loc: value.loc.clone(),
            static_val: None,
        });
        arch.signals.push(o);
        let target = HExpr {
            kind: HExprKind::Obj(o),
            ty,
            loc: value.loc.clone(),
        };
        let mut sens = Vec::new();
        self.signals_read(&value, &mut sens);
        arch.processes.push(Process {
            label: String::new(),
            postponed: false,
            sens: Some(sens),
            locals: Vec::new(),
            stmts: vec![HStmt {
                kind: HStmtKind::SignalAssign {
                    target: target.clone(),
                    delay: None,
                    waves: vec![HWave {
                        value: Some(value),
                        after: None,
                    }],
                },
                loc: loc.clone(),
            }],
            loc: loc.clone(),
        });
        Some(target)
    }

    /// Whether a subtype has every index range (a scalar always has).
    pub fn constrained(&self, t: TypeId) -> bool {
        match &self.types[t].kind {
            TypeKind::Array { .. } => false,
            TypeKind::Subtype {
                constraint: Some(HConstraint::Index(v, _)),
                ..
            } => v.iter().all(|x| x.is_some()),
            TypeKind::Subtype { base, .. } => self.constrained(*base),
            _ => true,
        }
    }

    /// Associate actuals with an entity's generics or ports (positional
    /// then named, §6.5.7.1); `None` for `open` / defaulted.
    fn map_formals(
        &mut self,
        r: RegionId,
        formals: &[ObjId],
        assocs: &[ast::Assoc],
        generics: bool,
        _loc: &Loc,
    ) -> Vec<(ObjId, Option<HExpr>)> {
        self.map_formals_ex(r, formals, assocs, generics)
            .into_iter()
            .map(|(f, a, _)| (f, a))
            .collect()
    }

    /// `map_formals`, also telling which formals are associated
    /// explicitly (an `open` actual included).
    pub fn map_formals_ex(
        &mut self,
        r: RegionId,
        formals: &[ObjId],
        assocs: &[ast::Assoc],
        generics: bool,
    ) -> Vec<(ObjId, Option<HExpr>, bool)> {
        let mut out: Vec<(ObjId, Option<HExpr>, bool)> =
            formals.iter().map(|f| (*f, None, false)).collect();
        for (i, a) in assocs.iter().enumerate() {
            let idx = match &a.formal {
                None => i,
                Some(f) => {
                    match &f.kind {
                        ast::NameKind::Simple(n) => {
                            match formals.iter().position(|o| self.objects[*o].name == n.name) {
                                Some(p) => p,
                                None => {
                                    self.error(
                                        f.span.clone(),
                                        format!(
                                            "no {} named '{}'",
                                            if generics { "generic" } else { "port" },
                                            n.name
                                        ),
                                    );
                                    continue;
                                }
                            }
                        }
                        _ => {
                            self.error(f.span.clone(), "partial association and conversion functions are not supported yet");
                            continue;
                        }
                    }
                }
            };
            let Some(&f) = formals.get(idx) else {
                self.error(a.span.clone(), "too many associations");
                continue;
            };
            out[idx].2 = true;
            let ast::Actual::Expr(e) = &a.actual else {
                continue;
            };
            let ft = self.objects[f].ty;
            if let Some(h) = self.expr(r, e, Some(ft)) {
                out[idx].1 = Some(h);
            }
        }
        out
    }

    pub fn stmts_signals_read(&self, stmts: &[HStmt], out: &mut Vec<HExpr>) {
        for s in stmts {
            match &s.kind {
                HStmtKind::Assert {
                    cond,
                    report,
                    severity,
                } => {
                    for x in [cond, report, severity].into_iter().flatten() {
                        self.signals_read(x, out);
                    }
                }
                HStmtKind::SignalAssign { target, waves, .. } => {
                    // Indices of the target are read.
                    if let HExprKind::Index(_, idx) = &target.kind {
                        for x in idx {
                            self.signals_read(x, out);
                        }
                    }
                    for w in waves {
                        for x in [&w.value, &w.after].into_iter().flatten() {
                            self.signals_read(x, out);
                        }
                    }
                }
                HStmtKind::VarAssign { value, .. } => self.signals_read(value, out),
                HStmtKind::Call(_, a) => {
                    for x in a {
                        self.signals_read(x, out);
                    }
                }
                HStmtKind::If(bs, e) => {
                    for (c, b) in bs {
                        self.signals_read(c, out);
                        self.stmts_signals_read(b, out);
                    }
                    if let Some(e) = e {
                        self.stmts_signals_read(e, out);
                    }
                }
                HStmtKind::Case { expr, alts } => {
                    self.signals_read(expr, out);
                    for (_, b) in alts {
                        self.stmts_signals_read(b, out);
                    }
                }
                HStmtKind::Loop { scheme, body, .. } => {
                    if let HLoop::While(c) = scheme {
                        self.signals_read(c, out);
                    }
                    self.stmts_signals_read(body, out);
                }
                HStmtKind::Next(_, c) | HStmtKind::Exit(_, c) => {
                    if let Some(c) = c {
                        self.signals_read(c, out);
                    }
                }
                HStmtKind::Return(Some(x)) => self.signals_read(x, out),
                _ => {}
            }
        }
    }
}

/// The object a formal part names: the formal of a partial association
/// (`f(i)`, `f(a to b)`, `f.e`) or the argument of a conversion.
fn formal_root(h: &HExpr) -> Option<ObjId> {
    match &h.kind {
        HExprKind::Obj(o) => Some(*o),
        HExprKind::Index(b, _) | HExprKind::Slice(b, _) | HExprKind::Field(b, _) => formal_root(b),
        HExprKind::Call(_, a) if a.len() == 1 => formal_root(&a[0]),
        HExprKind::Convert(x) => formal_root(x),
        _ => None,
    }
}

fn obj_expr(d: &Design, o: ObjId) -> HExpr {
    HExpr {
        kind: HExprKind::Obj(o),
        ty: d.objects[o].ty,
        loc: d.objects[o].loc.clone(),
    }
}

/// Whether two static names denote the same object part.
pub fn same_name(a: &HExpr, b: &HExpr) -> bool {
    match (&a.kind, &b.kind) {
        (HExprKind::Obj(x), HExprKind::Obj(y)) => x == y,
        (HExprKind::Index(x, i), HExprKind::Index(y, j)) => {
            same_name(x, y)
                && i.len() == j.len()
                && i.iter()
                    .zip(j)
                    .all(|(p, q)| format!("{:?}", p.kind) == format!("{:?}", q.kind))
        }
        (HExprKind::Field(x, i), HExprKind::Field(y, j)) => i == j && same_name(x, y),
        (HExprKind::Slice(x, r1), HExprKind::Slice(y, r2)) => {
            same_name(x, y) && r1.static_val == r2.static_val
        }
        _ => false,
    }
}
