//! Statements (IEEE 1076-2008 §10, §11): sequential statements, and
//! concurrent statements rewritten as their equivalent processes (§11.3,
//! §11.5–§11.7).

use super::decl::name_text;
use super::hir::*;
use super::{Design, RegionId, Sym};
use crate::vhdl::ast;

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
            HExprKind::Attr(name, p, param) => {
                // `s'event` etc. read the prefix signal; `'stable(t)` too.
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
    fn static_name(&self, h: &HExpr) -> bool {
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
                if *guarded {
                    self.error(
                        s.span.clone(),
                        "guarded signal assignments are not supported yet",
                    );
                    return;
                }
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
            ast::ConcKind::Block { .. } => {
                self.error(s.span.clone(), "block statements are not supported yet")
            }
            ast::ConcKind::ForGenerate { .. }
            | ast::ConcKind::IfGenerate(_)
            | ast::ConcKind::CaseGenerate { .. } => {
                self.error(s.span.clone(), "generate statements are not supported yet")
            }
            ast::ConcKind::Unsupported(what) => {
                self.error(s.span.clone(), format!("{} is not supported yet", what))
            }
        }
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
        // The entity: `entity lib.e(a)`, or a component of the same name as
        // an entity of the work library (default binding, §7.3.3).
        let (lib, ent, archn) = match unit {
            ast::InstUnit::Entity(n, a) => {
                let (lib, en) = match &n.kind {
                    ast::NameKind::Selected(p, ast::Suffix::Ident(e)) => {
                        match self.name_sym(r, p) {
                            Some(Sym::Library(l)) => (l, e.name.clone()),
                            _ => {
                                self.error(
                                    n.span.clone(),
                                    "an entity name lib.entity was expected",
                                );
                                return;
                            }
                        }
                    }
                    ast::NameKind::Simple(e) => (self.cur_lib.clone(), e.name.clone()),
                    _ => {
                        self.error(n.span.clone(), "an entity name was expected");
                        return;
                    }
                };
                (lib, en, a.as_ref().map(|a| a.name.clone()))
            }
            ast::InstUnit::Component(n) => match n.kind {
                ast::NameKind::Simple(ref i) => (self.cur_lib.clone(), i.name.clone(), None),
                _ => {
                    self.error(
                        n.span.clone(),
                        "component instantiation of this form is not supported yet",
                    );
                    return;
                }
            },
            ast::InstUnit::Configuration(n) => {
                self.error(
                    n.span.clone(),
                    "configuration instantiation is not supported yet",
                );
                return;
            }
        };
        let Some(info) = self.analyze_entity(&lib, &ent) else {
            self.error(
                loc.span.clone(),
                format!("no entity '{}' in library '{}'", ent, lib),
            );
            return;
        };
        let generic_map = self.map_formals(r, &info.generics, generic_map, true, &loc);
        let port_map = self.map_formals(r, &info.ports, port_map, false, &loc);
        let generic_map: Vec<(ObjId, HExpr)> = generic_map
            .into_iter()
            .filter_map(|(f, a)| a.map(|a| (f, a)))
            .collect();
        arch.instances.push(Instance {
            label: label_s,
            library: lib,
            entity: ent,
            arch: archn,
            generic_map,
            port_map,
            loc,
        });
    }

    /// Associate actuals with an entity's generics or ports (positional
    /// then named, §6.5.7.1); `None` for `open` / defaulted.
    fn map_formals(
        &mut self,
        r: RegionId,
        formals: &[ObjId],
        assocs: &[ast::Assoc],
        generics: bool,
        loc: &Loc,
    ) -> Vec<(ObjId, Option<HExpr>)> {
        let mut out: Vec<(ObjId, Option<HExpr>)> = formals.iter().map(|f| (*f, None)).collect();
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
            let ast::Actual::Expr(e) = &a.actual else {
                continue;
            };
            let ft = self.objects[f].ty;
            if let Some(h) = self.expr(r, e, Some(ft)) {
                out[idx].1 = Some(h);
            }
        }
        let _ = loc;
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
