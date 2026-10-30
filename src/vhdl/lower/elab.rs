//! Elaboration of the design hierarchy (IEEE 1076-2008 §14) into one
//! flattened module, and the generated VHDL simulation kernel.
//!
//! Instances are flattened depth-first in statement order. A port
//! associated with a signal (or a static part of one) is that signal: the
//! formal and the actual share the effective value and the drivers
//! (§14.7.3.4 for ports without conversions), so no delta is added. An
//! unassociated or `open` port is a signal of its own.
//!
//! Each process has one driver per signal it assigns (§14.7.2). A driver
//! of a whole signal keeps a queue of whole values; a driver assigned
//! through elements or slices keeps per-element transactions, and covers the
//! elements its assignments can reach (the longest static prefix). A signal
//! with one whole driver and no resolution function takes the driver's
//! value; otherwise its value is computed element by element from the
//! drivers covering each element, through the resolution function where
//! there is one (§14.7.3.2).

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use super::leaves::{DSel, Sel};
use super::{Lw, Repr, sv_ident, sv_string};
use crate::vhdl::ast::{Dir, Mode, ObjClass, SignalKind};
use crate::vhdl::sema::hir::*;

/// A signal of the flattened design.
#[derive(Clone, Debug)]
pub(super) struct Sig {
    pub obj: ObjId,
    pub ty: TypeId,
    /// The instance whose context evaluates the initial value.
    pub inst: usize,
    /// An actual's value as the initial value (`port map (p => '0')`).
    pub init_expr: Option<(HExpr, usize)>,
    /// An implicit signal (index into `Lw::imps`).
    pub implicit: Option<usize>,
}

/// The kinds of implicit signals (§16.2.4, §11.2).
#[derive(Clone, Debug)]
pub(super) enum ImpKind {
    Stable,
    Quiet,
    Delayed,
    Transaction,
    /// GUARD: the guard expression and the instance it is evaluated in.
    Guard(HExpr, usize),
}

/// An implicit signal, updated by the kernel after the explicit signals
/// of each simulation cycle (§14.7.5.3 b, c).
#[derive(Clone, Debug)]
pub(super) struct Imp {
    pub kind: ImpKind,
    pub sig: usize,
    /// The prefix's event (`'stable`, `'delayed`) or activity (`'quiet`,
    /// `'transaction`) in this cycle (SV).
    pub trig: String,
    /// `'delayed`: the prefix's value (SV).
    pub value: String,
    /// The time parameter T (SV).
    pub delay: String,
    /// Implicit signals (signal ids) it reads, updated before it.
    pub deps: Vec<usize>,
}

/// A procedure lowered for one calling process and one binding of its
/// signal parameters to the actual signals (§4.2.2.3): it may wait and
/// drive signals for that process.
#[derive(Clone, Debug)]
pub(super) struct Spec {
    pub sub: SubId,
    pub inst: usize,
    pub proc: usize,
    pub binds: Vec<(ObjId, SigRef)>,
}

/// How an object names a signal: the whole signal or a static part.
#[derive(Clone, Debug, PartialEq)]
pub(super) enum Part {
    Whole,
    /// Record elements, elements and a trailing slice (offsets from the
    /// left; a slice keeps the formal's bounds).
    Path(Vec<Sel>),
}

#[derive(Clone, Debug)]
pub(super) struct SigRef {
    pub sig: usize,
    pub part: Part,
}

/// The elements a driver covers.
#[derive(Clone, Debug, PartialEq)]
pub(super) enum Cov {
    All,
    Set(BTreeSet<i64>),
}

impl Cov {
    /// Whether two coverages share a leaf in `base..base + count`.
    pub(super) fn overlaps(&self, other: &Cov, base: i64, count: i64) -> bool {
        match (self, other) {
            (Cov::All, Cov::All) => count > 0,
            (Cov::All, Cov::Set(x)) | (Cov::Set(x), Cov::All) => {
                x.range(base..base + count).next().is_some()
            }
            (Cov::Set(a), Cov::Set(b)) => a
                .range(base..base + count)
                .any(|k| b.contains(k)),
        }
    }
    fn add(&mut self, other: Cov) {
        match (std::mem::replace(self, Cov::All), other) {
            (Cov::Set(mut a), Cov::Set(b)) => {
                a.extend(b);
                *self = Cov::Set(a);
            }
            _ => *self = Cov::All,
        }
    }
}

#[derive(Clone, Debug)]
pub(super) struct Driver {
    pub cov: Cov,
    /// Assigned through elements or slices: per-element transactions.
    pub slots: bool,
    /// Assigned through a port with a default value, and the instance:
    /// the driver's initial value (§14.7.2).
    pub init: Option<(ObjId, usize)>,
}

#[derive(Clone, Debug)]
pub(super) struct InstInfo {
    pub arch: usize,
    /// Generic values given by the instance's generic map.
    pub generics: BTreeMap<ObjId, (HExpr, usize)>,
    /// The enclosing instance of a block or generate iteration, whose
    /// objects it sees.
    pub parent: Option<usize>,
    /// The instance containing this one, and its label there (the top:
    /// its entity name), for external names (§8.7).
    pub container: Option<usize>,
    pub label: String,
}

/// A wait site: the conditions (SV, kernel scope) of the events it is
/// sensitive to.
pub(super) struct Site {
    pub conds: Vec<String>,
}

/// The target of a signal assignment.
enum Target {
    Whole(usize),
    /// A part: signal, path, scalar leaves covered.
    Path(usize, Vec<DSel>, Cov),
}

/// Package objects and top-level instance objects keep plain names.
pub(super) const GLOBAL: usize = usize::MAX;

/// Driver ids from here on are the drivers of port associations with a
/// formal conversion or partial formal (`Link`), not processes.
pub(super) const PSEUDO: usize = 1 << 30;

/// A step of the update phase (`Lw::update_order`).
#[derive(Clone, Copy, Debug)]
enum UpdStep {
    /// A signal's update by its drivers.
    Sig(usize),
    /// An in-port link (index into `links`).
    In(usize),
}

/// Whether two parts of one signal may overlap: `false` only when their
/// paths provably select different elements.
fn parts_overlap(a: &Part, b: &Part) -> bool {
    let (Part::Path(x), Part::Path(y)) = (a, b) else {
        return true;
    };
    for (p, q) in x.iter().zip(y) {
        let disjoint = match (p, q) {
            (Sel::Field(i), Sel::Field(j)) => i != j,
            (Sel::Elem(i), Sel::Elem(j)) => i != j,
            (Sel::Elem(i), Sel::Slice(o, n)) | (Sel::Slice(o, n), Sel::Elem(i)) => {
                *i < *o || *i >= o + n
            }
            (Sel::Slice(o1, n1), Sel::Slice(o2, n2)) => o1 + n1 <= *o2 || o2 + n2 <= *o1,
            _ => return true,
        };
        if disjoint {
            return false;
        }
        if p != q {
            return true;
        }
    }
    true
}

/// A port association through a conversion or a partial formal: a
/// signal (part) computed from others without a delta (§14.7.3.4). Mode
/// `in` writes the formal's effective value; mode `out` the driving value
/// of the actual (a driver of it).
#[derive(Clone, Debug)]
pub(super) struct Link {
    pub inn: bool,
    pub target: SigRef,
    /// The value and the instance context it is evaluated in.
    pub value: HExpr,
    pub ctx: usize,
    /// The signals whose activity recomputes it.
    pub sources: Vec<usize>,
    /// Mode `out`: the driver of the actual.
    pub drv: usize,
    /// A driver with an SV value (`mixed::ForeignIn`, by index).
    pub foreign: Option<usize>,
}

impl<'a> Lw<'a> {
    // ---- the instance tree ----------------------------------------------------------

    /// Elaborate the hierarchy below the top architecture: signals,
    /// port associations and processes in elaboration order.
    pub(super) fn elaborate(&mut self, top: usize) {
        // The objects each architecture's scope declares (for the scopes
        // of blocks and generate iterations).
        self.arch_objs = self
            .d
            .archs
            .iter()
            .map(|a| {
                let mut set: std::collections::HashSet<ObjId> = std::collections::HashSet::new();
                set.extend(
                    a.generics
                        .iter()
                        .chain(&a.ports)
                        .chain(&a.signals)
                        .chain(&a.constants),
                );
                for p in &a.processes {
                    set.extend(p.locals.iter().copied());
                }
                set
            })
            .collect();
        self.insts.push(InstInfo {
            arch: top,
            generics: BTreeMap::new(),
            parent: None,
            container: None,
            label: self.d.archs[top].entity.clone(),
        });
        // Signals declared in packages.
        let pkg_sigs: Vec<ObjId> = self
            .d
            .packages
            .values()
            .flat_map(|(p, _)| p.objects.iter().copied())
            .filter(|o| matches!(self.d.objects[*o].kind, ObjKind::Signal))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        for o in pkg_sigs {
            self.new_sig(GLOBAL, o);
        }
        let ports = self.d.archs[top].ports.clone();
        for p in ports {
            self.new_sig(0, p);
        }
        self.elab_inst(0);
    }

    fn new_sig(&mut self, inst: usize, o: ObjId) -> usize {
        let id = self.sigs.len();
        self.sigs.push(Sig {
            obj: o,
            ty: self.d.objects[o].ty,
            inst,
            init_expr: None,
            implicit: None,
        });
        self.sig_map.insert(
            (inst, o),
            SigRef {
                sig: id,
                part: Part::Whole,
            },
        );
        id
    }

    fn elab_inst(&mut self, inst: usize) {
        let ai = self.insts[inst].arch;
        let signals = self.d.archs[ai].signals.clone();
        for s in signals {
            self.new_sig(inst, s);
        }
        // Concurrent statements in source order.
        let mut items: Vec<(usize, bool, usize)> = Vec::new();
        for (pi, p) in self.d.archs[ai].processes.iter().enumerate() {
            items.push((p.loc.span.start, false, pi));
        }
        for (ii, i) in self.d.archs[ai].instances.iter().enumerate() {
            items.push((i.loc.span.start, true, ii));
        }
        items.sort();
        for (_, is_inst, i) in items {
            if !is_inst {
                self.procs.push((inst, ai, i));
                continue;
            }
            let ins = self.d.archs[ai].instances[i].clone();
            let Some(child_arch) = ins.arch_index else {
                self.err(
                    &ins.loc,
                    "the instantiated design entity has no architecture",
                );
                continue;
            };
            let child = self.insts.len();
            let generics = ins
                .generic_map
                .iter()
                .map(|(f, e)| (*f, (e.clone(), inst)))
                .collect();
            let nested = self.d.archs[child_arch].nested;
            self.insts.push(InstInfo {
                arch: child_arch,
                generics,
                parent: nested.then_some(inst),
                container: Some(inst),
                label: ins.label.to_ascii_lowercase(),
            });
            let mut mapped = BTreeSet::new();
            for (formal, actual) in &ins.port_map {
                mapped.insert(*formal);
                match actual {
                    None => {
                        self.new_sig(child, *formal);
                    }
                    Some(e) => match self.actual_ref(inst, e) {
                        Some(r) => {
                            self.sig_map.insert((child, *formal), r);
                        }
                        None if self.is_static_actual(e) => {
                            // A static expression: a signal of its own with
                            // that value.
                            let s = self.new_sig(child, *formal);
                            self.sigs[s].init_expr = Some((e.clone(), inst));
                        }
                        None => {
                            self.err(&e.loc, "this port actual is not supported yet");
                            self.new_sig(child, *formal);
                        }
                    },
                }
            }
            let ports = self.d.archs[child_arch].ports.clone();
            for p in ports {
                if !mapped.contains(&p) {
                    self.new_sig(child, p);
                }
            }
            for pc in &ins.port_conv {
                let inn = pc.mode == Mode::In;
                let (tctx, vctx) = if inn { (child, inst) } else { (inst, child) };
                let Some(target) = self.actual_ref(tctx, &pc.target) else {
                    self.err(&pc.target.loc, "this port association is not supported yet");
                    continue;
                };
                let mut sources = Vec::new();
                self.sig_sources(vctx, &pc.value, &mut sources);
                let drv = PSEUDO + self.links.len();
                if !inn {
                    let (cov, slots) = match &target.part {
                        Part::Whole => (Cov::All, false),
                        Part::Path(p) => (
                            self.path_cov(self.sigs[target.sig].ty, &dsels(p)),
                            true,
                        ),
                    };
                    self.add_driver(target.sig, drv, cov, slots);
                }
                self.links.push(Link {
                    inn,
                    target,
                    value: pc.value.clone(),
                    ctx: vctx,
                    sources,
                    drv,
                    foreign: None,
                });
            }
            self.elab_inst(child);
        }
        // SV modules bound to components.
        let foreign = self.d.archs[ai].foreign.clone();
        for fi in &foreign {
            self.sv_instance(inst, fi);
        }
    }

    /// The signal (part) an actual names in the context of `inst`.
    pub(super) fn actual_ref(&self, inst: usize, e: &HExpr) -> Option<SigRef> {
        let (base, sel) = match &e.kind {
            HExprKind::Obj(o) => return self.lookup_sig(inst, *o),
            HExprKind::Field(b, i) => (self.actual_ref(inst, b)?, vec![Sel::Field(*i)]),
            HExprKind::Index(b, idx) => {
                let base = self.actual_ref(inst, b)?;
                let mut sels = Vec::new();
                for (k, x) in idx.iter().enumerate() {
                    let i = self.d.eval(x)?.as_i64()?;
                    let (l, dir, _) = if k == 0 {
                        self.static_bounds(b.ty)?
                    } else {
                        let sr = self.d.array_index_ranges(b.ty)?.get(k)?.clone()?;
                        (sr.left.as_i64()?, sr.dir, 0)
                    };
                    sels.push(Sel::Elem(match dir {
                        Dir::To => i - l,
                        Dir::Downto => l - i,
                    }));
                }
                (base, sels)
            }
            HExprKind::Slice(b, r) => {
                let base = self.actual_ref(inst, b)?;
                let (l, dir, _) = self.static_bounds(b.ty)?;
                let (left, len) = match &r.static_val {
                    Some(sr) => (sr.left.as_i64()?, sr.length()),
                    None => {
                        let a = self.d.eval(&r.left)?.as_i64()?;
                        let z = self.d.eval(&r.right)?.as_i64()?;
                        (a, if r.dir == Dir::To { z - a + 1 } else { a - z + 1 })
                    }
                };
                let off = match dir {
                    Dir::To => left - l,
                    Dir::Downto => l - left,
                };
                (base, vec![Sel::Slice(off, len.max(0))])
            }
            _ => return None,
        };
        let mut path = match base.part {
            Part::Whole => Vec::new(),
            Part::Path(p) => p,
        };
        for s in sel {
            // An element or slice of a slice: offsets from the slice's start.
            match (path.last().cloned(), s) {
                (Some(Sel::Slice(o, _)), Sel::Elem(k)) => {
                    path.pop();
                    path.push(Sel::Elem(o + k));
                }
                (Some(Sel::Slice(o, _)), Sel::Slice(k, n)) => {
                    path.pop();
                    path.push(Sel::Slice(o + k, n));
                }
                (Some(Sel::Slice(..)), Sel::Field(_)) => return None,
                (_, s) => path.push(s),
            }
        }
        Some(SigRef {
            sig: base.sig,
            part: Part::Path(path),
        })
    }

    fn is_static_actual(&self, e: &HExpr) -> bool {
        self.d.eval(e).is_some()
    }

    /// The signals an expression reads, in the context of `inst`.
    fn sig_sources(&self, inst: usize, h: &HExpr, out: &mut Vec<usize>) {
        match &h.kind {
            HExprKind::Obj(o) => {
                if matches!(self.d.objects[*o].kind, ObjKind::Signal | ObjKind::Port(_))
                    && let Some(r) = self.lookup_sig(inst, *o)
                    && !out.contains(&r.sig)
                {
                    out.push(r.sig);
                }
            }
            HExprKind::Call(_, a) | HExprKind::RecordAgg(a) => {
                for x in a {
                    self.sig_sources(inst, x, out);
                }
            }
            HExprKind::Cond(arms, last) => {
                for (c, v) in arms {
                    self.sig_sources(inst, c, out);
                    self.sig_sources(inst, v, out);
                }
                self.sig_sources(inst, last, out);
            }
            HExprKind::Index(b, i) => {
                self.sig_sources(inst, b, out);
                for x in i {
                    self.sig_sources(inst, x, out);
                }
            }
            HExprKind::Slice(b, _)
            | HExprKind::Field(b, _)
            | HExprKind::Convert(b)
            | HExprKind::Qualified(b) => self.sig_sources(inst, b, out),
            _ => {}
        }
    }

    /// The function applying link `n`: an `in` link recomputes the
    /// formal's value (`init`: its initial value); an `out` link the
    /// driving value it contributes to the actual.
    fn link_sv(&mut self, n: usize) -> String {
        let l = self.links[n].clone();
        let s = l.target.sig;
        let sig = self.sigs[s].clone();
        let loc = self.d.objects[sig.obj].loc.clone();
        let r = self.repr(sig.ty, &loc);
        let saved = std::mem::replace(&mut self.inst, l.ctx);
        self.temps.clear();
        let dst = if l.inn {
            "nv".to_string()
        } else {
            format!("vh_dv{}_{}", s, l.drv)
        };
        let assign = match (l.target.part.clone(), l.foreign) {
            (Part::Whole, Some(k)) => {
                let v = self.foreign_value(k);
                format!("    {} = {};\n", dst, v)
            }
            (Part::Whole, None) => {
                let target = HExpr {
                    kind: HExprKind::Obj(sig.obj),
                    ty: sig.ty,
                    loc: loc.clone(),
                };
                let v = self.store_value_init(&target, &l.value);
                format!("    {} = {};\n", dst, v)
            }
            (Part::Path(path), f) => {
                let (sel, slice, at) = self.path_sv(sig.ty, &path, &loc);
                let tr = match slice {
                    None => self.repr(at, &loc),
                    Some((_, len)) => match self.repr(at, &loc) {
                        Repr::Pk(w, _) => Repr::Pk(w, len),
                        r => r,
                    },
                };
                let v = match f {
                    Some(k) => {
                        let v = self.foreign_value(k);
                        let fr = self.repr(self.fins[k].ty, &loc);
                        let bsv = self.static_bounds(self.fins[k].ty).map(|b| self.bounds_sv(b));
                        self.coerce(v, &fr, &tr, bsv, &loc)
                    }
                    None => self.ex_as(&l.value, &tr),
                };
                match (slice, &tr) {
                    (None, _) => format!("    {}{} = {};\n", dst, sel, v),
                    (Some((k, len)), Repr::Pk(w, _)) => {
                        let Repr::Pk(_, n) = self.repr(at, &loc) else {
                            unreachable!()
                        };
                        let part = Self::pk_part(&format!("{}{}", dst, sel), *w, n, k, len);
                        format!("    {} = {};\n", part, v)
                    }
                    (Some((k, len)), _) => {
                        let (f, line, _) = self.file_line(&l.value.loc);
                        format!(
                            "    vh_lv = {v};\n    if (vh_lv.d.size() != {len}) vh_fatal($sformatf(\"bound check failure at %s:%0d\", {f}, {line}));\n    else for (int j = 0; j < {len}; j++) {dst}{sel}.d[{k} + j] = vh_lv.d[j];\n",
                            v = v,
                            len = len,
                            f = sv_string(&f),
                            line = line,
                            dst = dst,
                            sel = sel,
                            k = k
                        )
                    }
                }
            }
        };
        let pre = self.flush_pre(4);
        let mut temps = String::new();
        for (name, t) in std::mem::take(&mut self.temps) {
            let _ = writeln!(temps, "    {} {};", t, name);
        }
        if let Part::Path(p) = &l.target.part
            && matches!(p.last(), Some(Sel::Slice(..)))
            && let (_, Some(_), at) = self.path_sv(sig.ty, p, &loc)
            && let r @ Repr::Arr(..) = self.repr(at, &loc)
        {
            let _ = writeln!(temps, "    {} vh_lv;", r.sv());
        }
        self.inst = saved;
        let t = r.sv();
        if l.inn {
            let eq = self.eq_expr(&r, "nv", &format!("vh_s{}", s));
            format!(
                "  function automatic void vh_lnk{n}(bit init);\n    {t} nv;\n{temps}    nv = vh_s{s};\n{pre}{assign}    if (init) begin vh_s{s} = nv; vh_s{s}_last = nv; end\n    else begin\n      vh_s{s}_act = 1;\n      if (!{eq}) begin if (!vh_s{s}_ev) vh_s{s}_last = vh_s{s}; vh_s{s} = nv; vh_s{s}_ev = 1; vh_s{s}_lev = $time; end\n    end\n  endfunction\n",
                n = n,
                t = t,
                temps = temps,
                s = s,
                pre = pre,
                assign = assign,
                eq = eq
            )
        } else {
            format!(
                "  function automatic void vh_lnk{n}();\n{temps}{pre}{assign}    vh_s{s}_act = 1;\n  endfunction\n",
                n = n,
                temps = temps,
                pre = pre,
                assign = assign,
                s = s
            )
        }
    }

    /// The order of the update phase (§14.7.3): each signal's update by
    /// its drivers (`UpdStep::Sig`, with the out-port links that drive it)
    /// and each in-port link (`UpdStep::In`, writing a part of its formal
    /// after the formal's update). A step follows the updates of the
    /// signals it reads and the in-port links that write a part of them it
    /// reads: a port with a mode view (VHDL-2019) has links both ways, and
    /// only parts tell `m.req` (driven inside, read out) from `m.ack`
    /// (written by a link from outside). Otherwise elaboration order.
    fn update_order(&self) -> Vec<UpdStep> {
        let nsig = self.sigs.len();
        let n = nsig + self.links.len();
        let node = |l: usize| {
            if self.links[l].inn {
                nsig + l
            } else {
                self.links[l].target.sig
            }
        };
        let mut deps: Vec<Vec<usize>> = vec![Vec::new(); n];
        let mut indeg = vec![0usize; n];
        let mut edge = |a: usize, b: usize, deps: &mut Vec<Vec<usize>>| {
            if a != b && !deps[a].contains(&b) {
                deps[a].push(b);
                indeg[b] += 1;
            }
        };
        for (li, l) in self.links.iter().enumerate() {
            if l.inn {
                edge(l.target.sig, nsig + li, &mut deps);
            }
            let read = self.actual_ref(l.ctx, &l.value);
            for &src in &l.sources {
                if src == l.target.sig {
                    continue;
                }
                edge(src, node(li), &mut deps);
                let part = match &read {
                    Some(r) if r.sig == src => r.part.clone(),
                    _ => Part::Whole,
                };
                for (mi, m) in self.links.iter().enumerate() {
                    if m.inn && mi != li && m.target.sig == src && parts_overlap(&part, &m.target.part) {
                        edge(nsig + mi, node(li), &mut deps);
                    }
                }
            }
        }
        let mut ready: BTreeSet<usize> = (0..n).filter(|&s| indeg[s] == 0).collect();
        let mut order = Vec::with_capacity(n);
        let mut done = vec![false; n];
        while let Some(s) = ready.pop_first() {
            order.push(s);
            done[s] = true;
            for &t in &deps[s] {
                indeg[t] -= 1;
                if indeg[t] == 0 {
                    ready.insert(t);
                }
            }
        }
        // A cycle (a link computed from its own target): the rest in order.
        order.extend((0..n).filter(|&s| !done[s]));
        // Out-port links are part of their targets' updates: no steps.
        order
            .into_iter()
            .filter_map(|s| {
                if s < nsig {
                    Some(UpdStep::Sig(s))
                } else {
                    self.links[s - nsig].inn.then_some(UpdStep::In(s - nsig))
                }
            })
            .collect()
    }

    pub(super) fn lookup_sig(&self, mut inst: usize, o: ObjId) -> Option<SigRef> {
        if self.d.externals.contains_key(&o) {
            let (i, x) = self.resolve_external(inst, o)?;
            return self.lookup_sig(i, x);
        }
        loop {
            if let Some(r) = self.sig_map.get(&(inst, o)) {
                return Some(r.clone());
            }
            match self.insts.get(inst).and_then(|i| i.parent) {
                Some(p) => inst = p,
                None => return self.sig_map.get(&(GLOBAL, o)).cloned(),
            }
        }
    }

    /// The object an external name denotes (§8.7), seen from instance
    /// `inst`: the instance declaring it and the object. An absolute
    /// path starts at the top entity, a relative one at `inst`; `^` goes
    /// up one level.
    pub(super) fn resolve_external(&self, inst: usize, o: ObjId) -> Option<(usize, ObjId)> {
        let path = self.d.externals.get(&o)?;
        let (mut cur, rest) = match path.strip_prefix('.') {
            Some(p) => {
                let mut parts = p.split('.');
                if parts.next()? != self.insts[0].label {
                    return None;
                }
                (0, parts.collect::<Vec<_>>())
            }
            None => (inst, path.split('.').collect::<Vec<_>>()),
        };
        let (last, labels) = rest.split_last()?;
        for l in labels {
            cur = if *l == "^" {
                self.insts[cur].container?
            } else {
                (0..self.insts.len())
                    .find(|&c| self.insts[c].container == Some(cur) && self.insts[c].label == *l)?
            };
        }
        let a = &self.d.archs[self.insts[cur].arch];
        let x = a
            .signals
            .iter()
            .chain(&a.ports)
            .chain(&a.constants)
            .chain(&a.generics)
            .copied()
            .find(|x| self.d.objects[*x].name == *last)?;
        Some((cur, x))
    }

    /// The instance whose scope declares object `o` as seen from `inst`:
    /// `inst` itself or the block or generate iteration enclosing it.
    pub(super) fn owner_inst(&self, inst: usize, o: ObjId) -> usize {
        let mut i = inst;
        loop {
            let Some(info) = self.insts.get(i) else {
                return inst;
            };
            let Some(p) = info.parent else {
                return if i == inst { inst } else { i };
            };
            if self.arch_objs[info.arch].contains(&o) {
                return i;
            }
            i = p;
        }
    }

    /// The SV expression reading a signal object (current or last value).
    pub(super) fn sig_read(&mut self, o: ObjId) -> String {
        let Some(r) = self.lookup_sig(self.inst, o) else {
            if self.d.externals.contains_key(&o) {
                let loc = self.d.objects[o].loc.clone();
                self.err(
                    &loc,
                    format!("no signal at external path '{}'", self.d.objects[o].name),
                );
            }
            return format!("vh_s{}", o);
        };
        if self.sigs[r.sig].implicit.is_some() {
            self.imp_refs.push(r.sig);
        }
        let base = match self.read_drv {
            Some((s, p)) if s == r.sig => format!("vh_dv{}_{}", s, p),
            _ if self.read_last => format!("vh_s{}_last", r.sig),
            _ => format!("vh_s{}", r.sig),
        };
        match r.part {
            Part::Whole => base,
            Part::Path(path) => {
                let ty = self.d.objects[o].ty;
                let loc = self.d.objects[o].loc.clone();
                self.path_read(&base, &path, r.sig, ty, &loc)
            }
        }
    }

    /// The signal behind a signal name (for the kernel bookkeeping).
    fn sig_of(&self, h: &HExpr) -> Option<usize> {
        match &h.kind {
            HExprKind::Obj(o) => self.lookup_sig(self.inst, *o).map(|r| r.sig),
            HExprKind::Index(b, _) | HExprKind::Slice(b, _) | HExprKind::Field(b, _) => {
                self.sig_of(b)
            }
            _ => None,
        }
    }

    /// Whether `h` names a whole signal (not a part of one).
    fn whole_sig(&self, h: &HExpr) -> Option<usize> {
        match &h.kind {
            HExprKind::Obj(o) => match self.lookup_sig(self.inst, *o) {
                Some(SigRef {
                    sig,
                    part: Part::Whole,
                }) => Some(sig),
                _ => None,
            },
            _ => None,
        }
    }

    /// A signal attribute of a signal name (`'event`, `'active`,
    /// `'last_value`, `'last_event`, `'last_active`, §16.2.4): of the whole
    /// signal, or for a part, from the whole signal's flags and the part's
    /// values.
    /// The process being lowered tests a signal's 'event.
    pub(super) fn mark_clocked(&mut self) {
        if let Some(p) = self.cur_proc {
            self.clocked.insert(p);
        }
    }

    pub(super) fn sig_attr(&mut self, x: &HExpr, name: &str) -> Option<String> {
        // An implicit signal.
        if let HExprKind::Attr(an, p, prm) = &x.kind
            && is_implicit(an)
            && let AttrPrefix::Expr(px) = p.as_ref()
        {
            let r = self.implicit_sig(an, px, prm.as_deref(), x.ty, &x.loc)?;
            self.imp_refs.push(r);
            return Some(self.whole_attr(r, name));
        }
        // A signal parameter: the attributes passed with it.
        if let HExprKind::Obj(o) = &x.kind
            && matches!(self.d.objects[*o].kind, ObjKind::Param(ObjClass::Signal, _))
            && self.lookup_sig(self.inst, *o).is_none()
        {
            let p = self.obj_name(*o);
            return Some(match name {
                "event" => format!("{}_ev", p),
                "active" => format!("{}_act", p),
                "last_value" => format!("{}_last", p),
                "last_active" => {
                    self.err(
                        &x.loc,
                        "'last_active of a signal parameter is not supported yet",
                    );
                    "0".into()
                }
                _ => format!("(vh_now - {}_lev)", p),
            });
        }
        if let HExprKind::Index(b, _) | HExprKind::Slice(b, _) | HExprKind::Field(b, _) = &x.kind
            && let HExprKind::Obj(o) = &b.kind
            && matches!(self.d.objects[*o].kind, ObjKind::Param(ObjClass::Signal, _))
            && self.lookup_sig(self.inst, *o).is_none()
        {
            let p = self.obj_name(*o);
            let cur = self.ex(x);
            let last = self.ex_last(x);
            let r = self.repr(x.ty, &x.loc);
            return Some(match name {
                "event" => format!("({}_ev && !{})", p, self.eq_expr(&r, &cur, &last)),
                "active" => format!("{}_act", p),
                "last_value" => last,
                "last_active" => {
                    self.err(
                        &x.loc,
                        "'last_active of a signal parameter is not supported yet",
                    );
                    "0".into()
                }
                _ => format!("(vh_now - {}_lev)", p),
            });
        }
        let s = self.sig_of(x)?;
        if self.whole_sig(x).is_some() {
            return Some(self.whole_attr(s, name));
        }
        let cur = self.ex(x);
        let last = self.ex_last(x);
        let r = self.repr(x.ty, &x.loc);
        Some(match name {
            "event" => format!("(vh_s{}_ev && !{})", s, self.eq_expr(&r, &cur, &last)),
            "last_value" => last,
            _ => self.whole_attr(s, name),
        })
    }

    /// A signal attribute of a whole signal.
    fn whole_attr(&mut self, s: usize, name: &str) -> String {
        match name {
            "event" => format!("vh_s{}_ev", s),
            "active" => format!("vh_s{}_act", s),
            "last_value" => format!("vh_s{}_last", s),
            "last_active" => {
                self.need_lact.insert(s);
                format!("(vh_now - vh_s{}_lact)", s)
            }
            _ => format!("(vh_now - vh_s{}_lev)", s),
        }
    }

    /// The implicit signal `x'name(t)` (§16.2.4), created on first use;
    /// `ty` is its type.
    pub(super) fn implicit_sig(
        &mut self,
        name: &str,
        x: &HExpr,
        param: Option<&HExpr>,
        ty: TypeId,
        loc: &Loc,
    ) -> Option<usize> {
        let root = self.d.sig_root(x);
        if let Some(o) = root
            && matches!(self.d.objects[o].kind, ObjKind::Param(ObjClass::Signal, _))
            && self.lookup_sig(self.inst, o).is_none()
        {
            self.err(
                loc,
                format!("'{} of a signal parameter is not supported yet", name),
            );
            return None;
        }
        let mark = self.imp_refs.len();
        let px = self.ex(x);
        let delay = match param {
            Some(t) => self.ex(t),
            None => "64'sd0".into(),
        };
        let key = format!("{}|{}|{}", name, px, delay);
        if let Some(&r) = self.imp_keys.get(&key) {
            self.imp_refs.truncate(mark);
            return Some(r);
        }
        let trig = self.sig_attr(
            x,
            if matches!(name, "stable" | "delayed") {
                "event"
            } else {
                "active"
            },
        );
        let Some(trig) = trig else {
            self.err(
                loc,
                format!("'{} of this signal is not supported yet", name),
            );
            return None;
        };
        let deps: Vec<usize> = self.imp_refs.drain(mark..).collect();
        let kind = match name {
            "stable" => ImpKind::Stable,
            "quiet" => ImpKind::Quiet,
            "delayed" => ImpKind::Delayed,
            _ => ImpKind::Transaction,
        };
        let r = self.sigs.len();
        self.sigs.push(Sig {
            obj: root.unwrap_or(0),
            ty,
            inst: self.inst,
            init_expr: None,
            implicit: Some(self.imps.len()),
        });
        self.imps.push(Imp {
            kind,
            sig: r,
            trig,
            value: px,
            delay,
            deps,
        });
        self.imp_keys.insert(key, r);
        Some(r)
    }

    /// `x'driving` / `x'driving_value` (§16.2.4): of the current process's
    /// driver of the signal.
    pub(super) fn driving(&mut self, name: &str, x: &HExpr, loc: &Loc) -> String {
        let (Some(p), Some(s)) = (self.cur_proc, self.sig_of(x)) else {
            self.err(loc, format!("'{} is only supported in a process", name));
            return "0".into();
        };
        self.drv_checks.push((s, p, loc.clone()));
        if name == "driving" {
            return if self.sig_kind(s).is_some() {
                format!("vh_don{}_{}", s, p)
            } else {
                "1'b1".into()
            };
        }
        let saved = self.read_drv.replace((s, p));
        let v = self.ex(x);
        self.read_drv = saved;
        v
    }

    /// The kind of a guarded signal (§6.4.2.3).
    pub(super) fn sig_kind(&self, s: usize) -> Option<SignalKind> {
        let sig = &self.sigs[s];
        if sig.implicit.is_some() {
            return None;
        }
        self.d.sig_kinds.get(&sig.obj).copied()
    }

    /// A call of a procedure lowered per process (`Spec`): its signal
    /// parameters are bound to the actual signals, the other actuals are
    /// passed.
    pub(super) fn spec_call(
        &mut self,
        sub: SubId,
        args: &[HExpr],
        ind: usize,
        loc: &Loc,
    ) -> String {
        let pad = " ".repeat(ind);
        let info = self.d.subprograms[sub].clone();
        let Some(p) = self.cur_proc else {
            self.err(
                loc,
                format!(
                    "procedure '{}' waits, assigns signals or has signal parameters; calls outside a process are not supported yet",
                    info.name
                ),
            );
            return String::new();
        };
        let inst = if self.in_package(sub) { 0 } else { self.inst };
        let mut binds = Vec::new();
        let mut a = Vec::new();
        for (param, x) in info.params.iter().zip(args) {
            if matches!(
                self.d.objects[*param].kind,
                ObjKind::Param(ObjClass::Signal, _)
            ) {
                match self.actual_ref(self.inst, x) {
                    Some(r) => binds.push((*param, r)),
                    None => {
                        self.err(
                            &x.loc,
                            "the actual of a signal parameter must be a static signal name",
                        );
                        return String::new();
                    }
                }
            } else {
                a.extend(self.arg_values(*param, x));
            }
        }
        let key = format!("{}|{}|{}|{:?}", sub, inst, p, binds);
        let n = match self.spec_keys.get(&key) {
            Some(n) => *n,
            None => {
                let n = self.specs.len();
                self.specs.push(Spec {
                    sub,
                    inst,
                    proc: p,
                    binds,
                });
                self.spec_keys.insert(key, n);
                self.spec_todo.push(n);
                n
            }
        };
        format!("{}{}({});\n", pad, self.spec_name(n), a.join(", "))
    }

    fn spec_name(&self, n: usize) -> String {
        let s = self.specs[n].sub;
        let clean: String = self.d.subprograms[s]
            .name
            .chars()
            .filter(|c| c.is_ascii_alphanumeric() || *c == '_')
            .collect();
        format!("vh_f{}_{}_x{}", s, clean, n)
    }

    /// Lower procedure specialization `n`: a task when it waits.
    pub(super) fn spec_sv(&mut self, n: usize) {
        let sp = self.specs[n].clone();
        let info = self.d.subprograms[sp.sub].clone();
        let Some(body) = info.body.clone() else {
            return;
        };
        let loc = info.loc.clone().unwrap_or(Loc {
            file: 0,
            span: 0..0,
        });
        let saved_inst = std::mem::replace(&mut self.inst, sp.inst);
        let saved_proc = self.cur_proc.replace(sp.proc);
        let saved_temps = std::mem::take(&mut self.temps);
        let saved_ret = self.cur_ret.take();
        let mut saved_map = Vec::new();
        for (o, r) in &sp.binds {
            saved_map.push((*o, self.sig_map.insert((sp.inst, *o), r.clone())));
        }
        let mut params = Vec::new();
        for p in &info.params {
            if !matches!(self.d.objects[*p].kind, ObjKind::Param(ObjClass::Signal, _)) {
                params.extend(self.param_decls(*p, &loc));
            }
        }
        let mut locals = String::new();
        let mut inits = String::new();
        for l in &body.locals {
            let o = self.d.objects[*l].clone();
            let r = self.repr(o.ty, &o.loc);
            let _ = writeln!(locals, "    {} {};", r.sv(), self.obj_name(*l));
            let v = match &o.init {
                Some(i) => {
                    let target = HExpr {
                        kind: HExprKind::Obj(*l),
                        ty: o.ty,
                        loc: o.loc.clone(),
                    };
                    self.store_value_init(&target, i)
                }
                None => self.default_value(o.ty, &o.loc),
            };
            let flushed = self.flush_pre(4);
            inits.push_str(&flushed);
            let _ = writeln!(inits, "    {} = {};", self.obj_name(*l), v);
        }
        let stmts = self.stmts(&body.stmts, 4);
        let mut temps = String::new();
        for (n, t) in std::mem::take(&mut self.temps) {
            let _ = writeln!(temps, "    {} {};", t, n);
        }
        let (open, close) = if self.sub_waits(sp.sub) {
            ("task automatic", "endtask")
        } else {
            ("function automatic void", "endfunction")
        };
        let _ = write!(
            self.sub_items,
            "  {} {}({});\n{}{}{}{}  {}\n",
            open,
            self.spec_name(n),
            params.join(", "),
            locals,
            temps,
            inits,
            stmts,
            close
        );
        for (o, old) in saved_map {
            match old {
                Some(r) => {
                    self.sig_map.insert((sp.inst, o), r);
                }
                None => {
                    self.sig_map.remove(&(sp.inst, o));
                }
            }
        }
        self.temps = saved_temps;
        self.cur_proc = saved_proc;
        self.cur_ret = saved_ret;
        self.inst = saved_inst;
    }

    /// `x` with the signals it names read at their last values.
    fn ex_last(&mut self, x: &HExpr) -> String {
        let saved = std::mem::replace(&mut self.read_last, true);
        let v = self.ex(x);
        self.read_last = saved;
        v
    }

    // ---- waits and signal assignments -------------------------------------------

    /// `wait on S until C for T` (§10.2): suspend at a site sensitive to S
    /// with an optional deadline; resumed by the kernel on an event of S
    /// (then C must hold) or at the deadline.
    pub(super) fn wait(
        &mut self,
        on: &[HExpr],
        until: Option<&HExpr>,
        timeout: Option<&HExpr>,
        ind: usize,
        loc: &Loc,
    ) -> String {
        let pad = " ".repeat(ind);
        let Some(p) = self.cur_proc else {
            self.err(loc, "wait statements in subprograms are not supported yet");
            return String::new();
        };
        let conds = self.sensitivity(on);
        let site = self.sites[p].len();
        self.sites[p].push(Site { conds });
        let deadline = match timeout {
            Some(t) => {
                let tv = self.ex(t);
                format!("vh_deadline({})", tv)
            }
            None => "-64'sd1".into(),
        };
        let cond = match until {
            Some(c) => self.ex(c),
            None => "1".into(),
        };
        let mut out = String::new();
        let _ = writeln!(out, "{}vh_dl[{}] = {};", pad, p, deadline);
        let _ = writeln!(out, "{}forever begin", pad);
        let _ = writeln!(
            out,
            "{}  vh_site[{p}] = {site}; vh_tmo[{p}] = vh_dl[{p}]; vh_go[{p}] = 0; wait (vh_go[{p}]);",
            pad,
            p = p,
            site = site
        );
        let _ = writeln!(out, "{}  if (vh_tmoh[{}] || ({})) break;", pad, p, cond);
        let _ = writeln!(out, "{}end", pad);
        out
    }

    /// The event conditions of a sensitivity list.
    pub(super) fn sensitivity(&mut self, on: &[HExpr]) -> Vec<String> {
        let mut conds = Vec::new();
        for s in on {
            match self.sig_attr(s, "event") {
                Some(c) => {
                    if !conds.contains(&c) {
                        conds.push(c);
                    }
                }
                None => self.err(&s.loc, "this sensitivity is not supported yet"),
            }
        }
        conds
    }

    /// The driver an assignment target updates.
    fn target(&mut self, t: &HExpr) -> Option<Target> {
        let (sig, path) = self.target_path(t)?;
        if path.is_empty() {
            return Some(Target::Whole(sig));
        }
        let cov = self.path_cov(self.sigs[sig].ty, &path);
        Some(Target::Path(sig, path, cov))
    }

    /// projected waveform of this process's driver of s.
    pub(super) fn signal_assign(
        &mut self,
        target: &HExpr,
        delay: Option<&HDelay>,
        waves: &[HWave],
        ind: usize,
    ) -> String {
        let pad = " ".repeat(ind);
        let loc = target.loc.clone();
        let Some(p) = self.cur_proc else {
            self.err(
                &loc,
                "signal assignments in subprograms are not supported yet",
            );
            return String::new();
        };
        let Some(tg) = self.target(target) else {
            self.err(
                &loc,
                "an assignment to this part of a signal is not supported yet",
            );
            return String::new();
        };
        let (sig, path) = match tg {
            Target::Whole(s) => {
                self.add_driver(s, p, Cov::All, false);
                (s, None)
            }
            Target::Path(s, path, cov) => {
                self.add_driver(s, p, cov, true);
                (s, Some(path))
            }
        };
        // A driver of an out port starts with the port's default value
        // (§6.5.2, §14.7.2).
        if let HExprKind::Obj(o) = &target.kind
            && matches!(self.d.objects[*o].kind, ObjKind::Port(_))
            && self.d.objects[*o].init.is_some()
            && let Some(dr) = self.drivers.get_mut(&(sig, p))
        {
            dr.init.get_or_insert((*o, self.inst));
        }
        let mut out = String::new();
        let transport = matches!(delay, Some(HDelay::Transport));
        let reject = match delay {
            Some(HDelay::Inertial(Some(r))) => Some(self.ex(r)),
            _ => None,
        };
        let guarded = self.sig_kind(sig).is_some();
        for (i, w) in waves.iter().enumerate() {
            let t = match &w.after {
                Some(a) => self.ex(a),
                None => "64'sd0".into(),
            };
            let (val, nl) = match &w.value {
                Some(v) => (self.store_value(target, v), ", 0"),
                // A null transaction (§10.5.2.2): turns the driver off.
                None if path.is_none() => (format!("vh_dv{}_{}", sig, p), ", 1"),
                None => {
                    self.err(
                        &loc,
                        "null transactions to part of a signal are not supported yet",
                    );
                    continue;
                }
            };
            let nl = if guarded { nl } else { "" };
            // The first element of an inertial assignment rejects pulses
            // shorter than the reject limit (default: its delay).
            let (mode, rej) = if i == 0 && !transport {
                (1, reject.clone().unwrap_or_else(|| t.clone()))
            } else {
                (if i == 0 { 0 } else { 2 }, "64'sd0".into())
            };
            match &path {
                // A whole zero-delay assignment to a driver assigned by
                // parts too: pending values leaf by leaf (compiled), not the
                // whole-value function's queued transactions.
                None if t == "64'sd0"
                    && mode == 1
                    && !guarded
                    && self.drivers.get(&(sig, p)).is_some_and(|d| d.slots) =>
                {
                    let vt = self.erepr(target).sv();
                    let tmp = format!("vh_tv{}", self.tmp);
                    self.tmp += 1;
                    self.temps.push((tmp.clone(), vt));
                    let _ = writeln!(out, "{}{} = {};", pad, tmp, val);
                    let code = self.drive_path(sig, p, &[], target.ty, &tmp, (&t, &rej, mode), ind);
                    out.push_str(&code);
                }
                None if t == "64'sd0" && self.fast_driver(sig, p) => {
                    let _ = writeln!(
                        out,
                        "{pad}if (vh_qn{s}_{p} == 0) begin vh_pv{s}_{p} = {v}; vh_pend{s}_{p} = 1; end else vh_drv_{s}_{p}({v}, 64'sd0, {rej}, {mode});",
                        pad = pad,
                        s = sig,
                        p = p,
                        v = val,
                        rej = rej,
                        mode = mode
                    );
                }
                None => {
                    let _ = writeln!(
                        out,
                        "{}vh_drv_{}_{}({}, {}, {}, {}{});",
                        pad, sig, p, val, t, rej, mode, nl
                    );
                }
                Some(path) => {
                    // The value once, then a transaction per scalar leaf.
                    let vt = self.erepr(target).sv();
                    let tmp = format!("vh_tv{}", self.tmp);
                    self.tmp += 1;
                    self.temps.push((tmp.clone(), vt.clone()));
                    let _ = writeln!(out, "{}{} = {};", pad, tmp, val);
                    if let Some(DSel::Slice(_, n, _)) = path.last()
                        && !vt.starts_with("bit [")
                    {
                        let (f, line, _) = self.file_line(&loc);
                        let _ = writeln!(
                            out,
                            "{}if ({}.d.size() != {}) vh_fatal($sformatf(\"bound check failure at %s:%0d\", {}, {}));",
                            pad,
                            tmp,
                            n,
                            sv_string(&f),
                            line
                        );
                    }
                    let m = mode.to_string();
                    let code = self.drive_path(sig, p, path, target.ty, &tmp, (&t, &rej, mode), ind);
                    let _ = m;
                    out.push_str(&code);
                }
            }
        }
        out
    }

    /// `s <= force v` / `s <= release` (§10.5.2.1): a request applied in
    /// the next simulation cycle (§14.7.3.1); a forced signal keeps the
    /// forced value whatever its drivers do, a released one takes their
    /// value again. A port shares its actual's signal, so the force modes
    /// `in` and `out` act alike.
    pub(super) fn force(&mut self, target: &HExpr, value: Option<&HExpr>, ind: usize) -> String {
        let pad = " ".repeat(ind);
        let Some(s) = self.whole_sig(target) else {
            self.err(&target.loc, "forcing part of a signal is not supported yet");
            return String::new();
        };
        self.forced.insert(s);
        match value {
            Some(v) => {
                let x = self.store_value(target, v);
                format!(
                    "{pad}vh_s{s}_fnv = {x}; vh_s{s}_freq = 1; vh_s{s}_rreq = 0; vh_fpend = 1;\n",
                    pad = pad,
                    s = s,
                    x = x
                )
            }
            None => format!(
                "{pad}vh_s{s}_rreq = 1; vh_s{s}_freq = 0; vh_fpend = 1;\n",
                pad = pad,
                s = s
            ),
        }
    }

    pub(super) fn add_driver(&mut self, s: usize, p: usize, cov: Cov, slots: bool) {
        match self.drivers.get_mut(&(s, p)) {
            Some(d) => {
                d.cov.add(cov);
                d.slots |= slots;
            }
            None => {
                self.drivers.insert(
                    (s, p),
                    Driver {
                        cov,
                        slots,
                        init: None,
                    },
                );
            }
        }
    }

    // ---- the module -------------------------------------------------------------

    /// The resolution function of a signal's subtype: of the signal itself
    /// (`false`) or of each element (`true`).
    pub(super) fn resolution(&self, t: TypeId) -> Option<(SubId, bool)> {
        let mut cur = t;
        loop {
            match &self.d.types[cur].kind {
                TypeKind::Subtype {
                    resolution: Some(f),
                    ..
                } => return Some((*f, false)),
                TypeKind::Subtype { base, .. } => cur = *base,
                _ => break,
            }
        }
        if self.ndims(t) == 1
            && let Some(e) = self.d.element_subtype(t)
            && let Some((f, false)) = self.resolution(e)
        {
            return Some((f, true));
        }
        None
    }

    /// The objects an instance declares, in elaboration order: generics,
    /// constants, process variables.
    fn inst_objects(&self, inst: usize) -> Vec<ObjId> {
        let a = &self.d.archs[self.insts[inst].arch];
        let mut v: Vec<ObjId> = a.generics.clone();
        v.extend(a.constants.iter().copied());
        v
    }

    pub(super) fn module(&mut self, top: usize) -> String {
        let d = self.d;
        self.elaborate(top);
        // A root instantiated from SV: its ports.
        let ports = if self.boundary.is_some() {
            self.boundary_ports(top)
        } else {
            String::new()
        };
        // GUARD signals of guarded blocks (§11.2): implicit signals.
        for si in 0..self.sigs.len() {
            if let Some(e) = d.guards.get(&self.sigs[si].obj) {
                self.sigs[si].implicit = Some(self.imps.len());
                self.imps.push(Imp {
                    kind: ImpKind::Guard(e.clone(), self.sigs[si].inst),
                    sig: si,
                    trig: String::new(),
                    value: String::new(),
                    delay: String::new(),
                    deps: Vec::new(),
                });
            }
        }
        let nprocs = self.procs.len();
        let np = nprocs.max(1);
        self.sites = (0..nprocs).map(|_| Vec::new()).collect();
        let mut elab = String::new();
        let mut decls = String::new();
        // Package objects (analysis order).
        let mut pkg_objs: Vec<ObjId> = Vec::new();
        for (p, _) in d.packages.values() {
            pkg_objs.extend(p.objects.iter().copied());
        }
        pkg_objs.sort();
        // A deferred constant is listed by its package and its body.
        pkg_objs.dedup();
        self.pkg_objs = pkg_objs.iter().copied().collect();
        self.temps.clear();
        let mut objs: Vec<(usize, ObjId)> = pkg_objs
            .iter()
            .filter(|o| !matches!(d.objects[**o].kind, ObjKind::Signal))
            .map(|o| (GLOBAL, *o))
            .collect();
        for i in 0..self.insts.len() {
            for o in self.inst_objects(i) {
                objs.push((i, o));
            }
        }
        for (inst, ai, pi) in self.procs.clone() {
            for o in &d.archs[ai].processes[pi].locals {
                objs.push((inst, *o));
            }
        }
        for (inst, o) in objs {
            let info = d.objects[o].clone();
            self.inst = if inst == GLOBAL { 0 } else { inst };
            let r = self.repr(info.ty, &info.loc);
            let name = self.obj_name(o);
            // A constant with a static scalar or packed value: a parameter,
            // which compiled code folds instead of reading a variable.
            let param_able = match (&r, &info.static_val) {
                (Repr::Pk(..), Some(Value::Array(_))) => true,
                (Repr::Arr(..) | Repr::Rec(_) | Repr::Pk(..), _) => false,
                (_, Some(Value::Array(_) | Value::Record(_) | Value::Null)) => false,
                (_, Some(_)) => true,
                _ => false,
            };
            if info.kind == ObjKind::Constant && param_able {
                let v = info.static_val.clone().unwrap();
                let lit = self.value(&v, info.ty, &info.loc);
                let _ = writeln!(decls, "  localparam {} {} = {};", r.sv(), name, lit);
                continue;
            }
            let _ = writeln!(decls, "  {} {};", r.sv(), name);
            // A sequential block's object: initialised when the block runs.
            if d.block_objs.contains(&o) {
                continue;
            }
            // A generic: the instance's actual, else its default.
            let init = match info.kind {
                ObjKind::Generic => match self.insts[self.inst].generics.get(&o).cloned() {
                    Some((e, pinst)) => Some((e, pinst)),
                    None => info.init.clone().map(|e| (e, self.inst)),
                },
                _ => info.init.clone().map(|e| (e, self.inst)),
            };
            let v = match init {
                Some((i, ctx)) => {
                    let target = HExpr {
                        kind: HExprKind::Obj(o),
                        ty: info.ty,
                        loc: info.loc.clone(),
                    };
                    let saved = std::mem::replace(&mut self.inst, ctx);
                    let v = self.store_value_init(&target, &i);
                    self.inst = saved;
                    v
                }
                None => self.default_value(info.ty, &info.loc),
            };
            let flushed = self.flush_pre(4);
            elab.push_str(&flushed);
            let _ = writeln!(elab, "    {} = {};", name, v);
            if matches!(info.kind, ObjKind::File) {
                let open = self.file_decl_open(o, 4);
                elab.push_str(&open);
            }
        }
        // Signals.
        let sigs = self.sigs.clone();
        for (si, s) in sigs.iter().enumerate() {
            let info = d.objects[s.obj].clone();
            self.inst = if s.inst == GLOBAL { 0 } else { s.inst };
            let r = self.repr(s.ty, &info.loc);
            let _ = writeln!(
                decls,
                "  {t} vh_s{s};\n  bit vh_s{s}_ev, vh_s{s}_act; {t} vh_s{s}_last; longint vh_s{s}_lev, vh_s{s}_lact;",
                s = si,
                t = r.sv()
            );
            let target = HExpr {
                kind: HExprKind::Obj(s.obj),
                ty: s.ty,
                loc: info.loc.clone(),
            };
            let init = match &s.init_expr {
                Some((e, ctx)) => Some((e.clone(), *ctx)),
                None => info.init.clone().map(|e| (e, self.inst)),
            };
            let v = match init {
                Some((i, ctx)) => {
                    let saved = std::mem::replace(&mut self.inst, ctx);
                    let v = self.store_value_init(&target, &i);
                    self.inst = saved;
                    v
                }
                None => self.default_value(s.ty, &info.loc),
            };
            let flushed = self.flush_pre(4);
            elab.push_str(&flushed);
            let _ = writeln!(
                elab,
                "    vh_s{s} = {v};\n    vh_s{s}_last = vh_s{s}; vh_s{s}_lev = -64'sd9223372036854775807; vh_s{s}_lact = vh_s{s}_lev;",
                s = si,
                v = v
            );
        }
        // Temporaries of the initial values, declared in vh_elab.
        let mut elab_temps = String::new();
        for (n, t) in std::mem::take(&mut self.temps) {
            let _ = writeln!(elab_temps, "    {} {};", t, n);
        }
        // Processes.
        let mut procs = String::new();
        // A process with a sensitivity list cannot wait (§11.3): it is a
        // function the kernel calls.
        self.fprocs = self
            .procs
            .iter()
            .enumerate()
            .filter(|(_, (_, ai, pi))| {
                let p = &d.archs[*ai].processes[*pi];
                p.sens.is_some() && !p.postponed
            })
            .map(|(gp, _)| gp)
            .collect();
        // A discovery pass over the process bodies: the drivers (and
        // whether one assigns parts, which decides its form) must be known
        // before an assignment is emitted.
        let nerr = self.errors.len();
        for (gp, (inst, ai, pi)) in self.procs.clone().into_iter().enumerate() {
            let p = d.archs[ai].processes[pi].clone();
            self.inst = inst;
            self.cur_proc = Some(gp);
            self.temps.clear();
            let _ = self.stmts(&p.stmts, 4);
            self.pre_stmts.clear();
        }
        self.sites = (0..nprocs).map(|_| Vec::new()).collect();
        self.drv_checks.clear();
        self.errors.truncate(nerr);
        for (gp, (inst, ai, pi)) in self.procs.clone().into_iter().enumerate() {
            let p = d.archs[ai].processes[pi].clone();
            self.inst = inst;
            self.cur_proc = Some(gp);
            self.temps.clear();
            self.proc_slow = false;
            let func = self.fprocs.contains(&gp);
            let body = self.stmts(&p.stmts, if func { 4 } else { 6 });
            let mut implicit = String::new();
            if let Some(sens) = &p.sens {
                let conds = self.sensitivity(sens);
                let site = self.sites[gp].len();
                self.sites[gp].push(Site { conds });
                let _ = writeln!(
                    implicit,
                    "      vh_site[{p}] = {site}; vh_tmo[{p}] = -64'sd1; vh_go[{p}] = 0; wait (vh_go[{p}]);",
                    p = gp,
                    site = site
                );
            }
            let mut temps = String::new();
            let mut slow = self.proc_slow;
            for (n, t) in std::mem::take(&mut self.temps) {
                // A temporary of a struct type: the body copies structs.
                if t.starts_with("vh_") {
                    slow = true;
                }
                let _ = writeln!(temps, "    {} {};", t, n);
            }
            let label = if p.label.is_empty() {
                format!("p{}", pi)
            } else {
                sv_ident(&p.label)
            };
            if func {
                let clk = if self.has_boundary() && self.clocked.contains(&gp) {
                    "    vh_clkd = 1;\n"
                } else {
                    ""
                };
                let body = format!("{}{}", clk, body);
                {
                    let _ = write!(
                        procs,
                        "  // process {label}\n  function automatic void vh_run{gp}();\n{temps}{body}  endfunction\n",
                        label = label,
                        gp = gp,
                        temps = temps,
                        body = body
                    );
                }
                if slow {
                    self.fproc_bodies
                        .push((gp, String::new(), format!("    vh_run{}();\n", gp)));
                } else {
                    self.fproc_bodies.push((gp, temps, body));
                }
                continue;
            }
            let _ = write!(
                procs,
                "  // process {label}\n  initial begin : vh_p{gp}_{label}\n{temps}    wait (vh_go[{gp}]);\n    forever begin\n{body}{implicit}    end\n  end\n",
                label = label,
                gp = gp,
                temps = temps,
                body = body,
                implicit = implicit
            );
        }
        self.cur_proc = None;
        self.inst = 0;
        let mut lnk = String::new();
        for n in 0..self.links.len() {
            let f = self.link_sv(n);
            lnk.push_str(&f);
        }
        let mut imp_fns = String::new();
        for n in 0..self.imps.len() {
            if matches!(self.imps[n].kind, ImpKind::Guard(..)) {
                let f = self.guard_sv(n);
                imp_fns.push_str(&f);
            }
        }
        // Subprograms the design calls (transitively), and the procedures
        // lowered per process.
        self.lower_subprograms();
        // Drivers and signal updates (their resolution functions are
        // lowered with the subprograms).
        self.temps.clear();
        let drv = self.drivers_sv(&mut elab);
        // Temporaries of drivers' initial values (port defaults).
        for (n, t) in std::mem::take(&mut self.temps) {
            let _ = writeln!(elab_temps, "    {} {};", t, n);
        }
        let (upd, upd_sigs) = self.updates_sv();
        self.lower_subprograms();
        for n in 0..self.imps.len() {
            if !matches!(self.imps[n].kind, ImpKind::Guard(..)) {
                let f = self.imp_sv(n, &mut decls);
                imp_fns.push_str(&f);
            }
        }
        // 'driving and 'driving_value need a driver of the process.
        for (s, p, loc) in std::mem::take(&mut self.drv_checks) {
            if !self.drivers.contains_key(&(s, p)) {
                let name = self.d.objects[self.sigs[s].obj].name.clone();
                self.err(
                    &loc,
                    format!("the process has no driver of signal '{}'", name),
                );
            }
        }
        // Forced signals: the force state and pending requests.
        for s in self.forced.clone() {
            let sig = self.sigs[s].clone();
            let loc = self.d.objects[sig.obj].loc.clone();
            let t = self.repr(sig.ty, &loc).sv();
            let _ = writeln!(
                decls,
                "  bit vh_s{s}_frc, vh_s{s}_freq, vh_s{s}_rreq; {t} vh_s{s}_fnv;",
                s = s,
                t = t
            );
        }
        let k = self.kernel(&upd_sigs);

        // Assemble.
        let mut logic_defs = String::new();
        for name in self.logic_arrs.clone() {
            let er = self.arr_elem_sv(&name);
            logic_defs.push_str(
                &super::runtime::LOGIC_TEMPLATE
                    .replace("ARR", &name)
                    .replace("ELEM", &er),
            );
        }
        let arch = &d.archs[top];
        let mut m = String::new();
        match self.boundary.clone() {
            Some(name) => {
                let _ = writeln!(m, "module {}({});", name, ports);
            }
            None => {
                let _ = writeln!(m, "module {};", sv_ident(&arch.entity));
            }
        }
        let _ = writeln!(m, "  timeunit 1fs; timeprecision 1fs;");
        let _ = writeln!(
            m,
            "  localparam int VH_STOP_LEVEL = {};\n  localparam int VH_IEEE_ASSERTS = {};",
            self.opts.assert_level, self.opts.ieee_asserts
        );
        m.push_str(super::runtime::COMMON);
        // The STRING heap (TEXTIO lines).
        if self.textio {
            let st = self.d.std.string;
            let acc = self
                .d
                .types
                .iter()
                .position(|t| matches!(t.kind, TypeKind::Access(x) if self.d.base(x) == st));
            if let Some(a) = acc {
                let loc = self.d.objects[0].loc.clone();
                self.heap(a, &loc);
            }
        }
        m.push_str(&self.type_defs);
        m.push_str(&self.heap_defs);
        m.push_str(&self.prot_defs);
        m.push_str(&logic_defs);
        m.push_str(super::runtime::MATCHING);
        m.push_str(
            "  function automatic vh_a_u8 vh_str(string s);\n    byte unsigned t[];\n    t = new[s.len()];\n    for (int i = 0; i < s.len(); i++) t[i] = s.getc(i);\n    return vh_a_u8_from(1, 0, t);\n  endfunction\n  function automatic string vh_sv(vh_a_u8 a);\n    string s;\n    s = \"\";\n    for (int i = 0; i < a.d.size(); i++) s = {s, string'(a.d[i])};\n    return s;\n  endfunction\n  // A BIT_VECTOR in digits of w bits (§5.3.2.4), padded with zeros on the left.\n  function automatic vh_a_u8 vh_bvstr(vh_a_u8 v, int w);\n    byte unsigned t[];\n    longint n, nd, x, k;\n    n = v.d.size();\n    nd = (n + w - 1) / w;\n    t = new[nd];\n    for (longint i = 0; i < nd; i++) begin\n      x = 0;\n      for (int j = 0; j < w; j++) begin\n        k = i * w + j - (nd * w - n);\n        x = x * 2 + (k >= 0 ? v.d[k] : 0);\n      end\n      t[i] = x < 10 ? 48 + x : 55 + x;\n    end\n    return vh_a_u8_from(1, 0, t);\n  endfunction\n  function automatic longint vh_deadline(longint t);\n    if (t < 0) return -64'sd1;\n    if (t > 64'sd9223372036854775807 - longint'($time)) return -64'sd1;\n    return longint'($time) + t;\n  endfunction\n",
        );
        let _ = writeln!(
            m,
            "  bit vh_go [0:{n}];\n  bit vh_pres [0:{n}];\n  bit vh_post [0:{n}];\n  bit vh_tmoh [0:{n}];\n  longint vh_tmo [0:{n}];\n  longint vh_dl [0:{n}];\n  int vh_site [0:{n}];\n  bit vh_stop, vh_fpend;",
            n = np
        );
        m.push_str(&self.tx_defs);
        let files = self.files_sv();
        m.push_str(&files);
        let bnd = self.boundary_sv();
        m.push_str(&bnd);
        m.push_str(&self.sv_items);
        m.push_str(&decls);
        m.push_str(&self.lit_items);
        let tio = self.textio_sv();
        m.push_str(&tio);
        m.push_str(&drv);
        m.push_str(&upd);
        m.push_str(&self.sub_items);
        m.push_str(&lnk);
        m.push_str(&imp_fns);
        let _ = write!(
            m,
            "  function automatic void vh_elab();\n{}    for (int p = 0; p <= {}; p++) vh_tmo[p] = -64'sd1;\n{}  endfunction\n",
            elab_temps, np, elab
        );
        m.push_str(&procs);
        m.push_str(&k);
        m.push_str("endmodule\n");
        m
    }

    fn lower_subprograms(&mut self) {
        loop {
            if let Some(n) = self.spec_todo.pop() {
                self.spec_sv(n);
                continue;
            }
            if let Some(k) = self.pspec_todo.pop() {
                let (s, inst) = (self.pspecs[k].sub, self.pspecs[k].inst);
                let saved = std::mem::replace(&mut self.inst, inst);
                self.subprogram_with(s, Some(k));
                self.inst = saved;
                continue;
            }
            let Some((s, inst)) = self.subs_todo.pop() else {
                break;
            };
            if self.subs_done.insert((s, inst)) {
                let saved = std::mem::replace(&mut self.inst, inst);
                self.subprogram(s);
                self.inst = saved;
            }
        }
    }

    /// The update function of GUARD (implicit signal `n`, §11.2): the
    /// guard expression, recomputed in every cycle.
    fn guard_sv(&mut self, n: usize) -> String {
        let ImpKind::Guard(e, inst) = self.imps[n].kind.clone() else {
            return String::new();
        };
        let r = self.imps[n].sig;
        let saved = std::mem::replace(&mut self.inst, inst);
        let saved_proc = self.cur_proc.take();
        self.temps.clear();
        let mark = self.imp_refs.len();
        let v = self.ex(&e);
        let deps: Vec<usize> = self.imp_refs.drain(mark..).filter(|&x| x != r).collect();
        self.imps[n].deps = deps;
        let pre = self.flush_pre(4);
        let mut temps = String::new();
        for (name, t) in std::mem::take(&mut self.temps) {
            let _ = writeln!(temps, "    {} {};", t, name);
        }
        self.inst = saved;
        self.cur_proc = saved_proc;
        let t = self.repr(e.ty, &e.loc).sv();
        format!(
            "  function automatic void vh_imp{n}(bit init);\n    {t} nv;\n{temps}{pre}    nv = {v};\n    if (init) begin vh_s{r} = nv; vh_s{r}_last = nv; end\n    else if (nv != vh_s{r}) begin vh_s{r}_last = vh_s{r}; vh_s{r} = nv; vh_s{r}_ev = 1; vh_s{r}_act = 1; vh_s{r}_lev = $time; end\n  endfunction\n",
            n = n,
            t = t,
            temps = temps,
            pre = pre,
            v = v,
            r = r
        )
    }

    /// The declarations (into `decls`) and the update function of
    /// implicit signal `n` (§16.2.4): `'stable(T)`/`'quiet(T)` turn FALSE
    /// in the cycle of an event/activity of the prefix and TRUE T later;
    /// `'delayed(T)` follows the prefix's events T later (transport);
    /// `'transaction` toggles in each cycle the prefix is active.
    fn imp_sv(&mut self, n: usize, decls: &mut String) -> String {
        let im = self.imps[n].clone();
        let r = im.sig;
        let sig = self.sigs[r].clone();
        let loc = self.d.objects[sig.obj].loc.clone();
        let rp = self.repr(sig.ty, &loc);
        let t = rp.sv();
        let _ = writeln!(
            decls,
            "  {t} vh_s{r};\n  bit vh_s{r}_ev, vh_s{r}_act; {t} vh_s{r}_last; longint vh_s{r}_lev, vh_s{r}_lact;",
            t = t,
            r = r
        );
        let init_common = format!(
            "vh_s{r}_last = vh_s{r}; vh_s{r}_lev = -64'sd9223372036854775807; vh_s{r}_lact = vh_s{r}_lev;",
            r = r
        );
        let ev = format!(
            "    if (!{}) begin vh_s{r}_last = o; vh_s{r}_ev = 1; vh_s{r}_lev = $time; end\n",
            self.eq_expr(&rp, &format!("vh_s{}", r), "o"),
            r = r
        );
        match im.kind {
            ImpKind::Stable | ImpKind::Quiet => {
                let _ = writeln!(decls, "  longint vh_s{}_due;", r);
                format!(
                    "  function automatic void vh_imp{n}(bit init);\n    {t} o;\n    if (init) begin vh_s{r} = 1; vh_s{r}_due = -64'sd1; {ic} return; end\n    o = vh_s{r};\n    if (vh_s{r}_due >= 0 && vh_s{r}_due <= $time) begin vh_s{r}_due = -64'sd1; vh_s{r} = 1; vh_s{r}_act = 1; end\n    if ({trig}) begin vh_s{r} = 0; vh_s{r}_act = 1; vh_s{r}_due = vh_deadline({d}); end\n{ev}  endfunction\n",
                    n = n,
                    t = t,
                    r = r,
                    ic = init_common,
                    trig = im.trig,
                    d = im.delay,
                    ev = ev
                )
            }
            ImpKind::Delayed => {
                let _ = writeln!(
                    decls,
                    "  longint vh_s{r}_qt[$];\n  {t} vh_s{r}_qv[$];",
                    r = r,
                    t = t
                );
                format!(
                    "  function automatic void vh_imp{n}(bit init);\n    {t} o;\n    longint tt;\n    longint qt[$];\n    {t} qv[$];\n    if (init) begin vh_s{r} = {v}; {ic} return; end\n    o = vh_s{r};\n    qt = vh_s{r}_qt;\n    qv = vh_s{r}_qv;\n    if (qt.size() > 0 && qt[0] <= $time) begin void'(qt.pop_front()); vh_s{r} = qv.pop_front(); vh_s{r}_act = 1; end\n    if ({trig}) begin\n      tt = vh_deadline({d});\n      if (tt >= 0) begin\n        while (qt.size() > 0 && qt[qt.size()-1] >= tt) begin void'(qt.pop_back()); void'(qv.pop_back()); end\n        qt.push_back(tt);\n        qv.push_back({v});\n      end\n    end\n    vh_s{r}_qt = qt;\n    vh_s{r}_qv = qv;\n{ev}  endfunction\n",
                    n = n,
                    t = t,
                    r = r,
                    v = im.value,
                    ic = init_common,
                    trig = im.trig,
                    d = im.delay,
                    ev = ev
                )
            }
            ImpKind::Transaction => format!(
                "  function automatic void vh_imp{n}(bit init);\n    if (init) begin vh_s{r} = 1; {ic} return; end\n    if ({trig}) begin vh_s{r}_last = vh_s{r}; vh_s{r} = 1 - vh_s{r}; vh_s{r}_ev = 1; vh_s{r}_act = 1; vh_s{r}_lev = $time; end\n  endfunction\n",
                n = n,
                r = r,
                ic = init_common,
                trig = im.trig
            ),
            ImpKind::Guard(..) => String::new(),
        }
    }

    /// Implicit signals in update order: each after those it reads.
    fn imp_order(&self) -> Vec<usize> {
        let mut order = Vec::new();
        let mut state = vec![0u8; self.imps.len()];
        fn visit(lw: &Lw, n: usize, state: &mut [u8], order: &mut Vec<usize>) {
            if state[n] != 0 {
                return;
            }
            state[n] = 1;
            for &d in &lw.imps[n].deps {
                if let Some(m) = lw.sigs[d].implicit {
                    visit(lw, m, state, order);
                }
            }
            state[n] = 2;
            order.push(n);
        }
        for n in 0..self.imps.len() {
            visit(self, n, &mut state, &mut order);
        }
        order
    }

    /// The drivers: transaction queues and the procedures updating their
    /// projected waveforms (§10.5.2.2).
    fn drivers_sv(&mut self, elab: &mut String) -> String {
        let drv = self.drivers_body(elab);
        // The leaf code's variables: the leaf and index of a pending value,
        // and the loop variables of whole-value assignments to parts.
        let mut head = String::from("  longint vh_lk, vh_lkk;\n  int vh_pi, vh_pj;\n");
        for v in &self.leaf_vars {
            let _ = writeln!(head, "  longint {};", v);
        }
        head + &drv
    }

    fn drivers_body(&mut self, elab: &mut String) -> String {
        let mut drv = String::new();
        let drivers: Vec<((usize, usize), Driver)> =
            self.drivers.iter().map(|(k, v)| (*k, v.clone())).collect();
        for ((s, p), dr) in &drivers {
            let sig = self.sigs[*s].clone();
            let loc = self.d.objects[sig.obj].loc.clone();
            let r = self.repr(sig.ty, &loc);
            let t = r.sv();
            let guarded = self.sig_kind(*s).is_some();
            if guarded {
                // Whether the driver is on (§14.7.3.2): a null transaction
                // turns it off.
                let _ = writeln!(drv, "  bit vh_don{}_{};", s, p);
                let _ = writeln!(elab, "    vh_don{}_{} = 1;", s, p);
            }
            if *p >= PSEUDO {
                // The driver of a port link: a value only.
                let _ = writeln!(drv, "  {} vh_dv{}_{};", t, s, p);
            } else if !dr.slots {
                // Parallel queues of transaction times and values (a queue
                // of structs holding a struct does not round-trip in the
                // simulator); for a guarded signal also null flags.
                let eq = self.eq_expr(&r, "qv[k]", "v");
                let (g_decl, g_param, g_local, g_get, g_pop, g_eq, g_del, g_push, g_put) =
                    if guarded {
                        (
                            format!("  bit vh_dn{s}_{p}[$];\n", s = s, p = p),
                            ", bit nl",
                            "    bit qn[$];\n",
                            format!("    qn = vh_dn{s}_{p};\n", s = s, p = p),
                            " void'(qn.pop_back());",
                            format!("qn[k] == nl && (nl || {})", eq),
                            " qn.delete(k);",
                            "    qn.push_back(nl);\n",
                            format!("    vh_dn{s}_{p} = qn;\n", s = s, p = p),
                        )
                    } else {
                        (
                            String::new(),
                            "",
                            "",
                            String::new(),
                            "",
                            eq.clone(),
                            "",
                            "",
                            String::new(),
                        )
                    };
                if !guarded {
                    // A zero-delay assignment to an empty waveform is kept
                    // as a pending value (no queue); a later transaction
                    // queues it first. `vh_qn` mirrors the queue's length.
                    let tx = self.whole_tx(&r);
                    let _ = write!(
                        drv,
                        "  longint vh_dt{s}_{p}[$];\n  {t} vh_dq{s}_{p}[$];\n  {t} vh_dv{s}_{p};\n  bit vh_pend{s}_{p};\n  {t} vh_pv{s}_{p};\n  int vh_qn{s}_{p};\n  function automatic void vh_drv_{s}_{p}({t} v, longint after, longint rej, int mode);\n    if (vh_pend{s}_{p}) begin {tx}(vh_dt{s}_{p}, vh_dq{s}_{p}, vh_pv{s}_{p}, 64'sd0, 64'sd0, 0); vh_pend{s}_{p} = 0; end\n    {tx}(vh_dt{s}_{p}, vh_dq{s}_{p}, v, after, rej, mode);\n    vh_qn{s}_{p} = vh_dt{s}_{p}.size();\n  endfunction\n",
                        s = s,
                        p = p,
                        t = t,
                        tx = tx
                    );
                } else {
                let _ = write!(
                    drv,
                    "  longint vh_dt{s}_{p}[$];\n  {t} vh_dq{s}_{p}[$];\n{g_decl}  {t} vh_dv{s}_{p};\n  int vh_qn{s}_{p};\n  // Update the projected output waveform (§10.5.2.2): mode 0 transport,\n  // 1 inertial first element (reject limit), 2 later elements.\n  function automatic void vh_drv_{s}_{p}({t} v, longint after, longint rej, int mode{g_param});\n    longint tt;\n    longint qt[$];\n    {t} qv[$];\n{g_local}    int k;\n    tt = longint'($time) + after;\n    qt = vh_dt{s}_{p};\n    qv = vh_dq{s}_{p};\n{g_get}    while (qt.size() > 0 && qt[qt.size()-1] >= tt) begin void'(qt.pop_back()); void'(qv.pop_back());{g_pop} end\n    if (mode == 1) begin\n      // Pulse rejection: of the old transactions in [tt - rej, tt), keep\n      // the run immediately before the new one that has its value.\n      k = qt.size() - 1;\n      while (k >= 0 && qt[k] >= tt - rej && ({g_eq})) k--;\n      while (k >= 0 && qt[k] >= tt - rej) begin qt.delete(k); qv.delete(k);{g_del} k--; end\n    end\n    qt.push_back(tt);\n    qv.push_back(v);\n{g_push}    vh_dt{s}_{p} = qt;\n    vh_dq{s}_{p} = qv;\n    vh_qn{s}_{p} = qt.size();\n{g_put}  endfunction\n",
                    t = t,
                    s = s,
                    p = p,
                    g_decl = g_decl,
                    g_param = g_param,
                    g_local = g_local,
                    g_get = g_get,
                    g_pop = g_pop,
                    g_eq = g_eq,
                    g_del = g_del,
                    g_push = g_push,
                    g_put = g_put
                );
                }
            } else {
                match self.slot_driver_sv(*s, *p, &t, &loc, guarded) {
                    Some(d) => drv.push_str(&d),
                    None => {
                        self.err(
                            &loc,
                            "an assignment to part of a signal whose bounds are not static is not supported yet",
                        );
                        continue;
                    }
                }
            }
            match dr.init {
                Some((o, inst)) => {
                    let info = self.d.objects[o].clone();
                    let target = HExpr {
                        kind: HExprKind::Obj(o),
                        ty: info.ty,
                        loc: info.loc.clone(),
                    };
                    let saved = std::mem::replace(&mut self.inst, inst);
                    let v = self.store_value_init(&target, info.init.as_ref().unwrap());
                    self.inst = saved;
                    let pre = self.flush_pre(4);
                    elab.push_str(&pre);
                    let _ = writeln!(elab, "    vh_dv{s}_{p} = {v};", s = s, p = p, v = v);
                }
                None => {
                    let _ = writeln!(elab, "    vh_dv{s}_{p} = vh_s{s};", s = s, p = p);
                }
            }
        }
        drv
    }

    /// Whether a signal takes its single whole driver's value directly.
    fn simple_sig(&self, s: usize, ds: &[(usize, Driver)]) -> bool {
        ds.len() == 1
            && !ds[0].1.slots
            && ds[0].1.cov == Cov::All
            && match self.resolution(self.sigs[s].ty) {
                None => true,
                // std_logic_1164.resolved of one value is that value (an
                // unguarded signal: a guarded one may have no driver on).
                Some((f, _)) => {
                    self.sig_kind(s).is_none()
                        && self.d.subprograms[f]
                            .path
                            .eq_ignore_ascii_case("ieee.std_logic_1164.resolved")
                }
            }
    }

    /// Whether signal `s` is an SV scalar (a packed vector included): the
    /// cycle block copies it; a struct is copied in a function (the
    /// simulator's compiled `always` blocks do not copy structs between
    /// module variables).
    fn sig_scalar(&self, s: usize) -> bool {
        let ty = self.sigs[s].ty;
        !matches!(
            self.d.types[self.base(ty)].kind,
            TypeKind::Array { .. } | TypeKind::Record(_)
        ) || self.pk_of(ty).is_some()
    }

    /// Whether driver (s, p) has the zero-delay fast path: a pending value
    /// instead of a queued transaction (whole, unguarded drivers of scalar
    /// signals).
    fn fast_driver(&self, s: usize, p: usize) -> bool {
        p < PSEUDO
            && self.sig_scalar(s)
            && self.sig_kind(s).is_none()
            && self.drivers.get(&(s, p)).is_some_and(|d| !d.slots)
    }

    fn sig_drivers(&self, s: usize) -> Vec<(usize, Driver)> {
        self.drivers
            .iter()
            .filter(|((x, _), _)| *x == s)
            .map(|((_, p), d)| (*p, d.clone()))
            .collect()
    }

    /// The update functions of signals computed from several drivers,
    /// parts, or a resolution function (§14.7.3.2): the new effective value,
    /// then the event. With `init`, the initial value only (§14.7.5.2).
    fn updates_sv(&mut self) -> (String, Vec<usize>) {
        let mut out = String::new();
        let mut list = Vec::new();
        for s in 0..self.sigs.len() {
            let ds = self.sig_drivers(s);
            if ds.is_empty() || self.simple_sig(s, &ds) {
                continue;
            }
            let sig = self.sigs[s].clone();
            let info = self.d.objects[sig.obj].clone();
            let r = self.repr(sig.ty, &info.loc);
            let res = self.resolution(sig.ty);
            let kind = self.sig_kind(s);
            let tsv = r.sv();
            let mut body = String::new();
            let any_slots = ds.iter().any(|(_, d)| d.slots);
            match (&r, res) {
                (_, Some((f, false))) if !any_slots => {
                    // A resolved signal: f over every driver's value.
                    let pt = self.d.objects[self.d.subprograms[f].params[0]].ty;
                    let (pname, per) = match self.repr(pt, &info.loc) {
                        Repr::Arr(n, e) => (n, e.sv()),
                        _ => continue,
                    };
                    self.need_sub(f);
                    let _ = writeln!(body, "    {} rv[];\n    {} nv;", per, tsv);
                    let _ = writeln!(body, "    rv = new[{}];", ds.len());
                    match kind {
                        None => {
                            for (i, (p, _)) in ds.iter().enumerate() {
                                let _ = writeln!(body, "    rv[{}] = vh_dv{}_{};", i, s, p);
                            }
                            let _ = writeln!(
                                body,
                                "    nv = {}({}_mk(0, {}, 0, rv));",
                                self.sub_name(f),
                                pname,
                                ds.len() as i64 - 1
                            );
                        }
                        Some(k) => {
                            // A guarded signal: the drivers that are on;
                            // with none, a register keeps its value
                            // (§14.7.3.2).
                            let _ = writeln!(body, "    {} ra[];\n    int c;\n    c = 0;", per);
                            for (p, _) in &ds {
                                let _ = writeln!(
                                    body,
                                    "    if (vh_don{s}_{p}) begin rv[c] = vh_dv{s}_{p}; c++; end",
                                    s = s,
                                    p = p
                                );
                            }
                            let _ = writeln!(
                                body,
                                "    ra = new[c];\n    for (int j = 0; j < c; j++) ra[j] = rv[j];"
                            );
                            let call =
                                format!("{}({}_mk(0, c - 1, 0, ra))", self.sub_name(f), pname);
                            if k == SignalKind::Register {
                                let _ = writeln!(body, "    nv = c == 0 ? vh_s{} : {};", s, call);
                            } else {
                                let _ = writeln!(body, "    nv = {};", call);
                            }
                        }
                    }
                }
                (Repr::Arr(..) | Repr::Rec(_) | Repr::Pk(..), _) => {
                    // Scalar by scalar (§14.7.3.2).
                    let Some(b) = self.leaf_update_body(s, &ds, &tsv, &info, kind) else {
                        continue;
                    };
                    body.push_str(&b);
                }
                _ => {
                    self.err(
                        &info.loc,
                        format!("signal '{}' has several drivers", info.name),
                    );
                    continue;
                }
            }
            let eq = self.eq_expr(&r, "nv", &format!("vh_s{}", s));
            let _ = write!(
                out,
                "  function automatic void vh_upd{s}(bit init);\n{body}    if (init) begin vh_s{s} = nv; vh_s{s}_last = nv; end\n    else if (!{eq}) begin vh_s{s}_last = vh_s{s}; vh_s{s} = nv; vh_s{s}_ev = 1; vh_s{s}_lev = $time; end\n  endfunction\n",
                s = s,
                body = body,
                eq = eq
            );
            list.push(s);
        }
        (out, list)
    }

    /// The kernel: the VHDL simulation cycle (§14.7.5). The work of a cycle
    /// (the update phase, the resumption scan with the sensitized
    /// processes' bodies, the time of the next cycle) is one `always`
    /// block, which the simulator compiles; the kernel thread only
    /// triggers it, hands control to processes that wait, and advances
    /// time. A mixed design's eager evaluation calls the same phases as
    /// functions.
    fn kernel(&mut self, upd_sigs: &[usize]) -> String {
        let nprocs = self.procs.len();
        let drivers: Vec<((usize, usize), Driver)> =
            self.drivers.iter().map(|(k, v)| (*k, v.clone())).collect();
        let post: Vec<usize> = (0..nprocs)
            .filter(|&p| {
                let (_, ai, pi) = self.procs[p];
                self.d.archs[ai].processes[pi].postponed
            })
            .collect();
        let imp_order = self.imp_order();
        let fp = self.fprocs.clone();
        let boundary = self.has_boundary();
        let order = self.update_order();
        let mut k = String::new();
        // The kernel's state: the cycle block's trigger and acknowledgement,
        // the initialization passes, the scan's start and the process it
        // hands over, the next cycle's time.
        let _ = writeln!(k, "  bit vh_tick, vh_tock;\n  int vh_from, vh_r;\n  longint vh_nxt;\n  // The current time, published by the kernel thread: `$time` in the\n  // cycle block would be an expression the simulator interprets.\n  longint vh_now;");

        // ---- the time of the next simulation cycle (§14.7.5.3 g), into vh_n.
        let mut nx = String::new();
        for ((s, p), dr) in drivers.iter().filter(|((_, p), _)| *p < PSEUDO) {
            if dr.slots {
                nx.push_str(&self.slot_driver_next(*s, *p).replace("n = ", "vh_n = ").replace("(n < 0", "(vh_n < 0").replace("< n)", "< vh_n)"));
                continue;
            }
            if self.fast_driver(*s, *p) {
                let _ = writeln!(
                    nx,
                    "    if (vh_pend{s}_{p}) vh_n = vh_now; else if (vh_qn{s}_{p} > 0 && (vh_n < 0 || vh_dt{s}_{p}[0] < vh_n)) vh_n = vh_dt{s}_{p}[0];",
                    s = s,
                    p = p
                );
            } else {
                let _ = writeln!(
                    nx,
                    "    if (vh_qn{s}_{p} > 0 && (vh_n < 0 || vh_dt{s}_{p}[0] < vh_n)) vh_n = vh_dt{s}_{p}[0];",
                    s = s,
                    p = p
                );
            }
        }
        let _ = writeln!(
            nx,
            "    for (int p = 0; p < {}; p++) if (vh_tmo[p] >= 0 && (vh_n < 0 || vh_tmo[p] < vh_n)) vh_n = vh_tmo[p];",
            nprocs
        );
        for im in &self.imps {
            match im.kind {
                ImpKind::Stable | ImpKind::Quiet => {
                    let _ = writeln!(
                        nx,
                        "    if (vh_s{r}_due >= 0 && (vh_n < 0 || vh_s{r}_due < vh_n)) vh_n = vh_s{r}_due;",
                        r = im.sig
                    );
                }
                ImpKind::Delayed => {
                    let _ = writeln!(
                        nx,
                        "    if (vh_s{r}_qt.size() > 0 && (vh_n < 0 || vh_s{r}_qt[0] < vh_n)) vh_n = vh_s{r}_qt[0];",
                        r = im.sig
                    );
                }
                _ => {}
            }
        }
        // Force and release requests take effect in the next cycle.
        let _ = writeln!(nx, "    if (vh_fpend && (vh_n < 0 || vh_now < vh_n)) vh_n = vh_now;");
        let _ = write!(
            k,
            "  function automatic longint vh_next();\n    longint vh_n;\n    vh_n = -64'sd1;\n{}    return vh_n;\n  endfunction\n",
            nx
        );

        // ---- the update phase (§14.7.3, §14.7.5.3 b, c), as text.
        let mut ub = String::new();
        for s in 0..self.sigs.len() {
            let _ = writeln!(ub, "    vh_s{s}_ev = 0; vh_s{s}_act = 0;", s = s);
        }
        let _ = writeln!(ub, "    vh_fpend = 0;");
        ub.push_str(&self.boundary_sample("    "));
        for ((s, p), dr) in drivers.iter().filter(|((_, p), _)| *p < PSEUDO) {
            if dr.slots {
                ub.push_str(&self.slot_driver_due(*s, *p, "    "));
            } else if self.fast_driver(*s, *p) {
                let _ = writeln!(
                    ub,
                    "    if (vh_pend{s}_{p}) begin vh_dv{s}_{p} = vh_pv{s}_{p}; vh_pend{s}_{p} = 0; vh_s{s}_act = 1; end else if (vh_qn{s}_{p} > 0 && vh_dt{s}_{p}[0] <= vh_now) begin void'(vh_dt{s}_{p}.pop_front()); vh_dv{s}_{p} = vh_dq{s}_{p}.pop_front(); vh_qn{s}_{p}--; vh_s{s}_act = 1; end",
                    s = s,
                    p = p
                );
            } else {
                let on = if self.sig_kind(*s).is_some() {
                    format!(" vh_don{s}_{p} = !vh_dn{s}_{p}.pop_front();", s = s, p = p)
                } else {
                    String::new()
                };
                let pop = format!(
                    "void'(vh_dt{s}_{p}.pop_front());{on} vh_dv{s}_{p} = vh_dq{s}_{p}.pop_front(); vh_qn{s}_{p}--; vh_s{s}_act = 1;",
                    s = s,
                    p = p,
                    on = on
                );
                let pop = if self.sig_scalar(*s) {
                    format!("begin {} end", pop)
                } else {
                    let _ = write!(
                        k,
                        "  function automatic void vh_pop{s}_{p}();
    {pop}
  endfunction
",
                        s = s,
                        p = p,
                        pop = pop
                    );
                    format!("vh_pop{}_{}();", s, p)
                };
                let _ = writeln!(
                    ub,
                    "    if (vh_qn{s}_{p} > 0 && vh_dt{s}_{p}[0] <= vh_now) {pop}",
                    s = s,
                    p = p,
                    pop = pop
                );
            }
        }
        let link_cond = |l: &Link| {
            if let Some(f) = l.foreign {
                format!("vh_fx{}", f)
            } else if l.sources.is_empty() {
                "0".to_string()
            } else {
                l.sources
                    .iter()
                    .map(|x| format!("vh_s{}_act", x))
                    .collect::<Vec<_>>()
                    .join(" || ")
            }
        };
        for &step in &order {
            // An in-port link: a part of its formal, after the formal's
            // update and the updates of what it reads.
            let s = match step {
                UpdStep::In(n) => {
                    let _ = writeln!(ub, "    if ({}) vh_lnk{}(0);", link_cond(&self.links[n]), n);
                    continue;
                }
                UpdStep::Sig(s) => s,
            };
            // Links into this signal: the driving values from converted or
            // partial out ports, before its update.
            for (n, l) in self.links.iter().enumerate() {
                if !l.inn && l.target.sig == s {
                    let _ = writeln!(ub, "    if ({}) vh_lnk{}();", link_cond(l), n);
                }
            }
            let ds = self.sig_drivers(s);
            // A forced signal keeps its forced value (§14.7.3.1).
            let unforced = if self.forced.contains(&s) {
                let sig = self.sigs[s].clone();
                let loc = self.d.objects[sig.obj].loc.clone();
                let r = self.repr(sig.ty, &loc);
                let eq = self.eq_expr(&r, &format!("vh_s{}_fnv", s), &format!("vh_s{}", s));
                let set = format!(
                    "vh_s{s}_last = vh_s{s}; vh_s{s} = vh_s{s}_fnv; vh_s{s}_ev = 1; vh_s{s}_lev = vh_now;",
                    s = s
                );
                let set = if self.sig_scalar(s) {
                    format!("if (!{}) begin {} end", eq, set)
                } else {
                    let _ = write!(
                        k,
                        "  function automatic void vh_setf{s}();\n    if (!{eq}) begin {set} end\n  endfunction\n",
                        s = s,
                        eq = eq,
                        set = set
                    );
                    format!("vh_setf{}();", s)
                };
                let _ = writeln!(
                    ub,
                    "    if (vh_s{s}_freq) begin vh_s{s}_freq = 0; vh_s{s}_frc = 1; vh_s{s}_act = 1; {set} end\n    if (vh_s{s}_rreq) begin vh_s{s}_rreq = 0; vh_s{s}_frc = 0; vh_s{s}_act = 1; end",
                    s = s,
                    set = set
                );
                format!(" && !vh_s{}_frc", s)
            } else {
                String::new()
            };
            if ds.is_empty() {
                continue;
            }
            if upd_sigs.contains(&s) {
                let _ = writeln!(
                    ub,
                    "    if (vh_s{s}_act{u}) vh_upd{s}(0);",
                    s = s,
                    u = unforced
                );
                continue;
            }
            let sig = self.sigs[s].clone();
            let loc = self.d.objects[sig.obj].loc.clone();
            let r = self.repr(sig.ty, &loc);
            let ne = format!(
                "!({})",
                self.eq_expr(
                    &r,
                    &format!("vh_dv{}_{}", s, ds[0].0),
                    &format!("vh_s{}", s)
                )
            );
            let set = format!(
                "vh_s{s}_last = vh_s{s}; vh_s{s} = vh_dv{s}_{p}; vh_s{s}_ev = 1; vh_s{s}_lev = vh_now;",
                s = s,
                p = ds[0].0
            );
            // A struct: compared and copied in a function (the compiled
            // cycle block neither copies structs nor passes them).
            let set = if self.sig_scalar(s) {
                format!("if ({}) begin {} end", ne, set)
            } else {
                let _ = write!(
                    k,
                    "  function automatic void vh_set{s}();\n    if ({ne}) begin {set} end\n  endfunction\n",
                    s = s,
                    ne = ne,
                    set = set
                );
                format!("vh_set{}();", s)
            };
            let _ = writeln!(
                ub,
                "    if (vh_s{s}_act{u}) {set}",
                s = s,
                u = unforced,
                set = set
            );
        }
        // Implicit signals (§14.7.5.3 c).
        for &n in &imp_order {
            let _ = writeln!(ub, "    vh_imp{}(0);", n);
        }
        for s in self.need_lact.clone() {
            let _ = writeln!(ub, "    if (vh_s{s}_act) vh_s{s}_lact = vh_now;", s = s);
        }
        ub.push_str(&self.boundary_write(false, "    "));
        if boundary {
            let _ = write!(
                k,
                "  // The update phase of a simulation cycle (§14.7.3, §14.7.5.3 b, c).\n  function automatic void vh_update();\n{}  endfunction\n",
                ub
            );
        }

        // ---- the resumption of processes (§14.7.5.3 e): the conditions.
        let mut conds: Vec<Option<String>> = Vec::new();
        for pi in 0..nprocs {
            let mut c = Vec::new();
            if !fp.contains(&pi) {
                c.push(format!(
                    "(vh_tmo[{p}] >= 0 && vh_tmo[{p}] <= vh_now)",
                    p = pi
                ));
            }
            for (si, site) in self.sites[pi].iter().enumerate() {
                if site.conds.is_empty() {
                    continue;
                }
                if fp.contains(&pi) {
                    c.push(format!("({})", site.conds.join(" || ")));
                } else {
                    c.push(format!(
                        "(vh_site[{}] == {} && ({}))",
                        pi,
                        si,
                        site.conds.join(" || ")
                    ));
                }
            }
            conds.push(if c.is_empty() { None } else { Some(c.join(" || ")) });
        }
        if boundary {
            // The eager path's function form: a process with a sensitivity
            // list runs here; one that waits is handed to the kernel (its
            // index is returned; -1 when none is left).
            let _ = writeln!(
                k,
                "  function automatic int vh_resume(int from);"
            );
            for (pi, c) in conds.iter().enumerate() {
                let Some(c) = c else { continue };
                if post.contains(&pi) {
                    let _ = writeln!(
                        k,
                        "    if (from <= {p} && !vh_go[{p}] && !vh_pres[{p}] && ({c})) begin vh_tmoh[{p}] = (vh_tmo[{p}] >= 0 && vh_tmo[{p}] <= vh_now); vh_tmo[{p}] = -64'sd1; vh_pres[{p}] = 1; end",
                        p = pi,
                        c = c
                    );
                } else if fp.contains(&pi) {
                    let _ = writeln!(k, "    if (from <= {p} && ({c})) vh_run{p}();", p = pi, c = c);
                } else {
                    let _ = writeln!(
                        k,
                        "    if (from <= {p} && !vh_go[{p}] && ({c})) begin vh_tmoh[{p}] = (vh_tmo[{p}] >= 0 && vh_tmo[{p}] <= vh_now); vh_tmo[{p}] = -64'sd1; return {p}; end",
                        p = pi,
                        c = c
                    );
                }
            }
            let _ = writeln!(k, "    return -1;\n  endfunction");
            k.push_str(&self.eager_sv());
        }

        // ---- the cycle blocks: the update phase, the resumption scan from
        // vh_from, the next cycle's time; split into a chain of always
        // blocks of bounded size (a block too large for the simulator's
        // register file is interpreted). Each block triggers the next; the
        // last acknowledges the kernel.
        const MAX_LINES: usize = 2500;
        #[derive(PartialEq, Clone, Copy)]
        enum Seg {
            Update,
            Scan,
            Next,
        }
        let mut segs: Vec<(Seg, String)> = Vec::new();
        for line in ub.lines() {
            segs.push((Seg::Update, format!("  {}\n", line)));
        }
        let bodies: std::collections::BTreeMap<usize, (String, String)> = self
            .fproc_bodies
            .iter()
            .map(|(gp, t, b)| (*gp, (t.clone(), b.clone())))
            .collect();
        // The blocks' variables at module scope: a block-local declaration
        // keeps the simulator from compiling the block.
        let mut cyc = String::new();
        let _ = writeln!(cyc, "  longint vh_cyc_n;");
        for (temps, _) in bodies.values() {
            for line in temps.lines() {
                let _ = writeln!(cyc, "  {}", line.trim_start());
            }
        }
        for (pi, c) in conds.iter().enumerate() {
            let Some(c) = c.clone() else { continue };
            let mut t = String::new();
            if post.contains(&pi) {
                let _ = writeln!(
                    t,
                    "    if (vh_r < 0 && vh_from <= {p} && !vh_go[{p}] && !vh_pres[{p}] && ({c})) begin vh_tmoh[{p}] = (vh_tmo[{p}] >= 0 && vh_tmo[{p}] <= vh_now); vh_tmo[{p}] = -64'sd1; vh_pres[{p}] = 1; end",
                    p = pi,
                    c = c
                );
            } else if fp.contains(&pi) {
                let body = bodies.get(&pi).map(|b| b.1.clone()).unwrap_or_default();
                let _ = writeln!(
                    t,
                    "    if (vh_r < 0 && vh_from <= {p} && ({c})) begin",
                    p = pi,
                    c = c
                );
                for line in body.lines() {
                    let _ = writeln!(t, "  {}", line);
                }
                let _ = writeln!(t, "    end");
            } else {
                let _ = writeln!(
                    t,
                    "    if (vh_r < 0 && vh_from <= {p} && !vh_go[{p}] && ({c})) begin vh_tmoh[{p}] = (vh_tmo[{p}] >= 0 && vh_tmo[{p}] <= vh_now); vh_tmo[{p}] = -64'sd1; vh_r = {p}; end",
                    p = pi,
                    c = c
                );
            }
            segs.push((Seg::Scan, t));
        }
        segs.push((Seg::Next, "      vh_cyc_n = -64'sd1;\n".into()));
        for line in nx.lines() {
            // `vh_n` only (not `vh_now`).
            segs.push((
                Seg::Next,
                format!(
                    "  {}\n",
                    line.replace("vh_now", "\u{1}").replace("vh_n", "vh_cyc_n").replace('\u{1}', "vh_now")
                ),
            ));
        }
        segs.push((Seg::Next, "      vh_nxt = vh_cyc_n;\n".into()));
        // Pack the segments into blocks.
        let mut blocks: Vec<Vec<(Seg, String)>> = vec![Vec::new()];
        let mut lines = 0usize;
        for seg in segs {
            let n = seg.1.lines().count();
            if lines + n > MAX_LINES && !blocks.last().unwrap().is_empty() {
                blocks.push(Vec::new());
                lines = 0;
            }
            lines += n;
            blocks.last_mut().unwrap().push(seg);
        }
        let nb = blocks.len();
        let mut trig = String::new();
        for i in 1..nb {
            let _ = write!(trig, " vh_tk{},", i);
        }
        if nb > 1 {
            let _ = writeln!(cyc, "  bit{};", trig.trim_end_matches(','));
        }
        for (i, block) in blocks.iter().enumerate() {
            let t = if i == 0 { "vh_tick".to_string() } else { format!("vh_tk{}", i) };
            let _ = writeln!(cyc, "  always @({}) begin : vh_cycle{}", t, i);
            let mut cur: Option<Seg> = None;
            for (kind, text) in block {
                if cur != Some(*kind) {
                    if let Some(k) = cur
                        && k != Seg::Scan
                    {
                        let _ = writeln!(cyc, "    end");
                    }
                    match kind {
                        Seg::Update => {
                            let _ = writeln!(cyc, "    if (vh_from == 0) begin");
                        }
                        Seg::Next => {
                            let _ = writeln!(cyc, "    if (vh_r < 0) begin");
                        }
                        Seg::Scan => {
                            // The first scan segment of the cycle resets the
                            // process found.
                            if i == 0 || blocks[..i].iter().all(|b| b.iter().all(|(k, _)| *k != Seg::Scan)) {
                                let _ = writeln!(cyc, "    vh_r = -1;");
                            }
                        }
                    }
                    cur = Some(*kind);
                }
                cyc.push_str(text);
            }
            if let Some(k) = cur
                && k != Seg::Scan
            {
                let _ = writeln!(cyc, "    end");
            }
            if i + 1 < nb {
                let _ = writeln!(cyc, "    vh_tk{} = !vh_tk{};", i + 1, i + 1);
            } else {
                let _ = writeln!(cyc, "    vh_tock = !vh_tock;");
            }
            let _ = writeln!(cyc, "  end");
        }
        k.push_str(&cyc);

        // ---- the kernel thread.
        // A clocked process that waits marks its resumption.
        let ct: Vec<String> = self
            .clocked
            .iter()
            .filter(|p| !fp.contains(p))
            .map(|p| format!("vh_r == {}", p))
            .collect();
        let mark = if boundary && !ct.is_empty() {
            format!(" if ({}) vh_clkd = 1;", ct.join(" || "))
        } else {
            String::new()
        };
        // One pass of the cycle block, handing control to the processes
        // that wait, until the scan finds none.
        let scan = |ind: &str| {
            format!(
                "{i}vh_now = $time;\n{i}forever begin\n{i}  vh_tick = !vh_tick; @(vh_tock);\n{i}  if (vh_r < 0) break;\n{i} {mark} vh_go[vh_r] = 1; wait (vh_go[vh_r] == 0); vh_from = vh_r + 1;\n{i}end\n",
                i = ind,
                mark = mark
            )
        };
        let _ = writeln!(k, "  initial begin : vh_kernel");
        let _ = writeln!(k, "    bit vh_any;");
        let _ = writeln!(k, "    vh_elab();\n    vh_now = $time;");
        k.push_str(&self.boundary_sample_init());
        // Initial effective values (§14.7.5.2), in update order.
        for &step in &order {
            let s = match step {
                UpdStep::In(n) => {
                    let _ = writeln!(k, "    vh_lnk{}(1);", n);
                    continue;
                }
                UpdStep::Sig(s) => s,
            };
            for (n, l) in self.links.iter().enumerate() {
                if !l.inn && l.target.sig == s {
                    let _ = writeln!(k, "    vh_lnk{}();", n);
                }
            }
            if upd_sigs.contains(&s) {
                let _ = writeln!(k, "    vh_upd{}(1);", s);
            } else if let [(p, dr)] = self.sig_drivers(s).as_slice()
                && (*p >= PSEUDO || dr.init.is_some())
            {
                let _ = writeln!(
                    k,
                    "    vh_s{s} = vh_dv{s}_{p}; vh_s{s}_last = vh_s{s};",
                    s = s,
                    p = p
                );
            }
        }
        // Implicit signals: their initial values (after those they read).
        for &n in &imp_order {
            let _ = writeln!(k, "    vh_imp{}(1);", n);
        }
        k.push_str(&self.boundary_write(true, "    "));
        let _ = writeln!(
            k,
            "    // Initialization (§14.7.5.2): every process runs until it suspends,\n    // the postponed ones last."
        );
        for p in &post {
            let _ = writeln!(k, "    vh_post[{}] = 1;", p);
        }
        for pass in [false, true] {
            for p in 0..nprocs {
                if post.contains(&p) != pass {
                    continue;
                }
                if fp.contains(&p) {
                    let _ = writeln!(k, "    vh_run{}();", p);
                } else {
                    let _ = writeln!(k, "    vh_go[{p}] = 1; wait (vh_go[{p}] == 0);", p = p);
                }
            }
        }
        let _ = writeln!(k, "    vh_nxt = vh_next();");
        if boundary {
            // The cycles at time 0 synchronously (the function path), so SV
            // code running at time 0 sees the settled design, as it did
            // the VHDL elaboration.
            let _ = writeln!(
                k,
                "    while (vh_nxt == $time && !vh_stop) begin\n      vh_now = $time;\n      vh_update();\n      vh_r = vh_resume(0);\n      while (vh_r >= 0) begin{mark} vh_go[vh_r] = 1; wait (vh_go[vh_r] == 0); vh_r = vh_resume(vh_r + 1); end\n      vh_nxt = vh_next();\n    end",
                mark = mark
            );
            let _ = writeln!(k, "    vh_started = 1;");
        }
        let _ = writeln!(k, "    forever begin");
        if boundary {
            // A cycle the eager evaluation left: its processes that wait,
            // then the rest of the scan.
            let _ = writeln!(
                k,
                "      if (vh_hand >= 0) begin\n        vh_busy = 1; vh_r = vh_hand; vh_hand = -1;\n       {mark} vh_go[vh_r] = 1; wait (vh_go[vh_r] == 0); vh_from = vh_r + 1;\n{scan}        vh_busy = 0;\n      end",
                mark = mark,
                scan = scan("        ")
            );
            // A clocked process ran: the next cycle waits for SV's NBA region,
            // as an SV flip-flop's update does.
            let _ = writeln!(
                k,
                "      if (vh_clkd) begin\n        vh_busy = 1; vh_clkd = 0;\n        vh_nbt <= !vh_nbt; @(vh_nbt);\n        vh_busy = 0;\n      end"
            );
            // A change on the SV side: a cycle now.
            let _ = writeln!(k, "      if (vh_extn != vh_exts) vh_nxt = $time;");
        }
        if !post.is_empty() {
            // §14.7.5.3 h: at the last cycle of a time step the resumed
            // postponed processes run; they must not cause a delta cycle.
            let _ = writeln!(
                k,
                "      if (vh_nxt != $time) begin\n        vh_any = 0;\n        for (int p = 0; p < {n}; p++) if (vh_pres[p]) begin vh_pres[p] = 0; vh_go[p] = 1; wait (vh_go[p] == 0); vh_any = 1; end\n        if (vh_any) begin\n          vh_nxt = vh_next();\n          if (vh_nxt == $time) begin vh_fatal(\"postponed process causes a delta cycle\"); break; end\n        end\n      end",
                n = nprocs
            );
        }
        if boundary {
            // Quiet VHDL waits for SV (the simulation ends with SV's).
            let w = "vh_extn != vh_exts || vh_kick != vh_ksn";
            let _ = writeln!(
                k,
                "      if (vh_stop) break;\n      if (vh_nxt < 0) begin wait ({w}); vh_ksn = vh_kick; continue; end\n      if (vh_nxt > $time) begin\n        fork\n          #(vh_nxt - $time);\n          wait ({w});\n        join_any\n        disable fork;\n        if ({w}) begin vh_ksn = vh_kick; continue; end\n      end\n      vh_busy = 1;",
                w = w
            );
        } else {
            let _ = writeln!(k, "      if (vh_nxt < 0 || vh_stop) break;");
            let _ = writeln!(k, "      if (vh_nxt > $time) #(vh_nxt - $time);");
        }
        let _ = writeln!(k, "      vh_from = 0;");
        k.push_str(&scan("      "));
        if boundary {
            let _ = writeln!(k, "      vh_busy = 0;");
        }
        let _ = writeln!(k, "    end");
        let _ = writeln!(k, "    $finish;");
        let _ = writeln!(k, "  end");
        k
    }

    /// The SV parameters of a subprogram parameter: a signal parameter
    /// of mode `in` also passes its attributes (§4.2.2.3).
    pub(super) fn param_decls(&mut self, p: ObjId, loc: &Loc) -> Vec<String> {
        let o = self.d.objects[p].clone();
        let r = self.obj_repr(p, loc);
        let name = self.obj_name(p);
        match o.kind {
            ObjKind::Param(ObjClass::Signal, Mode::In) => vec![
                format!("input {} {}", r.sv(), name),
                format!("input bit {}_ev", name),
                format!("input bit {}_act", name),
                format!("input {} {}_last", r.sv(), name),
                format!("input longint {}_lev", name),
            ],
            ObjKind::Param(ObjClass::Signal, _) => {
                self.err(
                    loc,
                    "signal parameters of mode out/inout are not supported yet",
                );
                vec![format!("input {} {}", r.sv(), name)]
            }
            // A composite `out` parameter has the actual's bounds (§4.2.2.2):
            // passed in as well.
            ObjKind::Param(_, Mode::Out) if matches!(r, Repr::Arr(..) | Repr::Rec(_)) => {
                vec![format!("inout {} {}", r.sv(), name)]
            }
            // A file parameter: the handle, which FILE_OPEN/FILE_CLOSE change.
            ObjKind::Param(ObjClass::File, _) => vec![format!("inout int {}", name)],
            ObjKind::Param(_, Mode::Out) => vec![format!("output {} {}", r.sv(), name)],
            ObjKind::Param(_, Mode::InOut) => vec![format!("inout {} {}", r.sv(), name)],
            _ => vec![format!("input {} {}", r.sv(), name)],
        }
    }

    /// The SV arguments of an actual: for a signal parameter, also the
    /// signal's attributes.
    pub(super) fn arg_values(&mut self, p: ObjId, a: &HExpr) -> Vec<String> {
        let pt = self.d.objects[p].ty;
        let pr = self.repr(pt, &a.loc);
        let ar = self.erepr(a);
        let mut v = self.ex_as(a, &pr);
        // An actual of a constrained array formal takes the formal's bounds
        // (§4.2.2.1, §14.6: the value is converted to the formal's subtype).
        if matches!(self.d.objects[p].kind, ObjKind::Param(_, Mode::In))
            && self.ndims(pt) == 1
            && self.static_bounds(pt).is_some()
            && let Repr::Arr(name, _) = pr.clone()
            && let Some((l, r, dn)) = self.dim_bounds(pt, 0)
        {
            let (f, line, _) = self.file_line(&a.loc);
            v = format!(
                "{}_rb({}, {}, {}, {}, {}, {})",
                name,
                v,
                l,
                r,
                dn,
                sv_string(&f),
                line
            );
        }
        if !matches!(
            self.d.objects[p].kind,
            ObjKind::Param(ObjClass::Signal, Mode::In)
        ) {
            return vec![v];
        }
        // The callee may test the signal's 'event (rising_edge of
        // std_logic_1164).
        self.mark_clocked();
        let mut out = vec![v];
        let bsv = self.shape(a).map(|b| self.bounds_sv(b));
        for n in ["event", "active", "last_value", "last_event"] {
            match self.sig_attr(a, n) {
                Some(x) => out.push(if n == "last_event" {
                    // The parameter carries the time of the last event.
                    format!("(vh_now - {})", x)
                } else if n == "last_value" {
                    self.coerce(x, &ar, &pr, bsv.clone(), &a.loc)
                } else {
                    x
                }),
                None => {
                    self.err(&a.loc, "a signal parameter needs a signal actual");
                    out.push("0".into());
                }
            }
        }
        out
    }
}

/// Attributes denoting implicit signals (§16.2.4).
pub(super) fn is_implicit(name: &str) -> bool {
    matches!(name, "stable" | "quiet" | "delayed" | "transaction")
}

/// An SV condition on `k` for a driver's coverage.

/// Static path steps as path steps with offsets in SV.
pub(super) fn dsels(path: &[Sel]) -> Vec<DSel> {
    path.iter()
        .map(|s| match s {
            Sel::Field(i) => DSel::Field(*i),
            Sel::Elem(k) => DSel::Elem(k.to_string(), Some(*k)),
            Sel::Slice(k, n) => DSel::Slice(k.to_string(), n.to_string(), Some((*k, *n))),
        })
        .collect()
}

/// The SV condition that number `v` is covered.
pub(super) fn cov_cond_var(c: &Cov, v: &str) -> String {
    match c {
        Cov::All => "1".into(),
        Cov::Set(set) => {
            // Runs of consecutive elements.
            let mut parts = Vec::new();
            let mut it = set.iter().copied().peekable();
            while let Some(a) = it.next() {
                let mut b = a;
                while it.peek() == Some(&(b + 1)) {
                    b = it.next().unwrap();
                }
                if a == b {
                    parts.push(format!("{} == {}", v, a));
                } else {
                    parts.push(format!("({v} >= {} && {v} <= {})", a, b, v = v));
                }
            }
            if parts.is_empty() {
                "0".into()
            } else {
                parts.join(" || ")
            }
        }
    }
}
