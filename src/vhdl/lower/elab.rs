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

use super::{Lw, Repr, sv_ident, sv_string};
use crate::vhdl::ast::{Dir, Mode, ObjClass};
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
}

/// How an object names a signal: the whole signal or a static part.
#[derive(Clone, Debug, PartialEq)]
pub(super) enum Part {
    Whole,
    Elem(i64),
    /// Offset and length; the bounds are the formal's.
    Slice(i64, i64),
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
    fn add(&mut self, other: Cov) {
        match (std::mem::replace(self, Cov::All), other) {
            (Cov::Set(mut a), Cov::Set(b)) => {
                a.extend(b);
                *self = Cov::Set(a);
            }
            _ => *self = Cov::All,
        }
    }
    fn covers(&self, k: i64) -> bool {
        match self {
            Cov::All => true,
            Cov::Set(s) => s.contains(&k),
        }
    }
}

#[derive(Clone, Debug)]
pub(super) struct Driver {
    pub cov: Cov,
    /// Assigned through elements or slices: per-element transactions.
    pub slots: bool,
}

#[derive(Clone, Debug)]
pub(super) struct InstInfo {
    pub arch: usize,
    /// Generic values given by the instance's generic map.
    pub generics: BTreeMap<ObjId, (HExpr, usize)>,
    /// The enclosing instance of a block or generate iteration, whose
    /// objects it sees.
    pub parent: Option<usize>,
}

/// A wait site: the conditions (SV, kernel scope) of the events it is
/// sensitive to.
pub(super) struct Site {
    pub conds: Vec<String>,
}

/// The target of a signal assignment.
enum Target {
    Whole(usize),
    /// Signal, offset of the first element (SV), number of elements
    /// (`None`: one element), coverage.
    Slots(usize, String, Option<String>, Cov),
}

/// Package objects and top-level instance objects keep plain names.
pub(super) const GLOBAL: usize = usize::MAX;

/// Driver ids from here on are the drivers of port associations with a
/// formal conversion or partial formal (`Link`), not processes.
const PSEUDO: usize = 1 << 30;

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
                    let (cov, slots) = match target.part {
                        Part::Whole => (Cov::All, false),
                        Part::Elem(k) => (Cov::Set([k].into_iter().collect()), true),
                        Part::Slice(k, n) => (Cov::Set((k..k + n).collect()), true),
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
                });
            }
            self.elab_inst(child);
        }
    }

    /// The signal (part) an actual names in the context of `inst`.
    fn actual_ref(&self, inst: usize, e: &HExpr) -> Option<SigRef> {
        match &e.kind {
            HExprKind::Obj(o) => self.lookup_sig(inst, *o),
            HExprKind::Index(b, idx) if idx.len() == 1 => {
                let base = self.actual_ref(inst, b)?;
                let i = self.d.eval(&idx[0])?.as_i64()?;
                let off = self.part_offset(&base, b.ty, i)?;
                Some(SigRef {
                    sig: base.sig,
                    part: Part::Elem(off),
                })
            }
            HExprKind::Slice(b, r) => {
                let base = self.actual_ref(inst, b)?;
                let sr = r.static_val.clone()?;
                let off = self.part_offset(&base, b.ty, sr.left.as_i64()?)?;
                Some(SigRef {
                    sig: base.sig,
                    part: Part::Slice(off, sr.length()),
                })
            }
            _ => None,
        }
    }

    /// The storage offset of index `i` of a (whole or sliced) signal.
    fn part_offset(&self, base: &SigRef, ty: TypeId, i: i64) -> Option<i64> {
        let (l, dir, _) = match base.part {
            Part::Whole | Part::Slice(..) => self.static_bounds(ty)?,
            Part::Elem(_) => return None,
        };
        let rel = match dir {
            Dir::To => i - l,
            Dir::Downto => l - i,
        };
        Some(match base.part {
            Part::Slice(off, _) => off + rel,
            _ => rel,
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
        let assign = match l.target.part {
            Part::Whole => {
                let target = HExpr {
                    kind: HExprKind::Obj(sig.obj),
                    ty: sig.ty,
                    loc: loc.clone(),
                };
                let v = self.store_value_init(&target, &l.value);
                format!("    {} = {};\n", dst, v)
            }
            Part::Elem(k) => {
                let v = self.ex(&l.value);
                format!("    {}.d[{}] = {};\n", dst, k, v)
            }
            Part::Slice(k, len) => {
                let v = self.ex(&l.value);
                let (f, line, _) = self.file_line(&l.value.loc);
                format!(
                    "    vh_lv = {v};\n    if (vh_lv.d.size() != {len}) vh_fatal($sformatf(\"bound check failure at %s:%0d\", {f}, {line}));\n    else for (int j = 0; j < {len}; j++) {dst}.d[{k} + j] = vh_lv.d[j];\n",
                    v = v,
                    len = len,
                    f = sv_string(&f),
                    line = line,
                    dst = dst,
                    k = k
                )
            }
        };
        let pre = self.flush_pre(4);
        let mut temps = String::new();
        for (name, t) in std::mem::take(&mut self.temps) {
            let _ = writeln!(temps, "    {} {};", t, name);
        }
        if let Part::Slice(..) = l.target.part {
            let vt = self.repr(l.value.ty, &l.value.loc).sv();
            let _ = writeln!(temps, "    {} vh_lv;", vt);
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

    /// The order signals are updated in (§14.7.3): a link's target after
    /// its sources, otherwise by elaboration order.
    fn update_order(&self) -> Vec<usize> {
        let n = self.sigs.len();
        let mut deps: Vec<Vec<usize>> = vec![Vec::new(); n];
        let mut indeg = vec![0usize; n];
        for l in &self.links {
            for &src in &l.sources {
                if src != l.target.sig {
                    deps[src].push(l.target.sig);
                    indeg[l.target.sig] += 1;
                }
            }
        }
        let mut ready: BTreeSet<usize> = (0..n).filter(|&s| indeg[s] == 0).collect();
        let mut order = Vec::with_capacity(n);
        while let Some(s) = ready.pop_first() {
            order.push(s);
            for &t in &deps[s] {
                indeg[t] -= 1;
                if indeg[t] == 0 {
                    ready.insert(t);
                }
            }
        }
        // A cycle (not expected from port associations): the rest in order.
        for s in 0..n {
            if !order.contains(&s) {
                order.push(s);
            }
        }
        order
    }

    pub(super) fn lookup_sig(&self, mut inst: usize, o: ObjId) -> Option<SigRef> {
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
            return format!("vh_s{}", o);
        };
        let base = if self.read_last {
            format!("vh_s{}_last", r.sig)
        } else {
            format!("vh_s{}", r.sig)
        };
        match r.part {
            Part::Whole => base,
            Part::Elem(off) => format!("{}.d[{}]", base, off),
            Part::Slice(off, len) => {
                let ty = self.d.objects[o].ty;
                let loc = self.d.objects[o].loc.clone();
                let name = self.arr_name(ty, &loc);
                // The formal's bounds, else the actual's.
                let (l, r, dn) = match self.dim_bounds(ty, 0) {
                    Some(b) => b,
                    None => {
                        let st = self.sigs[r.sig].ty;
                        let (al, adir, _) = self.static_bounds(st).unwrap_or((0, Dir::To, 0));
                        let (l, rr) = match adir {
                            Dir::To => (al + off, al + off + len - 1),
                            Dir::Downto => (al - off, al - off - len + 1),
                        };
                        (
                            self.scalar_lit(&Value::Int(l), &Repr::I64),
                            self.scalar_lit(&Value::Int(rr), &Repr::I64),
                            ((adir == Dir::Downto) as u8).to_string(),
                        )
                    }
                };
                format!(
                    "{}_sub({}, {}, {}, {}, {}, {})",
                    name, base, off, len, l, r, dn
                )
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
    /// `'last_value`, `'last_event`, §16.2.4): of the whole signal, or for a
    /// part, from the whole signal's flags and the part's values.
    pub(super) fn sig_attr(&mut self, x: &HExpr, name: &str) -> Option<String> {
        // A signal parameter: the attributes passed with it.
        if let HExprKind::Obj(o) = &x.kind
            && matches!(self.d.objects[*o].kind, ObjKind::Param(ObjClass::Signal, _))
        {
            let p = self.obj_name(*o);
            return Some(match name {
                "event" => format!("{}_ev", p),
                "active" => format!("{}_act", p),
                "last_value" => format!("{}_last", p),
                _ => format!("(longint'($time) - {}_lev)", p),
            });
        }
        if let HExprKind::Index(b, _) | HExprKind::Slice(b, _) | HExprKind::Field(b, _) = &x.kind
            && let HExprKind::Obj(o) = &b.kind
            && matches!(self.d.objects[*o].kind, ObjKind::Param(ObjClass::Signal, _))
        {
            let p = self.obj_name(*o);
            let cur = self.ex(x);
            let last = self.ex_last(x);
            let r = self.repr(x.ty, &x.loc);
            return Some(match name {
                "event" => format!("({}_ev && !{})", p, self.eq_expr(&r, &cur, &last)),
                "active" => format!("{}_act", p),
                "last_value" => last,
                _ => format!("(longint'($time) - {}_lev)", p),
            });
        }
        let s = self.sig_of(x)?;
        if self.whole_sig(x).is_some() {
            return Some(match name {
                "event" => format!("vh_s{}_ev", s),
                "active" => format!("vh_s{}_act", s),
                "last_value" => format!("vh_s{}_last", s),
                _ => format!("(longint'($time) - vh_s{}_lev)", s),
            });
        }
        let cur = self.ex(x);
        let last = self.ex_last(x);
        let r = self.repr(x.ty, &x.loc);
        Some(match name {
            "event" => format!("(vh_s{}_ev && !{})", s, self.eq_expr(&r, &cur, &last)),
            "active" => format!("vh_s{}_act", s),
            "last_value" => last,
            _ => format!("(longint'($time) - vh_s{}_lev)", s),
        })
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
        let (f, l, _) = self.file_line(&t.loc);
        match &t.kind {
            HExprKind::Obj(o) => {
                let r = self.lookup_sig(self.inst, *o)?;
                Some(match r.part {
                    Part::Whole => Target::Whole(r.sig),
                    Part::Elem(off) => Target::Slots(
                        r.sig,
                        off.to_string(),
                        None,
                        Cov::Set([off].into_iter().collect()),
                    ),
                    Part::Slice(off, len) => Target::Slots(
                        r.sig,
                        off.to_string(),
                        Some(len.to_string()),
                        Cov::Set((off..off + len).collect()),
                    ),
                })
            }
            HExprKind::Index(b, idx) if idx.len() == 1 => {
                let HExprKind::Obj(o) = &b.kind else {
                    return None;
                };
                let r = self.lookup_sig(self.inst, *o)?;
                let (base_off, base_cov) = match r.part {
                    Part::Whole => (0, Cov::All),
                    Part::Slice(off, len) => (off, Cov::Set((off..off + len).collect())),
                    Part::Elem(_) => return None,
                };
                let bv = self.ex(b);
                let i = self.ex(&idx[0]);
                let off = format!(
                    "({} + vh_ix({}, {b}.l, {b}.r, {b}.dn, {}, {}))",
                    base_off,
                    i,
                    sv_string(&f),
                    l,
                    b = bv
                );
                let cov = match self.d.eval(&idx[0]).and_then(|v| v.as_i64()) {
                    Some(iv) => match self.part_offset(&r, b.ty, iv) {
                        Some(k) => Cov::Set([k].into_iter().collect()),
                        None => base_cov,
                    },
                    None => base_cov,
                };
                Some(Target::Slots(r.sig, off, None, cov))
            }
            HExprKind::Slice(b, rg) => {
                let HExprKind::Obj(o) = &b.kind else {
                    return None;
                };
                let r = self.lookup_sig(self.inst, *o)?;
                let (base_off, base_cov) = match r.part {
                    Part::Whole => (0, Cov::All),
                    Part::Slice(off, len) => (off, Cov::Set((off..off + len).collect())),
                    Part::Elem(_) => return None,
                };
                let bv = self.ex(b);
                let (left, right, dn) = self.range_parts(rg);
                let off = format!(
                    "({} + vh_ix({}, {b}.l, {b}.r, {b}.dn, {}, {}))",
                    base_off,
                    left,
                    sv_string(&f),
                    l,
                    b = bv
                );
                let n = format!("vh_len({}, {}, {})", left, right, dn);
                let cov = match &rg.static_val {
                    Some(sr) => {
                        match sr
                            .left
                            .as_i64()
                            .and_then(|lv| self.part_offset(&r, b.ty, lv))
                        {
                            Some(k) => Cov::Set((k..k + sr.length()).collect()),
                            None => base_cov,
                        }
                    }
                    None => base_cov,
                };
                Some(Target::Slots(r.sig, off, Some(n), cov))
            }
            _ => None,
        }
    }

    /// `s <= [delay] w1 after t1, w2 after t2, …` (§10.5.2): update the
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
        let (sig, call) = match &tg {
            Target::Whole(s) => {
                self.add_driver(*s, p, Cov::All, false);
                (*s, None)
            }
            Target::Slots(s, off, n, cov) => {
                self.add_driver(*s, p, cov.clone(), true);
                (*s, Some((off.clone(), n.clone())))
            }
        };
        let (f, line, _) = self.file_line(&loc);
        let mut out = String::new();
        let transport = matches!(delay, Some(HDelay::Transport));
        let reject = match delay {
            Some(HDelay::Inertial(Some(r))) => Some(self.ex(r)),
            _ => None,
        };
        for (i, w) in waves.iter().enumerate() {
            let t = match &w.after {
                Some(a) => self.ex(a),
                None => "64'sd0".into(),
            };
            let Some(v) = &w.value else {
                self.err(&loc, "null transactions are not supported yet");
                continue;
            };
            let val = self.store_value(target, v);
            // The first element of an inertial assignment rejects pulses
            // shorter than the reject limit (default: its delay).
            let (mode, rej) = if i == 0 && !transport {
                (1, reject.clone().unwrap_or_else(|| t.clone()))
            } else {
                (if i == 0 { 0 } else { 2 }, "64'sd0".into())
            };
            match &call {
                None => {
                    let _ = writeln!(
                        out,
                        "{}vh_drv_{}_{}({}, {}, {}, {});",
                        pad, sig, p, val, t, rej, mode
                    );
                }
                Some((off, None)) => {
                    let _ = writeln!(
                        out,
                        "{}vh_drs_{}_{}({}, {}, {}, {}, {});",
                        pad, sig, p, off, val, t, rej, mode
                    );
                }
                Some((off, Some(n))) => {
                    let _ = writeln!(
                        out,
                        "{}vh_drsl_{}_{}({}, {}, {}, {}, {}, {}, {}, {});",
                        pad,
                        sig,
                        p,
                        off,
                        n,
                        val,
                        t,
                        rej,
                        mode,
                        sv_string(&f),
                        line
                    );
                }
            }
        }
        out
    }

    fn add_driver(&mut self, s: usize, p: usize, cov: Cov, slots: bool) {
        match self.drivers.get_mut(&(s, p)) {
            Some(d) => {
                d.cov.add(cov);
                d.slots |= slots;
            }
            None => {
                self.drivers.insert((s, p), Driver { cov, slots });
            }
        }
    }

    // ---- the module -------------------------------------------------------------

    /// The resolution function of a signal's subtype: of the signal itself
    /// (`false`) or of each element (`true`).
    fn resolution(&self, t: TypeId) -> Option<(SubId, bool)> {
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
            if matches!(info.kind, ObjKind::File) {
                continue;
            }
            self.inst = if inst == GLOBAL { 0 } else { inst };
            let r = self.repr(info.ty, &info.loc);
            let name = self.obj_name(o);
            let _ = writeln!(decls, "  {} {};", r.sv(), name);
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
        }
        // Signals.
        let sigs = self.sigs.clone();
        for (si, s) in sigs.iter().enumerate() {
            let info = d.objects[s.obj].clone();
            self.inst = if s.inst == GLOBAL { 0 } else { s.inst };
            let r = self.repr(s.ty, &info.loc);
            let _ = writeln!(
                decls,
                "  {t} vh_s{s};\n  bit vh_s{s}_ev, vh_s{s}_act; {t} vh_s{s}_last; longint vh_s{s}_lev;",
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
                "    vh_s{s} = {v};\n    vh_s{s}_last = vh_s{s}; vh_s{s}_lev = -64'sd9223372036854775807;",
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
        for (gp, (inst, ai, pi)) in self.procs.clone().into_iter().enumerate() {
            let p = d.archs[ai].processes[pi].clone();
            self.inst = inst;
            self.cur_proc = Some(gp);
            self.temps.clear();
            let body = self.stmts(&p.stmts, 6);
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
            for (n, t) in std::mem::take(&mut self.temps) {
                let _ = writeln!(temps, "    {} {};", t, n);
            }
            let label = if p.label.is_empty() {
                format!("p{}", pi)
            } else {
                sv_ident(&p.label)
            };
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
        // Drivers and signal updates (their resolution functions are
        // lowered with the subprograms).
        let drv = self.drivers_sv(&mut elab);
        let (upd, upd_sigs) = self.updates_sv();
        let mut lnk = String::new();
        for n in 0..self.links.len() {
            let f = self.link_sv(n);
            lnk.push_str(&f);
        }
        // Subprograms the design calls (transitively).
        while let Some((s, inst)) = self.subs_todo.pop() {
            if self.subs_done.insert((s, inst)) {
                let saved = std::mem::replace(&mut self.inst, inst);
                self.subprogram(s);
                self.inst = saved;
            }
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
        let _ = writeln!(m, "module {};", sv_ident(&arch.entity));
        let _ = writeln!(m, "  timeunit 1fs; timeprecision 1fs;");
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
        m.push_str(&logic_defs);
        m.push_str(super::runtime::MATCHING);
        m.push_str(
            "  function automatic vh_a_u8 vh_str(string s);\n    byte unsigned t[];\n    t = new[s.len()];\n    for (int i = 0; i < s.len(); i++) t[i] = s.getc(i);\n    return vh_a_u8_from(1, 0, t);\n  endfunction\n  function automatic string vh_sv(vh_a_u8 a);\n    string s;\n    s = \"\";\n    for (int i = 0; i < a.d.size(); i++) s = {s, string'(a.d[i])};\n    return s;\n  endfunction\n  function automatic longint vh_deadline(longint t);\n    if (t < 0) return -64'sd1;\n    if (t > 64'sd9223372036854775807 - longint'($time)) return -64'sd1;\n    return longint'($time) + t;\n  endfunction\n",
        );
        let _ = writeln!(
            m,
            "  bit vh_go [0:{n}];\n  bit vh_tmoh [0:{n}];\n  longint vh_tmo [0:{n}];\n  longint vh_dl [0:{n}];\n  int vh_site [0:{n}];\n  bit vh_stop;",
            n = np
        );
        m.push_str(&decls);
        m.push_str(&self.lit_items);
        let tio = self.textio_sv();
        m.push_str(&tio);
        m.push_str(&drv);
        m.push_str(&upd);
        m.push_str(&self.sub_items);
        m.push_str(&lnk);
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

    /// The drivers: transaction queues and the procedures updating their
    /// projected waveforms (§10.5.2.2).
    fn drivers_sv(&mut self, elab: &mut String) -> String {
        let mut drv = String::new();
        let drivers: Vec<((usize, usize), Driver)> =
            self.drivers.iter().map(|(k, v)| (*k, v.clone())).collect();
        for ((s, p), dr) in &drivers {
            let sig = self.sigs[*s].clone();
            let loc = self.d.objects[sig.obj].loc.clone();
            let r = self.repr(sig.ty, &loc);
            let t = r.sv();
            if *p >= PSEUDO {
                // The driver of a port link: a value only.
                let _ = writeln!(drv, "  {} vh_dv{}_{};", t, s, p);
            } else if !dr.slots {
                // Parallel queues of transaction times and values (a queue
                // of structs holding a struct does not round-trip in the
                // simulator).
                let eq = self.eq_expr(&r, "qv[k]", "v");
                let _ = write!(
                    drv,
                    "  longint vh_dt{s}_{p}[$];\n  {t} vh_dq{s}_{p}[$];\n  {t} vh_dv{s}_{p};\n  // Update the projected output waveform (§10.5.2.2): mode 0 transport,\n  // 1 inertial first element (reject limit), 2 later elements.\n  function automatic void vh_drv_{s}_{p}({t} v, longint after, longint rej, int mode);\n    longint tt;\n    longint qt[$];\n    {t} qv[$];\n    int k;\n    tt = longint'($time) + after;\n    qt = vh_dt{s}_{p};\n    qv = vh_dq{s}_{p};\n    while (qt.size() > 0 && qt[qt.size()-1] >= tt) begin void'(qt.pop_back()); void'(qv.pop_back()); end\n    if (mode == 1) begin\n      // Pulse rejection: of the old transactions in [tt - rej, tt), keep\n      // the run immediately before the new one that has its value.\n      k = qt.size() - 1;\n      while (k >= 0 && qt[k] >= tt - rej && ({eq})) k--;\n      while (k >= 0 && qt[k] >= tt - rej) begin qt.delete(k); qv.delete(k); k--; end\n    end\n    qt.push_back(tt);\n    qv.push_back(v);\n    vh_dt{s}_{p} = qt;\n    vh_dq{s}_{p} = qv;\n  endfunction\n",
                    t = t,
                    s = s,
                    p = p,
                    eq = eq
                );
            } else {
                let Repr::Arr(name, er) = &r else {
                    self.err(
                        &loc,
                        "an assignment to part of this signal is not supported yet",
                    );
                    continue;
                };
                let et = er.sv();
                let eq = self.eq_expr(er, "qv[i]", "v");
                let _ = write!(
                    drv,
                    "  longint vh_dt{s}_{p}[$];\n  longint vh_dk{s}_{p}[$];\n  {et} vh_dq{s}_{p}[$];\n  {t} vh_dv{s}_{p};\n  // The projected waveform of element k (§10.5.2.2), transactions kept in\n  // time order.\n  function automatic void vh_drs_{s}_{p}(longint k, {et} v, longint after, longint rej, int mode);\n    longint tt;\n    longint qt[$];\n    longint qk[$];\n    {et} qv[$];\n    int i, pos;\n    bit keep;\n    tt = longint'($time) + after;\n    qt = vh_dt{s}_{p};\n    qk = vh_dk{s}_{p};\n    qv = vh_dq{s}_{p};\n    for (i = qt.size() - 1; i >= 0; i--) if (qk[i] == k && qt[i] >= tt) begin qt.delete(i); qk.delete(i); qv.delete(i); end\n    if (mode == 1) begin\n      keep = 1;\n      for (i = qt.size() - 1; i >= 0; i--) begin\n        if (qk[i] != k) continue;\n        if (qt[i] < tt - rej) break;\n        if (keep && ({eq})) continue;\n        keep = 0;\n        qt.delete(i); qk.delete(i); qv.delete(i);\n      end\n    end\n    pos = qt.size();\n    for (i = 0; i < qt.size(); i++) if (qt[i] > tt) begin pos = i; break; end\n    if (pos == qt.size()) begin\n      qt.push_back(tt); qk.push_back(k); qv.push_back(v);\n    end else begin\n      qt.insert(pos, tt); qk.insert(pos, k); qv.insert(pos, v);\n    end\n    vh_dt{s}_{p} = qt;\n    vh_dk{s}_{p} = qk;\n    vh_dq{s}_{p} = qv;\n  endfunction\n  // A slice: its elements from offset `off`.\n  function automatic void vh_drsl_{s}_{p}(longint off, longint n, {t} v, longint after, longint rej, int mode, string file, int line);\n    if (v.d.size() != n) begin\n      vh_fatal($sformatf(\"bound check failure at %s:%0d\", file, line));\n      return;\n    end\n    for (int j = 0; j < n; j++) vh_drs_{s}_{p}(off + j, v.d[j], after, rej, mode);\n  endfunction\n  // The whole signal: every element.\n  function automatic void vh_drv_{s}_{p}({t} v, longint after, longint rej, int mode);\n    for (int j = 0; j < v.d.size(); j++) vh_drs_{s}_{p}(j, v.d[j], after, rej, mode);\n  endfunction\n",
                    et = et,
                    t = t,
                    s = s,
                    p = p,
                    eq = eq
                );
                let _ = name;
            }
            let _ = writeln!(elab, "    vh_dv{s}_{p} = vh_s{s};", s = s, p = p);
        }
        drv
    }

    /// Whether a signal takes its single whole driver's value directly.
    fn simple_sig(&self, s: usize, ds: &[(usize, Driver)]) -> bool {
        ds.len() == 1
            && !ds[0].1.slots
            && ds[0].1.cov == Cov::All
            && self.resolution(self.sigs[s].ty).is_none()
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
            let tsv = r.sv();
            let mut body = String::new();
            match (&r, res) {
                (_, Some((f, false))) => {
                    // A resolved signal: f over every driver's value.
                    let pt = self.d.objects[self.d.subprograms[f].params[0]].ty;
                    let (pname, per) = match self.repr(pt, &info.loc) {
                        Repr::Arr(n, e) => (n, e.sv()),
                        _ => continue,
                    };
                    self.need_sub(f);
                    let _ = writeln!(body, "    {} rv[];\n    {} nv;", per, tsv);
                    let _ = writeln!(body, "    rv = new[{}];", ds.len());
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
                (Repr::Arr(_, er), res) => {
                    // Element by element: the drivers covering it.
                    let et = er.sv();
                    let n = self.static_bounds(sig.ty).map(|(l, dir, rr)| match dir {
                        Dir::To => (rr - l + 1).max(0),
                        Dir::Downto => (l - rr + 1).max(0),
                    });
                    if res.is_none() {
                        // At most one driver per element of an unresolved
                        // signal (§14.7.2).
                        if let Some(n) = n {
                            for k in 0..n {
                                if ds.iter().filter(|(_, d)| d.cov.covers(k)).count() > 1 {
                                    self.err(
                                        &info.loc,
                                        format!(
                                            "unresolved signal '{}' has several drivers",
                                            info.name
                                        ),
                                    );
                                    break;
                                }
                            }
                        }
                    }
                    let _ = writeln!(body, "    {} nv;\n    {} rv[];\n    int c;", tsv, et);
                    let _ = writeln!(body, "    nv = vh_s{};", s);
                    let _ = writeln!(body, "    rv = new[{}];", ds.len());
                    let _ = writeln!(body, "    for (int k = 0; k < nv.d.size(); k++) begin");
                    let _ = writeln!(body, "      c = 0;");
                    for (p, dr) in &ds {
                        let cond = cov_cond(&dr.cov);
                        let _ = writeln!(
                            body,
                            "      if ({}) begin rv[c] = vh_dv{}_{}.d[k]; c++; end",
                            cond, s, p
                        );
                    }
                    match res {
                        Some((f, _)) => {
                            let pt = self.d.objects[self.d.subprograms[f].params[0]].ty;
                            let pname = self.arr_name(pt, &info.loc);
                            self.need_sub(f);
                            let _ = writeln!(
                                body,
                                "      if (c > 0) begin\n        {et} ra[];\n        ra = new[c];\n        for (int j = 0; j < c; j++) ra[j] = rv[j];\n        nv.d[k] = {}({}_mk(0, c - 1, 0, ra));\n      end",
                                self.sub_name(f),
                                pname,
                                et = et
                            );
                        }
                        None => {
                            let _ = writeln!(body, "      if (c > 0) nv.d[k] = rv[0];");
                        }
                    }
                    let _ = writeln!(body, "    end");
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

    /// The kernel: the VHDL simulation cycle (§14.7.5).
    fn kernel(&mut self, upd_sigs: &[usize]) -> String {
        let nprocs = self.procs.len();
        let drivers: Vec<((usize, usize), Driver)> =
            self.drivers.iter().map(|(k, v)| (*k, v.clone())).collect();
        let mut k = String::new();
        let _ = writeln!(k, "  initial begin : vh_kernel");
        let _ = writeln!(k, "    longint vh_nxt;");
        let _ = writeln!(k, "    vh_elab();");
        // Initial effective values (§14.7.5.2), in update order.
        let order = self.update_order();
        for &s in &order {
            for (n, l) in self.links.iter().enumerate() {
                if !l.inn && l.target.sig == s {
                    let _ = writeln!(k, "    vh_lnk{}();", n);
                }
            }
            if upd_sigs.contains(&s) {
                let _ = writeln!(k, "    vh_upd{}(1);", s);
            } else if let [(p, _)] = self.sig_drivers(s).as_slice()
                && *p >= PSEUDO
            {
                let _ = writeln!(
                    k,
                    "    vh_s{s} = vh_dv{s}_{p}; vh_s{s}_last = vh_s{s};",
                    s = s,
                    p = p
                );
            }
            for (n, l) in self.links.iter().enumerate() {
                if l.inn && l.target.sig == s {
                    let _ = writeln!(k, "    vh_lnk{}(1);", n);
                }
            }
        }
        let _ = writeln!(
            k,
            "    // Initialization (§14.7.5.2): every process runs until it suspends."
        );
        let _ = writeln!(
            k,
            "    for (int p = 0; p < {}; p++) begin vh_go[p] = 1; wait (vh_go[p] == 0); end",
            nprocs
        );
        let _ = writeln!(k, "    forever begin");
        let _ = writeln!(k, "      vh_nxt = -64'sd1;");
        for ((s, p), _) in drivers.iter().filter(|((_, p), _)| *p < PSEUDO) {
            let _ = writeln!(
                k,
                "      if (vh_dt{s}_{p}.size() > 0 && (vh_nxt < 0 || vh_dt{s}_{p}[0] < vh_nxt)) vh_nxt = vh_dt{s}_{p}[0];",
                s = s,
                p = p
            );
        }
        let _ = writeln!(
            k,
            "      for (int p = 0; p < {}; p++) if (vh_tmo[p] >= 0 && (vh_nxt < 0 || vh_tmo[p] < vh_nxt)) vh_nxt = vh_tmo[p];",
            nprocs
        );
        let _ = writeln!(k, "      if (vh_nxt < 0 || vh_stop) break;");
        let _ = writeln!(k, "      if (vh_nxt > $time) #(vh_nxt - $time);");
        let _ = writeln!(k, "      // Signal update (§14.7.3).");
        for s in 0..self.sigs.len() {
            let _ = writeln!(k, "      vh_s{s}_ev = 0; vh_s{s}_act = 0;", s = s);
        }
        for ((s, p), dr) in drivers.iter().filter(|((_, p), _)| *p < PSEUDO) {
            if dr.slots {
                let _ = writeln!(
                    k,
                    "      while (vh_dt{s}_{p}.size() > 0 && vh_dt{s}_{p}[0] <= $time) begin void'(vh_dt{s}_{p}.pop_front()); vh_dv{s}_{p}.d[vh_dk{s}_{p}.pop_front()] = vh_dq{s}_{p}.pop_front(); vh_s{s}_act = 1; end",
                    s = s,
                    p = p
                );
            } else {
                let _ = writeln!(
                    k,
                    "      if (vh_dt{s}_{p}.size() > 0 && vh_dt{s}_{p}[0] <= $time) begin void'(vh_dt{s}_{p}.pop_front()); vh_dv{s}_{p} = vh_dq{s}_{p}.pop_front(); vh_s{s}_act = 1; end",
                    s = s,
                    p = p
                );
            }
        }
        for &s in &order {
            // Links into this signal: the driving values from converted or
            // partial out ports first, the in ports after its update.
            let link_cond = |l: &Link| {
                if l.sources.is_empty() {
                    "0".to_string()
                } else {
                    l.sources
                        .iter()
                        .map(|x| format!("vh_s{}_act", x))
                        .collect::<Vec<_>>()
                        .join(" || ")
                }
            };
            for (n, l) in self.links.iter().enumerate() {
                if !l.inn && l.target.sig == s {
                    let _ = writeln!(k, "      if ({}) vh_lnk{}();", link_cond(l), n);
                }
            }
            let ins: Vec<String> = self
                .links
                .iter()
                .enumerate()
                .filter(|(_, l)| l.inn && l.target.sig == s)
                .map(|(n, l)| format!("      if ({}) vh_lnk{}(0);\n", link_cond(l), n))
                .collect();
            let ds = self.sig_drivers(s);
            if ds.is_empty() {
                k.push_str(&ins.concat());
                continue;
            }
            if upd_sigs.contains(&s) {
                let _ = writeln!(k, "      if (vh_s{s}_act) vh_upd{s}(0);", s = s);
                k.push_str(&ins.concat());
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
            let _ = writeln!(
                k,
                "      if (vh_s{s}_act && {ne}) begin vh_s{s}_last = vh_s{s}; vh_s{s} = vh_dv{s}_{p}; vh_s{s}_ev = 1; vh_s{s}_lev = $time; end",
                s = s,
                p = ds[0].0,
                ne = ne
            );
            k.push_str(&ins.concat());
        }
        let _ = writeln!(k, "      // Resume (§14.7.5.3), in elaboration order.");
        for pi in 0..nprocs {
            let mut conds = vec![format!(
                "(vh_tmo[{p}] >= 0 && vh_tmo[{p}] <= $time)",
                p = pi
            )];
            for (si, site) in self.sites[pi].iter().enumerate() {
                if site.conds.is_empty() {
                    continue;
                }
                conds.push(format!(
                    "(vh_site[{}] == {} && ({}))",
                    pi,
                    si,
                    site.conds.join(" || ")
                ));
            }
            let _ = writeln!(
                k,
                "      if (!vh_go[{p}] && ({c})) begin vh_tmoh[{p}] = (vh_tmo[{p}] >= 0 && vh_tmo[{p}] <= $time); vh_tmo[{p}] = -64'sd1; vh_go[{p}] = 1; wait (vh_go[{p}] == 0); end",
                p = pi,
                c = conds.join(" || ")
            );
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
        let r = self.repr(o.ty, loc);
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
            ObjKind::Param(_, Mode::Out) => vec![format!("output {} {}", r.sv(), name)],
            ObjKind::Param(_, Mode::InOut) => vec![format!("inout {} {}", r.sv(), name)],
            _ => vec![format!("input {} {}", r.sv(), name)],
        }
    }

    /// The SV arguments of an actual: for a signal parameter, also the
    /// signal's attributes.
    pub(super) fn arg_values(&mut self, p: ObjId, a: &HExpr) -> Vec<String> {
        let v = self.ex(a);
        if !matches!(
            self.d.objects[p].kind,
            ObjKind::Param(ObjClass::Signal, Mode::In)
        ) {
            return vec![v];
        }
        let mut out = vec![v];
        for n in ["event", "active", "last_value", "last_event"] {
            match self.sig_attr(a, n) {
                Some(x) => out.push(if n == "last_event" {
                    // The parameter carries the time of the last event.
                    format!("(longint'($time) - {})", x)
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

/// An SV condition on `k` for a driver's coverage.
fn cov_cond(c: &Cov) -> String {
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
                    parts.push(format!("k == {}", a));
                } else {
                    parts.push(format!("(k >= {} && k <= {})", a, b));
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
