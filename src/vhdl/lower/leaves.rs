//! Drivers of parts of signals (§14.7.2) and the effective values computed
//! from them (§14.7.3.2), at the level of the scalar subelements.
//!
//! The scalar subelements of a signal's type fall into leaf classes: those
//! reached through the same record elements and array dimensions (`r.f`,
//! `a(i)(j)`, `a(i).f(j)`). The leaves of a class are numbered by their
//! array offsets (mixed radix, outermost dimension first) and the classes
//! of a type numbered after one another, so a scalar subelement has a
//! global number. A driver of a part of a signal (a process assigning
//! `a(i)(j) <= v`, an `out` port associated with `r.f`) keeps, for each
//! class, a queue of transactions (leaf, time, value); a signal with such
//! drivers, or several drivers, takes each scalar subelement from the
//! drivers covering it, through the subelement's resolution function where
//! it has one.

use std::collections::BTreeSet;
use std::fmt::Write as _;

use super::elab::{Cov, Driver};
use super::{Lw, Repr, sv_string};
use crate::vhdl::ast::Dir;
use crate::vhdl::sema::hir::*;

/// A step of a static path into a signal's value.
#[derive(Clone, Debug, PartialEq)]
pub(super) enum Sel {
    Field(usize),
    /// An element: its offset (0 for the left one) in this dimension.
    Elem(i64),
    /// A slice: offset and length; the last step of a path.
    Slice(i64, i64),
}

/// A step of a path whose offsets may be computed at run time (SV), with
/// their static values when known.
#[derive(Clone, Debug)]
pub(super) enum DSel {
    Field(usize),
    Elem(String, Option<i64>),
    Slice(String, String, Option<(i64, i64)>),
}

/// A step from a signal to a class of scalar leaves.
#[derive(Clone, Debug, PartialEq)]
enum Step {
    Field(usize),
    /// An array dimension and its length.
    Dim(i64),
    /// The dimension of a packed array: its length and element bits.
    PDim(i64, u32),
}

#[derive(Clone, Debug)]
pub(super) struct LeafClass {
    steps: Vec<Step>,
    pub scalar: TypeId,
    pub count: i64,
    pub base: i64,
}

impl LeafClass {
    fn dims(&self) -> Vec<i64> {
        self.steps
            .iter()
            .filter_map(|s| match s {
                Step::Dim(n) | Step::PDim(n, _) => Some(*n),
                _ => None,
            })
            .collect()
    }
}

/// Coverage sets larger than this are kept as `Cov::All`.
const MAX_COV: i64 = 1 << 16;

impl<'a> Lw<'a> {
    /// The leaf classes of type `t` (`None` when an array of it has bounds
    /// that are not static).
    pub(super) fn leaf_classes(&self, t: TypeId) -> Option<Vec<LeafClass>> {
        let mut out = Vec::new();
        self.collect_classes(t, &mut Vec::new(), &mut out, true)?;
        let mut base = 0;
        for c in &mut out {
            c.base = base;
            base += c.count;
        }
        Some(out)
    }

    /// `packed`: the storage of `t` may be a packed vector (not for a
    /// record field whose declared type is unconstrained).
    fn collect_classes(&self, t: TypeId, steps: &mut Vec<Step>, out: &mut Vec<LeafClass>, packed: bool) -> Option<()> {
        let b = self.base(t);
        match &self.d.types[b].kind {
            TypeKind::Record(_) => {
                let storage = self.field_storage(t);
                for (i, (_, ft)) in self.d.record_fields(t).into_iter().enumerate() {
                    steps.push(Step::Field(i));
                    let pk = self.pk_of(storage[i]).is_some() || self.ndims(storage[i]) == 0;
                    self.collect_classes(ft, steps, out, pk)?;
                    steps.pop();
                }
                Some(())
            }
            TypeKind::Array { index, .. } => {
                let ranges = self.d.array_index_ranges(t)?;
                let n0 = steps.len();
                if packed && let Some(Repr::Pk(w, n)) = self.pk_of(t) {
                    steps.push(Step::PDim(n, w));
                } else {
                    for k in 0..index.len() {
                        let r = ranges.get(k)?.clone()?;
                        steps.push(Step::Dim(r.length().max(0)));
                    }
                }
                let e = self.d.element_subtype(t)?;
                self.collect_classes(e, steps, out, true)?;
                steps.truncate(n0);
                Some(())
            }
            _ => {
                let count = steps
                    .iter()
                    .map(|s| match s {
                        Step::Dim(n) | Step::PDim(n, _) => *n,
                        _ => 1,
                    })
                    .product();
                out.push(LeafClass {
                    steps: steps.clone(),
                    scalar: t,
                    count,
                    base: 0,
                });
                Some(())
            }
        }
    }

    /// The SV selection of leaf `k` (SV) of a class.
    fn leaf_sv(c: &LeafClass, k: &str) -> String {
        let dims = c.dims();
        let mut out = String::new();
        let mut di = 0;
        for s in &c.steps {
            match s {
                Step::Field(i) => {
                    let _ = write!(out, ".f{}", i);
                }
                Step::Dim(n) | Step::PDim(n, _) => {
                    let stride: i64 = dims[di + 1..].iter().product();
                    di += 1;
                    let idx = match (stride, dims.len() == 1) {
                        (1, true) => k.to_string(),
                        (1, false) => format!("(({}) % {})", k, n),
                        _ => format!("((({}) / {}) % {})", k, stride, n),
                    };
                    match s {
                        Step::PDim(n, w) => {
                            let _ = write!(out, "[{} * ({} - ({})) +: {}]", w, n - 1, idx, w);
                        }
                        _ => {
                            let _ = write!(out, ".d[{}]", idx);
                        }
                    }
                }
            }
        }
        out
    }

    /// The global numbers of the leaves under a path; a step with an
    /// offset computed at run time covers every offset of its dimension.
    pub(super) fn path_cov(&self, t: TypeId, path: &[DSel]) -> Cov {
        let Some(classes) = self.leaf_classes(t) else {
            return Cov::All;
        };
        let mut set = BTreeSet::new();
        for c in &classes {
            // Per dimension of the class: the offsets the path allows.
            let dims = c.dims();
            let mut allowed: Vec<Option<(i64, i64)>> = vec![None; dims.len()];
            let mut di = 0;
            let mut ok = true;
            let mut steps = c.steps.iter();
            for sel in path {
                // Skip to the step this selector applies to.
                let Some(step) = steps.next() else {
                    ok = false;
                    break;
                };
                match (sel, step) {
                    (DSel::Field(i), Step::Field(j)) if i == j => {}
                    (DSel::Elem(_, v), Step::Dim(_) | Step::PDim(..)) => {
                        allowed[di] = v.map(|k| (k, 1));
                        di += 1;
                    }
                    (DSel::Slice(_, _, v), Step::Dim(_) | Step::PDim(..)) => {
                        allowed[di] = *v;
                        di += 1;
                    }
                    _ => {
                        ok = false;
                        break;
                    }
                }
            }
            if !ok {
                continue;
            }
            let total: i64 = dims
                .iter()
                .zip(&allowed)
                .map(|(n, a)| a.map_or(*n, |(_, len)| len))
                .product();
            if total > MAX_COV || set.len() as i64 + total > MAX_COV {
                return Cov::All;
            }
            // Enumerate the allowed offsets (mixed radix).
            let ranges: Vec<(i64, i64)> = dims
                .iter()
                .zip(&allowed)
                .map(|(n, a)| a.unwrap_or((0, *n)))
                .collect();
            if ranges.iter().any(|r| r.1 <= 0) {
                continue;
            }
            let mut idx: Vec<i64> = ranges.iter().map(|r| r.0).collect();
            'next: loop {
                let mut key = 0;
                for (k, n) in dims.iter().enumerate() {
                    key = key * n + idx[k];
                }
                set.insert(c.base + key);
                let mut k = dims.len();
                loop {
                    if k == 0 {
                        break 'next;
                    }
                    k -= 1;
                    idx[k] += 1;
                    if idx[k] < ranges[k].0 + ranges[k].1 {
                        break;
                    }
                    idx[k] = ranges[k].0;
                }
            }
        }
        Cov::Set(set)
    }

    /// The transaction function shared by the per-leaf drivers of values of
    /// representation `r` (§10.5.2.2): queues of times, leaves and values,
    /// kept in time order; mode 0 transport, 1 inertial first element
    /// (reject limit), 2 later elements.
    pub(super) fn slot_tx(&mut self, r: &Repr) -> String {
        let name = format!("vh_txs_{}", r.key());
        if self.tx_keys.insert(name.clone()) {
            let et = r.sv();
            let eq = self.eq_expr(r, "qv[i]", "v");
            let _ = write!(
                self.tx_defs,
                "  function automatic void {name}(ref longint qt[$], ref longint qk[$], ref {et} qv[$], input longint k, input {et} v, input longint after, input longint rej, input int mode);\n    longint tt;\n    int i, pos;\n    bit keep;\n    tt = longint'($time) + after;\n    for (i = qt.size() - 1; i >= 0; i--) if (qk[i] == k && qt[i] >= tt) begin qt.delete(i); qk.delete(i); qv.delete(i); end\n    if (mode == 1) begin\n      keep = 1;\n      for (i = qt.size() - 1; i >= 0; i--) begin\n        if (qk[i] != k) continue;\n        if (qt[i] < tt - rej) break;\n        if (keep && ({eq})) continue;\n        keep = 0;\n        qt.delete(i); qk.delete(i); qv.delete(i);\n      end\n    end\n    pos = qt.size();\n    for (i = 0; i < qt.size(); i++) if (qt[i] > tt) begin pos = i; break; end\n    if (pos == qt.size()) begin\n      qt.push_back(tt); qk.push_back(k); qv.push_back(v);\n    end else begin\n      qt.insert(pos, tt); qk.insert(pos, k); qv.insert(pos, v);\n    end\n  endfunction\n",
                name = name,
                et = et,
                eq = eq
            );
        }
        name
    }

    /// The transaction function shared by the drivers of whole values of
    /// representation `r` (§10.5.2.2): mode 0 transport, 1 inertial first
    /// element (reject limit), 2 later elements.
    pub(super) fn whole_tx(&mut self, r: &Repr) -> String {
        let name = format!("vh_txw_{}", r.key());
        if self.tx_keys.insert(name.clone()) {
            let t = r.sv();
            let eq = self.eq_expr(r, "qv[k]", "v");
            let _ = write!(
                self.tx_defs,
                "  function automatic void {name}(ref longint qt[$], ref {t} qv[$], input {t} v, input longint after, input longint rej, input int mode);\n    longint tt;\n    int k;\n    tt = longint'($time) + after;\n    while (qt.size() > 0 && qt[qt.size()-1] >= tt) begin void'(qt.pop_back()); void'(qv.pop_back()); end\n    if (mode == 1) begin\n      // Pulse rejection: of the old transactions in [tt - rej, tt), keep\n      // the run immediately before the new one that has its value.\n      k = qt.size() - 1;\n      while (k >= 0 && qt[k] >= tt - rej && ({eq})) k--;\n      while (k >= 0 && qt[k] >= tt - rej) begin qt.delete(k); qv.delete(k); k--; end\n    end\n    qt.push_back(tt);\n    qv.push_back(v);\n  endfunction\n",
                name = name,
                t = t,
                eq = eq
            );
        }
        name
    }

    /// The leaf classes driver (s, p) covers (only those get queues).
    fn driver_classes(&self, s: usize, p: usize) -> Vec<usize> {
        let Some(classes) = self.leaf_classes(self.sigs[s].ty) else {
            return Vec::new();
        };
        let cov = self.drivers.get(&(s, p)).map(|d| d.cov.clone());
        classes
            .iter()
            .enumerate()
            .filter(|(_, c)| match &cov {
                Some(Cov::Set(set)) => set.range(c.base..c.base + c.count).next().is_some(),
                _ => true,
            })
            .map(|(i, _)| i)
            .collect()
    }

    /// Driver (s, p) of a signal assigned by parts: per leaf class, queues
    /// of transaction times, leaves and values, the function adding a
    /// transaction (§10.5.2.2) and the one applying those due; and
    /// `vh_drv_{s}_{p}` driving every leaf from a whole value.
    pub(super) fn slot_driver_sv(
        &mut self,
        s: usize,
        p: usize,
        t: &str,
        loc: &Loc,
        guarded: bool,
    ) -> Option<String> {
        let ty = self.sigs[s].ty;
        let classes = self.leaf_classes(ty)?;
        let mut out = String::new();
        let _ = writeln!(out, "  {} vh_dv{}_{};", t, s, p);
        let used = self.driver_classes(s, p);
        for (ci, c) in classes.iter().enumerate() {
            if !used.contains(&ci) {
                continue;
            }
            let r = self.repr(c.scalar, loc);
            let et = r.sv();
            let tx = self.slot_tx(&r);
            let _ = write!(
                out,
                "  longint vh_dt{s}_{p}_c{c}[$];\n  longint vh_dk{s}_{p}_c{c}[$];\n  {et} vh_dq{s}_{p}_c{c}[$];\n  function automatic void vh_drs_{s}_{p}_c{c}(longint k, {et} v, longint after, longint rej, int mode);\n    {tx}(vh_dt{s}_{p}_c{c}, vh_dk{s}_{p}_c{c}, vh_dq{s}_{p}_c{c}, k, v, after, rej, mode);\n  endfunction\n  function automatic void vh_drd_{s}_{p}_c{c}();\n    longint k;\n    while (vh_dt{s}_{p}_c{c}.size() > 0 && vh_dt{s}_{p}_c{c}[0] <= $time) begin\n      void'(vh_dt{s}_{p}_c{c}.pop_front());\n      k = vh_dk{s}_{p}_c{c}.pop_front();\n      vh_dv{s}_{p}{leaf} = vh_dq{s}_{p}_c{c}.pop_front();\n      vh_s{s}_act = 1;\n    end\n  endfunction\n",
                s = s,
                p = p,
                c = ci,
                et = et,
                tx = tx,
                leaf = Self::leaf_sv(c, "k")
            );
        }
        // Whole assignments: only by a driver covering every leaf.
        if used.len() != classes.len() {
            return Some(out);
        }
        let mut body = String::new();
        if guarded {
            body.push_str("    if (nl) begin vh_fatal(\"a null transaction to a signal also assigned by parts is not supported\"); return; end\n");
        }
        self.emit_leaves(s, p, ty, "v", &mut Vec::new(), None, None, &mut body, 4, 0);
        let _ = write!(
            out,
            "  // The whole signal: every leaf.\n  function automatic void vh_drv_{s}_{p}({t} v, longint after, longint rej, int mode{g});\n{body}  endfunction\n",
            s = s,
            p = p,
            t = t,
            g = if guarded { ", bit nl" } else { "" },
            body = body
        );
        Some(out)
    }

    /// Code adding a transaction for every scalar leaf of value `val` of
    /// type `t`, at path `path` (SV offsets) of signal `s`; `slice_start`
    /// shifts the offsets of the value's first dimension (a slice target,
    /// whose value has `slice_len` elements when static).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn emit_leaves(
        &mut self,
        s: usize,
        p: usize,
        t: TypeId,
        val: &str,
        path: &mut Vec<(Option<usize>, String)>,
        slice_start: Option<String>,
        slice_len: Option<i64>,
        out: &mut String,
        ind: usize,
        depth: usize,
    ) {
        let pad = " ".repeat(ind);
        let b = self.base(t);
        match &self.d.types[b].kind.clone() {
            TypeKind::Record(_) => {
                // Fields as stored (an unconstrained element is a struct).
                for (i, ft) in self.field_storage(t).into_iter().enumerate() {
                    path.push((Some(i), String::new()));
                    self.emit_leaves(s, p, ft, &format!("{}.f{}", val, i), path, None, None, out, ind, depth);
                    path.pop();
                }
            }
            TypeKind::Array { index, .. } => {
                let ndim = index.len();
                let Some(e) = self.d.element_subtype(t) else { return };
                let mut v = val.to_string();
                let mut opened = 0;
                // A packed value: `pk_n` elements (a slice target's value has
                // the slice's length, `slice_len`).
                let pk = match self.repr(t, &self.d.objects[0].loc.clone()) {
                    Repr::Pk(w, n) => Some((w, slice_len.unwrap_or(n))),
                    _ => None,
                };
                for k in 0..ndim {
                    let iv = format!("vh_li{}_{}", depth, k);
                    let off = match (&slice_start, k) {
                        (Some(st), 0) => format!("({} + {})", st, iv),
                        _ => iv.clone(),
                    };
                    let count = match pk {
                        Some((_, n)) => n.to_string(),
                        None => format!("{}.d.size()", v),
                    };
                    let _ = writeln!(
                        out,
                        "{}{}for (longint {iv} = 0; {iv} < {count}; {iv}++) begin",
                        pad,
                        "  ".repeat(opened),
                        iv = iv,
                        count = count
                    );
                    opened += 1;
                    path.push((None, off));
                    v = match pk {
                        Some((w, n)) => Lw::pk_sel(&v, w, n, &iv),
                        None => format!("{}.d[{}]", v, iv),
                    };
                }
                self.emit_leaves(s, p, e, &v, path, None, None, out, ind + 2 * opened, depth + 1);
                for _ in 0..ndim {
                    path.pop();
                }
                for k in (0..opened).rev() {
                    let _ = writeln!(out, "{}{}end", pad, "  ".repeat(k));
                }
            }
            _ => {
                // The class of this leaf: the same fields and dimensions.
                let Some(classes) = self.leaf_classes(self.sigs[s].ty) else { return };
                let shape: Vec<Step> = path
                    .iter()
                    .map(|(f, _)| match f {
                        Some(i) => Step::Field(*i),
                        None => Step::Dim(0),
                    })
                    .collect();
                let Some((ci, c)) = classes.iter().enumerate().find(|(_, c)| {
                    c.steps.len() == shape.len()
                        && c.steps.iter().zip(&shape).all(|(a, b)| match (a, b) {
                            (Step::Field(x), Step::Field(y)) => x == y,
                            (Step::Dim(_) | Step::PDim(..), Step::Dim(_)) => true,
                            _ => false,
                        })
                }) else {
                    return;
                };
                let dims = c.dims();
                let offs: Vec<&String> = path.iter().filter(|(f, _)| f.is_none()).map(|(_, o)| o).collect();
                let mut key = String::from("0");
                for (k, n) in dims.iter().enumerate() {
                    key = if key == "0" {
                        offs[k].clone()
                    } else {
                        format!("({}) * {} + {}", key, n, offs[k])
                    };
                }
                let _ = writeln!(
                    out,
                    "{}vh_drs_{}_{}_c{}({}, {}, after, rej, mode);",
                    pad, s, p, ci, key, val
                );
            }
        }
    }

    /// Kernel: apply the due transactions of driver (s, p) by parts.
    pub(super) fn slot_driver_due(&self, s: usize, p: usize, ind: &str) -> String {
        let mut out = String::new();
        for c in self.driver_classes(s, p) {
            let _ = writeln!(out, "{}vh_drd_{}_{}_c{}();", ind, s, p, c);
        }
        out
    }

    /// The next transaction time of driver (s, p) by parts.
    pub(super) fn slot_driver_next(&self, s: usize, p: usize) -> String {
        let mut out = String::new();
        for c in self.driver_classes(s, p) {
            let _ = writeln!(
                out,
                "    if (vh_dt{s}_{p}_c{c}.size() > 0 && (n < 0 || vh_dt{s}_{p}_c{c}[0] < n)) n = vh_dt{s}_{p}_c{c}[0];",
                s = s,
                p = p,
                c = c
            );
        }
        out
    }

    /// The body computing the new value `nv` of signal `s` from drivers
    /// `ds`, leaf by leaf: from the driver covering a leaf, or through the
    /// leaf's resolution function over those covering it (§14.7.3.2). For
    /// a guarded signal only the drivers that are on take part; with none,
    /// a register keeps its value and a bus resolves no values.
    pub(super) fn leaf_update_body(
        &mut self,
        s: usize,
        ds: &[(usize, Driver)],
        tsv: &str,
        info: &ObjInfo,
        kind: Option<crate::vhdl::ast::SignalKind>,
    ) -> Option<String> {
        let ty = self.sigs[s].ty;
        let Some(classes) = self.leaf_classes(ty) else {
            self.err(
                &info.loc,
                format!("signal '{}' has drivers of parts but bounds that are not static", info.name),
            );
            return None;
        };
        let mut body = String::new();
        let _ = writeln!(body, "    {} nv;\n    int c, cc;\n    longint g;", tsv);
        let _ = writeln!(body, "    nv = vh_s{};", s);
        for c in &classes {
            let cov: Vec<&(usize, Driver)> = ds
                .iter()
                .filter(|(_, d)| match &d.cov {
                    Cov::All => true,
                    Cov::Set(set) => set.range(c.base..c.base + c.count).next().is_some(),
                })
                .collect();
            if cov.is_empty() {
                continue;
            }
            let res = self.resolution(c.scalar);
            if res.is_none() && kind.is_none() {
                // At most one driver of each scalar of an unresolved signal.
                for (i, a) in cov.iter().enumerate() {
                    for b in &cov[i + 1..] {
                        if a.1.cov.overlaps(&b.1.cov, c.base, c.count) {
                            self.err(
                                &info.loc,
                                format!("unresolved signal '{}' has several drivers", info.name),
                            );
                            return None;
                        }
                    }
                }
            }
            let et = self.repr(c.scalar, &info.loc).sv();
            let leaf = Self::leaf_sv(c, "k");
            let _ = writeln!(
                body,
                "    for (longint k = 0; k < {}; k++) begin\n      {} rv[{}];\n      g = {} + k;\n      c = 0; cc = 0;",
                c.count,
                et,
                cov.len(),
                c.base
            );
            for (p, d) in &cov {
                let cond = super::elab::cov_cond_var(&d.cov, "g");
                if kind.is_some() {
                    let _ = writeln!(
                        body,
                        "      if ({cond}) begin cc++; if (vh_don{s}_{p}) begin rv[c] = vh_dv{s}_{p}{leaf}; c++; end end",
                        cond = cond,
                        s = s,
                        p = p,
                        leaf = leaf
                    );
                } else {
                    let _ = writeln!(
                        body,
                        "      if ({cond}) begin rv[c] = vh_dv{s}_{p}{leaf}; c++; end",
                        cond = cond,
                        s = s,
                        p = p,
                        leaf = leaf
                    );
                }
            }
            let any = if kind == Some(crate::vhdl::ast::SignalKind::Bus) {
                "cc"
            } else {
                "c"
            };
            match res {
                Some((f, _)) => {
                    let pt = self.d.objects[self.d.subprograms[f].params[0]].ty;
                    let pname = self.arr_name(pt, &info.loc);
                    self.need_sub(f);
                    let _ = writeln!(
                        body,
                        "      if ({any} > 0) begin\n        {et} ra[];\n        ra = new[c];\n        for (int j = 0; j < c; j++) ra[j] = rv[j];\n        nv{leaf} = {f}({p}_mk(0, c - 1, 0, ra));\n      end",
                        any = any,
                        et = et,
                        leaf = leaf,
                        f = self.sub_name(f),
                        p = pname
                    );
                }
                None => {
                    let _ = writeln!(body, "      if (c > 0) nv{} = rv[0];", leaf);
                }
            }
            let _ = writeln!(body, "    end");
        }
        Some(body)
    }

    /// The path an assignment target names (`a(i)(j)`, `r.f(3 downto 0)`):
    /// the signal and the steps, with offsets computed where the target is
    /// lowered; `None` when it is not a signal (part).
    pub(super) fn target_path(&mut self, t: &HExpr) -> Option<(usize, Vec<DSel>)> {
        let (f, l, _) = self.file_line(&t.loc);
        match &t.kind {
            HExprKind::Obj(o) => {
                let r = self.lookup_sig(self.inst, *o)?;
                let path = match r.part {
                    super::elab::Part::Whole => Vec::new(),
                    super::elab::Part::Path(p) => p
                        .into_iter()
                        .map(|s| match s {
                            Sel::Field(i) => DSel::Field(i),
                            Sel::Elem(k) => DSel::Elem(k.to_string(), Some(k)),
                            Sel::Slice(k, n) => DSel::Slice(k.to_string(), n.to_string(), Some((k, n))),
                        })
                        .collect(),
                };
                Some((r.sig, path))
            }
            HExprKind::Field(b, i) => {
                let (s, mut path) = self.target_path(b)?;
                path.push(DSel::Field(*i));
                Some((s, path))
            }
            HExprKind::Index(b, idx) => {
                let (s, mut path) = self.target_path(b)?;
                // Within a slice: offsets from the slice's start.
                let (start, start_v) = match path.last() {
                    Some(DSel::Slice(o, _, v)) => (Some(o.clone()), Some(v.map(|x| x.0))),
                    _ => (None, None),
                };
                if start.is_some() {
                    path.pop();
                }
                let bounds = self.shape(b);
                let bv = match bounds {
                    Some(_) => String::new(),
                    None => self.ex(b),
                };
                for (k, x) in idx.iter().enumerate() {
                    let i = self.ex(x);
                    let arr = if k == 0 { bv.clone() } else { format!("{}{}", bv, ".d[0]".repeat(k)) };
                    let mut off = match (k, bounds) {
                        (0, Some(bnd)) => self.pk_off(&i, bnd, &t.loc),
                        _ => format!(
                            "vh_ix({}, {a}.l, {a}.r, {a}.dn, {}, {})",
                            i,
                            sv_string(&f),
                            l,
                            a = arr
                        ),
                    };
                    let mut v = match (k, bounds, self.d.eval(x).and_then(|v| v.as_i64())) {
                        (0, Some((lb, dir, _)), Some(iv)) => Some(match dir {
                            Dir::To => iv - lb,
                            Dir::Downto => lb - iv,
                        }),
                        _ => None,
                    };
                    if k == 0
                        && let Some(st) = &start
                    {
                        off = format!("({} + {})", st, off);
                        v = match (v, start_v.flatten()) {
                            (Some(a), Some(b)) => Some(a + b),
                            _ => None,
                        };
                    }
                    path.push(DSel::Elem(off, v));
                }
                Some((s, path))
            }
            HExprKind::Slice(b, rg) => {
                let (s, mut path) = self.target_path(b)?;
                let (start, start_v) = match path.last() {
                    Some(DSel::Slice(o, _, v)) => (Some(o.clone()), Some(v.map(|x| x.0))),
                    _ => (None, None),
                };
                if start.is_some() {
                    path.pop();
                }
                let bounds = self.shape(b);
                let (left, right, dn) = self.range_parts(rg);
                let mut off = match bounds {
                    Some(bnd) => self.pk_off(&left, bnd, &t.loc),
                    None => {
                        let bv = self.ex(b);
                        format!(
                            "vh_ix({}, {b}.l, {b}.r, {b}.dn, {}, {})",
                            left,
                            sv_string(&f),
                            l,
                            b = bv
                        )
                    }
                };
                let n = format!("vh_len({}, {}, {})", left, right, dn);
                let mut v = match (self.range_bounds(rg), bounds) {
                    (Some(sr), Some((lb, dir, _))) => {
                        let o = match dir {
                            Dir::To => sr.0 - lb,
                            Dir::Downto => lb - sr.0,
                        };
                        Some((o, super::packed::bounds_len(sr)))
                    }
                    _ => None,
                };
                if let Some(st) = &start {
                    off = format!("({} + {})", st, off);
                    v = match (v, start_v.flatten()) {
                        (Some((a, len)), Some(b)) => Some((a + b, len)),
                        _ => None,
                    };
                }
                path.push(DSel::Slice(off, n, v));
                Some((s, path))
            }
            _ => None,
        }
    }

    /// The transactions of an assignment of `val` (of type `t`) to path
    /// `path` of signal `s` by process `p`.
    pub(super) fn drive_path(
        &mut self,
        s: usize,
        p: usize,
        path: &[DSel],
        t: TypeId,
        val: &str,
        timing: (&str, &str, i32),
        ind: usize,
    ) -> String {
        let pad = " ".repeat(ind);
        let mut prefix: Vec<(Option<usize>, String)> = Vec::new();
        let mut slice_start = None;
        let mut slice_len = None;
        for sel in path {
            match sel {
                DSel::Field(i) => prefix.push((Some(*i), String::new())),
                DSel::Elem(o, _) => prefix.push((None, o.clone())),
                DSel::Slice(o, _, v) => {
                    slice_start = Some(o.clone());
                    slice_len = v.map(|x| x.1);
                }
            }
        }
        let mut body = String::new();
        self.emit_leaves(s, p, t, val, &mut prefix, slice_start, slice_len, &mut body, ind + 2, 0);
        let (after, rej, mode) = timing;
        format!(
            "{pad}begin\n{pad}  longint after, rej;\n{pad}  int mode;\n{pad}  after = {after}; rej = {rej}; mode = {mode};\n{body}{pad}end\n",
            pad = pad,
            after = after,
            rej = rej,
            mode = mode,
            body = body
        )
    }

    /// The SV reading part `path` of value `base` of signal `s` (a formal
    /// associated with that part: `ty`, the formal's subtype).
    pub(super) fn path_read(&mut self, base: &str, path: &[Sel], s: usize, ty: TypeId, loc: &Loc) -> String {
        let (sel, slice, at) = self.path_sv(self.sigs[s].ty, path, loc);
        let Some((off, len)) = slice else {
            return format!("{}{}", base, sel);
        };
        if let Repr::Pk(w, n) = self.repr(at, loc) {
            return Lw::pk_part(&format!("{}{}", base, sel), w, n, off, len);
        }
        let name = self.arr_name(ty, loc);
        // The formal's bounds, else those of the actual's part.
        let (l, r, dn) = match self.dim_bounds(ty, 0) {
            Some(b) => b,
            None => {
                let st = self.path_type(self.sigs[s].ty, &path[..path.len() - 1]);
                let (al, adir, _) = st
                    .and_then(|t| self.static_bounds(t))
                    .unwrap_or((0, Dir::To, 0));
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
        format!("{}_sub({}{}, {}, {}, {}, {}, {})", name, base, sel, off, len, l, r, dn)
    }

    /// The subtype at a static path from type `t`.
    pub(super) fn path_type(&self, t: TypeId, path: &[Sel]) -> Option<TypeId> {
        let mut cur = t;
        for s in path {
            cur = match s {
                Sel::Field(i) => self.d.record_fields(cur).get(*i)?.1,
                Sel::Elem(_) => self.d.element_subtype(cur)?,
                Sel::Slice(..) => cur,
            };
        }
        Some(cur)
    }
}
