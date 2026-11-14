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
                // One vector, not one class per field. A partial assign
                // overlays that vector (`packed_record_drive`); two
                // drivers overlap it and are rejected as an unresolved
                // signal with several drivers.
                if packed && let Some((ew, n)) = self.record_array_pack(t) {
                    let total = ew as i64 * n;
                    steps.push(Step::PDim(1, total as u32));
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
                    steps.pop();
                    return Some(());
                }
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
                let pk = self.elem_packs(t);
                self.collect_classes(e, steps, out, pk)?;
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

    /// The element of the outer dimension of a class, selected by `k`, and
    /// the number of leaves under it, when only array dimensions lie below
    /// that dimension (a record field below it is a class of its own, which
    /// another driver may cover).
    fn leaf_elem_sv(c: &LeafClass, k: &str) -> Option<(i64, String)> {
        let first = c.steps.iter().position(|s| matches!(s, Step::Dim(_)))?;
        if c.steps[..first]
            .iter()
            .any(|s| !matches!(s, Step::Field(_)))
            || c.steps[first + 1..]
                .iter()
                .any(|s| matches!(s, Step::Field(_)))
            || first + 1 == c.steps.len()
        {
            return None;
        }
        let mut out = String::new();
        for s in &c.steps[..first] {
            if let Step::Field(i) = s {
                let _ = write!(out, ".f{}", i);
            }
        }
        let _ = write!(out, ".d[{}]", k);
        let stride: i64 = c.dims()[1..].iter().product();
        Some((stride, out))
    }

    /// A class that is one packed vector under record fields: the fields'
    /// selection, the element bits and the length.
    fn whole_class(c: &LeafClass) -> Option<(String, u32, i64)> {
        let (last, fields) = c.steps.split_last()?;
        let Step::PDim(n, w) = last else { return None };
        let mut pre = String::new();
        for s in fields {
            let Step::Field(i) = s else { return None };
            let _ = write!(pre, ".f{}", i);
        }
        (*n >= 1).then_some((pre, *w, *n))
    }

    /// The packed word a class's trailing `PDim` selects, indexed by word
    /// number `k` rather than by scalar leaf. `None` when the class is not
    /// a packed vector of more than one element under record and array steps.
    ///
    /// The leaf walk would otherwise copy that word a nibble at a time
    /// (`[4*(31-(k%32)) +: 4]`), which keeps `vh_upd` on the interpreter.
    /// One assignment of the word is the same value when the driver covers
    /// every element of it.
    fn packed_word_sv(c: &LeafClass, k: &str) -> Option<String> {
        let last = c.steps.len().checked_sub(1)?;
        let Step::PDim(n, _) = c.steps[last] else {
            return None;
        };
        if n <= 1 {
            return None;
        }
        let dims: Vec<i64> = c.steps[..last]
            .iter()
            .filter_map(|s| match s {
                Step::Dim(d) | Step::PDim(d, _) => Some(*d),
                Step::Field(_) => None,
            })
            .collect();
        let mut out = String::new();
        let mut di = 0;
        for s in &c.steps[..last] {
            match s {
                Step::Field(i) => {
                    let _ = write!(out, ".f{}", i);
                }
                Step::Dim(d) | Step::PDim(d, _) => {
                    let stride: i64 = dims[di + 1..].iter().copied().product();
                    di += 1;
                    let idx = match (stride, dims.len() == 1) {
                        (1, true) => k.to_string(),
                        (1, false) => format!("(({}) % {})", k, d),
                        _ => format!("((({}) / {}) % {})", k, stride, d),
                    };
                    match s {
                        Step::PDim(nn, w) => {
                            let _ = write!(out, "[{} * ({} - ({})) +: {}]", w, nn - 1, idx, w);
                        }
                        _ => {
                            let _ = write!(out, ".d[{}]", idx);
                        }
                    }
                }
            }
        }
        Some(out)
    }

    /// A packed word under an array: the number of words, the element
    /// bits and the elements per word. A bare packed vector is handled by
    /// `whole_class` and is not this.
    fn word_pending(c: &LeafClass) -> Option<(i64, u32, i64)> {
        let (n, w) = match c.steps.last() {
            Some(Step::PDim(n, w)) if *n > 1 => (*n, *w),
            _ => return None,
        };
        if !c.steps.iter().any(|s| matches!(s, Step::Dim(_))) {
            return None;
        }
        let nwords = c.count / n;
        (nwords >= 1).then_some((nwords, w, n))
    }

    /// The word number of a packed element reached by `path` (the indices
    /// above the trailing `PDim`).
    fn word_key(c: &LeafClass, path: &[(Option<usize>, String)]) -> Option<String> {
        let last = c.steps.len().checked_sub(1)?;
        let dims: Vec<i64> = c.steps[..last]
            .iter()
            .filter_map(|s| match s {
                Step::Dim(d) | Step::PDim(d, _) => Some(*d),
                Step::Field(_) => None,
            })
            .collect();
        let offs: Vec<&String> = path.iter().filter(|(f, _)| f.is_none()).map(|(_, o)| o).collect();
        if dims.is_empty() || dims.len() != offs.len() {
            return None;
        }
        let mut key = String::from("0");
        for (k, n) in dims.iter().enumerate() {
            key = if key == "0" {
                offs[k].clone()
            } else {
                format!("({}) * {} + {}", key, n, offs[k])
            };
        }
        Some(key)
    }

    /// The class of the packed vector at `path` (the path steps, then its
    /// `PDim` of `n` elements).
    fn packed_class<'b>(
        classes: &'b [LeafClass],
        path: &[(Option<usize>, String)],
        n: i64,
    ) -> Option<(usize, &'b LeafClass)> {
        classes.iter().enumerate().find(|(_, c)| {
            let Some(Step::PDim(pn, _)) = c.steps.last() else {
                return false;
            };
            *pn == n
                && c.steps.len() == path.len() + 1
                && c.steps[..path.len()].iter().zip(path).all(|(a, (f, _))| match (a, f) {
                    (Step::Field(x), Some(y)) => x == y,
                    (Step::Dim(_), None) => true,
                    _ => false,
                })
        })
    }

    /// The runs of consecutive leaves of a coverage in `base..base + count`.
    fn cov_runs(cov: &Cov, base: i64, count: i64) -> Vec<(i64, i64)> {
        let mut runs: Vec<(i64, i64)> = Vec::new();
        let leaves: Vec<i64> = match cov {
            Cov::All => {
                return if count > 0 {
                    vec![(base, base + count - 1)]
                } else {
                    Vec::new()
                };
            }
            Cov::Set(set) => set.range(base..base + count).copied().collect(),
        };
        for x in leaves {
            match runs.last_mut() {
                Some((_, b)) if *b + 1 == x => *b = x,
                _ => runs.push((x, x)),
            }
        }
        runs
    }

    /// The global numbers of the leaves under a path; a step with an
    /// offset computed at run time covers every offset of its dimension.
    pub(super) fn path_cov(&self, t: TypeId, path: &[DSel]) -> Cov {
        // The packed record array is one leaf: every part drives it.
        if self.record_array_pack(t).is_some() {
            return Cov::All;
        }
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
            let cap = c.count.max(1);
            // A zero-delay assignment of the whole vector is one pending
            // value (`emit_leaves`); a queued transaction first queues it.
            let mut flush = String::new();
            let mut wflush = String::new();
            if let Some((nwords, w, n)) = Self::word_pending(c) {
                let bits = w as i64 * n - 1;
                let _ = writeln!(
                    out,
                    "  bit [{bits}:0] vh_pww{s}_{p}_c{ci} [0:{nw}];\n  bit vh_pwwm{s}_{p}_c{ci} [0:{nw}];\n  longint vh_pwwi{s}_{p}_c{ci} [0:{nw}];\n  int vh_pwwn{s}_{p}_c{ci};",
                    bits = bits,
                    nw = nwords - 1,
                    s = s,
                    p = p,
                    ci = ci
                );
                let _ = write!(
                    wflush,
                    "    if (vh_pwwn{s}_{p}_c{ci} > 0) begin for (vh_pi = 0; vh_pi < vh_pwwn{s}_{p}_c{ci}; vh_pi = vh_pi + 1) begin vh_lkk = vh_pwwi{s}_{p}_c{ci}[vh_pi]; if (vh_pwwm{s}_{p}_c{ci}[vh_lkk]) begin for (vh_pj = 0; vh_pj < {n}; vh_pj = vh_pj + 1) {tx}(vh_dt{s}_{p}_c{ci}, vh_dk{s}_{p}_c{ci}, vh_dq{s}_{p}_c{ci}, vh_lkk * {n} + vh_pj, vh_pww{s}_{p}_c{ci}[vh_lkk][{w} * ({n1} - vh_pj) +: {w}], 64'sd0, 64'sd0, 0); vh_pwwm{s}_{p}_c{ci}[vh_lkk] = 0; end end vh_pwwn{s}_{p}_c{ci} = 0; end\n",
                    n1 = n - 1,
                    s = s,
                    p = p,
                    ci = ci,
                    tx = tx,
                    n = n,
                    w = w
                );
            }
            if let Some((_, w, n)) = Self::whole_class(c) {
                let _ = writeln!(
                    out,
                    "  bit [{hi}:0] vh_pw{s}_{p}_c{ci};\n  bit vh_pwf{s}_{p}_c{ci};",
                    hi = w as i64 * n - 1
                );
                let _ = write!(
                    flush,
                    "    if (vh_pwf{s}_{p}_c{ci}) begin\n      vh_pwf{s}_{p}_c{ci} = 0;\n      for (vh_pj = 0; vh_pj < {n}; vh_pj = vh_pj + 1) {tx}(vh_dt{s}_{p}_c{ci}, vh_dk{s}_{p}_c{ci}, vh_dq{s}_{p}_c{ci}, vh_pj, vh_pw{s}_{p}_c{ci}[{w} * ({n1} - vh_pj) +: {w}], 64'sd0, 64'sd0, 0);\n    end\n",
                    n1 = n - 1
                );
            }
            // Pending zero-delay values by leaf, the leaves pending (each
            // once), and their number (the fast path of `emit_leaves`); a
            // queued transaction first moves the pending ones into the queue.
            let _ = write!(
                out,
                "  longint vh_dt{s}_{p}_c{c}[$];\n  longint vh_dk{s}_{p}_c{c}[$];\n  {et} vh_dq{s}_{p}_c{c}[$];\n  int vh_sqn{s}_{p}_c{c};\n  {et} vh_pf{s}_{p}_c{c} [0:{cnt1}];\n  bit vh_pm{s}_{p}_c{c} [0:{cnt1}];\n  longint vh_pl{s}_{p}_c{c} [0:{cap1}];\n  int vh_pn{s}_{p}_c{c};\n  function automatic void vh_drs_{s}_{p}_c{c}(longint k, {et} v, longint after, longint rej, int mode);\n{wflush}{flush}    for (vh_pj = 0; vh_pj < vh_pn{s}_{p}_c{c}; vh_pj = vh_pj + 1) begin\n      vh_lkk = vh_pl{s}_{p}_c{c}[vh_pj];\n      if (vh_pm{s}_{p}_c{c}[vh_lkk]) begin {tx}(vh_dt{s}_{p}_c{c}, vh_dk{s}_{p}_c{c}, vh_dq{s}_{p}_c{c}, vh_lkk, vh_pf{s}_{p}_c{c}[vh_lkk], 64'sd0, 64'sd0, 0); vh_pm{s}_{p}_c{c}[vh_lkk] = 0; end\n    end\n    vh_pn{s}_{p}_c{c} = 0;\n    {tx}(vh_dt{s}_{p}_c{c}, vh_dk{s}_{p}_c{c}, vh_dq{s}_{p}_c{c}, k, v, after, rej, mode);\n    vh_sqn{s}_{p}_c{c} = vh_dt{s}_{p}_c{c}.size();\n  endfunction\n  function automatic void vh_drd_{s}_{p}_c{c}();\n    longint k;\n    while (vh_dt{s}_{p}_c{c}.size() > 0 && vh_dt{s}_{p}_c{c}[0] <= vh_now) begin\n      void'(vh_dt{s}_{p}_c{c}.pop_front());\n      k = vh_dk{s}_{p}_c{c}.pop_front();\n      vh_dv{s}_{p}{leaf} = vh_dq{s}_{p}_c{c}.pop_front();\n      vh_s{s}_act = 1;\n    end\n    vh_sqn{s}_{p}_c{c} = vh_dt{s}_{p}_c{c}.size();\n  endfunction\n",
                s = s,
                p = p,
                c = ci,
                et = et,
                tx = tx,
                wflush = wflush,
                flush = flush,
                cnt1 = c.count.max(1) - 1,
                cap1 = cap - 1,
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
        // A whole packed record array is one pending vector. Parts are
        // overlaid by `drive_path` before this is reached.
        if path.is_empty()
            && slice_start.is_none()
            && self.record_array_pack(t).is_some()
            && let Some(ci) = self.packed_record_class(s)
        {
            let _ = writeln!(
                out,
                "{pad}if (vh_sqn{s}_{p}_c{ci} == 0) begin vh_pw{s}_{p}_c{ci} = {val}; vh_pwf{s}_{p}_c{ci} = 1; end else vh_drs_{s}_{p}_c{ci}(0, {val}, after, rej, mode);",
                pad = pad,
                s = s,
                p = p,
                ci = ci,
                val = val
            );
            return;
        }
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
                // The elements as stored (an element constraint of an array
                // of unconstrained arrays leaves them structs).
                let Some(e) = self.elem_storage(t) else { return };
                let mut v = val.to_string();
                let mut opened = 0;
                // A packed value: `pk_n` elements (a slice target's value has
                // the slice's length, `slice_len`).
                let pk = match self.repr(t, &self.d.objects[0].loc.clone()) {
                    Repr::Pk(w, n) => Some((w, slice_len.unwrap_or(n))),
                    _ => None,
                };
                // The whole of a packed vector, with no queued transaction:
                // one pending value, which replaces those pending by leaf.
                let mut whole = false;
                if let Some((_, n)) = pk
                    && ndim == 1
                    && slice_start.is_none()
                    && slice_len.is_none()
                    && self.leaf_zero
                    && self.sig_kind(s).is_none()
                    && path.iter().all(|(f, _)| f.is_some())
                    && self.ndims(e) == 0
                    && let Some(classes) = self.leaf_classes(self.sigs[s].ty)
                {
                    let pre: String = path.iter().map(|(f, _)| format!(".f{}", f.unwrap_or(0))).collect();
                    if let Some(ci) = classes
                        .iter()
                        .position(|c| Self::whole_class(c).is_some_and(|(q, _, m)| q == pre && m == n))
                        && self.driver_classes(s, p).contains(&ci)
                    {
                        whole = true;
                        let _ = writeln!(
                            out,
                            "{pad}if (vh_sqn{s}_{p}_c{c} == 0) begin\n{pad}  if (vh_pn{s}_{p}_c{c} > 0) begin for (vh_pi = 0; vh_pi < vh_pn{s}_{p}_c{c}; vh_pi = vh_pi + 1) vh_pm{s}_{p}_c{c}[vh_pl{s}_{p}_c{c}[vh_pi]] = 0; vh_pn{s}_{p}_c{c} = 0; end\n{pad}  vh_pw{s}_{p}_c{c} = {val}; vh_pwf{s}_{p}_c{c} = 1;\n{pad}end else begin",
                            pad = pad,
                            c = ci
                        );
                    }
                }
                // The same, for one element of an array: one pending word
                // instead of a nibble per element. A nibble already pending
                // (a bit assigned earlier in this process) keeps the loop,
                // and the due phase applies nibbles after words so the bit
                // wins.
                let mut word = false;
                if !whole
                    && let Some((_, n)) = pk
                    && ndim == 1
                    && slice_start.is_none()
                    && slice_len.is_none()
                    && self.leaf_zero
                    && self.sig_kind(s).is_none()
                    && path.iter().any(|(f, _)| f.is_none())
                    && self.ndims(e) == 0
                    && let Some(classes) = self.leaf_classes(self.sigs[s].ty)
                    && let Some((ci, c)) = Self::packed_class(&classes, path, n)
                    && Self::word_pending(c).is_some()
                    && self.driver_classes(s, p).contains(&ci)
                    && let Some(key) = Self::word_key(c, path)
                {
                    word = true;
                    let _ = writeln!(
                        out,
                        "{pad}if (vh_sqn{s}_{p}_c{c} == 0 && vh_pn{s}_{p}_c{c} == 0) begin\n{pad}  vh_lk = {key};\n{pad}  vh_pww{s}_{p}_c{c}[vh_lk] = {val}; if (!vh_pwwm{s}_{p}_c{c}[vh_lk]) begin vh_pwwm{s}_{p}_c{c}[vh_lk] = 1; vh_pwwi{s}_{p}_c{c}[vh_pwwn{s}_{p}_c{c}] = vh_lk; vh_pwwn{s}_{p}_c{c} = vh_pwwn{s}_{p}_c{c} + 1; end\n{pad}end else begin",
                        pad = pad,
                        key = key,
                        c = ci,
                        val = val
                    );
                }
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
                    self.leaf_vars.insert(iv.clone());
                    let _ = writeln!(
                        out,
                        "{}{}for ({iv} = 0; {iv} < {count}; {iv} = {iv} + 1) begin",
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
                if whole || word {
                    let _ = writeln!(out, "{}end", pad);
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
                if self.leaf_zero && self.sig_kind(s).is_none() {
                    // A zero-delay assignment to a leaf without queued
                    // transactions: a pending value (compiled code), applied
                    // by the update phase; else the queue (`vh_drs`).
                    let _ = writeln!(
                        out,
                        "{pad}vh_lk = {key};\n{pad}if (vh_sqn{s}_{p}_c{c} == 0) begin vh_pf{s}_{p}_c{c}[vh_lk] = {val}; if (!vh_pm{s}_{p}_c{c}[vh_lk]) begin vh_pm{s}_{p}_c{c}[vh_lk] = 1; vh_pl{s}_{p}_c{c}[vh_pn{s}_{p}_c{c}] = vh_lk; vh_pn{s}_{p}_c{c} = vh_pn{s}_{p}_c{c} + 1; end end else vh_drs_{s}_{p}_c{c}(vh_lk, {val}, after, rej, mode);",
                        pad = pad,
                        key = key,
                        s = s,
                        p = p,
                        c = ci,
                        val = val
                    );
                    return;
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
        let Some(classes) = self.leaf_classes(self.sigs[s].ty) else {
            return out;
        };
        for c in self.driver_classes(s, p) {
            let leaf = Self::leaf_sv(&classes[c], "vh_lk");
            if let Some((pre, ..)) = Self::whole_class(&classes[c]) {
                let _ = writeln!(
                    out,
                    "{ind}if (vh_pwf{s}_{p}_c{c}) begin vh_dv{s}_{p}{pre} = vh_pw{s}_{p}_c{c}; vh_pwf{s}_{p}_c{c} = 0; vh_s{s}_act = 1; end"
                );
            }
            if Self::word_pending(&classes[c]).is_some()
                && let Some(pre) = Self::packed_word_sv(&classes[c], "vh_lk")
            {
                let _ = writeln!(
                    out,
                    "{ind}if (vh_pwwn{s}_{p}_c{c} > 0) begin for (vh_pi = 0; vh_pi < vh_pwwn{s}_{p}_c{c}; vh_pi = vh_pi + 1) begin vh_lk = vh_pwwi{s}_{p}_c{c}[vh_pi]; if (vh_pwwm{s}_{p}_c{c}[vh_lk]) begin vh_dv{s}_{p}{pre} = vh_pww{s}_{p}_c{c}[vh_lk]; vh_pwwm{s}_{p}_c{c}[vh_lk] = 0; end end vh_pwwn{s}_{p}_c{c} = 0; vh_s{s}_act = 1; end"
                );
            }
            let _ = writeln!(
                out,
                "{ind}if (vh_pn{s}_{p}_c{c} > 0) begin for (vh_pi = 0; vh_pi < vh_pn{s}_{p}_c{c}; vh_pi = vh_pi + 1) begin vh_lk = vh_pl{s}_{p}_c{c}[vh_pi]; if (vh_pm{s}_{p}_c{c}[vh_lk]) begin vh_dv{s}_{p}{leaf} = vh_pf{s}_{p}_c{c}[vh_lk]; vh_pm{s}_{p}_c{c}[vh_lk] = 0; end end vh_pn{s}_{p}_c{c} = 0; vh_s{s}_act = 1; end",
                ind = ind,
                s = s,
                p = p,
                c = c,
                leaf = leaf
            );
            let _ = writeln!(out, "{ind}if (vh_sqn{s}_{p}_c{c} > 0) vh_drd_{s}_{p}_c{c}();", ind = ind, s = s, p = p, c = c);
        }
        out
    }

    /// The next transaction time of driver (s, p) by parts.
    pub(super) fn slot_driver_next(&self, s: usize, p: usize) -> String {
        let mut out = String::new();
        let classes = self.leaf_classes(self.sigs[s].ty).unwrap_or_default();
        for c in self.driver_classes(s, p) {
            if classes.get(c).is_some_and(|c| Self::whole_class(c).is_some()) {
                let _ = writeln!(out, "    if (vh_pwf{s}_{p}_c{c}) n = vh_now;");
            }
            if classes.get(c).is_some_and(|c| Self::word_pending(c).is_some()) {
                let _ = writeln!(out, "    if (vh_pwwn{s}_{p}_c{c} > 0) n = vh_now;");
            }
            let _ = writeln!(
                out,
                "    if (vh_pn{s}_{p}_c{c} > 0) n = vh_now; else if (vh_sqn{s}_{p}_c{c} > 0 && (n < 0 || vh_dt{s}_{p}_c{c}[0] < n)) n = vh_dt{s}_{p}_c{c}[0];",
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
        // Declarations first: a local declared in the loop over the leaves
        // keeps the loop on the interpreter.
        let mut decls = String::new();
        let _ = writeln!(decls, "    {} nv;\n    int c, cc;\n    longint g, k;", tsv);
        let mut body = String::new();
        let _ = writeln!(body, "    nv = vh_s{};", s);
        for (ci, c) in classes.iter().enumerate() {
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
            // Sources that share no leaf (each process driving its own
            // element, the usual case): a leaf has at most one, whose value
            // it takes (an unresolved signal, or RESOLVED of one value).
            // Each driver copies the leaves it covers, whole elements of the
            // outer dimension where its runs cover them.
            let one_source = match res {
                None => true,
                Some((f, _)) => self.d.subprograms[f]
                    .path
                    .eq_ignore_ascii_case("ieee.std_logic_1164.resolved"),
            };
            let disjoint = cov.iter().enumerate().all(|(i, a)| {
                cov[i + 1..]
                    .iter()
                    .all(|b| !a.1.cov.overlaps(&b.1.cov, c.base, c.count))
            });
            if kind.is_none() && one_source && disjoint {
                let elem = Self::leaf_elem_sv(c, "k");
                for (p, d) in &cov {
                    for (a, b) in Self::cov_runs(&d.cov, c.base, c.count) {
                        let (a, b) = (a - c.base, b - c.base);
                        // A run of whole packed words (every element of each
                        // word, no partial word at either end): one assignment
                        // per word. A nibble loop over the same leaves does
                        // not compile. A bare packed vector (no array
                        // dimension above the word) already has the
                        // one-assignment path below.
                        if c.steps.iter().any(|s| matches!(s, Step::Dim(_)))
                            && let Some(Step::PDim(n, _)) = c.steps.last()
                            && *n > 1
                            && a % *n == 0
                            && (b + 1) % *n == 0
                            && let Some(pre) = Self::packed_word_sv(c, "k")
                        {
                            let _ = writeln!(
                                body,
                                "    for (k = {}; k <= {}; k++) nv{pre} = vh_dv{s}_{p}{pre};",
                                a / *n,
                                b / *n,
                                pre = pre,
                                s = s,
                                p = p
                            );
                            continue;
                        }
                        // The whole class, a scalar or one packed vector
                        // under record fields: one assignment.
                        if a == 0
                            && b == c.count - 1
                            && c.steps.iter().filter(|s| !matches!(s, Step::Field(_))).count() <= 1
                            && !c.steps.iter().any(|s| matches!(s, Step::Dim(_)))
                            && matches!(c.steps.last(), None | Some(Step::Field(_) | Step::PDim(..)))
                        {
                            let pre: String = c
                                .steps
                                .iter()
                                .filter_map(|s| match s {
                                    Step::Field(i) => Some(format!(".f{}", i)),
                                    _ => None,
                                })
                                .collect();
                            let _ = writeln!(body, "    nv{pre} = vh_dv{s}_{p}{pre};", pre = pre, s = s, p = p);
                            continue;
                        }
                        match &elem {
                            Some((stride, e)) if a % stride == 0 && (b + 1) % stride == 0 => {
                                let _ = writeln!(
                                    body,
                                    "    for (k = {}; k <= {}; k++) nv{e} = vh_dv{s}_{p}{e};",
                                    a / stride,
                                    b / stride,
                                    e = e,
                                    s = s,
                                    p = p
                                );
                            }
                            _ => {
                                let _ = writeln!(
                                    body,
                                    "    for (k = {}; k <= {}; k++) nv{leaf} = vh_dv{s}_{p}{leaf};",
                                    a,
                                    b,
                                    leaf = leaf,
                                    s = s,
                                    p = p
                                );
                            }
                        }
                    }
                }
                continue;
            }
            let _ = writeln!(decls, "    {} rv{}[{}];", et, ci, cov.len());
            let _ = writeln!(
                body,
                "    for (k = 0; k < {}; k++) begin\n      g = {} + k;\n      c = 0; cc = 0;",
                c.count, c.base
            );
            for (p, d) in &cov {
                let cond = super::elab::cov_cond_var(&d.cov, "g");
                if kind.is_some() {
                    let _ = writeln!(
                        body,
                        "      if ({cond}) begin cc++; if (vh_don{s}_{p}) begin rv{ci}[c] = vh_dv{s}_{p}{leaf}; c++; end end",
                        cond = cond,
                        s = s,
                        p = p,
                        ci = ci,
                        leaf = leaf
                    );
                } else {
                    let _ = writeln!(
                        body,
                        "      if ({cond}) begin rv{ci}[c] = vh_dv{s}_{p}{leaf}; c++; end",
                        cond = cond,
                        s = s,
                        p = p,
                        ci = ci,
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
                    let _ = writeln!(decls, "    {} ra{}[];", et, ci);
                    // STD_LOGIC's RESOLVED returns the value of a single
                    // source (`s'length = 1`, the IEEE body): a leaf driven
                    // once, the usual case, skips the call.
                    let single = if self.d.subprograms[f]
                        .path
                        .eq_ignore_ascii_case("ieee.std_logic_1164.resolved")
                    {
                        format!(
                            "if (c == 1) nv{leaf} = rv{ci}[0];\n      else ",
                            leaf = leaf,
                            ci = ci
                        )
                    } else {
                        String::new()
                    };
                    let _ = writeln!(
                        body,
                        "      {single}if ({any} > 0) begin\n        ra{ci} = new[c];\n        for (int j = 0; j < c; j++) ra{ci}[j] = rv{ci}[j];\n        nv{leaf} = {f}({p}_mk(0, c - 1, 0, ra{ci}));\n      end",
                        single = single,
                        any = any,
                        ci = ci,
                        leaf = leaf,
                        f = self.sub_name(f),
                        p = pname
                    );
                }
                None => {
                    let _ = writeln!(body, "      if (c > 0) nv{} = rv{}[0];", leaf, ci);
                }
            }
            let _ = writeln!(body, "    end");
        }
        Some(decls + &body)
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
                let bty = b.ty;
                // Dimension 0 of a static array does not need the value
                // (`pk_off` uses the bounds). A later dimension does, unless
                // its own bounds are static: `.d[0]` with an empty prefix
                // is not a select.
                let mut value = match bounds {
                    Some(_) => String::new(),
                    None => self.ex(b),
                };
                for (k, x) in idx.iter().enumerate() {
                    let i = self.ex(x);
                    let static_b = if k == 0 {
                        bounds
                    } else {
                        self.static_dim(bty, k).and_then(|sr| {
                            Some((sr.left.as_i64()?, sr.dir, sr.right.as_i64()?))
                        })
                    };
                    let mut off = if let Some(bnd) = static_b {
                        self.pk_off(&i, bnd, &t.loc)
                    } else {
                        if value.is_empty() {
                            value = self.ex(b);
                        }
                        let arr = if k == 0 {
                            value.clone()
                        } else {
                            format!("{}{}", value, ".d[0]".repeat(k))
                        };
                        format!(
                            "vh_ix({}, {a}.l, {a}.r, {a}.dn, {}, {})",
                            i,
                            sv_string(&f),
                            l,
                            a = arr
                        )
                    };
                    let mut v = match (static_b, self.d.eval(x).and_then(|val| val.as_i64())) {
                        (Some((lb, dir, _)), Some(iv)) => Some(match dir {
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

    /// The class index of a signal stored as one packed record array.
    fn packed_record_class(&self, s: usize) -> Option<usize> {
        if self.record_array_pack(self.sigs[s].ty).is_none() {
            return None;
        }
        let classes = self.leaf_classes(self.sigs[s].ty)?;
        classes
            .iter()
            .position(|c| matches!(c.steps.as_slice(), [Step::PDim(1, _)]))
    }

    /// Low bit and width of `path` in a packed record array of element
    /// width `ew` and length `n`. `None` for a slice.
    fn packed_record_span(
        &self,
        ty: TypeId,
        path: &[DSel],
        ew: u32,
        n: i64,
    ) -> Option<(String, u32)> {
        if path.is_empty() {
            return Some(("0".into(), (ew as i64 * n) as u32));
        }
        let DSel::Elem(off, _) = &path[0] else {
            return None;
        };
        let mut lo = Lw::bit_mul(ew, n - 1, off);
        let mut width = ew;
        let mut cur = self.d.element_subtype(ty)?;
        for sel in &path[1..] {
            match sel {
                DSel::Field(i) => {
                    let (shift, fw) = self.record_field_lo(cur, *i)?;
                    lo = Lw::bit_sum(lo, shift.to_string());
                    width = fw;
                    cur = self.field_storage(cur).get(*i).copied()?;
                }
                DSel::Elem(off2, _) => {
                    let Repr::Pk(w, n2) = self.pk_of(cur)? else {
                        return None;
                    };
                    lo = Lw::bit_sum(lo, Lw::bit_mul(w, n2 - 1, off2));
                    width = w;
                    cur = self.d.element_subtype(cur)?;
                }
                DSel::Slice(..) => return None,
            }
        }
        Some((lo, width))
    }

    /// A zero-delay assign onto the pending packed vector, or one
    /// transaction of that vector when the assign is delayed. `None` when
    /// `s` is not a packed record array or the path is a slice.
    fn packed_record_drive(
        &self,
        s: usize,
        p: usize,
        path: &[DSel],
        val: &str,
        timing: (&str, &str, i32),
        ind: usize,
    ) -> Option<String> {
        let ty = self.sigs[s].ty;
        let (ew, n) = self.record_array_pack(ty)?;
        let (lo, width) = self.packed_record_span(ty, path, ew, n)?;
        let ci = self.packed_record_class(s)?;
        let (after, rej, mode) = timing;
        let pad = " ".repeat(ind);
        let zero = after == "64'sd0" && rej == "64'sd0" && mode == 1;
        let inner = if zero {
            format!(
                "{pad}  if (vh_sqn{s}_{p}_c{ci} == 0) begin\n\
                 {pad}    if (!vh_pwf{s}_{p}_c{ci}) begin vh_pw{s}_{p}_c{ci} = vh_dv{s}_{p}; vh_pwf{s}_{p}_c{ci} = 1; end\n\
                 {pad}    vh_pw{s}_{p}_c{ci}[({lo}) +: {width}] = {val};\n\
                 {pad}  end else vh_drs_{s}_{p}_c{ci}(0, vh_pw{s}_{p}_c{ci}, after, rej, mode);\n",
                pad = pad,
                s = s,
                p = p,
                ci = ci,
                lo = lo,
                width = width,
                val = val
            )
        } else {
            format!(
                "{pad}  begin\n\
                 {pad}    bit [{hi}:0] vh_pr;\n\
                 {pad}    vh_pr = vh_dv{s}_{p};\n\
                 {pad}    vh_pr[({lo}) +: {width}] = {val};\n\
                 {pad}    vh_drs_{s}_{p}_c{ci}(0, vh_pr, after, rej, mode);\n\
                 {pad}  end\n",
                pad = pad,
                hi = ew as i64 * n - 1,
                s = s,
                p = p,
                lo = lo,
                width = width,
                val = val,
                ci = ci
            )
        };
        Some(format!(
            "{pad}begin\n{pad}  longint after, rej;\n{pad}  int mode;\n{pad}  after = {after}; rej = {rej}; mode = {mode};\n{inner}{pad}end\n",
            pad = pad,
            after = after,
            rej = rej,
            mode = mode,
            inner = inner
        ))
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
        if let Some(body) = self.packed_record_drive(s, p, path, val, timing, ind) {
            return body;
        }
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
        let (after, rej, mode) = timing;
        let saved = std::mem::replace(&mut self.leaf_zero, after == "64'sd0" && rej == "64'sd0" && mode == 1);
        self.emit_leaves(s, p, t, val, &mut prefix, slice_start, slice_len, &mut body, ind + 2, 0);
        self.leaf_zero = saved;
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
