//! Signals of record types driven element by element (§14.7.2): a
//! process assigning `r.f <= v` has a driver of each scalar or array leaf
//! of the record it reaches, with its own projected output waveform; the
//! signal's value is assembled leaf by leaf from the drivers covering each
//! leaf, through the leaf's resolution function where it has one
//! (§14.7.3.2; a record element of a resolved subtype is a resolved
//! signal).

use std::fmt::Write as _;

use super::elab::{Cov, Driver};
use super::{Lw, Repr};
use crate::vhdl::sema::hir::*;

impl<'a> Lw<'a> {
    /// The leaves of a record type: element paths (field indices from the
    /// record) and subtypes, depth-first; a non-record type is its own
    /// single leaf.
    pub(super) fn rec_leaves(&self, t: TypeId) -> Vec<(Vec<usize>, TypeId)> {
        let mut out = Vec::new();
        self.collect_leaves(t, &mut Vec::new(), &mut out);
        out
    }

    fn collect_leaves(&self, t: TypeId, path: &mut Vec<usize>, out: &mut Vec<(Vec<usize>, TypeId)>) {
        if !matches!(self.d.types[self.base(t)].kind, TypeKind::Record(_)) {
            out.push((path.clone(), t));
            return;
        }
        for (i, (_, ft)) in self.d.record_fields(t).into_iter().enumerate() {
            path.push(i);
            self.collect_leaves(ft, path, out);
            path.pop();
        }
    }

    /// Whether signal `s` is of a record type.
    pub(super) fn is_record_sig(&self, s: usize) -> bool {
        matches!(self.d.types[self.base(self.sigs[s].ty)].kind, TypeKind::Record(_))
    }

    /// The leaves (indices into `rec_leaves`) under element path `path`.
    pub(super) fn path_cov(&self, t: TypeId, path: &[usize]) -> Cov {
        Cov::Set(
            self.rec_leaves(t)
                .iter()
                .enumerate()
                .filter(|(_, (p, _))| p.starts_with(path))
                .map(|(k, _)| k as i64)
                .collect(),
        )
    }

    /// The SV selection of an element path (`.f1.f0`).
    pub(super) fn path_sv(path: &[usize]) -> String {
        path.iter().map(|i| format!(".f{}", i)).collect()
    }

    /// Driver (s, p) of record signal `s` assigned by elements: per leaf,
    /// queues of transaction times and values and the function updating
    /// them; `vh_drv_{s}_{p}` drives every leaf from a whole value.
    pub(super) fn record_driver_sv(&mut self, s: usize, p: usize, t: &str, loc: &Loc) -> String {
        let ty = self.sigs[s].ty;
        let leaves = self.rec_leaves(ty);
        let mut out = String::new();
        let _ = writeln!(out, "  {} vh_dv{}_{};", t, s, p);
        let mut whole = String::new();
        for (j, (path, lt)) in leaves.iter().enumerate() {
            let r = self.repr(*lt, loc);
            let et = r.sv();
            let eq = self.eq_expr(&r, "qv[k]", "v");
            let _ = write!(
                out,
                "  longint vh_dt{s}_{p}_l{j}[$];\n  {et} vh_dq{s}_{p}_l{j}[$];\n  function automatic void vh_drl_{s}_{p}_{j}({et} v, longint after, longint rej, int mode);\n    longint tt;\n    longint qt[$];\n    {et} qv[$];\n    int k;\n    tt = longint'($time) + after;\n    qt = vh_dt{s}_{p}_l{j};\n    qv = vh_dq{s}_{p}_l{j};\n    while (qt.size() > 0 && qt[qt.size()-1] >= tt) begin void'(qt.pop_back()); void'(qv.pop_back()); end\n    if (mode == 1) begin\n      k = qt.size() - 1;\n      while (k >= 0 && qt[k] >= tt - rej && ({eq})) k--;\n      while (k >= 0 && qt[k] >= tt - rej) begin qt.delete(k); qv.delete(k); k--; end\n    end\n    qt.push_back(tt);\n    qv.push_back(v);\n    vh_dt{s}_{p}_l{j} = qt;\n    vh_dq{s}_{p}_l{j} = qv;\n  endfunction\n",
                s = s,
                p = p,
                j = j,
                et = et,
                eq = eq
            );
            let _ = writeln!(
                whole,
                "    vh_drl_{}_{}_{}(v{}, after, rej, mode);",
                s,
                p,
                j,
                Self::path_sv(path)
            );
        }
        let _ = write!(
            out,
            "  // The whole record: every leaf.\n  function automatic void vh_drv_{s}_{p}({t} v, longint after, longint rej, int mode);\n{whole}  endfunction\n",
            s = s,
            p = p,
            t = t,
            whole = whole
        );
        out
    }

    /// Kernel: the transactions of driver (s, p) of a record signal due now.
    pub(super) fn record_driver_due(&self, s: usize, p: usize, ind: &str) -> String {
        let mut out = String::new();
        for (j, (path, _)) in self.rec_leaves(self.sigs[s].ty).iter().enumerate() {
            let _ = writeln!(
                out,
                "{ind}if (vh_dt{s}_{p}_l{j}.size() > 0 && vh_dt{s}_{p}_l{j}[0] <= $time) begin void'(vh_dt{s}_{p}_l{j}.pop_front()); vh_dv{s}_{p}{f} = vh_dq{s}_{p}_l{j}.pop_front(); vh_s{s}_act = 1; end",
                ind = ind,
                s = s,
                p = p,
                j = j,
                f = Self::path_sv(path)
            );
        }
        out
    }

    /// The next transaction time of driver (s, p) of a record signal.
    pub(super) fn record_driver_next(&self, s: usize, p: usize) -> String {
        let mut out = String::new();
        for j in 0..self.rec_leaves(self.sigs[s].ty).len() {
            let _ = writeln!(
                out,
                "    if (vh_dt{s}_{p}_l{j}.size() > 0 && (n < 0 || vh_dt{s}_{p}_l{j}[0] < n)) n = vh_dt{s}_{p}_l{j}[0];",
                s = s,
                p = p,
                j = j
            );
        }
        out
    }

    /// The body of the update of record signal `s` from drivers `ds`: leaf
    /// by leaf, the value of the one driver covering it or the resolution
    /// of those covering it.
    pub(super) fn record_update_body(
        &mut self,
        s: usize,
        ds: &[(usize, Driver)],
        tsv: &str,
        info: &ObjInfo,
    ) -> Option<String> {
        let ty = self.sigs[s].ty;
        let mut body = String::new();
        let _ = writeln!(body, "    {} nv;\n    nv = vh_s{};", tsv, s);
        for (j, (path, lt)) in self.rec_leaves(ty).iter().enumerate() {
            let f = Self::path_sv(path);
            let cov: Vec<usize> = ds
                .iter()
                .filter(|(_, d)| d.cov.covers(j as i64))
                .map(|(p, _)| *p)
                .collect();
            if cov.is_empty() {
                continue;
            }
            match self.resolution(*lt) {
                None => {
                    if cov.len() > 1 {
                        self.err(
                            &info.loc,
                            format!("unresolved signal '{}' has several drivers", info.name),
                        );
                        return None;
                    }
                    let _ = writeln!(body, "    nv{} = vh_dv{}_{}{};", f, s, cov[0], f);
                }
                Some((rf, elementwise)) => {
                    let pt = self.d.objects[self.d.subprograms[rf].params[0]].ty;
                    let (pname, per) = match self.repr(pt, &info.loc) {
                        Repr::Arr(n, e) => (n, e.sv()),
                        _ => return None,
                    };
                    self.need_sub(rf);
                    let call = format!("{}({}_mk(0, {}, 0, rv))", self.sub_name(rf), pname, cov.len() - 1);
                    let _ = writeln!(body, "    begin\n      {} rv[];\n      rv = new[{}];", per, cov.len());
                    if elementwise {
                        let _ = writeln!(body, "      for (int k = 0; k < nv{}.d.size(); k++) begin", f);
                        for (i, p) in cov.iter().enumerate() {
                            let _ = writeln!(body, "        rv[{}] = vh_dv{}_{}{}.d[k];", i, s, p, f);
                        }
                        let _ = writeln!(body, "        nv{}.d[k] = {};\n      end", f, call);
                    } else {
                        for (i, p) in cov.iter().enumerate() {
                            let _ = writeln!(body, "      rv[{}] = vh_dv{}_{}{};", i, s, p, f);
                        }
                        let _ = writeln!(body, "      nv{} = {};", f, call);
                    }
                    let _ = writeln!(body, "    end");
                }
            }
        }
        Some(body)
    }
}
