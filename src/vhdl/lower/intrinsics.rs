//! Native fast paths for the hot subprograms of the IEEE packages on packed
//! values. The IEEE bodies compute bit by bit through tables (which the
//! simulator's compiled tier declines); on operands made only of '0' and
//! '1' the result is plain binary arithmetic, so a wrapper computes it
//! natively and calls the specialised body for anything else (metavalues,
//! truncations: their warnings and results stay those of the IEEE source).
//! numeric_bit values have no metavalues, so their arithmetic is native.
//!
//! A std_ulogic element is its position (`U X 0 1 Z W L H -` = 0..8) in 4
//! bits: a vector is "clean" when every nibble is 2 or 3, and the binary
//! value is then bit 0 of each nibble (`compress`), put back by `spread`.

use std::fmt::Write as _;

use super::{Lw, Repr};
use crate::vhdl::sema::hir::*;

/// What a parameter or result type is, for the intrinsics.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Cls {
    /// std_ulogic.
    Ul,
    /// A one-dimensional array of std_ulogic.
    UlVec,
    /// numeric_std UNSIGNED / SIGNED.
    U,
    S,
    /// numeric_bit UNSIGNED / SIGNED (bit elements).
    BitU,
    BitS,
    /// INTEGER and its subtypes.
    Int,
    Other,
}

/// A W-bit hex literal with nibble `nib` repeated n times.
fn nib_pat(n: i64, nib: char) -> String {
    format!("{}'h{}", 4 * n, std::iter::repeat_n(nib, n as usize).collect::<String>())
}

/// A W-bit literal: within each period of `period` bits the low `keep` bits.
fn period_mask(w: i64, period: i64, keep: i64) -> String {
    let mut bits = vec![false; w as usize];
    for (i, b) in bits.iter_mut().enumerate() {
        *b = (i as i64 % period) < keep;
    }
    // Hex digits from the top.
    let mut hex = String::new();
    let mut i = w;
    while i > 0 {
        let mut d = 0;
        for k in (0..4).rev() {
            let p = i - 4 + k;
            d = d * 2 + (p >= 0 && bits[p as usize]) as u32;
        }
        hex.push(std::char::from_digit(d, 16).unwrap());
        i -= 4;
    }
    format!("{}'h{}", w, hex)
}

impl<'a> Lw<'a> {
    fn cls(&self, t: TypeId) -> Cls {
        let b = self.base(t);
        if Some(b) == self.d.std.std_ulogic {
            return Cls::Ul;
        }
        if self.d.is_integer(b) {
            return Cls::Int;
        }
        let name = self.d.types[b].name.to_ascii_lowercase();
        let elem = self.d.element_subtype(b).map(|e| self.base(e));
        let ul_elem = elem.is_some() && elem == self.d.std.std_ulogic;
        let bit_elem = elem == Some(self.d.std.bit);
        match name.as_str() {
            "unresolved_unsigned" | "unsigned" if ul_elem => Cls::U,
            "unresolved_signed" | "signed" if ul_elem => Cls::S,
            "unsigned" if bit_elem => Cls::BitU,
            "signed" if bit_elem => Cls::BitS,
            _ if ul_elem && self.ndims(b) == 1 => Cls::UlVec,
            _ => Cls::Other,
        }
    }

    /// `v` (W = 4n bits) has only '0' and '1' elements.
    fn clean(n: i64, v: &str) -> String {
        format!("(({} & {}) == {})", v, nib_pat(n, 'e'), nib_pat(n, '2'))
    }

    /// The compression of the value bits of a clean n-element vector into
    /// n bits (and the inverse): log steps of shift-or-mask.
    fn cmp_fn(&mut self, n: i64) -> String {
        let f = format!("vh_cmp4_{}", n);
        if self.pk_fns.insert(f.clone()) {
            let w = 4 * n;
            let mut body = format!("    x = v & {};\n", period_mask(w, 4, 1));
            let (mut p, mut k) = (4i64, 1i64);
            while p < w {
                let s = 3 * k;
                p *= 2;
                k *= 2;
                let _ = writeln!(body, "    x = (x | (x >> {})) & {};", s, period_mask(w, p, k));
            }
            let _ = write!(
                self.type_defs,
                "  function automatic bit [{nh}:0] {f}(bit [{wh}:0] v);\n    bit [{wh}:0] x;\n{body}    return x;\n  endfunction\n",
                nh = n - 1,
                f = f,
                wh = w - 1,
                body = body
            );
        }
        f
    }

    fn spr_fn(&mut self, n: i64) -> String {
        let f = format!("vh_spr4_{}", n);
        if self.pk_fns.insert(f.clone()) {
            let w = 4 * n;
            // The masks of the compression, top level first.
            let mut levels = vec![(4i64, 1i64, 0i64)];
            let (mut p, mut k) = (4i64, 1i64);
            while p < w {
                let s = 3 * k;
                p *= 2;
                k *= 2;
                levels.push((p, k, s));
            }
            let mut body = String::from("    x = v;\n");
            for j in (1..levels.len()).rev() {
                let (pp, kk, _) = levels[j - 1];
                let s = levels[j].2;
                let _ = writeln!(body, "    x = (x | (x << {})) & {};", s, period_mask(w, pp, kk));
            }
            let _ = write!(
                self.type_defs,
                "  function automatic bit [{wh}:0] {f}(bit [{nh}:0] v);\n    bit [{wh}:0] x;\n{body}    return x | {two};\n  endfunction\n",
                wh = w - 1,
                f = f,
                nh = n - 1,
                body = body,
                two = nib_pat(n, '2')
            );
        }
        f
    }

    /// A native fast path for a call of an IEEE subprogram, when there is
    /// one for its operand types and representations.
    pub(super) fn intrinsic(&mut self, s: SubId, args: &[HExpr], h: &HExpr) -> Option<String> {
        let info = self.d.subprograms[s].clone();
        if info.builtin.is_some() || info.body.is_none() {
            return None;
        }
        let path = info.path.to_ascii_lowercase();
        let (pkg, name) = path.rsplit_once('.')?;
        let name = name.trim_matches('"');
        let pts: Vec<TypeId> = info.params.iter().map(|p| self.d.objects[*p].ty).collect();
        let cls: Vec<Cls> = pts.iter().map(|t| self.cls(*t)).collect();
        match pkg {
            "ieee.std_logic_1164" => self.intrinsic_1164(s, name, &cls, args),
            "ieee.numeric_std" => self.intrinsic_numeric(s, name, &cls, args, h, false),
            "ieee.numeric_bit" => self.intrinsic_numeric(s, name, &cls, args, h, true),
            _ => None,
        }
    }

    fn intrinsic_1164(&mut self, s: SubId, name: &str, cls: &[Cls], args: &[HExpr]) -> Option<String> {
        let logical = matches!(name, "and" | "or" | "xor" | "nand" | "nor" | "xnor");
        match cls {
            [Cls::Ul, Cls::Ul] if logical => {
                let (x, y) = (self.ex(&args[0]), self.ex(&args[1]));
                Some(match name {
                    "and" => format!("vh_ul_and({}, {})", x, y),
                    "or" => format!("vh_ul_or({}, {})", x, y),
                    "xor" => format!("vh_ul_xor({}, {})", x, y),
                    "nand" => format!("vh_ul_not(vh_ul_and({}, {}))", x, y),
                    "nor" => format!("vh_ul_not(vh_ul_or({}, {}))", x, y),
                    _ => format!("vh_ul_not(vh_ul_xor({}, {}))", x, y),
                })
            }
            [Cls::Ul] if name == "not" => {
                let x = self.ex(&args[0]);
                Some(format!("vh_ul_not({})", x))
            }
            [Cls::Ul] if name == "to_x01" => {
                let x = self.ex(&args[0]);
                Some(format!("vh_ul_x01({})", x))
            }
            [Cls::UlVec, Cls::UlVec] if logical => {
                let (Repr::Pk(4, n), Repr::Pk(4, n2)) = (self.erepr(&args[0]), self.erepr(&args[1]))
                else {
                    return None;
                };
                if n != n2 {
                    return None;
                }
                let k = self.try_specialise(s, args)?;
                let fb = self.pspecs[k].name.clone();
                let f = format!("vh_in_s{}", k);
                if self.pk_fns.insert(f.clone()) {
                    let (one, two) = (nib_pat(n, '1'), nib_pat(n, '2'));
                    let fast = match name {
                        "and" => "(a & b)".to_string(),
                        "or" => "(a | b)".to_string(),
                        "xor" => format!("((a ^ b) | {})", two),
                        "nand" => format!("((a & b) ^ {})", one),
                        "nor" => format!("((a | b) ^ {})", one),
                        _ => format!("(((a ^ b) | {}) ^ {})", two, one),
                    };
                    let _ = write!(
                        self.type_defs,
                        "  function automatic bit [{wh}:0] {f}(bit [{wh}:0] a, bit [{wh}:0] b);\n    if ({ca} && {cb}) return {fast};\n    return {fb}(a, b);\n  endfunction\n",
                        wh = 4 * n - 1,
                        f = f,
                        ca = Self::clean(n, "a"),
                        cb = Self::clean(n, "b"),
                        fast = fast,
                        fb = fb
                    );
                }
                let r = Repr::Pk(4, n);
                let (x, y) = (self.ex_as(&args[0], &r), self.ex_as(&args[1], &r));
                Some(format!("{}({}, {})", f, x, y))
            }
            [Cls::UlVec] if name == "not" => {
                let Repr::Pk(4, n) = self.erepr(&args[0]) else {
                    return None;
                };
                let k = self.try_specialise(s, args)?;
                let fb = self.pspecs[k].name.clone();
                let f = format!("vh_in_s{}", k);
                if self.pk_fns.insert(f.clone()) {
                    let _ = write!(
                        self.type_defs,
                        "  function automatic bit [{wh}:0] {f}(bit [{wh}:0] a);\n    if ({ca}) return a ^ {one};\n    return {fb}(a);\n  endfunction\n",
                        wh = 4 * n - 1,
                        f = f,
                        ca = Self::clean(n, "a"),
                        one = nib_pat(n, '1'),
                        fb = fb
                    );
                }
                let x = self.ex_as(&args[0], &Repr::Pk(4, n));
                Some(format!("{}({})", f, x))
            }
            _ => None,
        }
    }

    /// numeric_std (`bit_elem` false) and numeric_bit (`true`): `+`, `-`,
    /// the relational operators, TO_INTEGER, TO_UNSIGNED and TO_SIGNED.
    fn intrinsic_numeric(
        &mut self,
        s: SubId,
        name: &str,
        cls: &[Cls],
        args: &[HExpr],
        h: &HExpr,
        bit_elem: bool,
    ) -> Option<String> {
        let w: u32 = if bit_elem { 1 } else { 4 };
        let is_vec = |c: Cls| {
            if bit_elem {
                matches!(c, Cls::BitU | Cls::BitS)
            } else {
                matches!(c, Cls::U | Cls::S)
            }
        };
        let signed = |c: Cls| matches!(c, Cls::S | Cls::BitS);
        let rel = matches!(name, "=" | "/=" | "<" | "<=" | ">" | ">=");
        let arith = matches!(name, "+" | "-");
        if !(arith || rel || matches!(name, "to_integer" | "to_unsigned" | "to_signed"))
            || args.len() > 2
            || args.len() != cls.len()
        {
            return None;
        }
        // The packed lengths of the array operands.
        let mut ns = Vec::new();
        for (c, a) in cls.iter().zip(args) {
            if is_vec(*c) {
                match self.erepr(a) {
                    Repr::Pk(ww, n) if ww == w => ns.push(Some(n)),
                    _ => return None,
                }
            } else {
                ns.push(None);
            }
        }
        let k = self.try_specialise(s, args)?;
        let fb = self.pspecs[k].name.clone();
        let f = format!("vh_in_s{}", k);
        let sv_op = match name {
            "=" => "==",
            "/=" => "!=",
            o => o,
        };
        // The value of operand i (clean vectors as n-bit numbers):
        // declarations at the function's top, the statements computing
        // them inside the fast path.
        let mut decls = String::new();
        let mut decl = String::new();
        let mut val = Vec::new();
        let mut conds = Vec::new();
        let mut formals = Vec::new();
        let names = ["a", "b"];
        for (i, (c, a)) in cls.iter().zip(args).enumerate() {
            let nm = names[i];
            match ns[i] {
                Some(n) => {
                    formals.push(format!("bit [{}:0] {}", w as i64 * n - 1, nm));
                    if bit_elem {
                        val.push(nm.to_string());
                    } else {
                        conds.push(Self::clean(n, nm));
                        let cf = self.cmp_fn(n);
                        let _ = writeln!(decls, "    bit [{}:0] x{};", n - 1, nm);
                        val.push(format!("x{}", nm));
                        decl.push_str(&format!("    x{} = {}({});\n", nm, cf, nm));
                    }
                    if signed(*c) {
                        // As a 64-bit two's complement number.
                        if n > 63 {
                            return None;
                        }
                        let _ = writeln!(decls, "    longint s{};", nm);
                        let _ = writeln!(
                            decl,
                            "    s{nm} = {v}; if ({v}[{m}]) s{nm} = s{nm} - (64'd1 << {n});",
                            nm = nm,
                            v = val[i],
                            m = n - 1,
                            n = n
                        );
                        val[i] = format!("s{}", nm);
                    }
                    let _ = a;
                }
                None => {
                    formals.push(format!("longint {}", nm));
                    val.push(nm.to_string());
                }
            }
        }
        // The integer operand must fit the vector's length (TO_UNSIGNED /
        // TO_SIGNED warn and truncate otherwise).
        let fits = |n: i64, sg: bool, k: &str| -> String {
            if sg {
                if n >= 64 {
                    "1".to_string()
                } else {
                    format!(
                        "({k} >= -(64'sd1 << {m}) && {k} < (64'sd1 << {m}))",
                        k = k,
                        m = n - 1
                    )
                }
            } else if n >= 63 {
                format!("({} >= 0)", k)
            } else {
                format!("({k} >= 0 && {k} < (64'sd1 << {n}))", k = k, n = n)
            }
        };
        let ret_pk = |lw: &mut Self| -> Option<(i64, String)> {
            match lw.pspecs[k].ret.clone() {
                Some(Repr::Pk(ww, n)) if ww == w => Some((n, format!("bit [{}:0]", w as i64 * n - 1))),
                _ => None,
            }
        };
        let body: String;
        let ret_sv: String;
        match (name, cls) {
            // Vector with vector.
            (_, [c0, c1]) if (arith || rel) && is_vec(*c0) && is_vec(*c1) => {
                if signed(*c0) != signed(*c1) {
                    return None;
                }
                let (n0, n1) = (ns[0].unwrap(), ns[1].unwrap());
                if arith {
                    let (n, rs) = ret_pk(self)?;
                    if n != n0.max(n1) {
                        return None;
                    }
                    ret_sv = rs;
                    let res = if bit_elem {
                        format!("x = {} {} {};\n    return x;", val[0], sv_op, val[1])
                    } else {
                        let sf = self.spr_fn(n);
                        format!("x = {} {} {};\n    return {}(x);", val[0], sv_op, val[1], sf)
                    };
                    let _ = writeln!(decls, "    bit [{}:0] x;", n - 1);
                    body = format!("{}    {}", decl, res);
                } else {
                    ret_sv = "byte unsigned".into();
                    body = format!(
                        "{}    return ({} {} {}) ? 1 : 0;",
                        decl, val[0], sv_op, val[1]
                    );
                }
            }
            // Vector with integer, integer with vector.
            (_, [c0, c1]) if (arith || rel) && (is_vec(*c0) != is_vec(*c1)) => {
                let (vi, ki) = if is_vec(*c0) { (0, 1) } else { (1, 0) };
                if !matches!(cls[ki], Cls::Int) {
                    return None;
                }
                let n = ns[vi].unwrap();
                let sg = signed(cls[vi]);
                conds.push(fits(n, sg, names[ki]));
                if arith {
                    let (rn, rs) = ret_pk(self)?;
                    if rn != n {
                        return None;
                    }
                    ret_sv = rs;
                    let res = if bit_elem {
                        format!("x = {} {} {};\n    return x;", val[0], sv_op, val[1])
                    } else {
                        let sf = self.spr_fn(n);
                        format!("x = {} {} {};\n    return {}(x);", val[0], sv_op, val[1], sf)
                    };
                    let _ = writeln!(decls, "    bit [{}:0] x;", n - 1);
                    body = format!("{}    {}", decl, res);
                } else {
                    ret_sv = "byte unsigned".into();
                    body = format!(
                        "{}    return ({} {} {}) ? 1 : 0;",
                        decl, val[0], sv_op, val[1]
                    );
                }
            }
            ("to_integer", [c0]) if is_vec(*c0) => {
                let n = ns[0].unwrap();
                if (!signed(*c0) && n > 31) || (signed(*c0) && n > 32) {
                    return None;
                }
                ret_sv = "int".into();
                body = format!("{}    return {};", decl, val[0]);
            }
            ("to_unsigned" | "to_signed", [Cls::Int, Cls::Int]) => {
                let (n, rs) = ret_pk(self)?;
                let sg = name == "to_signed";
                conds.push(fits(n, sg, "a"));
                ret_sv = rs;
                let res = if bit_elem {
                    "x = a;\n    return x;".to_string()
                } else {
                    let sf = self.spr_fn(n);
                    format!("x = a;\n    return {}(x);", sf)
                };
                let _ = writeln!(decls, "    bit [{}:0] x;", n - 1);
                body = format!("    {}", res);
            }
            _ => return None,
        }
        let _ = h;
        if self.pk_fns.insert(f.clone()) {
            let cond = if conds.is_empty() {
                "1".to_string()
            } else {
                conds.join(" && ")
            };
            let fargs: Vec<&str> = names[..args.len()].to_vec();
            let _ = write!(
                self.type_defs,
                "  function automatic {ret} {f}({formals});\n{decls}    if ({cond}) begin\n  {body}\n    end\n    return {fb}({fargs});\n  endfunction\n",
                ret = ret_sv,
                f = f,
                formals = formals.join(", "),
                decls = decls,
                cond = cond,
                body = body.replace('\n', "\n  "),
                fb = fb,
                fargs = fargs.join(", ")
            );
        }
        let prs = self.pspecs[k].params.clone();
        let mut a = Vec::new();
        for (x, pr) in args.iter().zip(&prs) {
            a.push(self.ex_as(x, pr));
        }
        Some(format!("{}({})", f, a.join(", ")))
    }
}
