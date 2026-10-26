//! The language boundary of a mixed design: a VHDL entity instantiated
//! from SystemVerilog is lowered to a module with SV ports.
//!
//! An SV value entering the VHDL design is a driver of the port's signal
//! (a link without sources, `elab::Link`): the kernel samples the SV side
//! at the start of every simulation cycle, and an `always` block counting
//! its changes wakes the kernel when SV changes it. A VHDL value leaving
//! the design is written to the SV side after every signal update in which
//! the signal has an event. Values cross as Questa passes them: std_ulogic
//! to 4-state as `U X W -` → x, `0 L` → 0, `1 H` → 1, `Z` → z, and back as
//! 0 1 x z → `'0' '1' 'X' 'Z'`; bit and boolean as 0/1 (x and z → 0);
//! integers as 32-bit two's complement; reals as reals.

use std::fmt::Write as _;

use super::elab::{Cov, Link, Part, SigRef};
use super::{Lw, Repr, port_ident, sv_ident};
use crate::vhdl::ast::{Dir, Mode};
use crate::vhdl::sema::hir::*;

/// How a value of a VHDL type crosses the boundary.
#[derive(Clone, Debug, PartialEq)]
pub(super) enum Bnd {
    /// std_ulogic (`true`) or bit/boolean (`false`).
    Bit(bool),
    /// A one-dimensional array of them: n elements, the left one the most
    /// significant bit.
    Vec(bool, i64),
    Int,
    Real,
    /// A one-dimensional array of integers or reals: an SV unpacked array
    /// with the VHDL bounds, `[left:right]`.
    Arr(Box<Bnd>, i64, i64),
}

impl Bnd {
    /// The SV data type on the boundary.
    fn sv(&self) -> String {
        match self {
            Bnd::Bit(_) => "logic".into(),
            Bnd::Vec(_, n) => format!("logic [{}:0]", n - 1),
            Bnd::Int => "logic signed [31:0]".into(),
            Bnd::Real => "real".into(),
            Bnd::Arr(e, _, _) => e.sv(),
        }
    }
    /// The unpacked dimension of a declaration.
    fn dims(&self) -> String {
        match self {
            Bnd::Arr(_, l, r) => format!(" [{}:{}]", l, r),
            _ => String::new(),
        }
    }
    /// The inequality of two values on the boundary.
    fn ne(&self, a: &str, b: &str) -> String {
        match self {
            Bnd::Real | Bnd::Arr(..) => format!("{} != {}", a, b),
            _ => format!("{} !== {}", a, b),
        }
    }
}

/// An SV value driving a VHDL signal.
#[derive(Clone, Debug)]
pub(super) struct ForeignIn {
    /// The SV expression sampled.
    pub sv: String,
    pub bnd: Bnd,
    pub ty: TypeId,
}

/// A VHDL signal (or constant) written to SV.
#[derive(Clone, Debug)]
pub(super) struct ForeignOut {
    /// The SV variable written.
    pub sv: String,
    pub bnd: Bnd,
    pub ty: TypeId,
    /// The signal, or a constant's value (SV, written once).
    pub sig: Option<SigRef>,
    pub konst: Option<String>,
    /// The variable is declared by the boundary (a mirror, not a port).
    pub decl: bool,
}

impl<'a> Lw<'a> {
    /// How values of type `t` cross the boundary.
    pub(super) fn bnd(&self, t: TypeId) -> Option<Bnd> {
        let b = self.base(t);
        let ul = Some(b) == self.d.std.std_ulogic;
        match &self.d.types[b].kind {
            TypeKind::Enum(_) if self.d.is_logic_enum(b) => Some(Bnd::Bit(ul)),
            TypeKind::Integer => Some(Bnd::Int),
            TypeKind::Real => Some(Bnd::Real),
            TypeKind::Array { index, elem } if index.len() == 1 => {
                let e = self.base(*elem);
                let (l, dir, r) = self.static_bounds(t)?;
                if !self.d.is_logic_enum(e) {
                    return match self.bnd(e)? {
                        x @ (Bnd::Int | Bnd::Real) => Some(Bnd::Arr(Box::new(x), l, r)),
                        _ => None,
                    };
                }
                let n = match dir {
                    Dir::To => r - l + 1,
                    Dir::Downto => l - r + 1,
                };
                (n > 0).then_some(Bnd::Vec(Some(e) == self.d.std.std_ulogic, n))
            }
            _ => None,
        }
    }

    /// The port list of a root (an entity instantiated from SV), and its
    /// boundary: the ports' SV values drive their signals, their signals'
    /// values are written to the SV ports.
    pub(super) fn boundary_ports(&mut self, top: usize) -> String {
        let ports = self.d.archs[top].ports.clone();
        let mut decls = Vec::new();
        for p in ports {
            let info = self.d.objects[p].clone();
            let ObjKind::Port(mode) = info.kind else {
                continue;
            };
            let Some(bnd) = self.bnd(info.ty) else {
                self.err(
                    &info.loc,
                    format!(
                        "port '{}' has a type that cannot be connected to SystemVerilog",
                        info.name
                    ),
                );
                continue;
            };
            let name = port_ident(&info.name);
            let sig = SigRef {
                sig: self.sig_map[&(0, p)].sig,
                part: Part::Whole,
            };
            let net = if bnd == Bnd::Real { "var" } else { "wire" };
            match mode {
                Mode::In if matches!(bnd, Bnd::Arr(..)) => {
                    self.err(
                        &info.loc,
                        format!(
                            "input port '{}' of an array of integers or reals cannot be connected to SystemVerilog yet",
                            info.name
                        ),
                    );
                }
                Mode::In => {
                    decls.push(format!("input {} {} {}", net, bnd.sv(), name));
                    self.foreign_driver(sig, name, bnd, info.ty, p);
                }
                Mode::Out | Mode::Buffer => {
                    decls.push(format!("output {} {}{}", bnd.sv(), name, bnd.dims()));
                    self.fouts.push(ForeignOut {
                        sv: name,
                        bnd,
                        ty: info.ty,
                        sig: Some(sig),
                        konst: None,
                        decl: false,
                    });
                }
                Mode::InOut | Mode::Linkage => {
                    self.err(
                        &info.loc,
                        format!(
                            "inout port '{}' cannot be connected to SystemVerilog yet",
                            info.name
                        ),
                    );
                }
            }
        }
        self.mirrors(top);
        decls.join(", ")
    }

    /// The root's signals and constants as SV variables of the same names,
    /// for hierarchical references from SV (`dut.sig`).
    fn mirrors(&mut self, top: usize) {
        let arch = &self.d.archs[top];
        let objs: Vec<ObjId> = arch
            .signals
            .iter()
            .chain(&arch.constants)
            .copied()
            .collect();
        for o in objs {
            let info = self.d.objects[o].clone();
            let Some(bnd) = self.bnd(info.ty) else {
                continue;
            };
            let sv = port_ident(&info.name);
            if self.fouts.iter().any(|f| f.sv == sv) {
                continue;
            }
            let (sig, konst) = match self.sig_map.get(&(0, o)) {
                Some(r) => (Some(r.clone()), None),
                None if matches!(info.kind, ObjKind::Constant) => {
                    self.inst = 0;
                    (None, Some(self.obj_name(o)))
                }
                None => continue,
            };
            self.fouts.push(ForeignOut {
                sv,
                bnd,
                ty: info.ty,
                sig,
                konst,
                decl: true,
            });
        }
    }

    /// A driver of signal `sig` with the value of SV expression `sv`.
    fn foreign_driver(&mut self, sig: SigRef, sv: String, bnd: Bnd, ty: TypeId, o: ObjId) {
        let k = self.fins.len();
        self.fins.push(ForeignIn { sv, bnd, ty });
        let drv = super::elab::PSEUDO + self.links.len();
        let cov = match &sig.part {
            Part::Path(path) => self.path_cov(self.sigs[sig.sig].ty, &super::elab::dsels(path)),
            Part::Whole => Cov::All,
        };
        let slots = sig.part != Part::Whole;
        self.add_driver(sig.sig, drv, cov, slots);
        let loc = self.d.objects[o].loc.clone();
        self.links.push(Link {
            inn: false,
            target: sig,
            value: HExpr {
                kind: HExprKind::Obj(o),
                ty,
                loc,
            },
            ctx: 0,
            sources: Vec::new(),
            drv,
            foreign: Some(k),
        });
    }

    /// Whether the design has a language boundary (the kernel then waits
    /// for SV instead of ending the simulation when VHDL is quiet).
    pub(super) fn has_boundary(&self) -> bool {
        self.boundary.is_some() || !self.fins.is_empty() || !self.fouts.is_empty()
    }

    /// The value of foreign driver `k` as a VHDL value (SV).
    pub(super) fn foreign_value(&mut self, k: usize) -> String {
        format!("vh_fci{}(vh_fl{})", k, k)
    }

    /// The boundary's declarations: the sampled SV values, the change
    /// counter and the conversions.
    pub(super) fn boundary_sv(&mut self) -> String {
        let mut s = String::new();
        if !self.has_boundary() {
            return s;
        }
        s.push_str("  int vh_extn, vh_exts;\n");
        s.push_str(
            "  // std_ulogic codes (U X 0 1 Z W L H -) and SV bits.\n  function automatic byte unsigned vh_l2u(logic b);\n    case (b)\n      1'b0: return 2;\n      1'b1: return 3;\n      1'bz: return 4;\n      default: return 1;\n    endcase\n  endfunction\n  function automatic logic vh_u2l(byte unsigned c);\n    case (c)\n      2, 6: return 1'b0;\n      3, 7: return 1'b1;\n      4: return 1'bz;\n      default: return 1'bx;\n    endcase\n  endfunction\n",
        );
        for (k, f) in self.fins.clone().into_iter().enumerate() {
            let loc = self.d.objects[0].loc.clone();
            let r = self.repr(f.ty, &loc);
            let _ = writeln!(s, "  {} vh_fl{k};\n  bit vh_fx{k};", f.bnd.sv(), k = k);
            let _ = writeln!(s, "  always @({}) vh_extn++;", f.sv);
            let body = self.conv_in(&f.bnd, &r, f.ty);
            let _ = write!(
                s,
                "  function automatic {t} vh_fci{k}({b} v);\n{body}  endfunction\n",
                t = r.sv(),
                k = k,
                b = f.bnd.sv(),
                body = body
            );
        }
        for (k, f) in self.fouts.clone().into_iter().enumerate() {
            let loc = self.d.objects[0].loc.clone();
            let r = self.repr(f.ty, &loc);
            if f.decl {
                let _ = writeln!(s, "  {} {}{};", f.bnd.sv(), f.sv, f.bnd.dims());
            }
            let part = f
                .sig
                .as_ref()
                .map(|r| r.part.clone())
                .unwrap_or(Part::Whole);
            let sty = f.sig.as_ref().map(|r| self.sigs[r.sig].ty).unwrap_or(f.ty);
            let body = self.conv_out(&f.bnd, &part, sty);
            let ret = if let Bnd::Arr(..) = f.bnd {
                let _ = writeln!(s, "  typedef {} vh_fat{}{};", f.bnd.sv(), k, f.bnd.dims());
                format!("vh_fat{}", k)
            } else {
                f.bnd.sv()
            };
            let _ = write!(
                s,
                "  function automatic {b} vh_fco{k}({t} a);\n{body}  endfunction\n",
                t = r.sv(),
                k = k,
                b = ret,
                body = body
            );
        }
        s
    }

    /// The body of the conversion of SV value `v` to a VHDL value.
    fn conv_in(&mut self, bnd: &Bnd, r: &Repr, ty: TypeId) -> String {
        let bit = |ul: bool, x: &str| {
            if ul {
                format!("vh_l2u({})", x)
            } else {
                format!("({} === 1'b1)", x)
            }
        };
        match bnd {
            Bnd::Bit(ul) => format!("    return {};\n", bit(*ul, "v")),
            Bnd::Vec(ul, n) => {
                if let Repr::Pk(w, _) = r {
                    return format!(
                        "    bit [{hi}:0] t;\n    for (int i = 0; i < {n}; i++) t[{w} * ({m} - i) +: {w}] = {b};\n    return t;\n",
                        hi = *w as i64 * n - 1,
                        n = n,
                        w = w,
                        m = n - 1,
                        b = bit(*ul, &format!("v[{} - i]", n - 1))
                    );
                }
                let Repr::Arr(name, er) = r else {
                    return "    return 0;\n".into();
                };
                let (l, dir, rr) = self.static_bounds(ty).unwrap_or((n - 1, Dir::Downto, 0));
                format!(
                    "    {et} t[];\n    t = new[{n}];\n    for (int i = 0; i < {n}; i++) t[i] = {b};\n    return {name}_mk({l}, {rr}, {dn}, t);\n",
                    et = er.sv(),
                    n = n,
                    b = bit(*ul, &format!("v[{} - i]", n - 1)),
                    name = name,
                    l = l,
                    rr = rr,
                    dn = (dir == Dir::Downto) as u8
                )
            }
            Bnd::Int => format!("    return $isunknown(v) ? 0 : {}'(v);\n", r.sv()),
            Bnd::Real => "    return v;\n".into(),
            Bnd::Arr(..) => "    return 0;\n".into(),
        }
    }

    /// The body of the conversion of VHDL value `a` (of a signal of type
    /// `sty`; `part` selects the part written) to an SV value.
    fn conv_out(&mut self, bnd: &Bnd, part: &Part, sty: TypeId) -> String {
        let bit = |ul: bool, x: &str| {
            if ul {
                format!("vh_u2l({})", x)
            } else {
                format!("logic'({} != 0)", x)
            }
        };
        let loc = self.d.objects[0].loc.clone();
        let (x, off, at) = match part {
            Part::Whole => ("a".to_string(), 0, sty),
            Part::Path(path) => {
                let (sel, slice, at) = self.path_sv(sty, path, &loc);
                (format!("a{}", sel), slice.map_or(0, |(o, _)| o), at)
            }
        };
        let pk = match self.repr(at, &loc) {
            Repr::Pk(w, n) => Some((w, n)),
            _ => None,
        };
        match bnd {
            Bnd::Bit(ul) => format!("    return {};\n", bit(*ul, &x)),
            Bnd::Vec(ul, n) => {
                let e = match pk {
                    Some((w, pn)) => Lw::pk_sel(&x, w, pn, &format!("{} + i", off)),
                    None => format!("{}.d[{} + i]", x, off),
                };
                format!(
                    "    {t} v;\n    for (int i = 0; i < {n}; i++) v[{m} - i] = {b};\n    return v;\n",
                    t = bnd.sv(),
                    n = n,
                    m = n - 1,
                    b = bit(*ul, &e)
                )
            }
            Bnd::Int | Bnd::Real => format!("    return {};\n", x),
            Bnd::Arr(_, l, r) => {
                let n = (l - r).abs() + 1;
                let step = if r >= l { "+" } else { "-" };
                format!(
                    "    {t} v{d};\n    for (int i = 0; i < {n}; i++) v[{l} {step} i] = {x}.d[{off} + i];\n    return v;\n",
                    t = bnd.sv(),
                    d = bnd.dims(),
                    n = n,
                    l = l,
                    step = step,
                    x = x,
                    off = off
                )
            }
        }
    }

    /// An SV module instantiated as a VHDL component in instance `inst`:
    /// its ports connected to SV variables the kernel writes (mode `in`)
    /// and to wires driving the actual signals (`out`).
    pub(super) fn sv_instance(&mut self, inst: usize, fi: &ForeignInst) {
        let m = self
            .d
            .sv_modules
            .get(&fi.module.to_ascii_lowercase())
            .cloned()
            .unwrap_or_default();
        let mut params = Vec::new();
        for (g, e) in &fi.generics {
            let Some(e) = e else { continue };
            let info = self.d.objects[*g].clone();
            let pname = m
                .params
                .iter()
                .find(|p| p.eq_ignore_ascii_case(&info.name))
                .cloned()
                .unwrap_or_else(|| sv_ident(&info.name));
            match self.d.eval(e).and_then(|v| self.sv_literal(info.ty, &v)) {
                Some(lit) => params.push(format!(".{}({})", pname, lit)),
                None => self.err(
                    &e.loc,
                    "the value of a generic of a SystemVerilog module must be a static integer, real, string or logic value",
                ),
            }
        }
        let mut conns = Vec::new();
        for (p, a) in &fi.ports {
            let info = self.d.objects[*p].clone();
            let ObjKind::Port(mode) = info.kind else {
                continue;
            };
            let pname = m
                .ports
                .iter()
                .find(|x| x.eq_ignore_ascii_case(&info.name))
                .cloned()
                .unwrap_or_else(|| sv_ident(&info.name));
            let Some(a) = a else {
                conns.push(format!(".{}()", pname));
                continue;
            };
            // The actual's subtype: the component's ports see the
            // component's default generics, not the generic map.
            let ty = if self.bnd(a.ty).is_some() {
                a.ty
            } else {
                info.ty
            };
            let Some(bnd) = self.bnd(ty) else {
                self.err(
                    &a.loc,
                    format!(
                        "port '{}' of SystemVerilog module '{}' has a type that cannot cross the language boundary",
                        info.name, m.name
                    ),
                );
                continue;
            };
            let k = self.sv_nets;
            self.sv_nets += 1;
            let r = self.actual_ref(inst, a);
            match (mode, r) {
                (Mode::In, Some(r)) => {
                    let sv = format!("vh_x{}", k);
                    let sty = self.sigs[r.sig].ty;
                    conns.push(format!(".{}({})", pname, sv));
                    self.fouts.push(ForeignOut {
                        sv,
                        bnd,
                        ty: sty,
                        sig: Some(r),
                        konst: None,
                        decl: true,
                    });
                }
                (Mode::In, None) => match self.d.eval(a).and_then(|v| self.sv_literal(ty, &v)) {
                    Some(lit) => conns.push(format!(".{}({})", pname, lit)),
                    None => self.err(
                        &a.loc,
                        "the actual of an input of a SystemVerilog module must be a signal or a static value",
                    ),
                },
                (Mode::Out | Mode::Buffer, Some(r)) => {
                    let w = format!("vh_w{}", k);
                    let _ = writeln!(self.sv_items, "  wire {} {};", bnd.sv(), w);
                    conns.push(format!(".{}({})", pname, w));
                    self.foreign_driver(r, w, bnd, ty, *p);
                }
                (Mode::Out | Mode::Buffer, None) => self.err(
                    &a.loc,
                    "the actual of an output of a SystemVerilog module must be a signal",
                ),
                _ => self.err(
                    &a.loc,
                    "an inout port of a SystemVerilog module cannot be connected yet",
                ),
            }
        }
        let label = self.inst_path(inst, &fi.label);
        let ps = if params.is_empty() {
            String::new()
        } else {
            format!(" #({})", params.join(", "))
        };
        let _ = writeln!(
            self.sv_items,
            "  {}{} {} ({});",
            m.name,
            ps,
            label,
            conns.join(", ")
        );
    }

    /// The SV instance name of `label` in VHDL instance `inst`: the labels
    /// of the instances below the top, joined.
    fn inst_path(&self, mut inst: usize, label: &str) -> String {
        let mut parts = vec![sv_ident(&label.to_ascii_lowercase())];
        while let Some(c) = self.insts[inst].container {
            parts.push(sv_ident(&self.insts[inst].label));
            inst = c;
        }
        parts.reverse();
        parts.join("_")
    }

    /// An SV literal of VHDL value `v` of type `t`.
    fn sv_literal(&self, t: TypeId, v: &Value) -> Option<String> {
        let b = self.base(t);
        let bit = |e: TypeId, v: &Value| -> Option<char> {
            let n = v.as_i64()?;
            if Some(self.base(e)) == self.d.std.std_ulogic {
                Some(match n {
                    2 | 6 => '0',
                    3 | 7 => '1',
                    4 => 'z',
                    _ => 'x',
                })
            } else {
                Some(if n != 0 { '1' } else { '0' })
            }
        };
        match (&self.d.types[b].kind, v) {
            (TypeKind::Integer | TypeKind::UniversalInteger, Value::Int(i)) => Some(i.to_string()),
            (TypeKind::Real | TypeKind::UniversalReal, Value::Real(r)) => Some(format!("{:?}", r)),
            (TypeKind::Enum(_), _) if self.d.is_logic_enum(b) => Some(format!("1'b{}", bit(b, v)?)),
            (TypeKind::Array { elem, .. }, Value::Array(a)) => {
                let e = self.base(*elem);
                if e == self.d.std.character {
                    let s: String = a
                        .elems
                        .iter()
                        .map(|c| c.as_i64().map(|c| c as u8 as char))
                        .collect::<Option<_>>()?;
                    return Some(super::sv_string(&s));
                }
                if !self.d.is_logic_enum(e) || a.elems.is_empty() {
                    return None;
                }
                let bits: String = a.elems.iter().map(|x| bit(e, x)).collect::<Option<_>>()?;
                Some(format!("{}'b{}", bits.len(), bits))
            }
            _ => None,
        }
    }

    /// Kernel, after elaboration: sample the SV values.
    pub(super) fn boundary_sample_init(&self) -> String {
        let mut s = String::new();
        for (k, f) in self.fins.iter().enumerate() {
            let _ = writeln!(s, "    vh_fl{} = {};", k, f.sv);
        }
        s
    }

    /// Kernel, at the start of a cycle: the SV values that changed.
    pub(super) fn boundary_sample(&self, ind: &str) -> String {
        let mut s = String::new();
        if !self.has_boundary() {
            return s;
        }
        let _ = writeln!(s, "{}vh_exts = vh_extn;", ind);
        for (k, f) in self.fins.iter().enumerate() {
            let _ = writeln!(
                s,
                "{ind}vh_fx{k} = {ne}; if (vh_fx{k}) vh_fl{k} = {sv};",
                ind = ind,
                k = k,
                ne = f.bnd.ne(&f.sv, &format!("vh_fl{}", k)),
                sv = f.sv
            );
        }
        s
    }

    /// The state the kernel shares with the eager evaluation, and the eager
    /// evaluation itself: a change of an SV value runs the simulation
    /// cycles of the current time at once, from a continuous assignment, as
    /// xezim settles SV combinational logic at the write (a cycle that
    /// resumes a process with waits is left to the kernel).
    pub(super) fn eager_sv(&self) -> String {
        let mut s = String::from(
            "  bit vh_busy, vh_started, vh_clkd, vh_nbt;\n  int vh_hand = -1;\n  int vh_kick, vh_ksn;\n",
        );
        if self.fins.is_empty() {
            return s;
        }
        let changed: Vec<String> = self
            .fins
            .iter()
            .enumerate()
            .map(|(k, f)| format!("({})", f.bnd.ne(&f.sv, &format!("vh_fl{}", k))))
            .collect();
        let _ = write!(
            s,
            "  // Writes nothing when there is nothing to do: the continuous assignment\n  // calling it is evaluated again when what it writes changes.\n  function automatic void vh_eager();\n    int r;\n    if (!vh_started || vh_busy || vh_hand >= 0 || vh_clkd || vh_stop) return;\n    if (!(({ch}) || vh_next() == $time)) return;\n    vh_busy = 1;\n    while (({ch}) || vh_next() == $time) begin\n      vh_update();\n      r = vh_resume(0);\n      if (r >= 0) begin vh_hand = r; break; end\n      if (vh_stop || vh_clkd) break;\n    end\n    vh_busy = 0;\n    vh_kick++;\n  endfunction\n",
            ch = changed.join(" || ")
        );
        let params: Vec<String> = self
            .fins
            .iter()
            .enumerate()
            .map(|(k, f)| format!("{} a{}", f.bnd.sv(), k))
            .collect();
        let args: Vec<String> = self.fins.iter().map(|f| f.sv.clone()).collect();
        let _ = write!(
            s,
            "  function automatic int vh_eagerf({});\n    vh_eager();\n    return 0;\n  endfunction\n  int vh_eagr;\n  assign vh_eagr = vh_eagerf({});\n",
            params.join(", "),
            args.join(", ")
        );
        s
    }

    /// Kernel: write the VHDL values to SV (`init`: all, else those with
    /// an event).
    pub(super) fn boundary_write(&self, init: bool, ind: &str) -> String {
        let mut s = String::new();
        for (k, f) in self.fouts.iter().enumerate() {
            let (v, sig) = match (&f.sig, &f.konst) {
                (Some(r), _) => (format!("vh_s{}", r.sig), r.sig),
                (None, Some(c)) if init => (c.clone(), 0),
                _ => continue,
            };
            if init {
                let _ = writeln!(s, "{}{} = vh_fco{}({});", ind, f.sv, k, v);
            } else {
                let _ = writeln!(
                    s,
                    "{}if (vh_s{}_ev) {} = vh_fco{}({});",
                    ind, sig, f.sv, k, v
                );
            }
        }
        s
    }
}
