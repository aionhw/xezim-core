//! Lowering an analysed VHDL design to SystemVerilog source text, parsed by
//! the SV parser and joined to the design before elaboration.
//!
//! The design is flattened into one module named after the top entity:
//! signals (effective value, event/active flags, last value and last event
//! time), one transaction queue per driver (signal × process), processes as
//! `initial` blocks, subprograms as automatic functions/tasks, and a
//! generated kernel `initial` block implementing the VHDL simulation cycle
//! (IEEE 1076-2008 §14.7.5): it updates signals from due transactions,
//! computes events, and resumes the processes waiting on them one at a
//! time, in elaboration order, waiting until each suspends again. VHDL
//! delta cycles therefore never depend on the SV scheduler's ordering.

mod runtime;

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::Write as _;

use super::ast::{Dir, Mode, ObjClass};
use super::sema::hir::*;
use super::sema::{Analysed, Design};

pub use runtime::real_image;

/// How a VHDL type is represented in SystemVerilog.
#[derive(Clone, Debug, PartialEq)]
enum Repr {
    /// Enumeration with ≤ 256 literals.
    U8,
    U32,
    I32,
    I64,
    Real,
    /// One-dimensional array: struct name and element representation.
    Arr(String, Box<Repr>),
    Rec(String),
}

impl Repr {
    fn sv(&self) -> String {
        match self {
            Repr::U8 => "byte unsigned".into(),
            Repr::U32 => "int unsigned".into(),
            Repr::I32 => "int".into(),
            Repr::I64 => "longint".into(),
            Repr::Real => "real".into(),
            Repr::Arr(n, _) => n.clone(),
            Repr::Rec(n) => n.clone(),
        }
    }
    fn key(&self) -> String {
        match self {
            Repr::U8 => "u8".into(),
            Repr::U32 => "u32".into(),
            Repr::I32 => "i32".into(),
            Repr::I64 => "i64".into(),
            Repr::Real => "r".into(),
            Repr::Arr(n, _) => n.clone(),
            Repr::Rec(n) => n.clone(),
        }
    }
}

pub struct Lowered {
    pub sv: String,
    pub top: String,
}

/// A wait site: the signals it is sensitive to.
struct Site {
    sigs: Vec<ObjId>,
}

struct Lw<'a> {
    d: &'a Design,
    items: String,
    arr_types: BTreeMap<String, (Repr, bool)>,
    rec_types: BTreeMap<TypeId, String>,
    lits: HashMap<String, String>,
    lit_items: String,
    dflt: HashMap<TypeId, String>,
    errors: Vec<String>,
    /// Signals of the flattened design.
    signals: Vec<ObjId>,
    /// Drivers (signal, process).
    drivers: BTreeSet<(ObjId, usize)>,
    /// Per process: its wait sites.
    sites: Vec<Vec<Site>>,
    subs_done: BTreeSet<SubId>,
    subs_todo: Vec<SubId>,
    sub_items: String,
    /// Process being lowered (for waits and drivers).
    cur_proc: Option<usize>,
    /// Lowering a subprogram that waits: the process id is the `vh_pid`
    /// argument.
    in_task: bool,
    tmp: usize,
    /// Enclosing loops: (label id, exit flag, next flag) for exits of outer
    /// loops.
    loops: Vec<usize>,
    loop_flags: BTreeSet<usize>,
    /// Statements to run before the statement being lowered (aggregate
    /// temporaries): (name, type, statement).
    pre_stmts: Vec<(String, String, String)>,
    /// Temporaries of the current scope: (name, type).
    temps: Vec<(String, String)>,
}

/// Lower the analysed design.
pub fn lower(an: &Analysed) -> Result<Lowered, Vec<String>> {
    let d = &an.design;
    let arch = &d.archs[an.top];
    let mut lw = Lw {
        d,
        items: String::new(),
        arr_types: BTreeMap::new(),
        rec_types: BTreeMap::new(),
        lits: HashMap::new(),
        lit_items: String::new(),
        dflt: HashMap::new(),
        errors: Vec::new(),
        signals: Vec::new(),
        drivers: BTreeSet::new(),
        sites: Vec::new(),
        subs_done: BTreeSet::new(),
        subs_todo: Vec::new(),
        sub_items: String::new(),
        cur_proc: None,
        in_task: false,
        tmp: 0,
        loops: Vec::new(),
        loop_flags: BTreeSet::new(),
        pre_stmts: Vec::new(),
        temps: Vec::new(),
    };
    if !arch.instances.is_empty() {
        let (f, l, c) = d.file_line(&arch.instances[0].loc);
        return Err(vec![format!(
            "{}:{}:{}: error: VHDL: component and entity instantiation are not supported yet",
            f, l, c
        )]);
    }
    let sv = lw.module(arch);
    if !lw.errors.is_empty() {
        lw.errors.dedup();
        return Err(lw.errors);
    }
    Ok(Lowered {
        sv,
        top: arch.entity.clone(),
    })
}

fn sv_ident(s: &str) -> String {
    s.chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect()
}

fn sv_string(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            c if (c as u32) < 32 || (c as u32) > 126 => {
                let _ = write!(out, "\\{:03o}", c as u32 & 0xff);
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

impl<'a> Lw<'a> {
    fn err(&mut self, loc: &Loc, msg: impl Into<String>) {
        let (f, l, c) = self.d.file_line(loc);
        self.errors
            .push(format!("{}:{}:{}: error: VHDL: {}", f, l, c, msg.into()));
    }

    fn file_line(&self, loc: &Loc) -> (String, usize, usize) {
        // Paths as given on the command line (GHDL prints them so).
        let f = &self.d.files[loc.file];
        let (l, c) = f.line_col(loc.span.start);
        (f.path.clone(), l, c)
    }

    fn base(&self, t: TypeId) -> TypeId {
        self.d.base(t)
    }

    // ---- types ------------------------------------------------------------------------

    fn repr(&mut self, t: TypeId, loc: &Loc) -> Repr {
        let b = self.base(t);
        match &self.d.types[b].kind {
            TypeKind::Enum(lits) => {
                if lits.len() <= 256 {
                    Repr::U8
                } else {
                    Repr::U32
                }
            }
            TypeKind::Integer => {
                let r = self.d.scalar_range(b);
                let fits = r.is_some_and(|r| {
                    let (a, z) = (r.left.as_i64().unwrap_or(0), r.right.as_i64().unwrap_or(0));
                    a >= i32::MIN as i64
                        && z <= i32::MAX as i64
                        && z >= i32::MIN as i64
                        && a <= i32::MAX as i64
                });
                if fits { Repr::I32 } else { Repr::I64 }
            }
            TypeKind::UniversalInteger | TypeKind::Physical(_) => Repr::I64,
            TypeKind::Real | TypeKind::UniversalReal => Repr::Real,
            TypeKind::Array { index, elem } => {
                if index.len() != 1 {
                    self.err(loc, "multi-dimensional arrays are not supported yet");
                    return Repr::I32;
                }
                let er = self.repr(*elem, loc);
                let name = format!("vh_a_{}", er.key());
                let logic = self.d.is_bit_or_bool(*elem);
                let e = self
                    .arr_types
                    .entry(name.clone())
                    .or_insert((er.clone(), false));
                e.1 |= logic;
                Repr::Arr(name, Box::new(er))
            }
            TypeKind::Record(fields) => {
                if let Some(n) = self.rec_types.get(&b) {
                    return Repr::Rec(n.clone());
                }
                let name = format!("vh_rec{}", b);
                self.rec_types.insert(b, name.clone());
                let mut s = String::from("  typedef struct {");
                let mut eqs = Vec::new();
                for (i, (_, ft)) in fields.clone().iter().enumerate() {
                    let r = self.repr(*ft, loc);
                    let _ = write!(s, " {} f{};", r.sv(), i);
                    eqs.push(self.eq_expr(&r, &format!("a.f{}", i), &format!("b.f{}", i)));
                }
                s.push_str(&format!(" }} {};\n", name));
                // Record equality, element by element (§9.2.3).
                let _ = writeln!(
                    s,
                    "  function automatic bit {n}_eq({n} a, {n} b);\n    return {};\n  endfunction",
                    if eqs.is_empty() {
                        "1".to_string()
                    } else {
                        eqs.join(" && ")
                    },
                    n = name
                );
                self.items.push_str(&s);
                Repr::Rec(name)
            }
            _ => {
                self.err(
                    loc,
                    format!(
                        "type '{}' is not supported in simulation yet",
                        self.d.types[b].name
                    ),
                );
                Repr::I32
            }
        }
    }

    /// The (left, dir, right) of a constrained array subtype, if static.
    fn static_bounds(&self, t: TypeId) -> Option<(i64, Dir, i64)> {
        let r = self.d.array_index_ranges(t)?;
        let sr = r.first()?.clone()?;
        Some((sr.left.as_i64()?, sr.dir, sr.right.as_i64()?))
    }

    /// The index subtype's left bound and direction (for concatenation
    /// results whose left operand is an element, §9.2.5).
    fn index_left_dir(&self, arr: TypeId) -> (i64, bool) {
        if let TypeKind::Array { index, .. } = &self.d.types[self.base(arr)].kind
            && let Some(sr) = self.d.scalar_range(index[0])
        {
            return (sr.left.as_i64().unwrap_or(0), sr.dir == Dir::Downto);
        }
        (0, false)
    }

    // ---- values ----------------------------------------------------------------------

    fn scalar_lit(&self, v: &Value, r: &Repr) -> String {
        match (v, r) {
            (Value::Real(f), _) => {
                if f.is_finite() {
                    format!("{:e}", f).replace("e", "e")
                } else if *f > 0.0 {
                    "1.0e308".into()
                } else {
                    "-1.0e308".into()
                }
            }
            (Value::Int(i) | Value::Phys(i), Repr::Real) => format!("{}.0", i),
            (Value::Int(i) | Value::Phys(i), _) => {
                if *i == i64::MIN {
                    "(-64'sd9223372036854775807 - 64'sd1)".into()
                } else if *i < 0 {
                    format!("(-64'sd{})", -(*i as i128))
                } else {
                    format!("64'sd{}", i)
                }
            }
            (Value::Enum(e), _) => format!("{}", e),
            _ => "0".into(),
        }
    }

    /// A static value of type `t` as SV text.
    fn value(&mut self, v: &Value, t: TypeId, loc: &Loc) -> String {
        let r = self.repr(t, loc);
        match (v, &r) {
            (Value::Array(av), Repr::Arr(name, er)) => {
                let key = format!("{}:{:?}", name, av);
                if let Some(f) = self.lits.get(&key) {
                    return format!("{}()", f);
                }
                let f = format!("vh_lit{}", self.lits.len());
                let elem_t = self.d.element_subtype(t).unwrap_or(t);
                let mut body = String::new();
                let _ = writeln!(
                    body,
                    "  function automatic {} {}();\n    {} t[];\n    t = new[{}];",
                    name,
                    f,
                    er.sv(),
                    av.elems.len()
                );
                for (i, e) in av.elems.iter().enumerate() {
                    let ev = self.value(e, elem_t, loc);
                    let _ = writeln!(body, "    t[{}] = {};", i, ev);
                }
                let _ = writeln!(
                    body,
                    "    return {}_from({}, {}, t);\n  endfunction",
                    name,
                    self.scalar_lit(&Value::Int(av.left), &Repr::I64),
                    (av.dir == Dir::Downto) as u8
                );
                self.lit_items.push_str(&body);
                self.lits.insert(key, f.clone());
                format!("{}()", f)
            }
            (Value::Record(vals), Repr::Rec(_)) => {
                let TypeKind::Record(fields) = self.d.types[self.base(t)].kind.clone() else {
                    return "'{default:0}".into();
                };
                let parts: Vec<String> = vals
                    .iter()
                    .zip(&fields)
                    .map(|(v, (_, ft))| self.value(v, *ft, loc))
                    .collect();
                format!("'{{{}}}", parts.join(", "))
            }
            _ => self.scalar_lit(v, &r),
        }
    }

    /// The default (initial) value of type `t` (§14.4.2.5: T'LEFT, element
    /// by element).
    fn default_value(&mut self, t: TypeId, loc: &Loc) -> String {
        let r = self.repr(t, loc);
        match &r {
            Repr::Arr(name, _) => {
                if let Some(f) = self.dflt.get(&t) {
                    return format!("{}()", f);
                }
                let f = format!("vh_dflt{}", t);
                self.dflt.insert(t, f.clone());
                let elem_t = self.d.element_subtype(t).unwrap_or(t);
                let ev = self.default_value(elem_t, loc);
                let er = match &r {
                    Repr::Arr(_, e) => e.sv(),
                    _ => unreachable!(),
                };
                let (l, dir, rr) = self.static_bounds(t).unwrap_or((0, Dir::To, -1));
                let n = match dir {
                    Dir::To => (rr - l + 1).max(0),
                    Dir::Downto => (l - rr + 1).max(0),
                };
                let _ = write!(
                    self.lit_items,
                    "  function automatic {} {}();\n    {} t[];\n    t = new[{}];\n    foreach (t[i]) t[i] = {};\n    return {}_from({}, {}, t);\n  endfunction\n",
                    name,
                    f,
                    er,
                    n,
                    ev,
                    name,
                    self.scalar_lit(&Value::Int(l), &Repr::I64),
                    (dir == Dir::Downto) as u8
                );
                format!("{}()", f)
            }
            Repr::Rec(_) => {
                let TypeKind::Record(fields) = self.d.types[self.base(t)].kind.clone() else {
                    return "'{default:0}".into();
                };
                let parts: Vec<String> = fields
                    .iter()
                    .map(|(_, ft)| self.default_value(*ft, loc))
                    .collect();
                format!("'{{{}}}", parts.join(", "))
            }
            _ => {
                let sr = self.d.scalar_range(t);
                match sr {
                    Some(sr) => self.scalar_lit(&sr.left, &r),
                    None => "0".into(),
                }
            }
        }
    }

    // ---- names -----------------------------------------------------------------------

    fn obj_name(&self, o: ObjId) -> String {
        let info = &self.d.objects[o];
        match info.kind {
            ObjKind::Signal | ObjKind::Port(_) => format!("vh_s{}", o),
            ObjKind::Param(..) => format!("p{}_{}", o, sv_ident(&info.name)),
            _ => format!("vh_o{}_{}", o, sv_ident(&info.name)),
        }
    }

    fn sub_name(&self, s: SubId) -> String {
        let n = &self.d.subprograms[s].name;
        let clean: String = n
            .chars()
            .filter(|c| c.is_ascii_alphanumeric() || *c == '_')
            .collect();
        format!("vh_f{}_{}", s, clean)
    }

    // ---- expressions -----------------------------------------------------------------

    fn ex(&mut self, h: &HExpr) -> String {
        match &h.kind {
            HExprKind::Lit(v) => self.value(v, h.ty, &h.loc),
            HExprKind::Obj(o) => {
                if let Some(v) = &self.d.objects[*o].static_val
                    && matches!(self.d.objects[*o].kind, ObjKind::Generic)
                {
                    return self.value(&v.clone(), h.ty, &h.loc);
                }
                self.obj_name(*o)
            }
            HExprKind::Qualified(x) => self.ex(x),
            HExprKind::Convert(x) => self.convert(x, h.ty, &h.loc),
            HExprKind::Call(s, args) => self.call(*s, args, h),
            HExprKind::Index(b, idx) => {
                let base = self.ex(b);
                let (f, l, _) = self.file_line(&h.loc);
                let i = self.ex(&idx[0]);
                format!(
                    "{}.d[vh_ix({}, {}.l, {}.r, {}.dn, {}, {})]",
                    base,
                    i,
                    base,
                    base,
                    base,
                    sv_string(&f),
                    l
                )
            }
            HExprKind::Slice(b, r) => {
                let base = self.ex(b);
                let (left, right, dn) = self.range_parts(r);
                let name = match self.repr(b.ty, &h.loc) {
                    Repr::Arr(n, _) => n,
                    _ => return "0".into(),
                };
                let (f, l, _) = self.file_line(&h.loc);
                format!(
                    "{}_slice({}, {}, {}, {}, {}, {})",
                    name,
                    base,
                    left,
                    right,
                    dn,
                    sv_string(&f),
                    l
                )
            }
            HExprKind::Field(b, i) => format!("{}.f{}", self.ex(b), i),
            HExprKind::ArrayAgg(items) => self.array_agg(items, h),
            HExprKind::RecordAgg(vals) => {
                let parts: Vec<String> = vals.iter().map(|v| self.ex(v)).collect();
                format!("'{{{}}}", parts.join(", "))
            }
            HExprKind::Attr(name, prefix, param) => self.attr(name, prefix, param.as_deref(), h),
            HExprKind::Deref(_) | HExprKind::New(_) => {
                self.err(&h.loc, "access types are not supported yet");
                "0".into()
            }
        }
    }

    fn range_parts(&mut self, r: &HRange) -> (String, String, String) {
        if let Some((o, dim, rev)) = &r.of_obj {
            let _ = dim;
            let b = self.ex(o);
            return if *rev {
                (format!("{}.r", b), format!("{}.l", b), format!("!{}.dn", b))
            } else {
                (format!("{}.l", b), format!("{}.r", b), format!("{}.dn", b))
            };
        }
        let l = self.ex(&r.left);
        let rr = self.ex(&r.right);
        (l, rr, ((r.dir == Dir::Downto) as u8).to_string())
    }

    fn convert(&mut self, x: &HExpr, to: TypeId, loc: &Loc) -> String {
        let v = self.ex(x);
        let (fb, tb) = (self.base(x.ty), self.base(to));
        if self.d.is_real(tb) && !self.d.is_real(fb) {
            return format!("real'({})", v);
        }
        if self.d.is_integer(tb) && self.d.is_real(fb) {
            return self.checked_int(format!("vh_rtoi({})", v), to, loc);
        }
        if self.d.is_integer(tb) && self.d.is_integer(fb) {
            return self.checked_int(v, to, loc);
        }
        // Closely related arrays: same representation, the value as is
        // (bounds kept, §9.3.6).
        v
    }

    /// Check an integer value against the (static) range of `t`.
    fn checked_int(&mut self, v: String, t: TypeId, loc: &Loc) -> String {
        match self.d.scalar_range(t) {
            Some(sr) => {
                let (lo, hi) = match sr.dir {
                    Dir::To => (
                        sr.left.as_i64().unwrap_or(0),
                        sr.right.as_i64().unwrap_or(0),
                    ),
                    Dir::Downto => (
                        sr.right.as_i64().unwrap_or(0),
                        sr.left.as_i64().unwrap_or(0),
                    ),
                };
                if lo == i64::MIN && hi == i64::MAX {
                    return v;
                }
                let (f, l, _) = self.file_line(loc);
                format!(
                    "vh_chk({}, {}, {}, {}, {})",
                    v,
                    self.scalar_lit(&Value::Int(lo), &Repr::I64),
                    self.scalar_lit(&Value::Int(hi), &Repr::I64),
                    sv_string(&f),
                    l
                )
            }
            None => v,
        }
    }

    fn call(&mut self, s: SubId, args: &[HExpr], h: &HExpr) -> String {
        let info = &self.d.subprograms[s];
        match info.builtin.clone() {
            Some(Builtin::Op(op)) => self.builtin_op(&op, s, args, h),
            Some(Builtin::MinMax(max)) => {
                if args.len() == 2 {
                    let (a, b) = (self.ex(&args[0]), self.ex(&args[1]));
                    format!(
                        "(({}) {} ({}) ? ({}) : ({}))",
                        a,
                        if max { ">" } else { "<" },
                        b,
                        a,
                        b
                    )
                } else {
                    self.err(&h.loc, "MINIMUM/MAXIMUM of an array is not supported yet");
                    "0".into()
                }
            }
            Some(Builtin::ToString) => self.image(&args[0], args[0].ty, false),
            Some(Builtin::RisingEdge) | Some(Builtin::FallingEdge) => {
                let a = &args[0];
                let HExprKind::Obj(o) = a.kind else {
                    self.err(
                        &h.loc,
                        "rising_edge/falling_edge of this signal is not supported yet",
                    );
                    return "0".into();
                };
                let one = matches!(info.builtin, Some(Builtin::RisingEdge));
                format!("(vh_s{}_ev && vh_s{} == {})", o, o, one as u8)
            }
            Some(Builtin::Now) => "longint'($time)".into(),
            Some(Builtin::Native(n)) => {
                self.err(&h.loc, format!("'{}' is not supported yet", n));
                "0".into()
            }
            Some(_) => {
                self.err(&h.loc, format!("'{}' is not supported yet", info.name));
                "0".into()
            }
            None => {
                self.need_sub(s);
                let mut a = Vec::new();
                for x in args {
                    a.push(self.ex(x));
                }
                format!("{}({})", self.sub_name(s), a.join(", "))
            }
        }
    }

    fn need_sub(&mut self, s: SubId) {
        if !self.subs_done.contains(&s) && !self.subs_todo.contains(&s) {
            self.subs_todo.push(s);
        }
    }

    fn arr_name(&mut self, t: TypeId, loc: &Loc) -> String {
        match self.repr(t, loc) {
            Repr::Arr(n, _) => n,
            _ => "vh_a_u8".into(),
        }
    }

    fn builtin_op(&mut self, op: &str, s: SubId, args: &[HExpr], h: &HExpr) -> String {
        let params = self.d.subprograms[s].params.clone();
        let pt: Vec<TypeId> = params.iter().map(|p| self.d.objects[*p].ty).collect();
        let ty = h.ty;
        let loc = h.loc.clone();
        let is_arr =
            |lw: &Self, t: TypeId| matches!(lw.d.types[lw.base(t)].kind, TypeKind::Array { .. });
        let a: Vec<String> = args.iter().map(|x| self.ex(x)).collect();
        if args.len() == 1 {
            let x = &a[0];
            return match op {
                "-" => self.arith(format!("-({})", x), ty, &loc),
                "+" => x.clone(),
                "abs" => self.arith(format!("((({x}) < 0) ? -({x}) : ({x}))", x = x), ty, &loc),
                "not" if is_arr(self, pt[0]) => {
                    format!("{}_not({})", self.arr_name(pt[0], &loc), x)
                }
                "not" => format!("(({}) == 0)", x),
                "??" => format!("(({}) == 1)", x),
                _ => {
                    self.err(&loc, format!("operator \"{}\" is not supported yet", op));
                    "0".into()
                }
            };
        }
        let (x, y) = (&a[0], &a[1]);
        let real = self.d.is_real(self.base(pt[0])) || self.d.is_real(self.base(pt[1]));
        match op {
            "=" | "/=" => {
                let r0 = self.repr(pt[0], &loc);
                let eq = self.eq_expr(&r0, x, y);
                if op == "=" { eq } else { format!("!{}", eq) }
            }
            "<" | "<=" | ">" | ">=" if is_arr(self, pt[0]) => {
                let n = self.arr_name(pt[0], &loc);
                match op {
                    "<" => format!("{}_lt({}, {})", n, x, y),
                    ">" => format!("{}_lt({}, {})", n, y, x),
                    "<=" => format!("!{}_lt({}, {})", n, y, x),
                    _ => format!("!{}_lt({}, {})", n, x, y),
                }
            }
            "<" | "<=" | ">" | ">=" => format!("(({}) {} ({}))", x, op, y),
            "and" | "or" | "nand" | "nor" | "xor" | "xnor"
                if is_arr(self, pt[0]) && is_arr(self, pt[1]) =>
            {
                let code = ["and", "or", "nand", "nor", "xor", "xnor"]
                    .iter()
                    .position(|o| *o == op)
                    .unwrap();
                let (f, l, _) = self.file_line(&loc);
                format!(
                    "{}_lop({}, {}, {}, {}, {})",
                    self.arr_name(pt[0], &loc),
                    x,
                    y,
                    code,
                    sv_string(&f),
                    l
                )
            }
            "and" => format!("(({}) & ({}))", x, y),
            "or" => format!("(({}) | ({}))", x, y),
            "xor" => format!("(({}) ^ ({}))", x, y),
            "nand" => format!("!(({}) & ({}))", x, y),
            "nor" => format!("!(({}) | ({}))", x, y),
            "xnor" => format!("!(({}) ^ ({}))", x, y),
            "&" => {
                let n = self.arr_name(ty, &loc);
                let (il, idn) = self.index_left_dir(ty);
                let il = self.scalar_lit(&Value::Int(il), &Repr::I64);
                match (is_arr(self, pt[0]), is_arr(self, pt[1])) {
                    (true, true) => format!("{}_cat({}, {})", n, x, y),
                    (true, false) => format!("{}_cat_ae({}, {}, {}, {})", n, x, y, il, idn as u8),
                    (false, true) => format!("{}_cat_ea({}, {}, {}, {})", n, x, y, il, idn as u8),
                    (false, false) => format!("{}_cat_ee({}, {}, {}, {})", n, x, y, il, idn as u8),
                }
            }
            "+" | "-" if real => format!("(({}) {} ({}))", x, op, y),
            "+" | "-" => self.arith(
                format!("(longint'({}) {} longint'({}))", x, op, y),
                ty,
                &loc,
            ),
            "*" if real && self.d.is_physical(ty) => {
                // physical × real (either order): rounded (§9.2.7).
                let (p, r) = if self.d.is_physical(pt[0]) {
                    (x, y)
                } else {
                    (y, x)
                };
                format!("vh_rtoi(real'({}) * ({}))", p, r)
            }
            "/" if real && self.d.is_physical(ty) => format!("vh_rtoi(real'({}) / ({}))", x, y),
            "*" | "/" if real => format!("(({}) {} ({}))", x, op, y),
            "*" => self.arith(format!("(longint'({}) * longint'({}))", x, y), ty, &loc),
            "/" => self.arith(format!("vh_div({}, {})", x, y), ty, &loc),
            "mod" => self.arith(format!("vh_mod({}, {})", x, y), ty, &loc),
            "rem" => self.arith(format!("vh_rem({}, {})", x, y), ty, &loc),
            "**" if real => format!("vh_powr({}, {})", x, y),
            "**" => self.arith(format!("vh_pow({}, {})", x, y), ty, &loc),
            _ => {
                self.err(&loc, format!("operator \"{}\" is not supported yet", op));
                "0".into()
            }
        }
    }

    /// Integer arithmetic checked against the result type's base range
    /// (overflow, §5.2.3.1).
    fn arith(&mut self, v: String, ty: TypeId, _loc: &Loc) -> String {
        let b = self.base(ty);
        if !matches!(self.d.types[b].kind, TypeKind::Integer) {
            return v;
        }
        match self.d.scalar_range(b) {
            Some(sr) => {
                let (lo, hi) = (
                    sr.left.as_i64().unwrap_or(0),
                    sr.right.as_i64().unwrap_or(0),
                );
                if lo == i64::MIN && hi == i64::MAX {
                    return v;
                }
                format!(
                    "vh_ovf({}, {}, {})",
                    v,
                    self.scalar_lit(&Value::Int(lo), &Repr::I64),
                    self.scalar_lit(&Value::Int(hi), &Repr::I64)
                )
            }
            None => v,
        }
    }

    /// `t'image(x)` (or TO_STRING): a STRING value (§16.2.2).
    fn image(&mut self, x: &HExpr, t: TypeId, _quote_unused: bool) -> String {
        let v = self.ex(x);
        let b = self.base(t);
        match self.d.types[b].kind.clone() {
            TypeKind::Integer | TypeKind::UniversalInteger => {
                format!("vh_str($sformatf(\"%0d\", {}))", v)
            }
            TypeKind::Real | TypeKind::UniversalReal => format!("vh_str($__vh_real_image({}))", v),
            TypeKind::Physical(units) => {
                format!("vh_str($sformatf(\"%0d {}\", {}))", units[0].0, v)
            }
            TypeKind::Enum(lits) => {
                let f = format!("vh_img{}", b);
                if !self.lits.contains_key(&f) {
                    let mut s = format!(
                        "  function automatic string {}(int unsigned p);\n    case (p)\n",
                        f
                    );
                    for (i, l) in lits.iter().enumerate() {
                        let _ = writeln!(s, "      {}: return {};", i, sv_string(l));
                    }
                    s.push_str("      default: return \"\";\n    endcase\n  endfunction\n");
                    self.lit_items.push_str(&s);
                    self.lits.insert(f.clone(), f.clone());
                }
                format!("vh_str({}({}))", f, v)
            }
            TypeKind::Array { .. } => v,
            _ => {
                self.err(&x.loc, "'image of this type is not supported yet");
                "vh_str(\"\")".into()
            }
        }
    }

    fn attr(
        &mut self,
        name: &str,
        prefix: &AttrPrefix,
        param: Option<&HExpr>,
        h: &HExpr,
    ) -> String {
        match prefix {
            AttrPrefix::Type(t) => match name {
                "image" => self.image(param.unwrap(), *t, true),
                "pos" => format!("longint'({})", self.ex(param.unwrap())),
                "val" => {
                    let v = self.ex(param.unwrap());
                    self.checked_int(v, *t, &h.loc)
                }
                "succ" | "pred" | "leftof" | "rightof" => {
                    let v = self.ex(param.unwrap());
                    let asc = self
                        .d
                        .scalar_range(*t)
                        .map(|r| r.dir == Dir::To)
                        .unwrap_or(true);
                    let up = match name {
                        "succ" => true,
                        "pred" => false,
                        "rightof" => asc,
                        _ => !asc,
                    };
                    let e = format!("(longint'({}) {} 1)", v, if up { "+" } else { "-" });
                    self.checked_int(e, *t, &h.loc)
                }
                "value" => {
                    self.err(&h.loc, "'value is not supported yet");
                    "0".into()
                }
                _ => {
                    self.err(
                        &h.loc,
                        format!("attribute '{} is not supported here yet", name),
                    );
                    "0".into()
                }
            },
            AttrPrefix::Expr(x) => {
                if let HExprKind::Obj(o) = &x.kind
                    && self.d.is_signal_expr(x)
                {
                    match name {
                        "event" => return format!("vh_s{}_ev", o),
                        "active" => return format!("vh_s{}_act", o),
                        "last_value" => return format!("vh_s{}_last", o),
                        "last_event" => return format!("(longint'($time) - vh_s{}_lev)", o),
                        _ => {}
                    }
                }
                let b = self.ex(x);
                match name {
                    "left" => format!("{}.l", b),
                    "right" => format!("{}.r", b),
                    "high" => format!("({b}.dn ? {b}.l : {b}.r)", b = b),
                    "low" => format!("({b}.dn ? {b}.r : {b}.l)", b = b),
                    "length" => format!("longint'({}.d.size())", b),
                    "ascending" => format!("!{}.dn", b),
                    "image" => self.image(x, x.ty, true),
                    _ => {
                        self.err(&h.loc, format!("attribute '{} is not supported yet", name));
                        "0".into()
                    }
                }
            }
        }
    }

    /// An array aggregate (§9.3.3): positional elements, then named
    /// choices and `others`. Built by statements run before the statement
    /// using it, into temporaries declared in the enclosing scope.
    fn array_agg(&mut self, items: &[(Vec<HChoice>, HExpr)], h: &HExpr) -> String {
        let t = h.ty;
        let name = self.arr_name(t, &h.loc);
        let er = match self.repr(t, &h.loc) {
            Repr::Arr(_, e) => e.sv(),
            _ => "int".into(),
        };
        self.tmp += 1;
        let agg = format!("vh_agg{}", self.tmp);
        let tv = format!("{}_t", agg);
        let setv = format!("{}_set", agg);
        let positional = items.iter().all(|(c, _)| c.is_empty());
        let mut body = String::new();
        let mut decls = vec![
            (agg.clone(), name.clone()),
            (format!("{}[]", tv), er.clone()),
        ];
        if positional {
            let (il, idn) = match self.static_bounds(t) {
                Some((l, d, _)) => (l, d == Dir::Downto),
                None => self.index_left_dir(t),
            };
            let _ = writeln!(body, "{} = new[{}];", tv, items.len());
            for (i, (_, v)) in items.iter().enumerate() {
                let x = self.ex(v);
                let _ = writeln!(body, "{}[{}] = {};", tv, i, x);
            }
            let _ = writeln!(
                body,
                "{} = {}_from({}, {}, {});",
                agg,
                name,
                self.scalar_lit(&Value::Int(il), &Repr::I64),
                idn as u8,
                tv
            );
        } else {
            // Named/others: the bounds come from the subtype.
            let Some((l, dir, r)) = self.static_bounds(t) else {
                self.err(
                    &h.loc,
                    "an aggregate with choices needs a constrained type here",
                );
                return "'{default:0}".into();
            };
            let n = match dir {
                Dir::To => (r - l + 1).max(0),
                Dir::Downto => (l - r + 1).max(0),
            };
            let dn = (dir == Dir::Downto) as u8;
            let ll = self.scalar_lit(&Value::Int(l), &Repr::I64);
            decls.push((format!("{}[]", setv), "bit".into()));
            let _ = writeln!(body, "{} = new[{}];", tv, n);
            let _ = writeln!(body, "{} = new[{}];", setv, n);
            let mut pos = 0i64;
            for (choices, v) in items {
                let x = self.ex(v);
                if choices.is_empty() {
                    let _ = writeln!(body, "{}[{}] = {}; {}[{}] = 1;", tv, pos, x, setv, pos);
                    pos += 1;
                    continue;
                }
                for c in choices {
                    match c {
                        HChoice::Others => {
                            let _ = writeln!(
                                body,
                                "foreach ({t}[k]) if (!{s}[k]) {t}[k] = {x};",
                                t = tv,
                                s = setv,
                                x = x
                            );
                        }
                        HChoice::Expr(e) => {
                            let i = self.ex(e);
                            let o = format!(
                                "({dn} ? {l} - ({i}) : ({i}) - {l})",
                                dn = dn,
                                l = ll,
                                i = i
                            );
                            let _ = writeln!(
                                body,
                                "{t}[{o}] = {x}; {s}[{o}] = 1;",
                                t = tv,
                                s = setv,
                                o = o,
                                x = x
                            );
                        }
                        HChoice::Range(hr) => {
                            let (a, b, _) = self.range_parts(hr);
                            let o = format!("({dn} ? {l} - k : k - {l})", dn = dn, l = ll);
                            let _ = writeln!(
                                body,
                                "for (longint k = (({a}) < ({b}) ? ({a}) : ({b})); k <= (({a}) < ({b}) ? ({b}) : ({a})); k++) begin {t}[{o}] = {x}; {s}[{o}] = 1; end",
                                a = a,
                                b = b,
                                t = tv,
                                s = setv,
                                o = o,
                                x = x
                            );
                        }
                    }
                }
            }
            let _ = writeln!(body, "{} = {}_from({}, {}, {});", agg, name, ll, dn, tv);
        }
        // Declarations go to the enclosing scope; the statements run first.
        for (n, ty) in decls.into_iter().skip(1) {
            let (n, dims) = match n.strip_suffix("[]") {
                Some(b) => (b.to_string(), "[]"),
                None => (n, ""),
            };
            self.temps.push((format!("{}{}", n, dims), ty));
        }
        self.pre_stmts.push((agg.clone(), name, body));
        agg
    }
}

// ---- statements, subprograms, processes, kernel ----------------------------------

impl<'a> Lw<'a> {
    /// The process id expression in the current context.
    fn pid(&self) -> String {
        if self.in_task {
            "vh_pid".into()
        } else {
            self.cur_proc.unwrap_or(0).to_string()
        }
    }

    /// Lower a statement list, indented.
    fn stmts(&mut self, stmts: &[HStmt], ind: usize) -> String {
        let mut out = String::new();
        for s in stmts {
            let body = self.stmt(s, ind);
            for (name, ty, st) in std::mem::take(&mut self.pre_stmts) {
                self.temps.push((name, ty));
                for line in st.lines() {
                    let _ = writeln!(out, "{}{}", " ".repeat(ind), line);
                }
            }
            out.push_str(&body);
        }
        out
    }

    /// An lvalue: the target of a variable assignment.
    fn assign_to(&mut self, target: &HExpr, value: String, ind: usize) -> String {
        let pad = " ".repeat(ind);
        let loc = target.loc.clone();
        let (f, l, _) = self.file_line(&loc);
        match &target.kind {
            HExprKind::Index(b, idx) => {
                let base = self.ex(b);
                let i = self.ex(&idx[0]);
                format!(
                    "{pad}{base}.d[vh_ix({i}, {base}.l, {base}.r, {base}.dn, {f}, {l})] = {value};\n",
                    pad = pad,
                    base = base,
                    i = i,
                    f = sv_string(&f),
                    l = l,
                    value = value
                )
            }
            HExprKind::Slice(b, r) => {
                let base = self.ex(b);
                let name = self.arr_name(b.ty, &loc);
                let (left, _right, _dn) = self.range_parts(r);
                format!(
                    "{pad}{base} = {name}_put({base}, vh_ix({left}, {base}.l, {base}.r, {base}.dn, {f}, {l}), {value}, {f}, {l});\n",
                    pad = pad,
                    base = base,
                    name = name,
                    left = left,
                    f = sv_string(&f),
                    l = l,
                    value = value
                )
            }
            _ => {
                let t = self.ex(target);
                format!("{}{} = {};\n", pad, t, value)
            }
        }
    }

    /// The value to store in an object of type `t` (array: length check
    /// and the target's bounds; scalar: range check).
    fn store_value(&mut self, target: &HExpr, v: &HExpr) -> String {
        let x = self.ex(v);
        let t = target.ty;
        match self.repr(t, &target.loc) {
            Repr::Arr(name, _) => {
                if matches!(target.kind, HExprKind::Slice(..)) {
                    return x;
                }
                let tv = self.ex(target);
                let (f, l, _) = self.file_line(&v.loc);
                format!("{}_conv({}, {}, {}, {})", name, tv, x, sv_string(&f), l)
            }
            Repr::I32 | Repr::I64 if self.d.is_integer(t) => self.checked_int(x, t, &v.loc),
            _ => x,
        }
    }

    fn stmt(&mut self, s: &HStmt, ind: usize) -> String {
        let pad = " ".repeat(ind);
        match &s.kind {
            HStmtKind::Null => String::new(),
            HStmtKind::VarAssign { target, value } => {
                let v = self.store_value(target, value);
                self.assign_to(target, v, ind)
            }
            HStmtKind::Assert {
                cond,
                report,
                severity,
            } => {
                let (f, l, c) = self.file_line(&s.loc);
                let is_assert = cond.is_some();
                let sev = match severity {
                    Some(x) => self.ex(x),
                    None => {
                        if is_assert {
                            "2".into()
                        } else {
                            "0".into()
                        }
                    }
                };
                let msg = match report {
                    Some(m) => format!("vh_sv({})", self.ex(m)),
                    None => "\"Assertion violation.\"".into(),
                };
                let call = format!(
                    "vh_report({}, {}, {}, {}, {}, {});",
                    sv_string(&f),
                    l,
                    c,
                    sev,
                    msg,
                    is_assert as u8
                );
                match cond {
                    Some(cnd) => {
                        let c = self.ex(cnd);
                        format!("{}if (!({})) {}\n", pad, c, call)
                    }
                    None => format!("{}{}\n", pad, call),
                }
            }
            HStmtKind::If(branches, else_b) => {
                let mut out = String::new();
                for (i, (c, body)) in branches.iter().enumerate() {
                    let cv = self.ex(c);
                    let _ = writeln!(
                        out,
                        "{}{}if ({}) begin",
                        pad,
                        if i == 0 { "" } else { "end else " },
                        cv
                    );
                    out.push_str(&self.stmts(body, ind + 2));
                }
                if let Some(e) = else_b {
                    let _ = writeln!(out, "{}end else begin", pad);
                    out.push_str(&self.stmts(e, ind + 2));
                }
                let _ = writeln!(out, "{}end", pad);
                out
            }
            HStmtKind::Case { expr, alts } => self.case(expr, alts, ind),
            HStmtKind::Loop {
                label,
                scheme,
                body,
            } => self.loop_(*label, scheme, body, ind, &s.loc),
            HStmtKind::Next(label, cond) | HStmtKind::Exit(label, cond) => {
                let is_exit = matches!(s.kind, HStmtKind::Exit(..));
                let inner = self.loops.last().copied();
                let act = if inner == Some(*label) {
                    if is_exit {
                        "break;".to_string()
                    } else {
                        "continue;".to_string()
                    }
                } else {
                    self.loop_flags.insert(*label);
                    format!(
                        "begin vh_{}{} = 1; break; end",
                        if is_exit { "x" } else { "n" },
                        label
                    )
                };
                match cond {
                    Some(c) => {
                        let cv = self.ex(c);
                        format!("{}if ({}) {}\n", pad, cv, act)
                    }
                    None => format!("{}{}\n", pad, act),
                }
            }
            HStmtKind::Return(v) => match v {
                Some(x) => {
                    let e = self.ex(x);
                    format!("{}return {};\n", pad, e)
                }
                None => format!("{}return;\n", pad),
            },
            HStmtKind::Wait { on, until, timeout } => {
                self.wait(on, until.as_ref(), timeout.as_ref(), ind, &s.loc)
            }
            HStmtKind::SignalAssign {
                target,
                delay,
                waves,
            } => self.signal_assign(target, delay.as_ref(), waves, ind),
            HStmtKind::Call(sub, args) => self.proc_call(*sub, args, ind, &s.loc),
        }
    }

    fn case(&mut self, expr: &HExpr, alts: &[(Vec<HChoice>, Vec<HStmt>)], ind: usize) -> String {
        let pad = " ".repeat(ind);
        let x = self.ex(expr);
        let mut out = String::new();
        let is_arr = matches!(
            self.d.types[self.base(expr.ty)].kind,
            TypeKind::Array { .. }
        );
        if is_arr {
            let name = self.arr_name(expr.ty, &expr.loc);
            let mut first = true;
            for (choices, body) in alts {
                let conds: Vec<String> = choices
                    .iter()
                    .map(|c| match c {
                        HChoice::Others => "1".to_string(),
                        HChoice::Expr(e) => format!("{}_eq({}, {})", name, x, self.ex(e)),
                        HChoice::Range(_) => "0".to_string(),
                    })
                    .collect();
                let _ = writeln!(
                    out,
                    "{}{}if ({}) begin",
                    pad,
                    if first { "" } else { "end else " },
                    conds.join(" || ")
                );
                out.push_str(&self.stmts(body, ind + 2));
                first = false;
            }
            let _ = writeln!(out, "{}end", pad);
            return out;
        }
        let _ = writeln!(out, "{}case ({}) inside", pad, x);
        for (choices, body) in alts {
            let mut labels = Vec::new();
            let mut others = false;
            for c in choices {
                match c {
                    HChoice::Others => others = true,
                    HChoice::Expr(e) => labels.push(self.ex(e)),
                    HChoice::Range(r) => {
                        let (a, b, _) = self.range_parts(r);
                        if r.dir == Dir::Downto {
                            labels.push(format!("[{}:{}]", b, a));
                        } else {
                            labels.push(format!("[{}:{}]", a, b));
                        }
                    }
                }
            }
            let head = if others {
                "default".to_string()
            } else {
                labels.join(", ")
            };
            let _ = writeln!(out, "{}  {}: begin", pad, head);
            out.push_str(&self.stmts(body, ind + 4));
            let _ = writeln!(out, "{}  end", pad);
        }
        let _ = writeln!(out, "{}endcase", pad);
        out
    }

    fn loop_(
        &mut self,
        label: usize,
        scheme: &HLoop,
        body: &[HStmt],
        ind: usize,
        _loc: &Loc,
    ) -> String {
        let pad = " ".repeat(ind);
        self.loops.push(label);
        let inner = self.stmts(body, ind + 2);
        self.loops.pop();
        let mut out = String::new();
        // Flags of exit/next statements of this loop from inner loops.
        let flagged = self.loop_flags.contains(&label);
        if flagged {
            self.temps.push((format!("vh_x{}", label), "bit".into()));
            self.temps.push((format!("vh_n{}", label), "bit".into()));
            let _ = writeln!(out, "{}vh_x{} = 0;", pad, label);
        }
        let after_inner = |out: &mut String| {
            // An inner loop finished with a flag for an outer loop.
            let _ = out;
        };
        after_inner(&mut out);
        match scheme {
            HLoop::Plain => {
                let _ = writeln!(out, "{}forever begin", pad);
            }
            HLoop::While(c) => {
                let cv = self.ex(c);
                let _ = writeln!(out, "{}while ({}) begin", pad, cv);
            }
            HLoop::For(o, r) => {
                let (a, b, dn) = self.range_parts(r);
                let v = self.obj_name(*o);
                self.temps.push((format!("{}_dn", v), "bit".into()));
                self.temps.push((format!("{}_end", v), "longint".into()));
                let _ = writeln!(out, "{}{}_dn = {};", pad, v, dn);
                let _ = writeln!(out, "{}{}_end = {};", pad, v, b);
                let _ = writeln!(
                    out,
                    "{pad}for (longint {v} = {a}; {v}_dn ? {v} >= {v}_end : {v} <= {v}_end; {v} = {v}_dn ? {v} - 1 : {v} + 1) begin",
                    pad = pad,
                    v = v,
                    a = a
                );
            }
        }
        if flagged {
            let _ = writeln!(out, "{}  vh_n{} = 0;", pad, label);
        }
        out.push_str(&inner);
        let _ = writeln!(out, "{}end", pad);
        // Propagate exits of outer loops through this one.
        let outer: Vec<usize> = self.loops.clone();
        for ol in outer {
            if self.loop_flags.contains(&ol) {
                let inner_most = self.loops.last() == Some(&ol);
                let _ = writeln!(out, "{}if (vh_x{ol}) break;", pad, ol = ol);
                let _ = writeln!(
                    out,
                    "{}if (vh_n{ol}) {};",
                    pad,
                    if inner_most { "continue" } else { "break" },
                    ol = ol
                );
            }
        }
        out
    }

    /// `wait on S until C for T` (§10.2): suspend at a site sensitive to S
    /// with an optional deadline; resumed by the kernel on an event of S
    /// (then C must hold) or at the deadline.
    fn wait(
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
        let mut sigs = Vec::new();
        for s in on {
            match self.signal_obj(s) {
                Some(o) => {
                    if !sigs.contains(&o) {
                        sigs.push(o);
                    }
                }
                None => self.err(&s.loc, "this sensitivity is not supported yet"),
            }
        }
        let site = self.sites[p].len();
        self.sites[p].push(Site { sigs });
        let pid = self.pid();
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
        let _ = pid;
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

    /// The signal object a sensitivity or target names (whole signals).
    fn signal_obj(&self, h: &HExpr) -> Option<ObjId> {
        match &h.kind {
            HExprKind::Obj(o)
                if matches!(self.d.objects[*o].kind, ObjKind::Signal | ObjKind::Port(_)) =>
            {
                Some(*o)
            }
            HExprKind::Index(b, _) | HExprKind::Slice(b, _) | HExprKind::Field(b, _) => {
                self.signal_obj(b)
            }
            _ => None,
        }
    }

    /// `s <= [delay] w1 after t1, w2 after t2, …` (§10.5.2): update the
    /// projected waveform of this process's driver of s.
    fn signal_assign(
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
        let HExprKind::Obj(sig) = target.kind else {
            self.err(
                &loc,
                "assignments to parts of a signal are not supported yet",
            );
            return String::new();
        };
        self.drivers.insert((sig, p));
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
            let _ = writeln!(
                out,
                "{}vh_drv_{}_{}({}, {}, {}, {});",
                pad, sig, p, val, t, rej, mode
            );
        }
        if waves.is_empty() {
            // `unaffected`
        }
        out
    }

    fn proc_call(&mut self, sub: SubId, args: &[HExpr], ind: usize, loc: &Loc) -> String {
        let pad = " ".repeat(ind);
        let info = self.d.subprograms[sub].clone();
        match info.builtin {
            Some(Builtin::Native(n)) => match n.as_str() {
                "env.finish" | "env.stop" => {
                    let word = if n == "env.finish" {
                        "finished"
                    } else {
                        "stopped"
                    };
                    format!(
                        "{}begin $display(\"simulation {} @%s\", vh_time_at($time)); vh_stop = 1; $finish; end\n",
                        pad, word
                    )
                }
                _ => {
                    self.err(
                        loc,
                        format!(
                            "'{}' is not supported yet",
                            n.replace("env.", "std.env.")
                                .replace("textio.", "std.textio.")
                        ),
                    );
                    String::new()
                }
            },
            Some(_) => {
                self.err(
                    loc,
                    format!("procedure '{}' is not supported yet", info.name),
                );
                String::new()
            }
            None => {
                self.need_sub(sub);
                let mut a = Vec::new();
                for x in args {
                    a.push(self.ex(x));
                }
                if self.sub_waits(sub) {
                    a.insert(0, self.pid());
                }
                format!("{}{}({});\n", pad, self.sub_name(sub), a.join(", "))
            }
        }
    }

    /// Whether a procedure (transitively) waits: lowered as a task with the
    /// calling process's id.
    fn sub_waits(&self, s: SubId) -> bool {
        fn has_wait(stmts: &[HStmt]) -> bool {
            stmts.iter().any(|s| match &s.kind {
                HStmtKind::Wait { .. } => true,
                HStmtKind::If(b, e) => {
                    b.iter().any(|(_, x)| has_wait(x)) || e.as_ref().is_some_and(|x| has_wait(x))
                }
                HStmtKind::Case { alts, .. } => alts.iter().any(|(_, x)| has_wait(x)),
                HStmtKind::Loop { body, .. } => has_wait(body),
                _ => false,
            })
        }
        self.d.subprograms[s]
            .body
            .as_ref()
            .is_some_and(|b| has_wait(&b.stmts))
    }

    fn subprogram(&mut self, s: SubId) {
        let info = self.d.subprograms[s].clone();
        let Some(body) = info.body.clone() else {
            let loc = info.loc.clone().unwrap_or(Loc {
                file: 0,
                span: 0..0,
            });
            self.err(&loc, format!("subprogram '{}' has no body", info.name));
            return;
        };
        let loc = info.loc.clone().unwrap_or(Loc {
            file: 0,
            span: 0..0,
        });
        if self.sub_waits(s) {
            self.err(
                &loc,
                "procedures with wait statements are not supported yet",
            );
            return;
        }
        let saved_temps = std::mem::take(&mut self.temps);
        let saved_proc = self.cur_proc.take();
        let mut params = Vec::new();
        for p in &info.params {
            let o = &self.d.objects[*p];
            let dir = match o.kind {
                ObjKind::Param(ObjClass::Signal, _) => {
                    self.err(&loc, "signal parameters are not supported yet");
                    "input"
                }
                ObjKind::Param(_, Mode::Out) => "output",
                ObjKind::Param(_, Mode::InOut) => "inout",
                _ => "input",
            };
            let r = self.repr(o.ty, &loc);
            params.push(format!("{} {} {}", dir, r.sv(), self.obj_name(*p)));
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
        let ret = match info.ret {
            Some(rt) => self.repr(rt, &loc).sv(),
            None => "void".into(),
        };
        let _ = write!(
            self.sub_items,
            "  function automatic {} {}({});\n{}{}{}{}  endfunction\n",
            ret,
            self.sub_name(s),
            params.join(", "),
            locals,
            temps,
            inits,
            stmts
        );
        self.temps = saved_temps;
        self.cur_proc = saved_proc;
    }

    fn store_value_init(&mut self, target: &HExpr, v: &HExpr) -> String {
        // An object's initial value: an array takes its declared bounds when
        // the subtype is constrained, else the value's own.
        if let Repr::Arr(name, _) = self.repr(target.ty, &target.loc)
            && self.static_bounds(target.ty).is_some()
        {
            let x = self.ex(v);
            let d = self.default_value(target.ty, &target.loc);
            let (f, l, _) = self.file_line(&v.loc);
            return format!("{}_conv({}, {}, {}, {})", name, d, x, sv_string(&f), l);
        }
        let x = self.ex(v);
        if self.d.is_integer(target.ty) {
            return self.checked_int(x, target.ty, &v.loc);
        }
        x
    }

    fn flush_pre(&mut self, ind: usize) -> String {
        let mut out = String::new();
        for (name, ty, st) in std::mem::take(&mut self.pre_stmts) {
            self.temps.push((name, ty));
            for line in st.lines() {
                let _ = writeln!(out, "{}{}", " ".repeat(ind), line);
            }
        }
        out
    }

    // ---- the module ----------------------------------------------------------------

    fn module(&mut self, arch: &Architecture) -> String {
        let d = self.d;
        let np = arch.processes.len().max(1);
        self.sites = (0..arch.processes.len()).map(|_| Vec::new()).collect();
        // Signals: ports of the top entity and the architecture's signals.
        let mut sigs: Vec<ObjId> = arch.ports.clone();
        sigs.extend(arch.signals.iter().copied());
        self.signals = sigs.clone();
        // Elaboration: package objects (analysis order), generics,
        // constants and signals of the architecture, process variables.
        let mut elab = String::new();
        let mut decls = String::new();
        let mut pkg_objs: Vec<ObjId> = Vec::new();
        for (p, _) in d.packages.values() {
            pkg_objs.extend(p.objects.iter().copied());
        }
        pkg_objs.sort();
        // A deferred constant is listed by its package and its body.
        pkg_objs.dedup();
        let mut objs: Vec<ObjId> = pkg_objs;
        objs.extend(arch.generics.iter().copied());
        objs.extend(arch.constants.iter().copied());
        let mut proc_vars: Vec<ObjId> = Vec::new();
        for p in &arch.processes {
            proc_vars.extend(p.locals.iter().copied());
        }
        self.temps.clear();
        for o in objs.iter().chain(&proc_vars).chain(&sigs) {
            let info = d.objects[*o].clone();
            if matches!(info.kind, ObjKind::File) {
                continue;
            }
            let r = self.repr(info.ty, &info.loc);
            let name = self.obj_name(*o);
            let _ = writeln!(decls, "  {} {};", r.sv(), name);
            let v = match &info.init {
                Some(i) => {
                    let target = HExpr {
                        kind: HExprKind::Obj(*o),
                        ty: info.ty,
                        loc: info.loc.clone(),
                    };
                    self.store_value_init(&target, i)
                }
                None => self.default_value(info.ty, &info.loc),
            };
            let flushed = self.flush_pre(4);
            elab.push_str(&flushed);
            let _ = writeln!(elab, "    {} = {};", name, v);
        }
        // Temporaries of the initial values, declared in vh_elab.
        let mut elab_temps = String::new();
        for (n, t) in std::mem::take(&mut self.temps) {
            let _ = writeln!(elab_temps, "    {} {};", t, n);
        }
        // Signal bookkeeping.
        for s in &sigs {
            let info = d.objects[*s].clone();
            let r = self.repr(info.ty, &info.loc);
            let _ = writeln!(
                decls,
                "  bit vh_s{s}_ev, vh_s{s}_act; {t} vh_s{s}_last; longint vh_s{s}_lev;",
                s = s,
                t = r.sv()
            );
            let _ = writeln!(
                elab,
                "    vh_s{s}_last = vh_s{s}; vh_s{s}_lev = -64'sd9223372036854775807;",
                s = s
            );
        }
        // Processes.
        let mut procs = String::new();
        for (pi, p) in arch.processes.iter().enumerate() {
            self.cur_proc = Some(pi);
            self.temps.clear();
            let body = self.stmts(&p.stmts, 6);
            let mut implicit = String::new();
            if let Some(sens) = &p.sens {
                let mut ss = Vec::new();
                for x in sens {
                    match self.signal_obj(x) {
                        Some(o) => {
                            if !ss.contains(&o) {
                                ss.push(o);
                            }
                        }
                        None => self.err(&x.loc, "this sensitivity is not supported yet"),
                    }
                }
                let site = self.sites[pi].len();
                self.sites[pi].push(Site { sigs: ss });
                let _ = writeln!(
                    implicit,
                    "      vh_site[{p}] = {site}; vh_tmo[{p}] = -64'sd1; vh_go[{p}] = 0; wait (vh_go[{p}]);",
                    p = pi,
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
                "  // process {label}\n  initial begin : vh_p{pi}_{label}\n{temps}    wait (vh_go[{pi}]);\n    forever begin\n{body}{implicit}    end\n  end\n",
                label = label,
                pi = pi,
                temps = temps,
                body = body,
                implicit = implicit
            );
        }
        self.cur_proc = None;
        // Subprograms the design calls (transitively).
        while let Some(s) = self.subs_todo.pop() {
            if self.subs_done.insert(s) {
                self.subprogram(s);
            }
        }
        // Drivers.
        let mut drv = String::new();
        let drivers: Vec<(ObjId, usize)> = self.drivers.iter().copied().collect();
        for (s, p) in &drivers {
            let info = d.objects[*s].clone();
            let r = self.repr(info.ty, &info.loc);
            let t = r.sv();
            // Parallel queues of transaction times and values (a queue of
            // structs holding a struct does not round-trip in the simulator).
            let eq = self.eq_expr(&r, "qv[k]", "v");
            let _ = write!(
                drv,
                "  longint vh_dt{s}_{p}[$];\n  {t} vh_dq{s}_{p}[$];\n  {t} vh_dv{s}_{p};\n  // Update the projected output waveform (§10.5.2.2): mode 0 transport,\n  // 1 inertial first element (reject limit), 2 later elements.\n  function automatic void vh_drv_{s}_{p}({t} v, longint after, longint rej, int mode);\n    longint tt;\n    longint qt[$];\n    {t} qv[$];\n    int k;\n    tt = longint'($time) + after;\n    qt = vh_dt{s}_{p};\n    qv = vh_dq{s}_{p};\n    while (qt.size() > 0 && qt[qt.size()-1] >= tt) begin void'(qt.pop_back()); void'(qv.pop_back()); end\n    if (mode == 1) begin\n      // Pulse rejection: of the old transactions in [tt - rej, tt), keep\n      // the run immediately before the new one that has its value.\n      k = qt.size() - 1;\n      while (k >= 0 && qt[k] >= tt - rej && ({eq})) k--;\n      while (k >= 0 && qt[k] >= tt - rej) begin qt.delete(k); qv.delete(k); k--; end\n    end\n    qt.push_back(tt);\n    qv.push_back(v);\n    vh_dt{s}_{p} = qt;\n    vh_dq{s}_{p} = qv;\n  endfunction\n",
                t = t,
                s = s,
                p = p,
                eq = eq
            );
            let _ = writeln!(elab, "    vh_dv{s}_{p} = vh_s{s};", s = s, p = p);
        }
        // Kernel.
        let mut k = String::new();
        let _ = writeln!(k, "  initial begin : vh_kernel");
        let _ = writeln!(k, "    longint vh_nxt;");
        let _ = writeln!(k, "    vh_elab();");
        let _ = writeln!(
            k,
            "    // Initialization (§14.7.5.2): every process runs until it suspends."
        );
        let _ = writeln!(
            k,
            "    for (int p = 0; p < {}; p++) begin vh_go[p] = 1; wait (vh_go[p] == 0); end",
            arch.processes.len()
        );
        let _ = writeln!(k, "    forever begin");
        let _ = writeln!(k, "      vh_nxt = -64'sd1;");
        for (s, p) in &drivers {
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
            arch.processes.len()
        );
        let _ = writeln!(k, "      if (vh_nxt < 0 || vh_stop) break;");
        let _ = writeln!(k, "      if (vh_nxt > $time) #(vh_nxt - $time);");
        let _ = writeln!(k, "      // Signal update (§14.7.3).");
        for s in &sigs {
            let _ = writeln!(k, "      vh_s{s}_ev = 0; vh_s{s}_act = 0;", s = s);
        }
        for (s, p) in &drivers {
            let _ = writeln!(
                k,
                "      if (vh_dt{s}_{p}.size() > 0 && vh_dt{s}_{p}[0] <= $time) begin void'(vh_dt{s}_{p}.pop_front()); vh_dv{s}_{p} = vh_dq{s}_{p}.pop_front(); vh_s{s}_act = 1; end",
                s = s,
                p = p
            );
        }
        for s in &sigs {
            let ds: Vec<usize> = drivers
                .iter()
                .filter(|(x, _)| x == s)
                .map(|(_, p)| *p)
                .collect();
            if ds.is_empty() {
                continue;
            }
            if ds.len() > 1 {
                let info = &d.objects[*s];
                let loc = info.loc.clone();
                self.err(
                    &loc,
                    format!(
                        "signal '{}' has several drivers (resolved signals are not supported yet)",
                        info.name
                    ),
                );
                continue;
            }
            let info = d.objects[*s].clone();
            let r = self.repr(info.ty, &info.loc);
            let ne = format!(
                "!({})",
                self.eq_expr(&r, &format!("vh_dv{}_{}", s, ds[0]), &format!("vh_s{}", s))
            );
            let _ = writeln!(
                k,
                "      if (vh_s{s}_act && {ne}) begin vh_s{s}_last = vh_s{s}; vh_s{s} = vh_dv{s}_{p}; vh_s{s}_ev = 1; vh_s{s}_lev = $time; end",
                s = s,
                p = ds[0],
                ne = ne
            );
        }
        let _ = writeln!(k, "      // Resume (§14.7.5.3), in elaboration order.");
        for pi in 0..arch.processes.len() {
            let mut conds = vec![format!(
                "(vh_tmo[{p}] >= 0 && vh_tmo[{p}] <= $time)",
                p = pi
            )];
            for (si, site) in self.sites[pi].iter().enumerate() {
                if site.sigs.is_empty() {
                    continue;
                }
                let evs: Vec<String> = site.sigs.iter().map(|s| format!("vh_s{}_ev", s)).collect();
                conds.push(format!(
                    "(vh_site[{}] == {} && ({}))",
                    pi,
                    si,
                    evs.join(" || ")
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

        // Assemble.
        let mut m = String::new();
        let _ = writeln!(m, "module {};", sv_ident(&arch.entity));
        let _ = writeln!(m, "  timeunit 1fs; timeprecision 1fs;");
        let mut arr_defs = String::new();
        for (name, (er, logic)) in self.arr_types.clone() {
            let eq = self.eq_expr(&er, "A", "B");
            let mut t = runtime::ARRAY_TEMPLATE
                .replace("ARR", &name)
                .replace("ELEM", &er.sv());
            t = t.replace(
                "EQ(x.d[i], y.d[i])",
                &eq.replace("A", "x.d[i]").replace("B", "y.d[i]"),
            );
            arr_defs.push_str(&t);
            if logic {
                arr_defs.push_str(
                    &runtime::LOGIC_TEMPLATE
                        .replace("ARR", &name)
                        .replace("ELEM", &er.sv()),
                );
            }
        }
        // STRING helpers (always: messages are strings).
        if !self.arr_types.contains_key("vh_a_u8") {
            let t = runtime::ARRAY_TEMPLATE
                .replace("ARR", "vh_a_u8")
                .replace("ELEM", "byte unsigned")
                .replace("EQ(x.d[i], y.d[i])", "x.d[i] == y.d[i]");
            arr_defs.push_str(&t);
        }
        m.push_str(runtime::COMMON);
        m.push_str(&self.items);
        m.push_str(&arr_defs);
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
        m.push_str(&drv);
        m.push_str(&self.sub_items);
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

    /// Equality of two values of a representation (SV expression).
    fn eq_expr(&self, r: &Repr, a: &str, b: &str) -> String {
        match r {
            Repr::Arr(n, _) => format!("{}_eq({}, {})", n, a, b),
            Repr::Rec(n) => format!("{}_eq({}, {})", n, a, b),
            _ => format!("({} == {})", a, b),
        }
    }
}
