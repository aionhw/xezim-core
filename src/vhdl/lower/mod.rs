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

mod elab;
mod files;
mod mixed;
mod records;
mod runtime;
mod textio;

use std::collections::{BTreeMap, BTreeSet, HashMap};

use elab::{Driver, GLOBAL, InstInfo, Sig, SigRef, Site};
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
    /// The module of the VHDL top level, if any.
    pub top: Option<String>,
}

struct Lw<'a> {
    d: &'a Design,
    /// Type definitions (records, array structs and their helpers), in
    /// creation order: a type's parts are defined before it.
    type_defs: String,
    arr_types: BTreeSet<String>,
    /// Heaps of designated types (by representation key), after the types.
    heaps: BTreeSet<String>,
    heap_defs: String,
    /// TEXTIO support code, when used.
    textio: bool,
    /// The design has file objects (support code in files.rs).
    files: bool,
    /// Protected types whose objects are made (`prot_new`), and their
    /// variables and constructors.
    prots: BTreeSet<TypeId>,
    prot_defs: String,
    /// In a method of a protected type: the SV name of its object.
    cur_self: Option<String>,
    /// Array types of BIT/BOOLEAN elements (logical operators).
    logic_arrs: BTreeSet<String>,
    rec_types: BTreeMap<TypeId, String>,
    lits: HashMap<String, String>,
    lit_items: String,
    dflt: HashMap<TypeId, String>,
    errors: Vec<String>,
    /// Signals of the flattened design.
    sigs: Vec<Sig>,
    /// The signal (part) each signal object of an instance names.
    sig_map: HashMap<(usize, ObjId), SigRef>,
    /// Instances, depth-first (0: the top).
    insts: Vec<InstInfo>,
    /// Objects declared by each architecture's scope (`elab::owner_inst`).
    arch_objs: Vec<std::collections::HashSet<ObjId>>,
    /// The instance being lowered.
    inst: usize,
    /// Processes in elaboration order: instance, architecture, index.
    procs: Vec<(usize, usize, usize)>,
    /// Drivers by (signal, process).
    drivers: BTreeMap<(usize, usize), Driver>,
    /// Port associations through conversions or partial formals.
    links: Vec<elab::Link>,
    /// Per process: its wait sites.
    sites: Vec<Vec<Site>>,
    /// Package objects (named without an instance).
    pkg_objs: BTreeSet<ObjId>,
    /// Lowering signal names as their last values (`'last_value`).
    read_last: bool,
    /// Subprograms by (subprogram, instance): one per instance when it is
    /// declared in an architecture.
    subs_done: BTreeSet<(SubId, usize)>,
    subs_todo: Vec<(SubId, usize)>,
    sub_items: String,
    /// Process being lowered (for waits and drivers).
    cur_proc: Option<usize>,
    /// Implicit signals, and their signals by attribute name and prefix.
    imps: Vec<elab::Imp>,
    imp_keys: HashMap<String, usize>,
    /// Implicit signals read while lowering (dependencies of an implicit
    /// signal's own update).
    imp_refs: Vec<usize>,
    /// Signals whose time of last activity is kept (`'last_active`).
    need_lact: BTreeSet<usize>,
    /// `'driving`/`'driving_value` uses: signal, process, location (the
    /// process must have a driver of the signal).
    drv_checks: Vec<(usize, usize, Loc)>,
    /// Lowering `'driving_value`: this signal reads this process's driver.
    read_drv: Option<(usize, usize)>,
    /// Signals forced or released (`elab::force`).
    forced: BTreeSet<usize>,
    /// Procedures lowered per calling process and signal actuals.
    specs: Vec<elab::Spec>,
    spec_keys: HashMap<String, usize>,
    spec_todo: Vec<usize>,
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
    /// A root instantiated from SV: the module's name (it has ports).
    boundary: Option<String>,
    /// SV values driving VHDL signals, VHDL signals written to SV.
    fins: Vec<mixed::ForeignIn>,
    fouts: Vec<mixed::ForeignOut>,
    /// SV module instances (VHDL components bound to SV modules) and their
    /// wires; a counter naming their nets.
    sv_items: String,
    sv_nets: usize,
    /// Processes with a sensitivity list, lowered as functions.
    fprocs: BTreeSet<usize>,
}

/// Lower the analysed design.
/// Lower the analysed design: the VHDL top level, and a module for each
/// entity instantiated from SystemVerilog (named by `roots`).
pub fn lower(an: &Analysed, roots: &[String]) -> Result<Lowered, Vec<String>> {
    let d = &an.design;
    let mut sv = String::new();
    let mut errors = Vec::new();
    let mut top = None;
    let mut units: Vec<(usize, Option<String>)> = Vec::new();
    if let Some(t) = an.top {
        units.push((t, None));
        top = Some(sv_ident(&d.archs[t].entity));
    }
    for (a, name) in an.roots.iter().zip(roots) {
        units.push((*a, Some(name.clone())));
    }
    for (a, boundary) in units {
        let mut lw = Lw::new(d, boundary);
        // STRING (messages) first.
        lw.arr_type(&Repr::U8);
        let m = lw.module(a);
        if lw.errors.is_empty() {
            sv.push_str(&m);
        } else {
            lw.errors.dedup();
            errors.extend(lw.errors);
        }
    }
    if !errors.is_empty() {
        return Err(errors);
    }
    Ok(Lowered { sv, top })
}

impl<'a> Lw<'a> {
    fn new(d: &'a Design, boundary: Option<String>) -> Self {
        Lw {
            d,
            type_defs: String::new(),
            arr_types: BTreeSet::new(),
            heaps: BTreeSet::new(),
            heap_defs: String::new(),
            textio: false,
            files: false,
            prots: BTreeSet::new(),
            prot_defs: String::new(),
            cur_self: None,
            logic_arrs: BTreeSet::new(),
            rec_types: BTreeMap::new(),
            lits: HashMap::new(),
            lit_items: String::new(),
            dflt: HashMap::new(),
            errors: Vec::new(),
            sigs: Vec::new(),
            sig_map: HashMap::new(),
            insts: Vec::new(),
            arch_objs: Vec::new(),
            inst: 0,
            procs: Vec::new(),
            drivers: BTreeMap::new(),
            links: Vec::new(),
            sites: Vec::new(),
            pkg_objs: BTreeSet::new(),
            read_last: false,
            subs_done: BTreeSet::new(),
            subs_todo: Vec::new(),
            sub_items: String::new(),
            cur_proc: None,
            imps: Vec::new(),
            imp_keys: HashMap::new(),
            imp_refs: Vec::new(),
            need_lact: BTreeSet::new(),
            drv_checks: Vec::new(),
            read_drv: None,
            forced: BTreeSet::new(),
            specs: Vec::new(),
            spec_keys: HashMap::new(),
            spec_todo: Vec::new(),
            tmp: 0,
            loops: Vec::new(),
            loop_flags: BTreeSet::new(),
            pre_stmts: Vec::new(),
            temps: Vec::new(),
            boundary,
            fins: Vec::new(),
            fouts: Vec::new(),
            sv_items: String::new(),
            sv_nets: 0,
            fprocs: BTreeSet::new(),
        }
    }
}

/// The SV name of a VHDL object on the language boundary (a port or a
/// mirrored signal): escaped when it is an SV keyword.
fn port_ident(s: &str) -> String {
    let id = sv_ident(s);
    if crate::sv_parser::lexer::token::keyword(&id).is_some() {
        format!("\\{} ", id)
    } else {
        id
    }
}

pub(super) fn sv_ident(s: &str) -> String {
    s.chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect()
}

pub(super) fn sv_string(s: &str) -> String {
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
                // A multi-dimensional array is an array (first dimension)
                // of arrays of the remaining dimensions.
                let er = self.repr(*elem, loc);
                let logic = self.d.is_bit_or_bool(*elem);
                let mut r = er;
                for k in (0..index.len()).rev() {
                    let name = self.arr_type(&r);
                    if k == index.len() - 1 && logic {
                        self.logic_arrs.insert(name.clone());
                    }
                    r = Repr::Arr(name, Box::new(r));
                }
                r
            }
            // An access value: a handle into the designated type's heap (0:
            // null, §5.4).
            TypeKind::Access(_) => Repr::I64,
            // A file object: its handle (files.rs).
            TypeKind::File(_) => Repr::I32,
            // An object of a protected type: a handle (see `prot_new`).
            TypeKind::Protected => Repr::I64,
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
                self.type_defs.push_str(&s);
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

    /// The heap of an access type's designated type (its key).
    fn heap(&mut self, acc: TypeId, loc: &Loc) -> String {
        let des = self.d.designated(acc).unwrap_or(acc);
        let r = self.repr(des, loc);
        let key = r.key();
        if self.heaps.insert(key.clone()) {
            let _ = write!(
                self.heap_defs,
                "  {t} vh_heap_{k}[longint];\n  longint vh_heap_{k}_n;\n  function automatic longint vh_new_{k}({t} v);\n    vh_heap_{k}_n++;\n    vh_heap_{k}[vh_heap_{k}_n] = v;\n    return vh_heap_{k}_n;\n  endfunction\n",
                t = r.sv(),
                k = key
            );
        }
        key
    }

    /// The array struct for elements represented as `er`, defined with its
    /// helpers on first use.
    fn arr_type(&mut self, er: &Repr) -> String {
        let name = format!("vh_a_{}", er.key());
        if self.arr_types.insert(name.clone()) {
            let eq = self.eq_expr(er, "x.d[i]", "y.d[i]");
            let scalar = !matches!(er, Repr::Arr(..) | Repr::Rec(_));
            let t = runtime::ARRAY_TEMPLATE
                .replace("EQ(x.d[i], y.d[i])", &eq)
                .replace(
                    "LT(x.d[i], y.d[i])",
                    if scalar { "x.d[i] < y.d[i]" } else { "0" },
                )
                .replace(
                    "GT(x.d[i], y.d[i])",
                    if scalar { "x.d[i] > y.d[i]" } else { "0" },
                )
                .replace("ARR", &name)
                .replace("ELEM", &er.sv());
            self.type_defs.push_str(&t);
        }
        name
    }

    /// The (left, dir, right) of a constrained array subtype, if static.
    fn static_bounds(&self, t: TypeId) -> Option<(i64, Dir, i64)> {
        let r = self.d.array_index_ranges(t)?;
        let sr = r.first()?.clone()?;
        Some((sr.left.as_i64()?, sr.dir, sr.right.as_i64()?))
    }

    /// The number of dimensions of an array type (0: not an array).
    fn ndims(&self, t: TypeId) -> usize {
        match &self.d.types[self.base(t)].kind {
            TypeKind::Array { index, .. } => index.len(),
            _ => 0,
        }
    }

    /// The static range of dimension `k` of a constrained array subtype.
    fn static_dim(&self, t: TypeId, k: usize) -> Option<StaticRange> {
        self.d.array_index_ranges(t)?.get(k)?.clone()
    }

    /// The bounds (left, right, dn) of dimension `k` of a constrained array
    /// subtype as SV expressions: static, or computed where the subtype is
    /// elaborated (§14.4.2.1).
    fn dim_bounds(&mut self, t: TypeId, k: usize) -> Option<(String, String, String)> {
        let cons = self.d.array_constraint(t)?;
        let hr = cons.get(k)?.clone()?;
        if let Some(sr) = &hr.static_val {
            return Some((
                self.scalar_lit(&sr.left, &Repr::I64),
                self.scalar_lit(&sr.right, &Repr::I64),
                ((sr.dir == Dir::Downto) as u8).to_string(),
            ));
        }
        Some(self.range_parts(&hr))
    }

    /// The array struct of each dimension (outermost first) of an array
    /// type, and the element representation.
    fn arr_levels(&mut self, t: TypeId, loc: &Loc) -> (Vec<String>, Repr) {
        let mut r = self.repr(t, loc);
        let mut levels = Vec::new();
        for _ in 0..self.ndims(t) {
            match r {
                Repr::Arr(n, e) => {
                    levels.push(n);
                    r = *e;
                }
                _ => break,
            }
        }
        (levels, r)
    }

    /// The left bound and direction of dimension `k`'s index subtype.
    fn index_left_dir_k(&self, arr: TypeId, k: usize) -> (i64, bool) {
        if let TypeKind::Array { index, .. } = &self.d.types[self.base(arr)].kind
            && let Some(it) = index.get(k)
            && let Some(sr) = self.d.scalar_range(*it)
        {
            return (sr.left.as_i64().unwrap_or(0), sr.dir == Dir::Downto);
        }
        (0, false)
    }

    /// An SV expression usable as a function argument: an assignment
    /// pattern goes through a temporary.
    fn as_arg(&mut self, x: String, sv_ty: &str) -> String {
        if !x.starts_with("'{") {
            return x;
        }
        self.tmp += 1;
        let n = format!("vh_e{}", self.tmp);
        self.pre_stmts
            .push((n.clone(), sv_ty.to_string(), format!("{} = {};", n, x)));
        n
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
            (Value::Array(av), Repr::Arr(..)) => self.value_arr(av, t, 0, loc),
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

    /// A static array value for dimension `k` of array type `t` (rows of a
    /// multi-dimensional array take the type's bounds of their dimension).
    fn value_arr(&mut self, av: &ArrayValue, t: TypeId, k: usize, loc: &Loc) -> String {
        let (levels, er) = self.arr_levels(t, loc);
        let n = levels.len();
        let (left, dir) = match self.static_dim(t, k) {
            Some(sr) if k > 0 => (sr.left.as_i64().unwrap_or(av.left), sr.dir),
            _ => (av.left, av.dir),
        };
        let name = levels[k].clone();
        let key = format!("{}:{}:{:?}:{:?}", name, left, dir, av.elems);
        if let Some(f) = self.lits.get(&key) {
            return format!("{}()", f);
        }
        let f = format!("vh_lit{}", self.lits.len());
        self.lits.insert(key, f.clone());
        let elem_sv = if k + 1 < n {
            levels[k + 1].clone()
        } else {
            er.sv()
        };
        let elem_t = self.d.element_subtype(t).unwrap_or(t);
        let mut body = String::new();
        let _ = writeln!(
            body,
            "  function automatic {} {}();\n    {} t[];\n    t = new[{}];",
            name,
            f,
            elem_sv,
            av.elems.len()
        );
        for (i, e) in av.elems.iter().enumerate() {
            let ev = match e {
                Value::Array(sub) if k + 1 < n => self.value_arr(sub, t, k + 1, loc),
                _ => self.value(e, elem_t, loc),
            };
            let _ = writeln!(body, "    t[{}] = {};", i, ev);
        }
        let cnt = av.elems.len() as i64;
        let right = match dir {
            Dir::To => left + cnt - 1,
            Dir::Downto => left - cnt + 1,
        };
        let right = if cnt == 0 { av.right } else { right };
        let _ = writeln!(
            body,
            "    return {}_mk({}, {}, {}, t);\n  endfunction",
            name,
            self.scalar_lit(&Value::Int(left), &Repr::I64),
            self.scalar_lit(&Value::Int(right), &Repr::I64),
            (dir == Dir::Downto) as u8
        );
        self.lit_items.push_str(&body);
        format!("{}()", f)
    }

    /// The default (initial) value of type `t` (§14.4.2.5: T'LEFT, element
    /// by element).
    fn default_value(&mut self, t: TypeId, loc: &Loc) -> String {
        if matches!(self.d.types[self.base(t)].kind, TypeKind::Protected) {
            return self.prot_new(self.base(t), loc);
        }
        let r = self.repr(t, loc);
        match &r {
            Repr::Arr(name, _) => {
                let n = self.ndims(t);
                if !(0..n).all(|k| self.static_dim(t, k).is_some()) {
                    // Bounds computed where the object is elaborated.
                    return self.default_arr(t, 0, loc);
                }
                if let Some(f) = self.dflt.get(&t) {
                    return format!("{}()", f);
                }
                let f = format!("vh_dflt{}", t);
                self.dflt.insert(t, f.clone());
                let saved = std::mem::take(&mut self.pre_stmts);
                let v = self.default_arr(t, 0, loc);
                let mut decls = String::new();
                let mut stmts = String::new();
                for (tn, tt, st) in std::mem::replace(&mut self.pre_stmts, saved) {
                    let _ = writeln!(decls, "    {} {};", tt, tn);
                    let _ = writeln!(stmts, "    {}", st);
                }
                let _ = write!(
                    self.lit_items,
                    "  function automatic {} {}();\n{}{}    return {};\n  endfunction\n",
                    name, f, decls, stmts, v
                );
                format!("{}()", f)
            }
            Repr::Rec(_) => {
                let fields = self.d.record_fields(t);
                if fields.is_empty() {
                    return "'{default:0}".into();
                }
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

    /// The default value of dimension `k` onwards of array type `t`.
    fn default_arr(&mut self, t: TypeId, k: usize, loc: &Loc) -> String {
        let (levels, er) = self.arr_levels(t, loc);
        let n = levels.len();
        let (e, e_sv) = if k + 1 < n {
            (self.default_arr(t, k + 1, loc), levels[k + 1].clone())
        } else {
            let elem_t = self.d.element_subtype(t).unwrap_or(t);
            (self.default_value(elem_t, loc), er.sv())
        };
        let e = self.as_arg(e, &e_sv);
        let (l, r, dn) = self
            .dim_bounds(t, k)
            .unwrap_or_else(|| ("64'sd0".into(), "(-64'sd1)".into(), "0".into()));
        format!("{}_fill({}, {}, {}, {})", levels[k], l, r, dn, e)
    }

    // ---- names -----------------------------------------------------------------------

    fn obj_name(&mut self, o: ObjId) -> String {
        // An external name (§8.7): the object it denotes.
        if self.d.externals.contains_key(&o) && self.d.objects[o].kind == ObjKind::Constant {
            let Some((i, x)) = self.resolve_external(self.inst, o) else {
                let loc = self.d.objects[o].loc.clone();
                self.err(
                    &loc,
                    format!("no object at external path '{}'", self.d.objects[o].name),
                );
                return "0".into();
            };
            let saved = std::mem::replace(&mut self.inst, i);
            let n = self.obj_name(x);
            self.inst = saved;
            return n;
        }
        // A variable of a protected type's body: the current object's.
        if self.d.prot_vars.contains_key(&o) {
            let me = self.cur_self.clone().unwrap_or_else(|| "0".into());
            return format!("vh_pv{}[{}]", o, me);
        }
        let info = &self.d.objects[o];
        match info.kind {
            ObjKind::Signal | ObjKind::Port(_) => self.sig_read(o),
            // A signal parameter of a procedure lowered per call: the
            // actual signal.
            ObjKind::Param(ObjClass::Signal, _) if self.lookup_sig(self.inst, o).is_some() => {
                self.sig_read(o)
            }
            ObjKind::Param(..) => format!("p{}_{}", o, sv_ident(&info.name)),
            _ if self.inst == GLOBAL || self.pkg_objs.contains(&o) => {
                format!("vh_o{}_{}", o, sv_ident(&info.name))
            }
            _ => match self.owner_inst(self.inst, o) {
                0 => format!("vh_o{}_{}", o, sv_ident(&info.name)),
                i => format!("vh_o{}_{}_i{}", o, sv_ident(&info.name), i),
            },
        }
    }

    /// Whether a subprogram is declared in a package (lowered once) rather
    /// than in an architecture or process (lowered per instance).
    fn in_package(&self, s: SubId) -> bool {
        let path = &self.d.subprograms[s].path;
        let mut it = path.split('.');
        match (it.next(), it.next()) {
            (Some(l), Some(p)) => self
                .d
                .packages
                .contains_key(&(l.to_string(), p.to_string())),
            _ => false,
        }
    }

    fn sub_name(&self, s: SubId) -> String {
        let n = &self.d.subprograms[s].name;
        let clean: String = n
            .chars()
            .filter(|c| c.is_ascii_alphanumeric() || *c == '_')
            .collect();
        if self.inst == 0 || self.in_package(s) {
            format!("vh_f{}_{}", s, clean)
        } else {
            format!("vh_f{}_{}_i{}", s, clean, self.inst)
        }
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
                let (levels, _) = self.arr_levels(b.ty, &h.loc);
                let mut cur = self.ex(b);
                let (f, l, _) = self.file_line(&h.loc);
                // A call result is evaluated once, through `_at`.
                let call = cur.contains('(');
                for (k, ix) in idx.iter().enumerate() {
                    let i = self.ex(ix);
                    cur = if call {
                        format!(
                            "{}_at({}, {}, {}, {})",
                            levels.get(k).cloned().unwrap_or_default(),
                            cur,
                            i,
                            sv_string(&f),
                            l
                        )
                    } else {
                        format!(
                            "{c}.d[vh_ix({i}, {c}.l, {c}.r, {c}.dn, {f}, {l})]",
                            c = cur,
                            i = i,
                            f = sv_string(&f),
                            l = l
                        )
                    };
                }
                cur
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
                // Built field by field into a temporary (a pattern of
                // struct-valued members is not copied reliably by the
                // simulator).
                let parts: Vec<String> = vals.iter().map(|v| self.ex(v)).collect();
                let t = self.repr(h.ty, &h.loc).sv();
                self.tmp += 1;
                let agg = format!("vh_rag{}", self.tmp);
                let mut body = String::new();
                for (i, p) in parts.iter().enumerate() {
                    let _ = writeln!(body, "{}.f{} = {};", agg, i, p);
                }
                self.pre_stmts.push((agg.clone(), t, body));
                agg
            }
            HExprKind::Attr(name, prefix, param) => self.attr(name, prefix, param.as_deref(), h),
            HExprKind::Deref(p) => {
                let key = self.heap(p.ty, &h.loc);
                let pv = self.ex(p);
                let (f, l, _) = self.file_line(&h.loc);
                format!("vh_heap_{}[vh_nn({}, {}, {})]", key, pv, sv_string(&f), l)
            }
            HExprKind::New(v) => {
                let key = self.heap(h.ty, &h.loc);
                let des = self.d.designated(h.ty).unwrap_or(h.ty);
                let x = match v {
                    Some(v) => {
                        let target = HExpr {
                            kind: HExprKind::Lit(Value::Null),
                            ty: des,
                            loc: v.loc.clone(),
                        };
                        self.store_value_init(&target, v)
                    }
                    None => self.default_value(des, &h.loc),
                };
                let r = self.repr(des, &h.loc);
                let x = self.as_arg(x, &r.sv());
                format!("vh_new_{}({})", key, x)
            }
            HExprKind::NewOf(st) => {
                let key = self.heap(h.ty, &h.loc);
                let x = self.default_value(*st, &h.loc);
                let r = self.repr(*st, &h.loc);
                let x = self.as_arg(x, &r.sv());
                format!("vh_new_{}({})", key, x)
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
        // Closely related arrays (§9.3.6): to a constrained subtype, its
        // bounds (lengths must match); else the operand's.
        if self.ndims(tb) == 1
            && let Some((l, r, dn)) = self.dim_bounds(to, 0)
        {
            let name = self.arr_name(to, loc);
            let (f, line, _) = self.file_line(loc);
            return format!(
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
            Some(Builtin::BitString(w)) => {
                let x = self.ex(&args[0]);
                format!("vh_bvstr({}, {})", x, w)
            }
            Some(Builtin::RisingEdge) | Some(Builtin::FallingEdge) => {
                let a = &args[0];
                let one = matches!(info.builtin, Some(Builtin::RisingEdge));
                let Some(ev) = self.sig_attr(a, "event") else {
                    self.err(&h.loc, "rising_edge/falling_edge needs a signal");
                    return "0".into();
                };
                let v = self.ex(a);
                format!("({} && {} == {})", ev, v, one as u8)
            }
            Some(Builtin::Now) => "longint'($time)".into(),
            Some(Builtin::EndFile) => self.endfile(&args[0]),
            Some(Builtin::Native(n)) if n == "textio.justify" => {
                self.textio = true;
                let a: Vec<String> = args.iter().map(|x| self.ex(x)).collect();
                format!("vh_tio_justify({}, {}, {})", a[0], a[1], a[2])
            }
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
                let params = self.d.subprograms[s].params.clone();
                let mut a = Vec::new();
                for (p, x) in params.iter().zip(args) {
                    a.extend(self.arg_values(*p, x));
                }
                format!("{}({})", self.sub_name(s), a.join(", "))
            }
        }
    }

    fn need_sub(&mut self, s: SubId) {
        let k = (s, if self.in_package(s) { 0 } else { self.inst });
        if !self.subs_done.contains(&k) && !self.subs_todo.contains(&k) {
            self.subs_todo.push(k);
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
        if op.starts_with('?') {
            return self.matching_op(op, pt[0], x, y, &loc);
        }
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
            // BIT/BOOLEAN `and`, `or`, `nand`, `nor` evaluate the right
            // operand only when needed (§9.2.2).
            "and" => format!("(({}) && ({}))", x, y),
            "or" => format!("(({}) || ({}))", x, y),
            "xor" => format!("(({}) ^ ({}))", x, y),
            "nand" => format!("!(({}) && ({}))", x, y),
            "nor" => format!("!(({}) || ({}))", x, y),
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

    /// The matching relational operators (§9.2.3) on BIT, STD_ULOGIC and
    /// their one-dimensional arrays (`?=`, `?/=` only).
    fn matching_op(&mut self, op: &str, t: TypeId, x: &str, y: &str, loc: &Loc) -> String {
        let ul = self.d.std.std_ulogic;
        let is_arr = self.ndims(t) == 1;
        let et = if is_arr {
            self.d.element_subtype(t).unwrap_or(t)
        } else {
            t
        };
        let std_ul = ul.is_some_and(|u| self.base(et) == u);
        let (f, l, _) = self.file_line(loc);
        if is_arr {
            let n = self.arr_name(t, loc);
            let eq = if std_ul {
                format!("vh_ul_meq_arr({}, {}, {}, {})", x, y, sv_string(&f), l)
            } else {
                format!("vh_bit_meq_arr({}, {}, {}, {})", x, y, sv_string(&f), l)
            };
            let _ = n;
            return match (op, std_ul) {
                ("?=", _) => eq,
                (_, true) => format!("vh_ul_not({})", eq),
                _ => format!("!{}", eq),
            };
        }
        if std_ul {
            return match op {
                "?=" => format!("vh_ul_meq({}, {})", x, y),
                "?/=" => format!("vh_ul_not(vh_ul_meq({}, {}))", x, y),
                "?<" => format!("vh_ul_mlt({}, {})", x, y),
                "?<=" => format!("vh_ul_not(vh_ul_mlt({}, {}))", y, x),
                "?>" => format!("vh_ul_mlt({}, {})", y, x),
                _ => format!("vh_ul_not(vh_ul_mlt({}, {}))", x, y),
            };
        }
        let cmp = match op {
            "?=" => "==",
            "?/=" => "!=",
            "?<" => "<",
            "?<=" => "<=",
            "?>" => ">",
            _ => ">=",
        };
        format!("(({}) {} ({}))", x, cmp, y)
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
    /// The text of a scalar value: as 'IMAGE (`quote`), or as TO_STRING,
    /// which gives a character literal without its quotes (§5.7).
    fn image(&mut self, x: &HExpr, t: TypeId, quote: bool) -> String {
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
                let unquote = !quote && lits.iter().any(|l| l.starts_with('\''));
                let f = format!("vh_img{}{}", if unquote { "s" } else { "" }, b);
                if !self.lits.contains_key(&f) {
                    let mut s = format!(
                        "  function automatic string {}(int unsigned p);\n    case (p)\n",
                        f
                    );
                    for (i, l) in lits.iter().enumerate() {
                        let l = match l.strip_prefix('\'').and_then(|x| x.strip_suffix('\'')) {
                            Some(c) if unquote => c,
                            _ => l.as_str(),
                        };
                        let _ = writeln!(s, "      {}: return {};", i, sv_string(l));
                    }
                    s.push_str("      default: return \"\";\n    endcase\n  endfunction\n");
                    self.lit_items.push_str(&s);
                    self.lits.insert(f.clone(), f.clone());
                }
                format!("vh_str({}({}))", f, v)
            }
            TypeKind::Array { elem, .. } => {
                // TO_STRING of an array of a character enumeration type
                // (§5.7): its elements' characters.
                let eb = self.base(elem);
                if eb == self.d.std.character {
                    return v;
                }
                let TypeKind::Enum(lits) = self.d.types[eb].kind.clone() else {
                    self.err(&x.loc, "TO_STRING of this array type is not supported yet");
                    return "vh_str(\"\")".into();
                };
                let name = self.arr_name(t, &x.loc);
                let f = format!("vh_tostr{}", eb);
                if !self.lits.contains_key(&f) {
                    let mut s = format!(
                        "  function automatic vh_a_u8 {}({} a);\n    byte unsigned t[];\n    t = new[a.d.size()];\n    foreach (t[i])\n      case (a.d[i])\n",
                        f, name
                    );
                    for (i, l) in lits.iter().enumerate() {
                        let c = l.as_bytes().get(1).copied().unwrap_or(b'?');
                        let _ = writeln!(s, "        {}: t[i] = {};", i, c);
                    }
                    s.push_str("        default: t[i] = 0;\n      endcase\n    return vh_a_u8_from(1, 0, t);\n  endfunction\n");
                    self.lit_items.push_str(&s);
                    self.lits.insert(f.clone(), f.clone());
                }
                format!("{}({})", f, v)
            }
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
                if matches!(
                    name,
                    "event" | "active" | "last_value" | "last_event" | "last_active"
                ) && self.d.is_signal_expr(x)
                    && let Some(v) = self.sig_attr(x, name)
                {
                    return v;
                }
                if elab::is_implicit(name) && self.d.is_signal_expr(x) {
                    let Some(r) = self.implicit_sig(name, x, param, h.ty, &h.loc) else {
                        return "0".into();
                    };
                    self.imp_refs.push(r);
                    return if self.read_last {
                        format!("vh_s{}_last", r)
                    } else {
                        format!("vh_s{}", r)
                    };
                }
                if matches!(name, "driving" | "driving_value") && self.d.is_signal_expr(x) {
                    return self.driving(name, x, &h.loc);
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
        self.array_agg_at(items, h.ty, 0, &h.loc)
    }

    /// The aggregate of dimension `k` of array type `t` (`k > 0`: a
    /// sub-aggregate of a multi-dimensional aggregate, §9.3.3.3).
    fn array_agg_at(
        &mut self,
        items: &[(Vec<HChoice>, HExpr)],
        t: TypeId,
        k: usize,
        loc: &Loc,
    ) -> String {
        let (levels, er) = self.arr_levels(t, loc);
        let n = levels.len();
        if k >= n {
            return "'{default:0}".into();
        }
        let name = levels[k].clone();
        let elem_sv = if k + 1 < n {
            levels[k + 1].clone()
        } else {
            er.sv()
        };
        let (f, line, _) = self.file_line(loc);
        self.tmp += 1;
        let agg = format!("vh_agg{}", self.tmp);
        let tv = format!("{}_t", agg);
        let setv = format!("{}_set", agg);
        let (lv, rv, dnv) = (
            format!("{}_l", agg),
            format!("{}_r", agg),
            format!("{}_dn", agg),
        );
        let positional = items.iter().all(|(c, _)| c.is_empty());
        let bounds = self.dim_bounds(t, k);
        let mut body = String::new();
        let mut decls = vec![
            (format!("{}[]", tv), elem_sv.clone()),
            (lv.clone(), "longint".to_string()),
            (rv.clone(), "longint".to_string()),
            (dnv.clone(), "bit".to_string()),
        ];
        // An element: a sub-aggregate of the next dimension, or a value.
        let elem = |lw: &mut Self, v: &HExpr| -> String {
            if k + 1 < n {
                if let HExprKind::ArrayAgg(sub) = &v.kind {
                    return lw.array_agg_at(sub, t, k + 1, &v.loc);
                }
                let x = lw.ex(v);
                if let Some((l, r, dn)) = lw.dim_bounds(t, k + 1) {
                    return format!(
                        "{}_rb({}, {}, {}, {}, {}, {})",
                        levels[k + 1],
                        x,
                        l,
                        r,
                        dn,
                        sv_string(&f),
                        line
                    );
                }
                return x;
            }
            lw.ex(v)
        };
        if positional {
            // The context's bounds when constrained, else from the index
            // subtype's left bound and direction (§9.3.3.3).
            let (l, dn) = match &bounds {
                Some((l, _, dn)) => (l.clone(), dn.clone()),
                None => {
                    let (il, idn) = self.index_left_dir_k(t, k);
                    (
                        self.scalar_lit(&Value::Int(il), &Repr::I64),
                        (idn as u8).to_string(),
                    )
                }
            };
            let _ = writeln!(body, "{} = new[{}];", tv, items.len());
            for (i, (_, v)) in items.iter().enumerate() {
                let x = elem(self, v);
                let _ = writeln!(body, "{}[{}] = {};", tv, i, x);
            }
            let _ = writeln!(
                body,
                "{} = {}; {} = {}; {} = {} ? {} - {} : {} + {};",
                lv,
                l,
                dnv,
                dn,
                rv,
                dnv,
                lv,
                items.len() as i64 - 1,
                lv,
                items.len() as i64 - 1
            );
        } else {
            // Named/others: the bounds come from the subtype; without one,
            // from the smallest and largest choices in the index subtype's
            // direction (§9.3.3.3).
            let has_others = items
                .iter()
                .any(|(c, _)| c.iter().any(|x| matches!(x, HChoice::Others)));
            let bounds = match bounds {
                Some(b) => Some(b),
                None if !has_others && items.iter().all(|(c, _)| !c.is_empty()) => {
                    let (lo, hi) = (format!("{}_lo", agg), format!("{}_hi", agg));
                    decls.push((lo.clone(), "longint".into()));
                    decls.push((hi.clone(), "longint".into()));
                    let mut first = true;
                    for (choices, _) in items {
                        for c in choices {
                            let (a, b) = match c {
                                HChoice::Expr(e) => {
                                    let x = self.ex(e);
                                    (x.clone(), x)
                                }
                                HChoice::Range(hr) => {
                                    let (a, b, dn) = self.range_parts(hr);
                                    (
                                        format!("(({dn}) ? ({b}) : ({a}))", dn = dn, a = a, b = b),
                                        format!("(({dn}) ? ({a}) : ({b}))", dn = dn, a = a, b = b),
                                    )
                                }
                                HChoice::Others => continue,
                            };
                            if first {
                                let _ = writeln!(body, "{} = {}; {} = {};", lo, a, hi, b);
                                first = false;
                            } else {
                                let _ = writeln!(
                                    body,
                                    "if ({a} < {lo}) {lo} = {a}; if ({b} > {hi}) {hi} = {b};",
                                    a = a,
                                    b = b,
                                    lo = lo,
                                    hi = hi
                                );
                            }
                        }
                    }
                    let (_, idn) = self.index_left_dir_k(t, k);
                    Some(if idn {
                        (hi, lo, "1".to_string())
                    } else {
                        (lo, hi, "0".to_string())
                    })
                }
                None => None,
            };
            let Some((l, r, dn)) = bounds else {
                self.err(
                    loc,
                    "an aggregate with choices needs a constrained type here",
                );
                return "'{default:0}".into();
            };
            decls.push((format!("{}[]", setv), "bit".into()));
            let _ = writeln!(body, "{} = {}; {} = {}; {} = {};", lv, l, rv, r, dnv, dn);
            let _ = writeln!(body, "{} = new[vh_len({}, {}, {})];", tv, lv, rv, dnv);
            let _ = writeln!(body, "{} = new[{}.size()];", setv, tv);
            let off = |i: &str| {
                format!(
                    "({dn} ? {l} - ({i}) : ({i}) - {l})",
                    dn = dnv,
                    l = lv,
                    i = i
                )
            };
            let mut pos = 0i64;
            for (choices, v) in items {
                let x = elem(self, v);
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
                            let o = off(&i);
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
                            let o = off("k");
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
        }
        let _ = writeln!(
            body,
            "{} = {}_mk({}, {}, {}, {});",
            agg, name, lv, rv, dnv, tv
        );
        // Declarations go to the enclosing scope; the statements run first.
        for (n, ty) in decls {
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
                let mut cur = self.ex(b);
                for ix in idx {
                    let i = self.ex(ix);
                    cur = format!(
                        "{c}.d[vh_ix({i}, {c}.l, {c}.r, {c}.dn, {f}, {l})]",
                        c = cur,
                        i = i,
                        f = sv_string(&f),
                        l = l
                    );
                }
                format!("{}{} = {};\n", pad, cur, value)
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
            Repr::Rec(_) => self.rec_conv(t, x, &v.loc),
            _ => x,
        }
    }

    /// A record value converted to record subtype `t` (§14.7.3.1): each
    /// array element takes the bounds of its constrained element subtype.
    fn rec_conv(&mut self, t: TypeId, x: String, loc: &Loc) -> String {
        let fields = self.d.record_fields(t);
        let mut body = String::new();
        let mut name = String::new();
        let (f, l, _) = self.file_line(loc);
        for (k, (_, ft)) in fields.iter().enumerate() {
            let Repr::Arr(an, _) = self.repr(*ft, loc) else {
                continue;
            };
            if self.ndims(*ft) != 1 {
                continue;
            }
            let Some((bl, br, bdn)) = self.dim_bounds(*ft, 0) else {
                continue;
            };
            if name.is_empty() {
                self.tmp += 1;
                name = format!("vh_rcv{}", self.tmp);
                let _ = writeln!(body, "{} = {};", name, x);
            }
            let _ = writeln!(
                body,
                "{n}.f{k} = {an}_rb({n}.f{k}, {bl}, {br}, {bdn}, {f}, {l});",
                n = name,
                k = k,
                an = an,
                bl = bl,
                br = br,
                bdn = bdn,
                f = sv_string(&f),
                l = l
            );
        }
        if name.is_empty() {
            return x;
        }
        let ts = self.repr(t, loc).sv();
        self.pre_stmts.push((name.clone(), ts, body));
        name
    }

    fn stmt(&mut self, s: &HStmt, ind: usize) -> String {
        let pad = " ".repeat(ind);
        match &s.kind {
            HStmtKind::Null => String::new(),
            HStmtKind::VarAssign { target, value } => {
                let v = self.store_value(target, value);
                self.assign_to(target, v, ind)
            }
            HStmtKind::Force { target, value } => self.force(target, value.as_ref(), ind),
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

    fn proc_call(&mut self, sub: SubId, args: &[HExpr], ind: usize, loc: &Loc) -> String {
        let pad = " ".repeat(ind);
        let info = self.d.subprograms[sub].clone();
        match info.builtin.clone() {
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
                n if n.starts_with("textio.") => {
                    self.textio_call(&n["textio.".len()..], &info, args, ind, loc)
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
            Some(
                b @ (Builtin::FileOpen
                | Builtin::FileClose
                | Builtin::Read
                | Builtin::Write
                | Builtin::Flush),
            ) => self.file_call(&b, args, ind, loc),
            Some(Builtin::Deallocate) => {
                let key = self.heap(args[0].ty, loc);
                let p = self.ex(&args[0]);
                format!(
                    "{pad}begin if ({p} != 0) vh_heap_{k}.delete({p}); {p} = 0; end\n",
                    pad = pad,
                    p = p,
                    k = key
                )
            }
            Some(_) => {
                self.err(
                    loc,
                    format!("procedure '{}' is not supported yet", info.name),
                );
                String::new()
            }
            None if self.needs_spec(sub) => self.spec_call(sub, args, ind, loc),
            None => {
                self.need_sub(sub);
                let mut a = Vec::new();
                let (mut before, mut after) = (String::new(), String::new());
                for (p, x) in info.params.iter().zip(args) {
                    let writes = matches!(
                        self.d.objects[*p].kind,
                        ObjKind::Param(ObjClass::Variable, Mode::Out | Mode::InOut)
                    );
                    if writes && matches!(x.kind, HExprKind::Slice(..)) {
                        // A slice actual of an out/inout parameter: through
                        // a temporary stored back into the slice after the
                        // call (§4.2.2.2).
                        let r = self.repr(x.ty, loc).sv();
                        self.tmp += 1;
                        let t = format!("vh_sa{}", self.tmp);
                        self.temps.push((t.clone(), r));
                        let v = self.ex(x);
                        let _ = writeln!(before, "{}{} = {};", pad, t, v);
                        after.push_str(&self.assign_to(x, t.clone(), ind));
                        a.push(t);
                    } else {
                        a.extend(self.arg_values(*p, x));
                    }
                }
                format!(
                    "{}{}{}({});\n{}",
                    before,
                    pad,
                    self.sub_name(sub),
                    a.join(", "),
                    after
                )
            }
        }
    }

    /// Whether a procedure (transitively) waits, and whether it
    /// (transitively) assigns signals.
    fn sub_effects(&self, s: SubId) -> (bool, bool) {
        fn walk(d: &Design, stmts: &[HStmt], seen: &mut BTreeSet<SubId>, fx: &mut (bool, bool)) {
            for s in stmts {
                match &s.kind {
                    HStmtKind::Wait { .. } => fx.0 = true,
                    HStmtKind::SignalAssign { .. } => fx.1 = true,
                    HStmtKind::If(b, e) => {
                        for (_, x) in b {
                            walk(d, x, seen, fx);
                        }
                        if let Some(x) = e {
                            walk(d, x, seen, fx);
                        }
                    }
                    HStmtKind::Case { alts, .. } => {
                        for (_, x) in alts {
                            walk(d, x, seen, fx);
                        }
                    }
                    HStmtKind::Loop { body, .. } => walk(d, body, seen, fx),
                    HStmtKind::Call(c, _) => {
                        if seen.insert(*c)
                            && let Some(b) = &d.subprograms[*c].body
                        {
                            walk(d, &b.stmts, seen, fx);
                        }
                    }
                    _ => {}
                }
            }
        }
        let mut fx = (false, false);
        let mut seen = BTreeSet::from([s]);
        if let Some(b) = &self.d.subprograms[s].body {
            walk(self.d, &b.stmts, &mut seen, &mut fx);
        }
        fx
    }

    fn sub_waits(&self, s: SubId) -> bool {
        self.sub_effects(s).0
    }

    /// Whether a procedure is lowered per calling process (`elab::Spec`):
    /// it waits, assigns signals or has signal parameters.
    fn needs_spec(&self, s: SubId) -> bool {
        let info = &self.d.subprograms[s];
        if info.is_function || info.body.is_none() {
            return false;
        }
        let (w, a) = self.sub_effects(s);
        w || a
            || info
                .params
                .iter()
                .any(|p| matches!(self.d.objects[*p].kind, ObjKind::Param(ObjClass::Signal, _)))
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
        // A method: its object is the first parameter.
        let me = if self.d.method_of.contains_key(&s) {
            Some(self.obj_name(info.params[0]))
        } else {
            None
        };
        let saved_self = std::mem::replace(&mut self.cur_self, me);
        let mut params = Vec::new();
        for p in &info.params {
            params.extend(self.param_decls(*p, &loc));
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
            if matches!(o.kind, ObjKind::File) {
                let open = self.file_decl_open(*l, 4);
                inits.push_str(&open);
            }
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
        self.cur_self = saved_self;
    }

    /// A new object of protected type `t` (§5.6.2): the next handle, with
    /// the body's variables at their initial values. Returns the call.
    fn prot_new(&mut self, t: TypeId, loc: &Loc) -> String {
        let f = format!("vh_pnew{}", t);
        if self.prots.contains(&t) {
            return format!("{}()", f);
        }
        self.prots.insert(t);
        let Some(info) = self.d.protected.get(&t).cloned() else {
            return "0".into();
        };
        if !info.has_body {
            self.err(
                loc,
                format!("protected type '{}' has no body", self.d.types[t].name),
            );
        }
        let saved_temps = std::mem::take(&mut self.temps);
        let saved_pre = std::mem::take(&mut self.pre_stmts);
        let saved_self = self.cur_self.replace("vh_pself".into());
        let mut decls = String::new();
        let mut inits = String::new();
        for v in &info.vars {
            let o = self.d.objects[*v].clone();
            let r = self.repr(o.ty, &o.loc);
            let _ = writeln!(decls, "  {} vh_pv{}[longint];", r.sv(), v);
            let val = match &o.init {
                Some(i) => {
                    let target = HExpr {
                        kind: HExprKind::Obj(*v),
                        ty: o.ty,
                        loc: o.loc.clone(),
                    };
                    self.store_value_init(&target, i)
                }
                None => self.default_value(o.ty, &o.loc),
            };
            let pre = self.flush_pre(4);
            inits.push_str(&pre);
            let _ = writeln!(inits, "    vh_pv{}[vh_pself] = {};", v, val);
        }
        let mut temps = String::new();
        for (n, ty) in std::mem::take(&mut self.temps) {
            let _ = writeln!(temps, "    {} {};", ty, n);
        }
        self.temps = saved_temps;
        self.pre_stmts = saved_pre;
        self.cur_self = saved_self;
        let _ = write!(
            self.prot_defs,
            "  longint vh_pt{t}_n;\n{decls}  function automatic longint {f}();\n    longint vh_pself;\n{temps}    vh_pt{t}_n++;\n    vh_pself = vh_pt{t}_n;\n{inits}    return vh_pself;\n  endfunction\n",
            t = t,
            decls = decls,
            f = f,
            temps = temps,
            inits = inits
        );
        format!("{}()", f)
    }

    fn store_value_init(&mut self, target: &HExpr, v: &HExpr) -> String {
        // An object's initial value: an array takes its declared bounds when
        // the subtype is constrained, else the value's own.
        if let Repr::Arr(name, _) = self.repr(target.ty, &target.loc)
            && self.ndims(target.ty) == 1
            && let Some((bl, br, bdn)) = self.dim_bounds(target.ty, 0)
        {
            let x = self.ex(v);
            let (f, l, _) = self.file_line(&v.loc);
            return format!(
                "{}_rb({}, {}, {}, {}, {}, {})",
                name,
                x,
                bl,
                br,
                bdn,
                sv_string(&f),
                l
            );
        }
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
        if let Repr::Rec(_) = self.repr(target.ty, &target.loc) {
            return self.rec_conv(target.ty, x, &v.loc);
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

    /// The SV element type of an array struct (from its name).
    fn arr_elem_sv(&self, name: &str) -> String {
        match &name["vh_a_".len()..] {
            "u8" => "byte unsigned".into(),
            "u32" => "int unsigned".into(),
            "i32" => "int".into(),
            "i64" => "longint".into(),
            "r" => "real".into(),
            other => other.to_string(),
        }
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
