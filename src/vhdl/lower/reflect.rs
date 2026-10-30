//! STD.REFLECTION (VHDL-2019 §16.?, the REFLECTION package): mirrors of
//! subtypes and values.
//!
//! A mirror (an access value of a mirror protected type) is an id into the
//! SV tables of `RUNTIME`; the conversions between a mirror and its class's
//! mirror (`to_enumeration`, `to_value_mirror`, ...) keep the id. `T'REFLECT`
//! calls `vh_rfs<T>()`, which makes T's subtype mirror once; `x'REFLECT`
//! calls `vh_rfv<T>(x)`, which records the value (a composite's elements
//! recursively, an access value's designated object eagerly). The methods
//! of the mirrors are natives (`reflection.<type>.<method>`) reading the
//! tables. Names are upper case and enumeration literal and record element
//! indices start at 0, physical unit indices at 1 (as in nvc).
//!
//! Per id: the class (TYPE_CLASS position), a name (a subtype's simple
//! name, a value's image), and lists of strings (enumeration literals,
//! record element names, unit names) and numbers (record element
//! subtypes/values, unit scales, array dimensions and elements). A value
//! has its subtype (`st`); a scalar subtype its bounds.

use std::fmt::Write as _;

use super::{Lw, sv_string};
use crate::vhdl::ast::Dir;
use crate::vhdl::sema::hir::*;

const RUNTIME: &str = r#"
  // ---- STD.REFLECTION (VHDL-2019): mirrors are ids into these tables.
  longint vh_rf_n;
  byte unsigned vh_rf_cls[longint];
  string vh_rf_name[longint];
  longint vh_rf_st[longint];
  longint vh_rf_iv[longint];
  real vh_rf_rv[longint];
  longint vh_rf_l[longint];
  longint vh_rf_r[longint];
  real vh_rf_rl[longint];
  real vh_rf_rr[longint];
  bit vh_rf_asc[longint];
  longint vh_rf_e[longint];
  string vh_rf_strs[$];
  longint vh_rf_nums[$];
  longint vh_rf_s0[longint];
  longint vh_rf_sn[longint];
  longint vh_rf_n0[longint];
  longint vh_rf_nn[longint];
  function automatic longint vh_rf_new(byte unsigned cls, string name);
    vh_rf_n++;
    vh_rf_cls[vh_rf_n] = cls;
    vh_rf_name[vh_rf_n] = name;
    vh_rf_asc[vh_rf_n] = 1;
    vh_rf_s0[vh_rf_n] = vh_rf_strs.size();
    vh_rf_sn[vh_rf_n] = 0;
    vh_rf_n0[vh_rf_n] = vh_rf_nums.size();
    vh_rf_nn[vh_rf_n] = 0;
    return vh_rf_n;
  endfunction
  // A value of subtype st, its image name.
  function automatic longint vh_rf_val(longint st, string img);
    longint id;
    id = vh_rf_new(vh_rf_cls[st], img);
    vh_rf_st[id] = st;
    return id;
  endfunction
  // Lists are filled right after vh_rf_new (contiguous in the queues).
  function automatic void vh_rf_str(longint id, string s);
    vh_rf_strs.push_back(s);
    vh_rf_sn[id]++;
  endfunction
  function automatic void vh_rf_num(longint id, longint x);
    vh_rf_nums.push_back(x);
    vh_rf_nn[id]++;
  endfunction
  function automatic string vh_rf_stri(longint id, longint i);
    if (i < 0 || i >= vh_rf_sn[id]) begin
      vh_fatal("index out of the range of the mirror's list");
      return "";
    end
    return vh_rf_strs[vh_rf_s0[id] + i];
  endfunction
  function automatic longint vh_rf_numi(longint id, longint i);
    if (i < 0 || i >= vh_rf_nn[id]) begin
      vh_fatal("index out of the range of the mirror's list");
      return 0;
    end
    return vh_rf_nums[vh_rf_n0[id] + i];
  endfunction
  // The position of a string in a list (case-insensitive when ci), -1.
  function automatic longint vh_rf_find(longint id, string s, bit ci);
    string x, y;
    y = s;
    if (ci) y = y.toupper();
    for (longint i = 0; i < vh_rf_sn[id]; i++) begin
      x = vh_rf_strs[vh_rf_s0[id] + i];
      if (ci) x = x.toupper();
      if (x == y) return i;
    end
    return -1;
  endfunction
  function automatic longint vh_rf_findx(longint id, string s, bit ci, string what);
    longint i;
    i = vh_rf_find(id, s, ci);
    if (i < 0) vh_fatal($sformatf("%s does not denote %s", s, what));
    return i;
  endfunction
  // A one-dimensional array subtype (dimension list: count, then per
  // dimension index subtype, left, right, ascending) with other bounds.
  function automatic longint vh_rf_arrsub(longint st, longint l, longint r, bit dn);
    longint id;
    id = vh_rf_new(vh_rf_cls[st], vh_rf_name[st]);
    vh_rf_e[id] = vh_rf_e[st];
    vh_rf_num(id, 1);
    vh_rf_num(id, vh_rf_numi(st, 1));
    vh_rf_num(id, l);
    vh_rf_num(id, r);
    vh_rf_num(id, !dn);
    return id;
  endfunction
  function automatic longint vh_rf_dim(longint st, longint d, longint k);
    if (d < 1 || d > vh_rf_numi(st, 0)) begin
      vh_fatal("dimension out of range");
      return 0;
    end
    return vh_rf_numi(st, 1 + 4 * (d - 1) + k);
  endfunction
  function automatic longint vh_rf_dimlen(longint st, longint d);
    longint l, r;
    l = vh_rf_dim(st, d, 1);
    r = vh_rf_dim(st, d, 2);
    if (vh_rf_dim(st, d, 3)) return r >= l ? r - l + 1 : 0;
    return l >= r ? l - r + 1 : 0;
  endfunction
  // The element of a one-dimensional array value at index idx.
  function automatic longint vh_rf_elem(longint v, longint idx);
    longint st, l, off;
    st = vh_rf_st[v];
    l = vh_rf_dim(st, 1, 1);
    off = vh_rf_dim(st, 1, 3) ? idx - l : l - idx;
    if (off < 0 || off >= vh_rf_nn[v]) begin
      vh_fatal("index out of the range of the array value mirror");
      return 0;
    end
    return vh_rf_numi(v, off);
  endfunction
  // A scalar value mirror of subtype st (its bounds' mirrors, a literal).
  function automatic longint vh_rf_int(longint st, longint x);
    longint id;
    id = vh_rf_val(st, $sformatf("%0d", x));
    vh_rf_iv[id] = x;
    return id;
  endfunction
  function automatic longint vh_rf_real(longint st, real x);
    longint id;
    id = vh_rf_val(st, $__vh_real_image(x));
    vh_rf_rv[id] = x;
    return id;
  endfunction
  function automatic longint vh_rf_enum(longint st, longint p);
    longint id;
    id = vh_rf_val(st, vh_rf_stri(st, p));
    vh_rf_iv[id] = p;
    return id;
  endfunction
  function automatic longint vh_rf_phys(longint st, longint x);
    longint id;
    string u;
    u = vh_rf_stri(st, 0);
    u = u.tolower();
    id = vh_rf_val(st, $sformatf("%0d %s", x, u));
    vh_rf_iv[id] = x;
    return id;
  endfunction
  // A mirror of the wrong class: an error (§16.2.2).
  function automatic longint vh_rf_as(longint id, byte unsigned cls);
    if (id == 0) begin
      vh_fatal("null access dereference");
      return 0;
    end
    if (vh_rf_cls[id] != cls) vh_fatal("the mirror is not of the requested class");
    return id;
  endfunction
"#;

impl Lw<'_> {
    fn rf_runtime(&mut self) {
        if !self.lits.contains_key("vh_rf_runtime") {
            self.lits.insert("vh_rf_runtime".into(), String::new());
            self.lit_items.push_str(RUNTIME);
        }
    }

    /// The TYPE_CLASS position of a type.
    fn rf_class(&self, t: TypeId) -> u8 {
        match &self.d.types[self.base(t)].kind {
            TypeKind::Enum(_) => 0,
            TypeKind::Integer | TypeKind::UniversalInteger => 1,
            TypeKind::Real | TypeKind::UniversalReal => 2,
            TypeKind::Physical(_) => 3,
            TypeKind::Record(_) => 4,
            TypeKind::Array { .. } => 5,
            TypeKind::Access(_) => 6,
            TypeKind::File(_) => 7,
            _ => 8,
        }
    }

    /// The simple name of a (sub)type: its own, else its base type's.
    fn rf_name(&self, t: TypeId) -> String {
        let mut n = self.d.types[t].name.clone();
        if n.is_empty() {
            n = self.d.types[self.base(t)].name.clone();
        }
        n.to_uppercase()
    }

    /// `vh_rfs<t>`: the function giving the subtype mirror of `t` (made
    /// once; its id is set before its elements' mirrors are made, so a
    /// type that reaches itself through an access type terminates).
    pub(super) fn rf_subtype(&mut self, t: TypeId, _loc: &Loc) -> String {
        self.rf_runtime();
        let f = format!("vh_rfs{}", t);
        if self.lits.contains_key(&f) {
            return f;
        }
        self.lits.insert(f.clone(), f.clone());
        let b = self.base(t);
        let mut body = String::new();
        let lit = |v: &Value| v.as_i64().unwrap_or(0);
        let range = self.d.scalar_range(t);
        let bounds = |body: &mut String, r: &Option<StaticRange>| {
            if let Some(r) = r {
                let _ = writeln!(
                    body,
                    "    vh_rf_l[id] = 64'sd{};\n    vh_rf_r[id] = 64'sd{};\n    vh_rf_asc[id] = {};",
                    lit(&r.left),
                    lit(&r.right),
                    (r.dir == Dir::To) as u8
                );
            }
        };
        match self.d.types[b].kind.clone() {
            TypeKind::Enum(lits) => {
                for l in &lits {
                    let _ = writeln!(body, "    vh_rf_str(id, {});", sv_string(l));
                }
                bounds(&mut body, &range);
            }
            TypeKind::Integer | TypeKind::UniversalInteger => bounds(&mut body, &range),
            TypeKind::Real | TypeKind::UniversalReal => {
                if let Some(r) = &range {
                    let _ = writeln!(
                        body,
                        "    vh_rf_rl[id] = {:?};\n    vh_rf_rr[id] = {:?};\n    vh_rf_asc[id] = {};",
                        r.left.as_real().unwrap_or(0.0),
                        r.right.as_real().unwrap_or(0.0),
                        (r.dir == Dir::To) as u8
                    );
                }
            }
            TypeKind::Physical(units) => {
                for (n, scale) in &units {
                    let _ = writeln!(
                        body,
                        "    vh_rf_str(id, {});\n    vh_rf_num(id, 64'sd{});",
                        sv_string(&n.to_uppercase()),
                        scale
                    );
                }
                bounds(&mut body, &range);
            }
            TypeKind::Record(fields) => {
                // Names first (contiguous), then the element subtypes.
                for (n, _) in &fields {
                    let _ = writeln!(body, "    vh_rf_str(id, {});", sv_string(&n.to_uppercase()));
                }
                let storage = self.field_storage(t);
                let mut subs = Vec::new();
                for st in &storage {
                    subs.push(self.rf_subtype(*st, _loc));
                }
                for s in subs {
                    let _ = writeln!(body, "    vh_rf_num(id, {}());", s);
                }
            }
            TypeKind::Array { index, elem } => {
                let ranges = self.d.array_index_ranges(t);
                let mut dims = String::new();
                let _ = writeln!(dims, "    vh_rf_num(id, {});", index.len());
                for (k, it) in index.iter().enumerate() {
                    let isub = self.rf_subtype(*it, _loc);
                    let r = ranges
                        .as_ref()
                        .and_then(|v| v.get(k).cloned().flatten())
                        .or_else(|| self.d.scalar_range(*it));
                    let (l, rr, asc) = match &r {
                        Some(r) => (lit(&r.left), lit(&r.right), r.dir == Dir::To),
                        None => (0, -1, true),
                    };
                    let _ = writeln!(
                        dims,
                        "    vh_rf_num(id, {}());\n    vh_rf_num(id, 64'sd{});\n    vh_rf_num(id, 64'sd{});\n    vh_rf_num(id, {});",
                        isub, l, rr, asc as u8
                    );
                }
                body.push_str(&dims.replace("64'sd-", "-64'sd"));
                let es = self.rf_subtype(elem, _loc);
                let _ = writeln!(body, "    vh_rf_e[id] = {}();", es);
            }
            TypeKind::Access(d) | TypeKind::File(d) => {
                let ds = self.rf_subtype(d, _loc);
                let _ = writeln!(body, "    vh_rf_e[id] = {}();", ds);
            }
            _ => {}
        }
        let body = body.replace("64'sd-", "-64'sd");
        let _ = write!(
            self.lit_items,
            "  longint {f}_id;\n  function automatic longint {f}();\n    longint id;\n    if ({f}_id != 0) return {f}_id;\n    id = vh_rf_new({cls}, {name});\n    {f}_id = id;\n{body}    return id;\n  endfunction\n",
            f = f,
            cls = self.rf_class(t),
            name = sv_string(&self.rf_name(t)),
            body = body
        );
        f
    }

    /// `vh_rfv<t>(v)`: the function making a value mirror of a value `v` of
    /// type `t` (an array as its struct).
    pub(super) fn rf_value(&mut self, t: TypeId, loc: &Loc) -> String {
        self.rf_runtime();
        let f = format!("vh_rfv{}", t);
        if self.lits.contains_key(&f) {
            return f;
        }
        self.lits.insert(f.clone(), f.clone());
        let st = self.rf_subtype(t, loc);
        let b = self.base(t);
        let arg = if self.ndims(t) >= 1 {
            self.fat_repr(t, loc).sv()
        } else {
            self.repr(t, loc).sv()
        };
        // An element's value: its SV value (an array as its struct).
        let elem_val = |lw: &mut Self, v: String, et: TypeId| -> String {
            let er = lw.repr(et, loc);
            let v = if lw.ndims(et) == 1 {
                let fat = lw.fat_repr(et, loc);
                let bnd = lw.static_bounds(et).map(|b| lw.bounds_sv(b));
                lw.coerce(v, &er, &fat, bnd, loc)
            } else {
                v
            };
            let ef = lw.rf_value(et, loc);
            format!("{}({})", ef, v)
        };
        let body = match self.d.types[b].kind.clone() {
            TypeKind::Enum(_) => format!("    return vh_rf_enum({}(), v);\n", st),
            TypeKind::Integer | TypeKind::UniversalInteger => {
                format!("    return vh_rf_int({}(), v);\n", st)
            }
            TypeKind::Real | TypeKind::UniversalReal => format!("    return vh_rf_real({}(), v);\n", st),
            TypeKind::Physical(_) => format!("    return vh_rf_phys({}(), v);\n", st),
            TypeKind::Record(_) => {
                let storage = self.field_storage(t);
                let mut kids = Vec::new();
                for (i, ft) in storage.iter().enumerate() {
                    kids.push(elem_val(self, format!("v.f{}", i), *ft));
                }
                let mut s = String::from("    longint id;\n    longint k[$];\n");
                for k in &kids {
                    let _ = writeln!(s, "    k.push_back({});", k);
                }
                let _ = writeln!(
                    s,
                    "    id = vh_rf_val({}(), \"\");\n    foreach (k[i]) vh_rf_num(id, k[i]);\n    return id;",
                    st
                );
                s
            }
            TypeKind::Array { index, elem } if index.len() == 1 => {
                let e = elem_val(self, "v.d[i]".into(), elem);
                format!(
                    "    longint id;\n    longint k[$];\n    foreach (v.d[i]) k.push_back({e});\n    id = vh_rf_val(vh_rf_arrsub({st}(), v.l, v.r, v.dn), \"\");\n    foreach (k[i]) vh_rf_num(id, k[i]);\n    return id;\n",
                    e = e,
                    st = st
                )
            }
            TypeKind::Access(d) => {
                let key = self.heap(t, loc);
                let dv = self.d.designated(t).unwrap_or(d);
                let dval = elem_val(self, format!("vh_heap_{}[v]", key), dv);
                format!(
                    "    longint id;\n    id = vh_rf_val({st}(), v == 0 ? \"null\" : \"\");\n    vh_rf_e[id] = v == 0 ? 0 : {dval};\n    return id;\n",
                    st = st,
                    dval = dval
                )
            }
            TypeKind::Array { .. } => {
                self.err(loc, "'reflect of a multi-dimensional array value is not supported yet");
                format!("    return vh_rf_val({}(), \"\");\n", st)
            }
            _ => format!("    return vh_rf_val({}(), \"\");\n", st),
        };
        let _ = write!(
            self.lit_items,
            "  function automatic longint {f}({arg} v);\n{body}  endfunction\n",
            f = f,
            arg = arg,
            body = body
        );
        f
    }

    /// The SV value of `x` for `rf_value`'s function.
    pub(super) fn rf_reflect_value(&mut self, x: &HExpr) -> String {
        let f = self.rf_value(x.ty, &x.loc);
        let v = if self.ndims(x.ty) >= 1 {
            self.ex_fat(x)
        } else {
            self.ex(x)
        };
        format!("{}({})", f, v)
    }

    /// A method of a mirror (`name` is `<protected type>.<method>`): the
    /// object is the first argument (the mirror's access value).
    pub(super) fn rf_method(&mut self, name: &str, args: &[HExpr], h: &HExpr) -> String {
        self.rf_runtime();
        let me = match &args[0].kind {
            HExprKind::Deref(p) => self.ex(p),
            _ => self.ex(&args[0]),
        };
        let (pt, m) = name.split_once('.').unwrap_or((name, ""));
        let class = pt.trim_end_matches("_pt");
        let is_value = class.ends_with("value_mirror");
        let kind = class
            .trim_end_matches("_value_mirror")
            .trim_end_matches("_subtype_mirror");
        let ret_string = self.ndims(h.ty) == 1;
        let s = |lw: &mut Self, i: usize| -> String {
            let a = lw.ex_fat(&args[i]);
            format!("vh_sv({})", a)
        };
        let a = |lw: &mut Self, i: usize| -> String { lw.ex(&args[i]) };
        let string_arg = args.len() > 1 && self.ndims(args[1].ty) == 1;
        let cls = |k: &str| -> u8 {
            match k {
                "enumeration" => 0,
                "integer" => 1,
                "floating" => 2,
                "physical" => 3,
                "record" => 4,
                "array" => 5,
                "access" => 6,
                "file" => 7,
                _ => 8,
            }
        };
        match (kind, is_value, m) {
            // Both generic mirrors.
            (_, _, "get_type_class") | (_, _, "get_value_class") => format!("vh_rf_cls[{}]", me),
            (_, _, "to_value_mirror") | (_, _, "to_subtype_mirror") => me.clone(),
            (_, true, "get_subtype_mirror") => format!("vh_rf_st[{}]", me),
            (_, _, to) if to.starts_with("to_") => {
                format!("vh_rf_as({}, {})", me, cls(&to[3..]))
            }
            (_, false, "simple_name") => format!("vh_str(vh_rf_name[{}])", me),
            (_, true, "image") => format!("vh_str(vh_rf_name[{}])", me),
            // Scalar values.
            ("enumeration", true, "pos") | ("integer", true, "value") | ("physical", true, "value") => {
                format!("vh_rf_iv[{}]", me)
            }
            ("floating", true, "value") => format!("vh_rf_rv[{}]", me),
            ("physical", true, "unit_index") => "64'sd1".into(),
            // Scalar subtypes.
            ("enumeration", false, "enumeration_literal") if string_arg => {
                let n = s(self, 1);
                format!(
                    "vh_rf_enum({me}, vh_rf_findx({me}, {n}, 0, \"an enumeration literal of the type\"))",
                    me = me,
                    n = n
                )
            }
            ("enumeration", false, "enumeration_literal") => {
                let i = a(self, 1);
                format!("vh_rf_enum({}, {})", me, i)
            }
            ("enumeration", false, b @ ("left" | "right" | "low" | "high")) => {
                let x = match b {
                    "left" => format!("vh_rf_l[{}]", me),
                    "right" => format!("vh_rf_r[{}]", me),
                    "low" => format!("(vh_rf_asc[{me}] ? vh_rf_l[{me}] : vh_rf_r[{me}])", me = me),
                    _ => format!("(vh_rf_asc[{me}] ? vh_rf_r[{me}] : vh_rf_l[{me}])", me = me),
                };
                format!("vh_rf_enum({}, {})", me, x)
            }
            ("integer" | "physical", false, b @ ("left" | "right" | "low" | "high")) => {
                let x = match b {
                    "left" => format!("vh_rf_l[{}]", me),
                    "right" => format!("vh_rf_r[{}]", me),
                    "low" => format!("(vh_rf_asc[{me}] ? vh_rf_l[{me}] : vh_rf_r[{me}])", me = me),
                    _ => format!("(vh_rf_asc[{me}] ? vh_rf_r[{me}] : vh_rf_l[{me}])", me = me),
                };
                let f = if kind == "integer" { "vh_rf_int" } else { "vh_rf_phys" };
                format!("{}({}, {})", f, me, x)
            }
            ("floating", false, b @ ("left" | "right" | "low" | "high")) => {
                let x = match b {
                    "left" => format!("vh_rf_rl[{}]", me),
                    "right" => format!("vh_rf_rr[{}]", me),
                    "low" => format!("(vh_rf_asc[{me}] ? vh_rf_rl[{me}] : vh_rf_rr[{me}])", me = me),
                    _ => format!("(vh_rf_asc[{me}] ? vh_rf_rr[{me}] : vh_rf_rl[{me}])", me = me),
                };
                format!("vh_rf_real({}, {})", me, x)
            }
            ("enumeration" | "integer" | "physical", false, "length") => format!(
                "(vh_rf_asc[{me}] ? (vh_rf_r[{me}] >= vh_rf_l[{me}] ? vh_rf_r[{me}] - vh_rf_l[{me}] + 1 : 0) : (vh_rf_l[{me}] >= vh_rf_r[{me}] ? vh_rf_l[{me}] - vh_rf_r[{me}] + 1 : 0))",
                me = me
            ),
            (_, false, "ascending") if args.len() == 1 && kind != "array" => {
                format!("vh_rf_asc[{}]", me)
            }
            // Physical subtypes: units 1-based.
            ("physical", false, "units_length") => format!("vh_rf_sn[{}]", me),
            ("physical", false, "unit_name") => {
                let i = a(self, 1);
                format!("vh_str(vh_rf_stri({}, ({}) - 1))", me, i)
            }
            ("physical", false, "unit_index") => {
                let n = s(self, 1);
                format!("(vh_rf_findx({}, {}, 1, \"a unit of the type\") + 1)", me, n)
            }
            ("physical", false, "scale") if string_arg => {
                let n = s(self, 1);
                format!(
                    "vh_rf_numi({me}, vh_rf_findx({me}, {n}, 1, \"a unit of the type\"))",
                    me = me,
                    n = n
                )
            }
            ("physical", false, "scale") => {
                let i = a(self, 1);
                format!("vh_rf_numi({}, ({}) - 1)", me, i)
            }
            // Records: elements 0-based.
            ("record", false, "length") => format!("vh_rf_sn[{}]", me),
            ("record", false, "element_name") => {
                let i = a(self, 1);
                format!("vh_str(vh_rf_stri({}, {}))", me, i)
            }
            ("record", false, "element_index") => {
                let n = s(self, 1);
                format!("vh_rf_findx({}, {}, 1, \"an element of the record type\")", me, n)
            }
            ("record", false, "element_subtype") if string_arg => {
                let n = s(self, 1);
                format!(
                    "vh_rf_numi({me}, vh_rf_findx({me}, {n}, 1, \"an element of the record type\"))",
                    me = me,
                    n = n
                )
            }
            ("record", false, "element_subtype") => {
                let i = a(self, 1);
                format!("vh_rf_numi({}, {})", me, i)
            }
            ("record", true, "get") if string_arg => {
                let n = s(self, 1);
                format!(
                    "vh_rf_numi({me}, vh_rf_findx(vh_rf_st[{me}], {n}, 1, \"an element of the record type\"))",
                    me = me,
                    n = n
                )
            }
            ("record", true, "get") => {
                let i = a(self, 1);
                format!("vh_rf_numi({}, {})", me, i)
            }
            // Arrays: dimensions 1-based (default 1).
            ("array", false, "dimensions") => format!("vh_rf_numi({}, 0)", me),
            ("array", false, "element_subtype") => format!("vh_rf_e[{}]", me),
            ("array", false, b @ ("index_subtype" | "left" | "right" | "low" | "high" | "length" | "ascending")) => {
                let d = if args.len() > 1 { a(self, 1) } else { "1".into() };
                match b {
                    "index_subtype" => format!("vh_rf_dim({}, {}, 0)", me, d),
                    "left" => format!("vh_rf_dim({}, {}, 1)", me, d),
                    "right" => format!("vh_rf_dim({}, {}, 2)", me, d),
                    "ascending" => format!("vh_rf_dim({}, {}, 3)", me, d),
                    "length" => format!("vh_rf_dimlen({}, {})", me, d),
                    "low" => format!(
                        "(vh_rf_dim({me}, {d}, 3) ? vh_rf_dim({me}, {d}, 1) : vh_rf_dim({me}, {d}, 2))",
                        me = me,
                        d = d
                    ),
                    _ => format!(
                        "(vh_rf_dim({me}, {d}, 3) ? vh_rf_dim({me}, {d}, 2) : vh_rf_dim({me}, {d}, 1))",
                        me = me,
                        d = d
                    ),
                }
            }
            ("array", true, "get") if args.len() == 2 && self.ndims(args[1].ty) == 0 => {
                let i = a(self, 1);
                format!("vh_rf_elem({}, {})", me, i)
            }
            // Access and file values and subtypes.
            ("access", true, "get") => format!("vh_rf_e[{}]", me),
            ("access", true, "is_null") => format!("(vh_rf_e[{}] == 0)", me),
            ("access" | "file", false, "designated_subtype") => format!("vh_rf_e[{}]", me),
            ("file", true, "get_file_logical_name") => "vh_str(\"\")".into(),
            ("file", true, "get_file_open_kind") => "0".into(),
            _ => {
                self.err(
                    &h.loc,
                    format!("'std.reflection.{}' is not supported yet", name),
                );
                if ret_string { "vh_str(\"\")".into() } else { "0".into() }
            }
        }
    }
}
