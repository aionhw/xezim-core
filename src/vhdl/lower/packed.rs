//! Packed arrays: a one-dimensional array with static bounds of an
//! enumeration element (`std_ulogic_vector(7 downto 0)`, `bit_vector(0 to
//! 3)`) is an SV packed vector of `w` bits per element (`Repr::Pk`), which
//! the simulator's compiled tier handles as a scalar, rather than the
//! struct of a dynamic array (`Repr::Arr`) that it interprets. Arrays whose
//! bounds are only known at run time keep the struct, so a value changes
//! representation where it flows between the two (`coerce`): the
//! representation of an expression is `erepr` and its static bounds
//! `shape`. A packed value carries no bounds: they are those of its subtype
//! (object, slice, aggregate), known where it is used.

use std::fmt::Write as _;

use super::elab::{Part, SigRef};
use super::leaves::Sel;
use super::{Lw, MAX_PK_BITS, Repr, sv_string};
use crate::vhdl::ast::{Dir, ObjClass};
use crate::vhdl::sema::hir::*;

/// Static bounds of a one-dimensional array: left, direction, right.
pub(super) type Bounds = (i64, Dir, i64);

pub(super) fn bounds_len(b: Bounds) -> i64 {
    let (l, dir, r) = b;
    match dir {
        Dir::To => r - l + 1,
        Dir::Downto => l - r + 1,
    }
    .max(0)
}

/// The bounds of `n` elements from `l` in direction `dir`.
pub(super) fn bounds_from(l: i64, dir: Dir, n: i64) -> Bounds {
    match dir {
        Dir::To => (l, dir, l + n - 1),
        Dir::Downto => (l, dir, l - n + 1),
    }
}

/// An integer literal as the lowering writes it (`scalar_lit`), as a value.
fn lit_i64(s: &str) -> Option<i64> {
    let t = s.trim();
    if let Some(x) = t.strip_prefix("64'sd") {
        return x.parse().ok();
    }
    if let Some(x) = t.strip_prefix("(-64'sd").and_then(|x| x.strip_suffix(')')) {
        return x.parse::<i64>().ok().map(|v| -v);
    }
    t.parse().ok()
}

impl<'a> Lw<'a> {
    /// The bits of a packed element of enumeration type `elem` (`None`:
    /// arrays of it keep the struct). CHARACTER arrays (STRING) stay
    /// structs: their lengths are mostly dynamic and TEXTIO takes them.
    pub(super) fn pack_elem(&self, elem: TypeId) -> Option<u32> {
        let b = self.base(elem);
        if b == self.d.std.character {
            return None;
        }
        match &self.d.types[b].kind {
            TypeKind::Enum(lits) if lits.len() <= 16 => {
                let n = lits.len().max(2);
                Some((usize::BITS - (n - 1).leading_zeros()).max(1))
            }
            _ => None,
        }
    }

    /// The packed representation of array subtype `t`: static bounds of
    /// one dimension, at least one element, a packable element.
    pub(super) fn pk_of(&self, t: TypeId) -> Option<Repr> {
        let b = self.base(t);
        let TypeKind::Array { index, elem } = &self.d.types[b].kind else {
            return None;
        };
        if index.len() != 1 {
            return None;
        }
        let w = self.pack_elem(*elem)?;
        let n = bounds_len(self.static_bounds(t)?);
        (n >= 1 && n * w as i64 <= MAX_PK_BITS).then_some(Repr::Pk(w, n))
    }

    /// Packed when `n` elements of `w` bits fit.
    fn pk_fits(w: u32, n: i64) -> bool {
        n >= 1 && n * w as i64 <= MAX_PK_BITS
    }

    /// The bounds of array subtype `t`: static, or folding in the active
    /// specialisation (`UNSIGNED(L_LEFT downto 0)` with L_LEFT a constant
    /// of the specialised formals).
    pub(super) fn type_bounds(&mut self, t: TypeId) -> Option<Bounds> {
        if let Some(b) = self.static_bounds(t) {
            return Some(b);
        }
        if self.spec_env.is_none() || self.ndims(t) != 1 {
            return None;
        }
        let cons = self.d.array_constraint(t)?;
        let r = cons.first()?.clone()?;
        self.range_bounds(&r)
    }

    /// `pk_of` with the active specialisation's bounds.
    pub(super) fn pk_of_env(&mut self, t: TypeId) -> Option<Repr> {
        if let Some(r) = self.pk_of(t) {
            return Some(r);
        }
        self.spec_env?;
        let b = self.base(t);
        let TypeKind::Array { index, elem } = &self.d.types[b].kind else {
            return None;
        };
        if index.len() != 1 {
            return None;
        }
        let w = self.pack_elem(*elem)?;
        let n = bounds_len(self.type_bounds(t)?);
        Self::pk_fits(w, n).then_some(Repr::Pk(w, n))
    }

    pub(super) fn bounds_sv(&self, b: Bounds) -> (String, String, String) {
        (
            self.scalar_lit(&Value::Int(b.0), &Repr::I64),
            self.scalar_lit(&Value::Int(b.2), &Repr::I64),
            ((b.1 == Dir::Downto) as u8).to_string(),
        )
    }

    // ---- static bounds of expressions ------------------------------------------

    /// The static bounds of an array-valued expression (`None` when they
    /// are only known at run time).
    pub(super) fn shape(&mut self, h: &HExpr) -> Option<Bounds> {
        match &h.kind {
            HExprKind::Obj(o) => self.obj_bounds(*o),
            HExprKind::Lit(Value::Array(av)) => Some((av.left, av.dir, av.right)),
            HExprKind::Lit(_) => None,
            // A qualified expression keeps its operand's bounds (§9.3.5); a
            // conversion to a constrained subtype takes its bounds (§9.3.6).
            HExprKind::Qualified(x) => self.shape(x).or_else(|| self.type_bounds(h.ty)),
            HExprKind::Convert(x) => {
                if self.constrained_dim0(h.ty) {
                    self.type_bounds(h.ty)
                } else {
                    self.shape(x)
                }
            }
            HExprKind::Slice(_, r) => self.range_bounds(r),
            HExprKind::Call(s, args) => self.call_shape(*s, args, h),
            // The values' bounds, when they all have the same.
            HExprKind::Cond(arms, last) => {
                let b = self.shape(last)?;
                for (_, v) in arms {
                    if self.shape(v) != Some(b) {
                        return None;
                    }
                }
                Some(b)
            }
            HExprKind::ArrayAgg(items) => {
                if let Some(b) = self.type_bounds(h.ty) {
                    return Some(b);
                }
                // Positional: from the index subtype's left bound (§9.3.3.3).
                if items.iter().all(|(c, _)| c.is_empty()) && self.ndims(h.ty) == 1 {
                    let (il, idn) = self.index_left_dir(h.ty);
                    let dir = if idn { Dir::Downto } else { Dir::To };
                    return Some(bounds_from(il, dir, items.len() as i64));
                }
                None
            }
            _ => self.type_bounds(h.ty),
        }
    }

    /// The types of the fields of a record's struct: those of the record
    /// type's declaration (an unconstrained element is a struct of a
    /// dynamic array whatever the constraint of the record subtype, §5.3.3).
    pub(super) fn field_storage(&self, t: TypeId) -> Vec<TypeId> {
        match &self.d.types[self.base(t)].kind {
            TypeKind::Record(fields) => fields.iter().map(|(_, ft)| *ft).collect(),
            _ => Vec::new(),
        }
    }

    /// The type of the storage at a static path from type `t`: record
    /// fields as declared (see `field_storage`), elements by their subtype.
    pub(super) fn path_storage_type(&self, t: TypeId, path: &[Sel]) -> Option<TypeId> {
        let mut cur = t;
        for s in path {
            cur = match s {
                Sel::Field(i) => *self.field_storage(cur).get(*i)?,
                Sel::Elem(_) => self.d.element_subtype(cur)?,
                Sel::Slice(..) => cur,
            };
        }
        Some(cur)
    }

    /// Whether the first dimension of array subtype `t` is constrained
    /// (statically or not).
    pub(super) fn constrained_dim0(&self, t: TypeId) -> bool {
        self.d
            .array_constraint(t)
            .is_some_and(|c| c.first().is_some_and(|r| r.is_some()))
    }

    /// The static bounds of a range.
    pub(super) fn range_bounds(&mut self, r: &HRange) -> Option<Bounds> {
        if let Some(sr) = &r.static_val {
            return Some((sr.left.as_i64()?, sr.dir, sr.right.as_i64()?));
        }
        if let Some((o, dim, rev)) = &r.of_obj {
            let b = if *dim == 0 {
                self.shape(o)?
            } else {
                let sr = self.static_dim(o.ty, *dim)?;
                (sr.left.as_i64()?, sr.dir, sr.right.as_i64()?)
            };
            return Some(if *rev {
                let d = if b.1 == Dir::To { Dir::Downto } else { Dir::To };
                (b.2, d, b.0)
            } else {
                b
            });
        }
        let l = self.eval_env(&r.left)?.as_i64()?;
        let rr = self.eval_env(&r.right)?.as_i64()?;
        Some((l, r.dir, rr))
    }

    /// The bounds of the array a signal or variable object names.
    pub(super) fn obj_bounds(&self, o: ObjId) -> Option<Bounds> {
        if let Some(b) = self.env_bounds(o) {
            return Some(b);
        }
        let info = &self.d.objects[o];
        if self.obj_is_sig(o)
            && let Some(r) = self.lookup_sig(self.inst, o)
        {
            return self.sigref_bounds(&r, info.ty);
        }
        self.static_bounds(info.ty)
    }

    /// Whether object `o` reads a signal of the flattened design (a
    /// signal, a port, or a signal parameter bound to its actual).
    pub(super) fn obj_is_sig(&self, o: ObjId) -> bool {
        match self.d.objects[o].kind {
            ObjKind::Signal | ObjKind::Port(_) => true,
            ObjKind::Param(ObjClass::Signal, _) => self.lookup_sig(self.inst, o).is_some(),
            _ => false,
        }
    }

    /// The bounds of the signal (part) a formal of subtype `formal_ty`
    /// names: the formal's when constrained, else the part's (§6.5.6.3).
    fn sigref_bounds(&self, r: &SigRef, formal_ty: TypeId) -> Option<Bounds> {
        if let Some(b) = self.static_bounds(formal_ty) {
            return Some(b);
        }
        let path: &[Sel] = match &r.part {
            Part::Whole => &[],
            Part::Path(p) => p.as_slice(),
        };
        match path.last() {
            Some(Sel::Slice(off, len)) => {
                let st = self.path_type(self.sigs[r.sig].ty, &path[..path.len() - 1])?;
                let (al, adir, _) = self.static_bounds(st)?;
                let l = match adir {
                    Dir::To => al + off,
                    Dir::Downto => al - off,
                };
                Some(bounds_from(l, adir, *len))
            }
            _ => self.static_bounds(self.path_type(self.sigs[r.sig].ty, path)?),
        }
    }

    /// The static bounds of the result of a call (§9.2.5 for `&`, the
    /// array operand's for the logical operators).
    fn call_shape(&mut self, s: SubId, args: &[HExpr], h: &HExpr) -> Option<Bounds> {
        let info = &self.d.subprograms[s];
        let Some(Builtin::Op(op)) = info.builtin.clone() else {
            // A specialised copy: its result's bounds.
            if info.builtin.is_none()
                && let Some(k) = self.try_specialise(s, args)
                && let Some(b) = self.pspecs[k].ret_bounds
            {
                return Some(b);
            }
            return self.type_bounds(h.ty);
        };
        match op.as_str() {
            "and" | "or" | "nand" | "nor" | "xor" | "xnor" | "not" => {
                let arr = args.iter().find(|a| self.ndims(a.ty) == 1)?.clone();
                self.shape(&arr)
            }
            "&" => {
                let params = info.params.clone();
                let pt: Vec<TypeId> = params.iter().map(|p| self.d.objects[*p].ty).collect();
                let (il, idn) = self.index_left_dir(h.ty);
                let idir = if idn { Dir::Downto } else { Dir::To };
                let n = |lw: &mut Self, x: &HExpr| lw.shape(x).map(bounds_len);
                match (self.ndims(pt[0]) == 1, self.ndims(pt[1]) == 1) {
                    (true, true) => {
                        let sa = self.shape(&args[0])?;
                        let sb = self.shape(&args[1])?;
                        let (na, nb) = (bounds_len(sa), bounds_len(sb));
                        if na + nb == 0 {
                            return None;
                        }
                        let (l, d) = if na == 0 { (sb.0, sb.1) } else { (sa.0, sa.1) };
                        Some(bounds_from(l, d, na + nb))
                    }
                    (true, false) => {
                        let sa = self.shape(&args[0])?;
                        let na = bounds_len(sa);
                        let (l, d) = if na == 0 { (il, idir) } else { (sa.0, sa.1) };
                        Some(bounds_from(l, d, na + 1))
                    }
                    (false, true) => {
                        let nb = n(self, &args[1])?;
                        Some(bounds_from(il, idir, nb + 1))
                    }
                    (false, false) => Some(bounds_from(il, idir, 2)),
                }
            }
            _ => self.type_bounds(h.ty),
        }
    }

    // ---- representation of expressions ---------------------------------------------

    /// The representation of an expression's value: packed when the
    /// lowering produces a packed vector for it.
    pub(super) fn erepr(&mut self, h: &HExpr) -> Repr {
        match &h.kind {
            HExprKind::Obj(o) => {
                if let Some(v) = &self.d.objects[*o].static_val
                    && matches!(self.d.objects[*o].kind, ObjKind::Generic)
                    && matches!(v, Value::Array(_))
                {
                    return self.repr(h.ty, &h.loc);
                }
                self.obj_repr(*o, &h.loc)
            }
            HExprKind::Lit(Value::Array(_)) => self.shape_repr(h),
            HExprKind::Qualified(x) => self.erepr(x),
            HExprKind::Convert(x) => {
                if self.ndims(h.ty) != 1 || self.constrained_dim0(h.ty) {
                    self.repr(h.ty, &h.loc)
                } else {
                    self.erepr(x)
                }
            }
            HExprKind::Slice(b, _) => match self.erepr(b) {
                Repr::Pk(w, _) => match self.shape(h) {
                    Some(sb) if Self::pk_fits(w, bounds_len(sb)) => Repr::Pk(w, bounds_len(sb)),
                    _ => self.fat_repr(h.ty, &h.loc),
                },
                r => r,
            },
            HExprKind::Call(s, args) => self.call_repr(*s, args, h),
            HExprKind::Cond(..) => self.cond_repr(h),
            HExprKind::ArrayAgg(_) => self.shape_repr(h),
            // A field: the struct member's representation.
            HExprKind::Field(b, i) => match self.field_storage(b.ty).get(*i) {
                Some(ft) => self.repr(*ft, &h.loc),
                None => self.repr(h.ty, &h.loc),
            },
            _ => self.repr(h.ty, &h.loc),
        }
    }

    /// Packed when the expression's bounds are static and its element
    /// packs, else the struct of its type.
    pub(super) fn shape_repr(&mut self, h: &HExpr) -> Repr {
        if self.ndims(h.ty) == 1
            && let Some(e) = self.d.element_subtype(h.ty)
            && let Some(w) = self.pack_elem(e)
            && let Some(b) = self.shape(h)
            && Self::pk_fits(w, bounds_len(b))
        {
            return Repr::Pk(w, bounds_len(b));
        }
        self.fat_repr(h.ty, &h.loc)
    }

    /// The representation of a signal or variable object: a signal's is
    /// its signal's (a port shares its actual's signal, a formal
    /// associated with a slice reads that slice).
    pub(super) fn obj_repr(&mut self, o: ObjId, loc: &Loc) -> Repr {
        if let Some(r) = self.env_repr(o, loc) {
            return r;
        }
        let ty = self.d.objects[o].ty;
        if self.obj_is_sig(o)
            && let Some(r) = self.lookup_sig(self.inst, o)
        {
            let sty = self.sigs[r.sig].ty;
            let (path, slice): (&[Sel], Option<i64>) = match &r.part {
                Part::Whole => (&[], None),
                Part::Path(p) => match p.last() {
                    Some(Sel::Slice(_, len)) => (&p[..p.len() - 1], Some(*len)),
                    _ => (p.as_slice(), None),
                },
            };
            if let Some(pt) = self.path_storage_type(sty, path) {
                let r = self.repr(pt, loc);
                return match (slice, r) {
                    (Some(len), Repr::Pk(w, _)) => {
                        if Self::pk_fits(w, len) {
                            Repr::Pk(w, len)
                        } else {
                            self.fat_repr(ty, loc)
                        }
                    }
                    (_, r) => r,
                };
            }
        }
        self.repr(ty, loc)
    }

    fn call_repr(&mut self, s: SubId, args: &[HExpr], h: &HExpr) -> Repr {
        let info = &self.d.subprograms[s];
        match info.builtin.clone() {
            Some(Builtin::Op(op)) => match op.as_str() {
                "and" | "or" | "nand" | "nor" | "xor" | "xnor" | "not" | "&"
                    if self.ndims(h.ty) == 1 =>
                {
                    // Native on packed operands of one length; else the
                    // struct helpers.
                    if op == "&" {
                        return self.shape_repr(h);
                    }
                    let arrs: Vec<Repr> = args
                        .iter()
                        .filter(|a| self.ndims(a.ty) == 1)
                        .collect::<Vec<_>>()
                        .into_iter()
                        .map(|a| self.erepr(a))
                        .collect();
                    match arrs.as_slice() {
                        [Repr::Pk(w, n)] => Repr::Pk(*w, *n),
                        [Repr::Pk(w, n), Repr::Pk(w2, n2)] if w == w2 && n == n2 => {
                            Repr::Pk(*w, *n)
                        }
                        _ => self.fat_repr(h.ty, &h.loc),
                    }
                }
                _ => self.repr(h.ty, &h.loc),
            },
            None => {
                if let Some(k) = self.try_specialise(s, args)
                    && let Some(r) = self.pspecs[k].ret.clone()
                {
                    return r;
                }
                self.repr(h.ty, &h.loc)
            }
            _ => self.repr(h.ty, &h.loc),
        }
    }

    /// The representation of a conditional expression (VHDL-2019): its
    /// values', when they all have the same (and packed ones the same
    /// bounds), else the struct of its type, which every value converts to.
    fn cond_repr(&mut self, h: &HExpr) -> Repr {
        let HExprKind::Cond(arms, last) = &h.kind else {
            return self.repr(h.ty, &h.loc);
        };
        let r0 = self.erepr(last);
        let s0 = self.shape(last);
        for (_, v) in arms {
            let r = self.erepr(v);
            if r != r0 || matches!(r0, Repr::Pk(..)) && self.shape(v) != s0 {
                return if self.ndims(h.ty) == 0 {
                    self.repr(h.ty, &h.loc)
                } else {
                    self.fat_repr(h.ty, &h.loc)
                };
            }
        }
        r0
    }

    // ---- conversions -----------------------------------------------------------------

    /// The expression as representation `to`.
    pub(super) fn ex_as(&mut self, h: &HExpr, to: &Repr) -> String {
        let v = self.ex(h);
        let from = self.erepr(h);
        if from == *to {
            return v;
        }
        let b = if matches!(from, Repr::Pk(..)) {
            self.shape(h).map(|b| self.bounds_sv(b))
        } else {
            None
        };
        self.coerce(v, &from, to, b, &h.loc)
    }

    /// The expression as the struct representation of its type.
    pub(super) fn ex_fat(&mut self, h: &HExpr) -> String {
        let to = self.fat_repr(h.ty, &h.loc);
        self.ex_as(h, &to)
    }

    /// Value `v` of representation `from` as representation `to`. A packed
    /// value becoming a struct takes bounds `b` (SV: left, right, downto);
    /// a struct becoming packed must have the packed length (a bound check
    /// failure otherwise, §14.7.3.1).
    pub(super) fn coerce(
        &mut self,
        v: String,
        from: &Repr,
        to: &Repr,
        b: Option<(String, String, String)>,
        loc: &Loc,
    ) -> String {
        if from == to {
            return v;
        }
        let (f, line, _) = self.file_line(loc);
        match (from, to) {
            (Repr::Pk(w, n), Repr::Arr(name, _)) => {
                let (l, r, dn) = b.unwrap_or_else(|| {
                    self.bounds_sv((*n - 1, Dir::Downto, 0))
                });
                let fname = self.pk_to_fat_fn(name, *w, *n);
                format!(
                    "{}({}, {}, {}, {}, {}, {})",
                    fname,
                    v,
                    l,
                    r,
                    dn,
                    sv_string(&f),
                    line
                )
            }
            (Repr::Arr(name, _), Repr::Pk(w, n)) => {
                let fname = self.fat_to_pk_fn(name, *w, *n);
                format!("{}({}, {}, {})", fname, v, sv_string(&f), line)
            }
            (Repr::Pk(w1, _), Repr::Pk(w2, n2)) if w1 == w2 => {
                // Lengths differ: a bound check failure where it is used.
                let fname = self.pk_fail_fn(*w2, *n2);
                format!("{}({}, {})", fname, sv_string(&f), line)
            }
            _ => {
                self.err(
                    loc,
                    format!(
                        "internal: no conversion from {} to {}",
                        from.sv(),
                        to.sv()
                    ),
                );
                v
            }
        }
    }

    /// The function making struct `name` from a packed vector, with bounds
    /// of the packed length.
    fn pk_to_fat_fn(&mut self, name: &str, w: u32, n: i64) -> String {
        let fname = format!("{}_pk{}_{}", name, w, n);
        if self.pk_fns.insert(fname.clone()) {
            let elem = self.arr_elem_sv(name);
            let _ = write!(
                self.type_defs,
                "  function automatic {name} {f}(bit [{hi}:0] vh_v, longint vh_l, longint vh_r, bit vh_dn, string file, int line);\n    {elem} vh_t[];\n    if (vh_len(vh_l, vh_r, vh_dn) != {n}) vh_fatal($sformatf(\"bound check failure at %s:%0d\", file, line));\n    vh_t = new[{n}];\n    for (int vh_i = 0; vh_i < {n}; vh_i++) vh_t[vh_i] = vh_v[{w} * ({m} - vh_i) +: {w}];\n    return {name}_mk(vh_l, vh_r, vh_dn, vh_t);\n  endfunction\n",
                name = name,
                f = fname,
                hi = w as i64 * n - 1,
                elem = elem,
                n = n,
                w = w,
                m = n - 1
            );
        }
        fname
    }

    /// The function packing struct `name` (checked to have `n` elements).
    fn fat_to_pk_fn(&mut self, name: &str, w: u32, n: i64) -> String {
        let fname = format!("vh_pk{}_{}_{}", w, n, name);
        if self.pk_fns.insert(fname.clone()) {
            let _ = write!(
                self.type_defs,
                "  function automatic bit [{hi}:0] {f}({name} vh_a, string file, int line);\n    bit [{hi}:0] vh_v;\n    if (vh_a.d.size() != {n}) begin vh_fatal($sformatf(\"bound check failure at %s:%0d\", file, line)); return vh_v; end\n    for (int vh_i = 0; vh_i < {n}; vh_i++) vh_v[{w} * ({m} - vh_i) +: {w}] = vh_a.d[vh_i];\n    return vh_v;\n  endfunction\n",
                name = name,
                f = fname,
                hi = w as i64 * n - 1,
                n = n,
                w = w,
                m = n - 1
            );
        }
        fname
    }

    /// A packed value of the wrong length: the bound check failure.
    pub(super) fn pk_fail_fn(&mut self, w: u32, n: i64) -> String {
        let fname = format!("vh_pkbad{}_{}", w, n);
        if self.pk_fns.insert(fname.clone()) {
            let _ = write!(
                self.type_defs,
                "  function automatic bit [{hi}:0] {f}(string file, int line);\n    vh_fatal($sformatf(\"bound check failure at %s:%0d\", file, line));\n    return 0;\n  endfunction\n",
                f = fname,
                hi = w as i64 * n - 1
            );
        }
        fname
    }

    /// The function storing element `e` at offset `off` of a packed value
    /// (`v = f(v, off, e)`): by mask arithmetic, which the simulator's
    /// compiled tier accepts in a function body where a part-select store
    /// into a local is not.
    pub(super) fn pk_set_fn(&mut self, w: u32, n: i64) -> String {
        let fname = format!("vh_pkset{}_{}", w, n);
        if self.pk_fns.insert(fname.clone()) {
            let hi = w as i64 * n - 1;
            let _ = write!(
                self.type_defs,
                "  function automatic bit [{hi}:0] {f}(bit [{hi}:0] vh_v, longint vh_off, byte unsigned vh_e);\n    bit [{hi}:0] vh_ve, vh_m;\n    int vh_sh;\n    vh_sh = {w} * ({m} - vh_off);\n    vh_ve = vh_e;\n    vh_m = 0;\n    vh_m = ~vh_m;\n    vh_m = vh_m >> {rest};\n    return (vh_v & ~(vh_m << vh_sh)) | ((vh_ve & vh_m) << vh_sh);\n  endfunction\n",
                hi = hi,
                f = fname,
                w = w,
                m = n - 1,
                rest = hi + 1 - w as i64
            );
        }
        fname
    }

    /// The function storing `len` elements from offset `off` of a packed
    /// value (`v = f(v, off, part)`).
    pub(super) fn pk_put_fn(&mut self, w: u32, n: i64, len: i64) -> String {
        let fname = format!("vh_pkput{}_{}_{}", w, n, len);
        if self.pk_fns.insert(fname.clone()) {
            let hi = w as i64 * n - 1;
            let _ = write!(
                self.type_defs,
                "  function automatic bit [{hi}:0] {f}(bit [{hi}:0] vh_v, longint vh_off, bit [{phi}:0] vh_p);\n    bit [{hi}:0] vh_vp, vh_m;\n    int vh_sh;\n    vh_sh = {w} * ({n} - vh_off - {len});\n    vh_vp = vh_p;\n    vh_m = 0;\n    vh_m = ~vh_m;\n    vh_m = vh_m >> {rest};\n    return (vh_v & ~(vh_m << vh_sh)) | ((vh_vp & vh_m) << vh_sh);\n  endfunction\n",
                hi = hi,
                f = fname,
                phi = w as i64 * len - 1,
                w = w,
                n = n,
                len = len,
                rest = hi + 1 - w as i64 * len
            );
        }
        fname
    }

    /// Concatenation helpers on packed values: an element with a vector
    /// (`ea`), a vector with an element (`ae`), two elements (`ee`).
    pub(super) fn pk_cat_fn(&mut self, kind: &str, w: u32, n: i64) -> String {
        let fname = format!("vh_cat_{}{}_{}", kind, w, n);
        if self.pk_fns.insert(fname.clone()) {
            let hi = w as i64 * n - 1;
            let body = match kind {
                "e" => format!(
                    "(byte unsigned vh_e);\n    return vh_e[{w1}:0];",
                    w1 = w - 1
                ),
                "ea" => format!(
                    "(byte unsigned vh_e, bit [{hi}:0] vh_a);\n    return {{vh_e[{w1}:0], vh_a}};",
                    hi = hi,
                    w1 = w - 1
                ),
                "ae" => format!(
                    "(bit [{hi}:0] vh_a, byte unsigned vh_e);\n    return {{vh_a, vh_e[{w1}:0]}};",
                    hi = hi,
                    w1 = w - 1
                ),
                _ => format!(
                    "(byte unsigned vh_e, byte unsigned vh_f);\n    return {{vh_e[{w1}:0], vh_f[{w1}:0]}};",
                    w1 = w - 1
                ),
            };
            let out_n = match kind {
                "ee" => 2,
                "e" => 1,
                _ => n + 1,
            };
            let _ = write!(
                self.type_defs,
                "  function automatic bit [{ohi}:0] {f}{body}\n  endfunction\n",
                ohi = w as i64 * out_n - 1,
                f = fname,
                body = body
            );
        }
        fname
    }

    // ---- packed values ---------------------------------------------------------------

    /// A packed literal of element positions `codes` (left to right).
    pub(super) fn pk_lit(w: u32, codes: &[u32]) -> String {
        let mut bits = String::with_capacity(codes.len() * w as usize);
        for c in codes {
            for k in (0..w).rev() {
                bits.push(if (c >> k) & 1 == 1 { '1' } else { '0' });
            }
        }
        let total = codes.len() as u32 * w;
        if w == 4 {
            let hex: String = codes
                .iter()
                .map(|c| std::char::from_digit(*c & 15, 16).unwrap_or('0'))
                .collect();
            return format!("{}'h{}", total, hex);
        }
        format!("{}'b{}", total, bits)
    }

    /// The packed literal of array value `av` (`None` when an element is not
    /// an enumeration value).
    pub(super) fn pk_value(w: u32, av: &ArrayValue) -> Option<String> {
        let codes: Vec<u32> = av
            .elems
            .iter()
            .map(|e| match e {
                Value::Enum(c) => Some(*c),
                Value::Int(i) => Some(*i as u32),
                _ => None,
            })
            .collect::<Option<_>>()?;
        Some(Self::pk_lit(w, &codes))
    }

    /// Element at offset `off` (SV, 0 for the left element) of packed
    /// value `v` of `n` elements of `w` bits.
    pub(super) fn pk_sel(v: &str, w: u32, n: i64, off: &str) -> String {
        if let Some(k) = lit_i64(off) {
            let lo = w as i64 * (n - 1 - k);
            return format!("{}[{}:{}]", v, lo + w as i64 - 1, lo);
        }
        format!("{}[{} * ({} - ({})) +: {}]", v, w, n - 1, off, w)
    }

    /// `len` elements from offset `off` (static) of packed value `v`.
    pub(super) fn pk_part(v: &str, w: u32, n: i64, off: i64, len: i64) -> String {
        let lo = w as i64 * (n - off - len);
        format!("{}[{}:{}]", v, lo + w as i64 * len - 1, lo)
    }

    /// The offset of index `i` (SV) in an array with static bounds `b`,
    /// checked (§8.4): a constant for a static index in range.
    pub(super) fn pk_off(&mut self, i: &str, b: Bounds, loc: &Loc) -> String {
        let (l, dir, r) = b;
        if let Some(iv) = lit_i64(i) {
            let (lo, hi) = if dir == Dir::To { (l, r) } else { (r, l) };
            if iv >= lo && iv <= hi {
                return match dir {
                    Dir::To => iv - l,
                    Dir::Downto => l - iv,
                }
                .to_string();
            }
        }
        let (ls, rs, dn) = self.bounds_sv(b);
        let (f, line, _) = self.file_line(loc);
        format!(
            "vh_ix({}, {}, {}, {}, {}, {})",
            i,
            ls,
            rs,
            dn,
            sv_string(&f),
            line
        )
    }

    /// Whether an SV expression can be selected from (a name, a member or
    /// an element of one), rather than a call or a literal.
    pub(super) fn selectable(s: &str) -> bool {
        !s.contains('(') && !s.contains('{') && !s.contains('\'') && !s.contains(' ')
    }

    /// `v` as a selectable name: a temporary when it is not one, or is a
    /// select already (a port associated with a slice; SV has no select
    /// of a select).
    pub(super) fn as_selectable(&mut self, v: String, r: &Repr) -> String {
        if Self::selectable(&v) && !v.contains('[') {
            return v;
        }
        self.as_tmp(v, &r.sv())
    }

    /// `v` stored in a temporary of SV type `sv_ty` before the statement.
    pub(super) fn as_tmp(&mut self, v: String, sv_ty: &str) -> String {
        self.tmp += 1;
        let n = format!("vh_e{}", self.tmp);
        self.pre_stmts
            .push((n.clone(), sv_ty.to_string(), format!("{} = {};", n, v)));
        n
    }

    /// The SV selection of a static path from a value of type `t`: the
    /// selection text, a trailing slice (offset, length) and the subtype
    /// reached (the array's, for a slice).
    pub(super) fn path_sv(&mut self, t: TypeId, path: &[Sel], loc: &Loc) -> (String, Option<(i64, i64)>, TypeId) {
        let mut out = String::new();
        let mut cur = t;
        for s in path {
            match s {
                Sel::Field(i) => {
                    let _ = write!(out, ".f{}", i);
                    cur = self.field_storage(cur).get(*i).copied().unwrap_or(cur);
                }
                Sel::Elem(k) => {
                    match self.repr(cur, loc) {
                        Repr::Pk(w, n) => {
                            let lo = w as i64 * (n - 1 - k);
                            let _ = write!(out, "[{}:{}]", lo + w as i64 - 1, lo);
                        }
                        _ => {
                            let _ = write!(out, ".d[{}]", k);
                        }
                    }
                    cur = self.d.element_subtype(cur).unwrap_or(cur);
                }
                Sel::Slice(k, n) => return (out, Some((*k, *n)), cur),
            }
        }
        (out, None, cur)
    }
}
