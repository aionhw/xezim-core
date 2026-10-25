//! Predefined operations (IEEE 1076-2008 §9.2, §5.2.6, §5.3.2.4): the
//! operators every type implicitly declares, created as subprograms with a
//! `Builtin` body on demand for the operand types in play, and the native
//! subprograms of packages STANDARD, ENV and TEXTIO.

use super::Design;
use super::hir::*;

/// The types an expression could have, before its context picks one
/// (used by overload resolution, §12.5).
#[derive(Clone, Debug, Default)]
pub struct TypeSet {
    /// Base types.
    pub types: Vec<TypeId>,
    pub univ_int: bool,
    pub univ_real: bool,
    /// A string or bit string literal: any one-dimensional array of an
    /// enumeration type with these characters.
    pub string_lit: Option<Vec<u8>>,
    /// An aggregate: any composite type.
    pub aggregate: bool,
    pub null: bool,
    /// Unknown (an error elsewhere): compatible with anything.
    pub any: bool,
}

impl TypeSet {
    pub fn of(t: TypeId) -> Self {
        TypeSet {
            types: vec![t],
            ..Default::default()
        }
    }

    pub fn add(&mut self, t: TypeId) {
        if !self.types.contains(&t) {
            self.types.push(t);
        }
    }

    pub fn merge(&mut self, o: &TypeSet) {
        for t in &o.types {
            self.add(*t);
        }
        self.univ_int |= o.univ_int;
        self.univ_real |= o.univ_real;
        self.aggregate |= o.aggregate;
        self.null |= o.null;
        self.any |= o.any;
        if self.string_lit.is_none() {
            self.string_lit = o.string_lit.clone();
        }
    }

    pub fn is_empty(&self) -> bool {
        self.types.is_empty()
            && !self.univ_int
            && !self.univ_real
            && self.string_lit.is_none()
            && !self.aggregate
            && !self.null
            && !self.any
    }
}

/// The relational, adding, … operator a symbol names.
fn op_class(op: &str) -> &'static str {
    match op {
        "and" | "or" | "nand" | "nor" | "xor" | "xnor" => "logical",
        "=" | "/=" => "equality",
        "<" | "<=" | ">" | ">=" => "ordering",
        "?=" | "?/=" | "?<" | "?<=" | "?>" | "?>=" => "matching",
        "sll" | "srl" | "sla" | "sra" | "rol" | "ror" => "shift",
        "+" | "-" => "adding",
        "&" => "concat",
        "*" | "/" => "multiplying",
        "mod" | "rem" => "modrem",
        "**" => "pow",
        "abs" => "abs",
        "not" => "not",
        "??" => "cond",
        _ => "",
    }
}

impl Design {
    pub fn is_integer(&self, t: TypeId) -> bool {
        matches!(
            self.types[self.base(t)].kind,
            TypeKind::Integer | TypeKind::UniversalInteger
        )
    }
    pub fn is_real(&self, t: TypeId) -> bool {
        matches!(
            self.types[self.base(t)].kind,
            TypeKind::Real | TypeKind::UniversalReal
        )
    }
    pub fn is_physical(&self, t: TypeId) -> bool {
        matches!(self.types[self.base(t)].kind, TypeKind::Physical(_))
    }
    pub fn is_enum(&self, t: TypeId) -> bool {
        matches!(self.types[self.base(t)].kind, TypeKind::Enum(_))
    }
    pub fn is_scalar(&self, t: TypeId) -> bool {
        self.is_integer(t) || self.is_real(t) || self.is_physical(t) || self.is_enum(t)
    }
    pub fn is_discrete(&self, t: TypeId) -> bool {
        self.is_integer(t) || self.is_enum(t)
    }
    pub fn is_numeric(&self, t: TypeId) -> bool {
        self.is_integer(t) || self.is_real(t) || self.is_physical(t)
    }
    pub fn is_array(&self, t: TypeId) -> bool {
        matches!(self.types[self.base(t)].kind, TypeKind::Array { .. })
    }
    pub fn is_access(&self, t: TypeId) -> bool {
        matches!(self.types[self.base(t)].kind, TypeKind::Access(_))
    }
    /// The designated subtype of an access type.
    pub fn designated(&self, t: TypeId) -> Option<TypeId> {
        match self.types[self.base(t)].kind {
            TypeKind::Access(d) => Some(d),
            _ => None,
        }
    }
    pub fn is_composite(&self, t: TypeId) -> bool {
        matches!(
            self.types[self.base(t)].kind,
            TypeKind::Array { .. } | TypeKind::Record(_)
        )
    }
    /// The element type of a one-dimensional array type.
    pub fn array1d_elem(&self, t: TypeId) -> Option<TypeId> {
        match &self.types[self.base(t)].kind {
            TypeKind::Array { index, elem } if index.len() == 1 => Some(*elem),
            _ => None,
        }
    }
    /// BIT or BOOLEAN (the logical operators' scalar types).
    pub fn is_bit_or_bool(&self, t: TypeId) -> bool {
        let b = self.base(t);
        b == self.std.bit || b == self.std.boolean
    }
    /// Enumeration literals of an enumeration type.
    pub fn enum_lits(&self, t: TypeId) -> Option<&Vec<String>> {
        match &self.types[self.base(t)].kind {
            TypeKind::Enum(l) => Some(l),
            _ => None,
        }
    }

    /// Whether an expression with possible types `s` can be of type `t`.
    pub fn compatible(&self, s: &TypeSet, t: TypeId) -> bool {
        let b = self.base(t);
        if s.any || s.types.contains(&b) {
            return true;
        }
        if s.univ_int && self.is_integer(b) || s.univ_real && self.is_real(b) {
            return true;
        }
        if s.aggregate && self.is_composite(b) || s.null && self.is_access(b) {
            return true;
        }
        // §9.3.2: a string literal fits any one-dimensional array of a
        // character type; its characters are checked once the type is known.
        if s.string_lit.is_some()
            && let Some(e) = self.array1d_elem(b)
            && let Some(lits) = self.enum_lits(e)
        {
            return lits.iter().any(|l| l.starts_with('\''));
        }
        // A universal type is compatible with its family.
        match &self.types[b].kind {
            TypeKind::UniversalInteger => s.types.iter().any(|x| self.is_integer(*x)),
            TypeKind::UniversalReal => s.types.iter().any(|x| self.is_real(*x)),
            _ => false,
        }
    }

    /// A predefined operation instance (cached by name and profile).
    pub fn pre_sub(
        &mut self,
        op: &str,
        params: &[TypeId],
        ret: Option<TypeId>,
        builtin: Builtin,
    ) -> SubId {
        let key = format!(
            "{}:{:?}:{:?}:{:?}",
            op,
            params.iter().map(|t| self.base(*t)).collect::<Vec<_>>(),
            ret.map(|t| self.base(t)),
            builtin
        );
        if let Some(id) = self.pre_cache.get(&key) {
            return *id;
        }
        let mut pids = Vec::new();
        for (i, p) in params.iter().enumerate() {
            pids.push(self.add_obj(ObjInfo {
                name: ["l", "r", "x"][i.min(2)].to_string(),
                kind: ObjKind::Param(
                    crate::vhdl::ast::ObjClass::Constant,
                    crate::vhdl::ast::Mode::In,
                ),
                ty: *p,
                init: None,
                loc: Loc {
                    file: 0,
                    span: 0..0,
                },
                static_val: None,
            }));
        }
        let id = self.add_sub(SubInfo {
            name: op.to_string(),
            is_function: true,
            pure: true,
            params: pids,
            ret,
            builtin: Some(builtin),
            body: None,
            loc: None,
            path: format!("<predefined>.{}", op),
        });
        self.pre_cache.insert(key, id);
        id
    }

    /// The predefined operators named `op` (without quotes) applicable to
    /// operands whose possible types are `sets`, with `expect` (the result
    /// type wanted, if known) as a hint for operands of no definite type.
    pub fn predefined_ops(
        &mut self,
        op: &str,
        sets: &[TypeSet],
        expect: Option<TypeId>,
    ) -> Vec<SubId> {
        // Candidate operand types: every definite type of the operands,
        // the expected type, and the universal types.
        let mut tys: Vec<TypeId> = Vec::new();
        for s in sets {
            for t in &s.types {
                if !tys.contains(t) {
                    tys.push(*t);
                }
            }
        }
        if let Some(e) = expect {
            let b = self.base(e);
            if !tys.contains(&b) {
                tys.push(b);
            }
            // `&` expecting an array: its element type too.
            if op == "&"
                && let Some(el) = self.array1d_elem(b)
            {
                let el = self.base(el);
                if !tys.contains(&el) {
                    tys.push(el);
                }
            }
        }
        // String literal operands: every one-dimensional array type of a
        // character type is a candidate (overload resolution, §12.5).
        if sets.iter().any(|s| s.string_lit.is_some()) {
            for (id, ti) in self.types.iter().enumerate() {
                if let TypeKind::Array { index, elem } = &ti.kind
                    && index.len() == 1
                    && self
                        .enum_lits(*elem)
                        .is_some_and(|l| l.iter().any(|x| x.starts_with('\'')))
                    && !tys.contains(&id)
                {
                    tys.push(id);
                }
            }
        }
        // `"…" & c` with no context: the array types of c's type.
        if op == "&" && expect.is_none() {
            let elems: Vec<TypeId> = tys.clone();
            for (id, ti) in self.types.iter().enumerate() {
                if let TypeKind::Array { index, elem } = &ti.kind
                    && index.len() == 1
                    && elems.contains(&self.base(*elem))
                    && !tys.contains(&id)
                {
                    tys.push(id);
                }
            }
        }
        if sets.iter().any(|s| s.univ_int) {
            tys.push(self.std.universal_integer);
        }
        if sets.iter().any(|s| s.univ_real) {
            tys.push(self.std.universal_real);
        }
        let boolean = self.std.boolean;
        let bit = self.std.bit;
        let integer = self.std.integer;
        let ui = self.std.universal_integer;
        let ur = self.std.universal_real;
        let mut out = Vec::new();
        let bin = sets.len() == 2;
        let pre = |d: &mut Self, ps: &[TypeId], r: TypeId, out: &mut Vec<SubId>| {
            let id = d.pre_sub(
                &format!("\"{}\"", op),
                ps,
                Some(r),
                Builtin::Op(op.to_string()),
            );
            if !out.contains(&id) {
                out.push(id);
            }
        };
        for &t in &tys {
            let t = self.base(t);
            let elem = self.array1d_elem(t);
            match (op_class(op), bin) {
                ("logical", true) => {
                    if self.is_bit_or_bool(t) {
                        pre(self, &[t, t], t, &mut out);
                    }
                    if let Some(e) = elem
                        && self.is_bit_or_bool(e)
                    {
                        pre(self, &[t, t], t, &mut out);
                        let e = self.base(e);
                        pre(self, &[t, e], t, &mut out);
                        pre(self, &[e, t], t, &mut out);
                    }
                }
                ("logical", false) => {
                    // VHDL-2008 reduction operators.
                    if let Some(e) = elem
                        && self.is_bit_or_bool(e)
                    {
                        let e = self.base(e);
                        pre(self, &[t], e, &mut out);
                    }
                }
                ("not", false) => {
                    if self.is_bit_or_bool(t) || elem.is_some_and(|e| self.is_bit_or_bool(e)) {
                        pre(self, &[t], t, &mut out);
                    }
                }
                ("equality", true) => {
                    if !matches!(self.types[t].kind, TypeKind::File(_) | TypeKind::Protected) {
                        pre(self, &[t, t], boolean, &mut out);
                    }
                }
                ("ordering", true) => {
                    if self.is_scalar(t) || elem.is_some_and(|e| self.is_discrete(e)) {
                        pre(self, &[t, t], boolean, &mut out);
                    }
                }
                ("matching", true) => {
                    // BIT and STD_ULOGIC (and, for ?= and ?/=, one-
                    // dimensional arrays of them) — §9.2.3.
                    let sul = self.std.std_ulogic;
                    let scalar = |d: &Self, x: TypeId| d.base(x) == bit || Some(d.base(x)) == sul;
                    if scalar(self, t) {
                        let b = self.base(t);
                        pre(self, &[t, t], b, &mut out);
                    }
                    if matches!(op, "?=" | "?/=")
                        && let Some(e) = elem
                        && scalar(self, e)
                    {
                        let e = self.base(e);
                        pre(self, &[t, t], e, &mut out);
                    }
                }
                ("shift", true) => {
                    if let Some(e) = elem
                        && self.is_bit_or_bool(e)
                    {
                        pre(self, &[t, integer], t, &mut out);
                    }
                }
                ("adding", true) => {
                    if self.is_numeric(t) {
                        pre(self, &[t, t], t, &mut out);
                    }
                }
                ("adding", false) | ("abs", false) => {
                    if self.is_numeric(t) {
                        pre(self, &[t], t, &mut out);
                    }
                }
                ("concat", true) => {
                    if let Some(e) = elem {
                        let e = self.base(e);
                        pre(self, &[t, t], t, &mut out);
                        pre(self, &[t, e], t, &mut out);
                        pre(self, &[e, t], t, &mut out);
                        pre(self, &[e, e], t, &mut out);
                    }
                }
                ("multiplying", true) => {
                    if self.is_integer(t) || self.is_real(t) {
                        pre(self, &[t, t], t, &mut out);
                    }
                    if self.is_physical(t) {
                        let real = self.std.real;
                        if op == "*" {
                            pre(self, &[t, integer], t, &mut out);
                            pre(self, &[t, real], t, &mut out);
                            pre(self, &[integer, t], t, &mut out);
                            pre(self, &[real, t], t, &mut out);
                        } else {
                            pre(self, &[t, integer], t, &mut out);
                            pre(self, &[t, real], t, &mut out);
                            pre(self, &[t, t], ui, &mut out);
                        }
                    }
                    if t == ui && op == "*" {
                        pre(self, &[ui, ur], ur, &mut out);
                        pre(self, &[ur, ui], ur, &mut out);
                    }
                    if t == ur && op == "/" {
                        pre(self, &[ur, ui], ur, &mut out);
                    }
                }
                ("modrem", true) => {
                    if self.is_integer(t) || self.is_physical(t) {
                        pre(self, &[t, t], t, &mut out);
                    }
                }
                ("pow", true) => {
                    if self.is_integer(t) || self.is_real(t) {
                        pre(self, &[t, integer], t, &mut out);
                    }
                }
                ("cond", false) => {
                    if self.base(t) == bit {
                        pre(self, &[t], boolean, &mut out);
                    }
                }
                _ => {}
            }
        }
        out
    }

    /// Predefined functions (not operators) visible for an argument type:
    /// MINIMUM, MAXIMUM, TO_STRING, RISING_EDGE, FALLING_EDGE (§5.2.6,
    /// §5.3.2.4, §16.2).
    pub fn predefined_funcs(&mut self, name: &str, sets: &[TypeSet]) -> Vec<SubId> {
        let mut tys: Vec<TypeId> = Vec::new();
        for s in sets {
            for t in &s.types {
                if !tys.contains(t) {
                    tys.push(*t);
                }
            }
            if s.univ_int {
                let i = self.std.integer;
                if !tys.contains(&i) {
                    tys.push(i);
                }
            }
            if s.univ_real {
                let r = self.std.real;
                if !tys.contains(&r) {
                    tys.push(r);
                }
            }
        }
        let string = self.std.string;
        let boolean = self.std.boolean;
        let mut out = Vec::new();
        for t in tys {
            let t = self.base(t);
            match (name, sets.len()) {
                ("minimum" | "maximum", 2)
                    if self.is_scalar(t)
                        || self.array1d_elem(t).is_some_and(|e| self.is_discrete(e)) =>
                {
                    out.push(self.pre_sub(
                        name,
                        &[t, t],
                        Some(t),
                        Builtin::MinMax(name == "maximum"),
                    ));
                }
                ("minimum" | "maximum", 1) => {
                    if let Some(e) = self.array1d_elem(t)
                        && self.is_scalar(e)
                    {
                        let e = self.base(e);
                        out.push(self.pre_sub(
                            name,
                            &[t],
                            Some(e),
                            Builtin::MinMax(name == "maximum"),
                        ));
                    }
                }
                ("to_string", 1) => {
                    let chars = self
                        .array1d_elem(t)
                        .and_then(|e| self.enum_lits(e))
                        .is_some_and(|l| l.iter().all(|x| x.starts_with('\'')));
                    if self.is_scalar(t) || chars {
                        out.push(self.pre_sub(name, &[t], Some(string), Builtin::ToString));
                    }
                }
                // §5.3.2.4: the string of a BIT_VECTOR in binary, octal or
                // hexadecimal digits.
                (
                    "to_bstring" | "to_binary_string" | "to_ostring" | "to_octal_string"
                    | "to_hstring" | "to_hex_string",
                    1,
                ) if t == self.std.bit_vector => {
                    let w = match name {
                        "to_ostring" | "to_octal_string" => 3,
                        "to_hstring" | "to_hex_string" => 4,
                        _ => 1,
                    };
                    out.push(self.pre_sub(name, &[t], Some(string), Builtin::BitString(w)));
                }
                ("deallocate", 1) if self.is_access(t) => {
                    let id = self.pre_sub(name, &[t], None, Builtin::Deallocate);
                    let p = self.subprograms[id].params[0];
                    self.objects[p].kind = ObjKind::Param(
                        crate::vhdl::ast::ObjClass::Variable,
                        crate::vhdl::ast::Mode::InOut,
                    );
                    self.subprograms[id].is_function = false;
                    out.push(id);
                }
                ("rising_edge" | "falling_edge", 1) if self.is_bit_or_bool(t) => {
                    let b = if name == "rising_edge" {
                        Builtin::RisingEdge
                    } else {
                        Builtin::FallingEdge
                    };
                    let id = self.pre_sub(name, &[t], Some(boolean), b);
                    let p = self.subprograms[id].params[0];
                    self.objects[p].kind = ObjKind::Param(
                        crate::vhdl::ast::ObjClass::Signal,
                        crate::vhdl::ast::Mode::In,
                    );
                    out.push(id);
                }
                _ => {}
            }
        }
        out
    }
}

/// Native subprograms of the standard packages: declared in the vendored
/// sources, implemented by the simulator.
pub fn native_builtin(path: &str, name: &str) -> Option<Builtin> {
    match (path, name) {
        ("std.standard", "now") => Some(Builtin::Now),
        ("std.env", n) => Some(Builtin::Native(format!("env.{}", n))),
        ("std.textio", n) => Some(Builtin::Native(format!("textio.{}", n))),
        _ => None,
    }
}

/// Whether an enumeration literal name is the character literal `c`.
pub fn is_char_lit(l: &str, c: u8) -> bool {
    let mut ch = l.chars();
    ch.next() == Some('\'')
        && ch.next() == Some(c as char)
        && ch.next() == Some('\'')
        && ch.next().is_none()
}
