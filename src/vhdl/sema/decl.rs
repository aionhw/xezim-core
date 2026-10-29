//! Declarations (IEEE 1076-2008 §5, §6): types and subtypes, objects,
//! subprograms, interfaces, components; and architectures, whose
//! concurrent statements become processes (§11).

use super::hir::*;
use super::{Design, EntityInfo, RegionId, Sym};
use crate::vhdl::ast::{self, Dir, Mode, ObjClass};

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum IfaceKind {
    Generic,
    Port,
    /// Subprogram parameters (function or procedure).
    Param {
        function: bool,
    },
}

impl Design {
    // ---- declarative parts ---------------------------------------------------------

    pub fn decls(
        &mut self,
        r: RegionId,
        decls: &[ast::Decl],
        objs: &mut Vec<ObjId>,
        subs: &mut Vec<SubId>,
        path: &str,
    ) {
        for d in decls {
            self.decl(r, d, objs, subs, path);
        }
    }

    fn decl(
        &mut self,
        r: RegionId,
        d: &ast::Decl,
        objs: &mut Vec<ObjId>,
        subs: &mut Vec<SubId>,
        path: &str,
    ) {
        match d {
            ast::Decl::Type(t) => self.type_decl(r, t, path),
            ast::Decl::Subtype { name, ind, .. } => {
                if let Some(t) = self.subtype_ind(r, ind) {
                    // A subtype declaration names a subtype: give an anonymous
                    // one its name, else declare a copy carrying the name.
                    let t = if self.types[t].name.is_empty() {
                        self.types[t].name = name.name.clone();
                        t
                    } else {
                        self.add_type(
                            &name.name,
                            TypeKind::Subtype {
                                base: t,
                                constraint: None,
                                resolution: None,
                            },
                            None,
                            Some(self.loc(name.span.clone())),
                        )
                    };
                    self.declare(r, &name.name, Sym::Type(t));
                }
            }
            ast::Decl::Constant(o) => {
                for id in self.object_decl(r, o, ObjKind::Constant) {
                    objs.push(id);
                }
            }
            ast::Decl::Signal { obj, kind } => {
                for id in self.object_decl(r, obj, ObjKind::Signal) {
                    objs.push(id);
                    if let Some(k) = kind {
                        // §6.4.2.3: a guarded signal is of a resolved subtype.
                        if !self.is_resolved(self.objects[id].ty) {
                            self.error(
                                obj.span.clone(),
                                "a guarded signal must be of a resolved subtype",
                            );
                        }
                        self.sig_kinds.insert(id, *k);
                        if let Some(m) = self.type_mark(r, &obj.ty.mark) {
                            self.guarded_marks.insert(id, m);
                        }
                    }
                }
            }
            ast::Decl::Disconnect(ds) => self.disconnect_spec(r, ds, objs),
            ast::Decl::Variable { obj, shared } => {
                let k = if *shared {
                    ObjKind::SharedVariable
                } else {
                    ObjKind::Variable
                };
                for id in self.object_decl(r, obj, k) {
                    objs.push(id);
                }
            }
            ast::Decl::File {
                names, ty, open, ..
            } => {
                let Some(t) = self.subtype_ind(r, ty) else {
                    return;
                };
                // The open information: the name, and the kind (READ_MODE
                // by default).
                let open = match open {
                    Some(fo) => {
                        let string = self.std.string;
                        let fok = self.std.file_open_kind;
                        let Some(name) = self.expr(r, &fo.name, Some(string)) else {
                            return;
                        };
                        let kind = match &fo.kind {
                            Some(k) => match self.expr(r, k, Some(fok)) {
                                Some(k) => k,
                                None => return,
                            },
                            None => lit_expr(Value::Enum(0), fok, name.loc.clone()),
                        };
                        Some((name, kind))
                    }
                    None => None,
                };
                for n in names {
                    let id = self.add_obj(ObjInfo {
                        name: n.name.clone(),
                        kind: ObjKind::File,
                        ty: t,
                        init: None,
                        loc: self.loc(n.span.clone()),
                        static_val: None,
                    });
                    self.declare(r, &n.name, Sym::Obj(id));
                    if let Some(o) = &open {
                        self.file_opens.insert(id, o.clone());
                    }
                    objs.push(id);
                }
            }
            ast::Decl::Alias {
                name,
                ty: decl_ty,
                target,
                signature,
                span,
            } => {
                let key = match name {
                    ast::Designator::Ident(i) => i.name.clone(),
                    ast::Designator::Op(o, _) => format!("\"{}\"", o),
                };
                // An alias of subprograms or enumeration literals (§6.6.3):
                // the overloads its signature selects (all without one).
                let mut targets = self.overload_targets(r, target);
                if targets.is_empty() {
                    // A predefined function: `TO_STRING`, or by expanded name
                    // `STD.STANDARD.RISING_EDGE`.
                    let pre_name = match &target.kind {
                        ast::NameKind::Simple(i) if self.lookup(r, &i.name).is_empty() => {
                            Some(i.name.clone())
                        }
                        ast::NameKind::Selected(p, ast::Suffix::Ident(i)) if matches!(self.name_sym(r, p), Some(Sym::Package(ref k)) if k.0 == "std" && k.1 == "standard") => {
                            Some(i.name.clone())
                        }
                        _ => None,
                    };
                    if let Some(n) = pre_name {
                        targets = self.predefined_alias_targets(r, &n, signature.as_ref());
                    }
                }
                if !targets.is_empty() {
                    let mut chosen = Vec::new();
                    for s in targets {
                        if self.signature_matches(r, &s, signature.as_ref()) {
                            chosen.push(s);
                        }
                    }
                    if chosen.is_empty() {
                        self.error(span.clone(), "no subprogram matches the alias signature");
                    }
                    for s in chosen {
                        self.declare(r, &key, s);
                    }
                    return;
                }
                // An alias of a type (§6.6.3).
                let n = self.errors.len();
                let ts = self.name_sym(r, target);
                self.errors.truncate(n);
                if let Some(Sym::Type(t)) = ts {
                    self.declare(r, &key, Sym::Type(t));
                    return;
                }
                let e = ast::Expr {
                    kind: ast::ExprKind::Name(target.clone()),
                    span: target.span.clone(),
                };
                let alias_ty = match decl_ty {
                    Some(ind) => self.subtype_ind(r, ind),
                    None => None,
                };
                match self.expr(r, &e, None) {
                    Some(h) => {
                        // With a subtype indication, the alias views the
                        // object with the subtype's bounds (§6.6.2). An alias
                        // of a constant or `in` parameter is a constant
                        // holding the converted value; of anything else, a
                        // conversion at each use (read-only).
                        let h = match alias_ty {
                            Some(at)
                                if self.is_array(at) && self.array_constraint(at).is_some() =>
                            {
                                let conv = HExpr {
                                    kind: HExprKind::Convert(Box::new(h.clone())),
                                    ty: at,
                                    loc: h.loc.clone(),
                                };
                                let readonly = root_obj(&h).is_some_and(|o| {
                                    matches!(
                                        self.objects[o].kind,
                                        ObjKind::Constant
                                            | ObjKind::Generic
                                            | ObjKind::Param(
                                                ast::ObjClass::Constant | ast::ObjClass::Variable,
                                                ast::Mode::In
                                            )
                                    )
                                });
                                if readonly {
                                    let id = self.add_obj(ObjInfo {
                                        name: key.clone(),
                                        kind: ObjKind::Constant,
                                        ty: at,
                                        init: Some(conv),
                                        loc: self.loc(span.clone()),
                                        static_val: None,
                                    });
                                    self.declare(r, &key, Sym::Obj(id));
                                    objs.push(id);
                                    return;
                                }
                                conv
                            }
                            _ => h,
                        };
                        self.aliases.push(h);
                        let id = self.aliases.len() - 1;
                        self.declare(r, &key, Sym::Alias(id));
                    }
                    None => self.error(span.clone(), "aliases of this kind are not supported yet"),
                }
            }
            ast::Decl::Component(c) => {
                let cr = self.new_region(Some(r));
                let p = format!("{}.{}", path, c.name.name);
                let generics = self.interface_list(cr, &c.generics, IfaceKind::Generic, &p);
                let ports = self.interface_list(cr, &c.ports, IfaceKind::Port, &p);
                self.components.push(super::ComponentInfo {
                    name: c.name.name.clone(),
                    generics,
                    ports,
                });
                let id = self.components.len() - 1;
                self.declare(r, &c.name.name, Sym::Component(id));
            }
            ast::Decl::ConfigSpec(c) => {
                let (lib, file) = (self.cur_lib.clone(), self.cur_file);
                self.cfg_specs.push((r, c.clone(), lib, file));
            }
            ast::Decl::Attribute { name, mark, .. } => {
                if let Some(t) = self.type_mark(r, mark) {
                    self.declare(r, &name.name, Sym::Attribute(t));
                }
            }
            // User-defined attribute values: not used by the simulation.
            ast::Decl::AttributeSpec(_) => {}
            ast::Decl::SubprogramDecl(spec) if !spec.generics.is_empty() => {
                self.declare_generic_sub(r, spec, None)
            }
            ast::Decl::SubprogramBody(b) if !b.spec.generics.is_empty() => {
                self.declare_generic_sub(r, &b.spec, Some(b))
            }
            ast::Decl::SubprogramDecl(spec) => {
                if let Some(id) = self.subprogram_spec(r, spec, path) {
                    subs.push(id);
                }
            }
            ast::Decl::SubprogramBody(b) => {
                if let Some(id) = self.subprogram_body(r, b, path)
                    && !subs.contains(&id)
                {
                    subs.push(id);
                }
            }
            ast::Decl::SubprogramInst {
                name,
                uninst,
                generic_map,
                span,
                ..
            } => {
                if let Some(id) =
                    self.instantiate_sub(r, name, uninst, generic_map, span.clone(), path)
                {
                    subs.push(id);
                }
            }
            ast::Decl::Use(names) => {
                for n in names {
                    self.use_clause(r, n);
                }
            }
            ast::Decl::Package(p) => {
                self.error(p.span.clone(), "nested packages are not supported yet")
            }
            ast::Decl::PackageBody(p) => {
                self.error(p.span.clone(), "nested packages are not supported yet")
            }
            ast::Decl::PackageInst(p) => {
                // A package instance declared in this region (§4.9).
                self.local_insts += 1;
                let key = (
                    self.cur_lib.clone(),
                    format!("{}_inst{}", p.name.name, self.local_insts),
                );
                let actx = super::generics::ActualCtx {
                    region: r,
                    lib: self.cur_lib.clone(),
                    file: self.cur_file,
                };
                if self.instantiate_package(&actx, p, key.clone()).is_some() {
                    self.declare(r, &p.name.name, Sym::Package(key));
                }
            }
            ast::Decl::Unsupported(what, span) => {
                self.error(span.clone(), format!("{} are not supported yet", what))
            }
        }
    }

    /// A disconnection specification (§7.4): the disconnection time of
    /// the named guarded signals, or of the others or all of the type
    /// declared in this declarative part.
    fn disconnect_spec(&mut self, r: RegionId, ds: &ast::DisconnectSpec, objs: &[ObjId]) {
        let Some(t) = self.type_mark(r, &ds.mark) else {
            return;
        };
        let time = self.std.time;
        let Some(after) = self.expr(r, &ds.after, Some(time)) else {
            return;
        };
        if self.eval(&after).is_none() {
            self.error(
                ds.after.span.clone(),
                "the disconnection time must be a static expression",
            );
            return;
        }
        let guarded = |d: &Self, o: ObjId| d.guarded_marks.get(&o) == Some(&t);
        let targets: Vec<ObjId> = match &ds.signals {
            ast::SignalList::Names(names) => {
                let mut v = Vec::new();
                for n in names {
                    match objs.iter().rev().find(|&&o| self.objects[o].name == n.name) {
                        Some(&o) if guarded(self, o) => v.push(o),
                        Some(_) => self.error(
                            n.span.clone(),
                            format!(
                                "'{}' is not a guarded signal of type '{}'",
                                n.name,
                                name_text(&ds.mark)
                            ),
                        ),
                        None => self.error(
                            n.span.clone(),
                            format!(
                                "no signal '{}' is declared in this declarative part",
                                n.name
                            ),
                        ),
                    }
                }
                v
            }
            ast::SignalList::Others => objs
                .iter()
                .copied()
                .filter(|&o| guarded(self, o) && !self.disconnect.contains_key(&o))
                .collect(),
            ast::SignalList::All => objs.iter().copied().filter(|&o| guarded(self, o)).collect(),
        };
        for o in targets {
            if self.disconnect.insert(o, after.clone()).is_some() {
                self.error(
                    ds.span.clone(),
                    format!(
                        "signal '{}' already has a disconnection specification",
                        self.objects[o].name
                    ),
                );
            }
        }
    }

    /// Whether a subtype has a resolution function (of its own or of its
    /// elements, §6.3).
    pub fn is_resolved(&self, t: TypeId) -> bool {
        let mut cur = t;
        loop {
            match &self.types[cur].kind {
                TypeKind::Subtype {
                    resolution: Some(_),
                    ..
                } => return true,
                TypeKind::Subtype { base, .. } => cur = *base,
                TypeKind::Array { .. } => {
                    return self
                        .element_subtype(t)
                        .is_some_and(|e| e != t && self.is_resolved(e));
                }
                _ => return false,
            }
        }
    }

    // ---- types --------------------------------------------------------------------

    /// A type mark: a name denoting a type or subtype.
    pub fn type_mark(&mut self, r: RegionId, n: &ast::Name) -> Option<TypeId> {
        match self.name_sym(r, n) {
            Some(Sym::Type(t)) => Some(t),
            Some(_) => {
                self.error(n.span.clone(), "not a type");
                None
            }
            None => {
                self.error(n.span.clone(), format!("unknown type '{}'", name_text(n)));
                None
            }
        }
    }

    /// The single named entity a (non-overloaded) name denotes.
    pub fn name_sym(&mut self, r: RegionId, n: &ast::Name) -> Option<Sym> {
        match &n.kind {
            ast::NameKind::Simple(i) => self.lookup(r, &i.name).into_iter().next(),
            ast::NameKind::Selected(prefix, suffix) => {
                let p = self.name_sym(r, prefix)?;
                let key = match suffix {
                    ast::Suffix::Ident(i) => i.name.clone(),
                    ast::Suffix::Char(c, _) => format!("'{}'", *c as char),
                    ast::Suffix::Op(o, _) => format!("\"{}\"", o),
                    ast::Suffix::All(_) => return None,
                };
                match p {
                    Sym::Library(lib) => self.unit_sym(&lib, &key),
                    Sym::Package(pkg) => self.pkg_syms_pub(&pkg, &key).into_iter().next(),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// The subprograms or enumeration literals a name denotes (for an
    /// alias), or nothing when it denotes something else.
    fn overload_targets(&mut self, r: RegionId, n: &ast::Name) -> Vec<Sym> {
        let syms = match &n.kind {
            ast::NameKind::Simple(i) => self.lookup(r, &i.name),
            ast::NameKind::Op(o) => self.lookup(r, &format!("\"{}\"", o.to_ascii_lowercase())),
            ast::NameKind::Char(c) => self.lookup(r, &format!("'{}'", *c as char)),
            ast::NameKind::Selected(prefix, suffix) => {
                let key = match suffix {
                    ast::Suffix::Ident(i) => i.name.clone(),
                    ast::Suffix::Char(c, _) => format!("'{}'", *c as char),
                    ast::Suffix::Op(o, _) => format!("\"{}\"", o),
                    ast::Suffix::All(_) => return Vec::new(),
                };
                match self.name_sym(r, prefix) {
                    Some(Sym::Package(pkg)) => self.pkg_syms_pub(&pkg, &key),
                    _ => return Vec::new(),
                }
            }
            _ => return Vec::new(),
        };
        if syms
            .iter()
            .all(|s| matches!(s, Sym::Sub(_) | Sym::EnumLit(..)))
        {
            syms
        } else {
            Vec::new()
        }
    }

    /// Predefined functions named `name` for a signature's parameter types.
    fn predefined_alias_targets(
        &mut self,
        r: RegionId,
        name: &str,
        sig: Option<&ast::Signature>,
    ) -> Vec<Sym> {
        let Some(sig) = sig else { return Vec::new() };
        let mut sets = Vec::new();
        for m in &sig.params {
            let n = self.errors.len();
            let t = self.type_mark(r, m);
            self.errors.truncate(n);
            let Some(t) = t else { return Vec::new() };
            let b = self.base(t);
            sets.push(super::predefined::TypeSet::of(b));
        }
        self.predefined_funcs(name, &sets)
            .into_iter()
            .map(Sym::Sub)
            .collect()
    }

    /// Whether a subprogram matches a signature's type marks.
    fn signature_matches(&mut self, r: RegionId, s: &Sym, sig: Option<&ast::Signature>) -> bool {
        let Some(sig) = sig else { return true };
        match s {
            Sym::Sub(id) => {
                let params = self.subprograms[*id].params.clone();
                if params.len() != sig.params.len() {
                    return false;
                }
                for (p, m) in params.iter().zip(&sig.params) {
                    let n = self.errors.len();
                    let t = self.type_mark(r, m);
                    self.errors.truncate(n);
                    match t {
                        Some(t) if self.base(t) == self.base(self.objects[*p].ty) => {}
                        _ => return false,
                    }
                }
                match (&sig.ret, self.subprograms[*id].ret) {
                    (None, None) => true,
                    (Some(m), Some(rt)) => {
                        let n = self.errors.len();
                        let t = self.type_mark(r, m);
                        self.errors.truncate(n);
                        t.is_some_and(|t| self.base(t) == self.base(rt))
                    }
                    _ => false,
                }
            }
            Sym::EnumLit(t, _) => match &sig.ret {
                Some(m) => {
                    let n = self.errors.len();
                    let rt = self.type_mark(r, m);
                    self.errors.truncate(n);
                    rt.is_some_and(|rt| self.base(rt) == self.base(*t)) && sig.params.is_empty()
                }
                None => sig.params.is_empty(),
            },
            _ => false,
        }
    }

    pub fn pkg_syms_pub(&mut self, pkg: &super::PkgKey, name: &str) -> Vec<Sym> {
        let Some(region) = self.package_region(pkg) else {
            return Vec::new();
        };
        self.regions[region]
            .syms
            .get(name)
            .cloned()
            .unwrap_or_default()
    }

    /// The base type of a type or subtype.
    pub fn base(&self, mut t: TypeId) -> TypeId {
        while let TypeKind::Subtype { base, .. } = &self.types[t].kind {
            t = *base;
        }
        t
    }

    fn type_decl(&mut self, r: RegionId, td: &ast::TypeDecl, path: &str) {
        let name = td.name.name.clone();
        let loc = Some(self.loc(td.name.span.clone()));
        match &td.def {
            Some(ast::TypeDef::Protected {
                generics,
                generic_map,
                decls,
            }) => {
                if !generics.is_empty() || generic_map.is_some() {
                    self.error(
                        td.name.span.clone(),
                        "generics of protected types (VHDL-2019) are not supported yet",
                    );
                }
                for d in decls {
                    if let ast::Decl::Variable { obj, .. } = d {
                        self.error(
                            obj.span.clone(),
                            "private variables of protected types (VHDL-2019) are not supported yet",
                        );
                    }
                }
                self.protected_decl(r, &name, decls, loc, path);
                return;
            }
            Some(ast::TypeDef::ProtectedBody(decls)) => {
                self.protected_body(r, td, decls, path);
                return;
            }
            _ => {}
        }
        let Some(def) = &td.def else {
            let t = self.add_type(&name, TypeKind::Incomplete, None, loc);
            self.declare(r, &name, Sym::Type(t));
            return;
        };
        let t = match def {
            ast::TypeDef::Enum(lits) => {
                let mut names: Vec<String> = lits
                    .iter()
                    .map(|l| match l {
                        ast::EnumLit::Ident(i) => i.name.clone(),
                        ast::EnumLit::Char(c, _) => format!("'{}'", *c as char),
                    })
                    .collect();
                // The IEEE source of STANDARD writes the no-break space
                // (160) and soft hyphen (173) of CHARACTER as ' ' and '-';
                // they are the Latin-1 characters 0xA0 and 0xAD (§16.3).
                if name == "character" && names.len() == 256 && self.cur_lib == "std" {
                    names[160] = format!("'{}'", 0xA0u8 as char);
                    names[173] = format!("'{}'", 0xADu8 as char);
                }
                let n = names.len() as u32;
                let t = self.add_type(
                    &name,
                    TypeKind::Enum(names.clone()),
                    Some(StaticRange {
                        left: Value::Enum(0),
                        dir: Dir::To,
                        right: Value::Enum(n.saturating_sub(1)),
                    }),
                    loc,
                );
                for (i, l) in names.iter().enumerate() {
                    self.declare(r, l, Sym::EnumLit(t, i as u32));
                }
                t
            }
            ast::TypeDef::ImplementationDefined => match name.as_str() {
                "integer" => self.add_type(
                    &name,
                    TypeKind::Integer,
                    Some(StaticRange {
                        left: Value::Int(i32::MIN as i64),
                        dir: Dir::To,
                        right: Value::Int(i32::MAX as i64),
                    }),
                    loc,
                ),
                "real" => self.add_type(
                    &name,
                    TypeKind::Real,
                    Some(StaticRange {
                        left: Value::Real(-f64::MAX),
                        dir: Dir::To,
                        right: Value::Real(f64::MAX),
                    }),
                    loc,
                ),
                _ => {
                    self.error(td.span.clone(), "implementation-defined range");
                    return;
                }
            },
            ast::TypeDef::Range(re) => {
                let Some(hr) = self.range_expr(r, re, None) else {
                    return;
                };
                let real = matches!(
                    self.types[self.base(hr.left.ty)].kind,
                    TypeKind::Real | TypeKind::UniversalReal
                );
                let Some(sr) = hr.static_val.clone() else {
                    self.error(re.span(), "the range of a type must be static");
                    return;
                };
                let sr = if real {
                    StaticRange {
                        left: Value::Real(to_f64(&sr.left)),
                        dir: sr.dir,
                        right: Value::Real(to_f64(&sr.right)),
                    }
                } else {
                    sr
                };
                self.add_type(
                    &name,
                    if real {
                        TypeKind::Real
                    } else {
                        TypeKind::Integer
                    },
                    Some(sr),
                    loc,
                )
            }
            ast::TypeDef::Physical {
                range,
                primary,
                secondary,
            } => {
                let sr = match range {
                    ast::RangeExpr::Attr(n) if name_text(n) == "implementation_defined" => {
                        StaticRange {
                            left: Value::Phys(i64::MIN),
                            dir: Dir::To,
                            right: Value::Phys(i64::MAX),
                        }
                    }
                    re => {
                        let Some(hr) = self.range_expr(r, re, None) else {
                            return;
                        };
                        let Some(sr) = hr.static_val else {
                            self.error(re.span(), "the range of a type must be static");
                            return;
                        };
                        StaticRange {
                            left: Value::Phys(sr.left.as_i64().unwrap_or(0)),
                            dir: sr.dir,
                            right: Value::Phys(sr.right.as_i64().unwrap_or(0)),
                        }
                    }
                };
                let t = self.add_type(
                    &name,
                    TypeKind::Physical(vec![(primary.name.clone(), 1)]),
                    Some(sr),
                    loc,
                );
                self.declare(r, &primary.name, Sym::Unit(t, 1));
                for (u, lit) in secondary {
                    let v = match self.expr(r, lit, Some(t)).and_then(|h| self.eval(&h)) {
                        Some(Value::Phys(v)) => v,
                        _ => {
                            self.error(lit.span.clone(), "a unit's value must be static");
                            continue;
                        }
                    };
                    if let TypeKind::Physical(units) = &mut self.types[t].kind {
                        units.push((u.name.clone(), v));
                    }
                    self.declare(r, &u.name, Sym::Unit(t, v));
                }
                t
            }
            ast::TypeDef::Array { index, elem } => {
                let Some(elem_t) = self.subtype_ind(r, elem) else {
                    return;
                };
                match index {
                    ast::ArrayIndex::Unbounded(marks) => {
                        let mut idx = Vec::new();
                        for m in marks {
                            idx.push(self.type_mark(r, m).unwrap_or(self.std.integer));
                        }
                        self.add_type(
                            &name,
                            TypeKind::Array {
                                index: idx,
                                elem: elem_t,
                            },
                            None,
                            loc,
                        )
                    }
                    ast::ArrayIndex::Constrained(ranges) => {
                        // An anonymous unconstrained base type and the named
                        // constrained subtype (§5.3.2.1).
                        let mut idx = Vec::new();
                        let mut cons = Vec::new();
                        for dr in ranges {
                            let Some((it, hr)) = self.discrete_range(r, dr, None) else {
                                return;
                            };
                            idx.push(it);
                            cons.push(Some(hr));
                        }
                        let base = self.add_type(
                            &format!("{}'base", name),
                            TypeKind::Array {
                                index: idx,
                                elem: elem_t,
                            },
                            None,
                            loc.clone(),
                        );
                        self.add_type(
                            &name,
                            TypeKind::Subtype {
                                base,
                                constraint: Some(HConstraint::Index(cons, None)),
                                resolution: None,
                            },
                            None,
                            loc,
                        )
                    }
                }
            }
            ast::TypeDef::Record(fields) => {
                let mut fs = Vec::new();
                for (names, ind) in fields {
                    let Some(ft) = self.subtype_ind(r, ind) else {
                        return;
                    };
                    for n in names {
                        fs.push((n.name.clone(), ft));
                    }
                }
                self.add_type(&name, TypeKind::Record(fs), None, loc)
            }
            ast::TypeDef::Access(ind) => {
                // The designated type may be an incomplete type completed later.
                let Some(dt) = self.subtype_ind(r, ind) else {
                    return;
                };
                self.add_type(&name, TypeKind::Access(dt), None, loc)
            }
            ast::TypeDef::File(mark) => {
                let Some(ft) = self.type_mark(r, mark) else {
                    return;
                };
                self.add_type(&name, TypeKind::File(ft), None, loc)
            }
            ast::TypeDef::Protected { .. } | ast::TypeDef::ProtectedBody(_) => return,
        };
        // Completing an incomplete type declaration: reuse its id.
        if let Some(Sym::Type(prev)) = self.regions[r]
            .syms
            .get(&name)
            .and_then(|v| v.first())
            .cloned()
            && matches!(self.types[prev].kind, TypeKind::Incomplete)
        {
            self.types[prev] = self.types[t].clone();
            return;
        }
        self.declare(r, &name, Sym::Type(t));
        if let TypeKind::File(elem) = self.types[t].kind {
            self.file_ops(r, t, elem);
        }
    }

    /// A protected type declaration (§5.6.2): its methods, declared in a
    /// region of their own.
    fn protected_decl(
        &mut self,
        r: RegionId,
        name: &str,
        decls: &[ast::Decl],
        loc: Option<Loc>,
        path: &str,
    ) {
        let t = self.add_type(name, TypeKind::Protected, None, loc);
        self.declare(r, name, Sym::Type(t));
        let pr = self.new_region(Some(r));
        self.protected.insert(
            t,
            super::ProtInfo {
                decl_region: pr,
                vars: Vec::new(),
                has_body: false,
            },
        );
        let saved = self.cur_prot.replace(t);
        let mut objs = Vec::new();
        let mut subs = Vec::new();
        self.decls(
            pr,
            decls,
            &mut objs,
            &mut subs,
            &format!("{}.{}", path, name),
        );
        self.cur_prot = saved;
    }

    /// A protected type body (§5.6.3): the variables each object of the
    /// type has, and the bodies of its methods (and private subprograms).
    fn protected_body(&mut self, r: RegionId, td: &ast::TypeDecl, decls: &[ast::Decl], path: &str) {
        let name = td.name.name.clone();
        let t = match self.lookup(r, &name).first() {
            Some(Sym::Type(t)) if matches!(self.types[*t].kind, TypeKind::Protected) => *t,
            _ => {
                self.error(
                    td.name.span.clone(),
                    format!("no protected type declaration '{}' for this body", name),
                );
                return;
            }
        };
        let Some(info) = self.protected.get(&t).cloned() else {
            return;
        };
        // The body sees its own context and the declaration's methods.
        let br = self.new_region(Some(r));
        let methods: Vec<(String, Vec<Sym>)> = self.regions[info.decl_region]
            .syms
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        for (k, v) in methods {
            for sym in v {
                self.declare(br, &k, sym);
            }
        }
        let saved = self.cur_prot.replace(t);
        let mut objs = Vec::new();
        let mut subs = Vec::new();
        self.decls(
            br,
            decls,
            &mut objs,
            &mut subs,
            &format!("{}.{}", path, name),
        );
        self.cur_prot = saved;
        let vars: Vec<ObjId> = objs
            .into_iter()
            .filter(|o| matches!(self.objects[*o].kind, ObjKind::Variable))
            .collect();
        for v in &vars {
            self.prot_vars.insert(*v, t);
        }
        if let Some(p) = self.protected.get_mut(&t) {
            p.vars = vars;
            p.has_body = true;
        }
    }

    /// The operations a file type declaration implicitly declares (§5.5.2):
    /// FILE_OPEN (with and without a status), FILE_CLOSE, READ (with a
    /// LENGTH for an unconstrained array), WRITE, FLUSH and ENDFILE.
    fn file_ops(&mut self, r: RegionId, ft: TypeId, elem: TypeId) {
        let std = self.std.clone();
        let loc = Loc {
            file: 0,
            span: 0..0,
        };
        let read_mode = lit_expr(Value::Enum(0), std.file_open_kind, loc.clone());
        let f = ("f", ObjClass::File, Mode::In, ft, None);
        let name = (
            "external_name",
            ObjClass::Constant,
            Mode::In,
            std.string,
            None,
        );
        let kind = (
            "open_kind",
            ObjClass::Constant,
            Mode::In,
            std.file_open_kind,
            Some(read_mode),
        );
        let status = (
            "status",
            ObjClass::Variable,
            Mode::Out,
            std.file_open_status,
            None,
        );
        let value_out = ("value", ObjClass::Variable, Mode::Out, elem, None);
        let value_in = ("value", ObjClass::Constant, Mode::In, elem, None);
        let length = ("length", ObjClass::Variable, Mode::Out, std.natural, None);
        let mut subs = vec![
            (
                "file_open",
                vec![f.clone(), name.clone(), kind.clone()],
                None,
                Builtin::FileOpen,
            ),
            (
                "file_open",
                vec![status, f.clone(), name, kind],
                None,
                Builtin::FileOpen,
            ),
            ("file_close", vec![f.clone()], None, Builtin::FileClose),
            ("write", vec![f.clone(), value_in], None, Builtin::Write),
            ("flush", vec![f.clone()], None, Builtin::Flush),
            (
                "endfile",
                vec![f.clone()],
                Some(std.boolean),
                Builtin::EndFile,
            ),
        ];
        if self.constrained(elem) {
            subs.push(("read", vec![f, value_out], None, Builtin::Read));
        } else {
            subs.push(("read", vec![f, value_out, length], None, Builtin::Read));
        }
        for (sub, params, ret, builtin) in subs {
            let mut pids = Vec::new();
            for (pn, class, mode, ty, init) in params {
                pids.push(self.add_obj(ObjInfo {
                    name: pn.to_string(),
                    kind: ObjKind::Param(class, mode),
                    ty,
                    init,
                    loc: loc.clone(),
                    static_val: None,
                }));
            }
            let id = self.add_sub(SubInfo {
                name: sub.to_string(),
                is_function: ret.is_some(),
                pure: false,
                params: pids,
                ret,
                builtin: Some(builtin),
                body: None,
                loc: None,
                path: format!("<file>.{}", sub),
            });
            self.declare(r, sub, Sym::Sub(id));
        }
    }

    /// A subtype indication (§6.3): a type mark with an optional constraint
    /// and resolution function. Returns the type mark itself when neither is
    /// given, else a new anonymous subtype.
    pub fn subtype_ind(&mut self, r: RegionId, ind: &ast::SubtypeInd) -> Option<TypeId> {
        let mark = self.type_mark(r, &ind.mark)?;
        let resolution = match &ind.resolution {
            None => None,
            Some(ast::Resolution::Function(n)) => self.resolution_function(r, n, mark),
            Some(ast::Resolution::Element(inner)) => {
                if let ast::Resolution::Function(n) = inner.as_ref() {
                    // `(resolved) std_ulogic_vector`: resolve each element.
                    let elem = match &self.types[self.base(mark)].kind {
                        TypeKind::Array { elem, .. } => *elem,
                        _ => {
                            self.error(ind.span.clone(), "element resolution needs an array type");
                            return None;
                        }
                    };
                    let f = self.resolution_function(r, n, elem);
                    let elem_t = self.add_type(
                        "",
                        TypeKind::Subtype {
                            base: elem,
                            constraint: None,
                            resolution: f,
                        },
                        None,
                        None,
                    );
                    return Some(self.add_type(
                        "",
                        TypeKind::Subtype {
                            base: mark,
                            constraint: Some(HConstraint::Index(Vec::new(), Some(elem_t))),
                            resolution: None,
                        },
                        None,
                        None,
                    ));
                }
                None
            }
            Some(ast::Resolution::Record(_)) => {
                self.error(ind.span.clone(), "record resolution is not supported yet");
                None
            }
        };
        let constraint = match &ind.constraint {
            None => None,
            Some(c) => Some(self.constraint(r, mark, c, ind.span.clone())?),
        };
        if constraint.is_none() && resolution.is_none() {
            return Some(mark);
        }
        Some(self.add_type(
            "",
            TypeKind::Subtype {
                base: mark,
                constraint,
                resolution,
            },
            None,
            None,
        ))
    }

    fn resolution_function(&mut self, r: RegionId, n: &ast::Name, elem: TypeId) -> Option<SubId> {
        let key = match &n.kind {
            ast::NameKind::Simple(i) => i.name.clone(),
            ast::NameKind::Selected(_, ast::Suffix::Ident(i)) => i.name.clone(),
            _ => {
                self.error(n.span.clone(), "a resolution function name was expected");
                return None;
            }
        };
        let cands: Vec<SubId> = match &n.kind {
            ast::NameKind::Simple(_) => self.lookup(r, &key),
            _ => match self.name_sym_prefix_pkg(r, n) {
                Some(pkg) => self.pkg_syms_pub(&pkg, &key),
                None => Vec::new(),
            },
        }
        .into_iter()
        .filter_map(|s| match s {
            Sym::Sub(id) => Some(id),
            _ => None,
        })
        .collect();
        let base = self.base(elem);
        let f = cands.into_iter().find(|&f| {
            self.subprograms[f]
                .ret
                .is_some_and(|rt| self.base(rt) == base)
                && self.subprograms[f].params.len() == 1
        });
        if f.is_none() {
            self.error(
                n.span.clone(),
                "no resolution function of this name for the type",
            );
        }
        f
    }

    fn name_sym_prefix_pkg(&mut self, r: RegionId, n: &ast::Name) -> Option<super::PkgKey> {
        if let ast::NameKind::Selected(prefix, _) = &n.kind
            && let Some(Sym::Package(p)) = self.name_sym(r, prefix)
        {
            return Some(p);
        }
        None
    }

    fn constraint(
        &mut self,
        r: RegionId,
        mark: TypeId,
        c: &ast::Constraint,
        span: ast::Span,
    ) -> Option<HConstraint> {
        let base = self.base(mark);
        match c {
            ast::Constraint::Range(re) => {
                let hr = self.range_expr(r, re, Some(base))?;
                Some(HConstraint::Range(hr))
            }
            ast::Constraint::Paren(groups) => {
                let (index, elem) = match &self.types[base].kind {
                    TypeKind::Array { index, elem } => (index.clone(), *elem),
                    TypeKind::Record(fields) => {
                        return self.record_constraint(r, &fields.clone(), groups, span);
                    }
                    _ => {
                        self.error(span, "an index constraint needs an array type");
                        return None;
                    }
                };
                let (first, rest) = groups.split_first()?;
                if first.len() != index.len() {
                    self.error(span, "wrong number of index ranges");
                    return None;
                }
                let mut ranges = Vec::new();
                for (a, it) in first.iter().zip(&index) {
                    match &a.actual {
                        ast::Actual::Open(_) => ranges.push(None),
                        ast::Actual::Expr(e) => {
                            let dr = expr_to_discrete_range(e);
                            let (_, hr) = self.discrete_range(r, &dr, Some(*it))?;
                            ranges.push(Some(hr));
                        }
                    }
                }
                let elem_t = if rest.is_empty() {
                    None
                } else {
                    let ec =
                        self.constraint(r, elem, &ast::Constraint::Paren(rest.to_vec()), span)?;
                    Some(self.add_type(
                        "",
                        TypeKind::Subtype {
                            base: elem,
                            constraint: Some(ec),
                            resolution: None,
                        },
                        None,
                        None,
                    ))
                };
                Some(HConstraint::Index(ranges, elem_t))
            }
        }
    }

    /// A record constraint (§5.3.3): element names with constraints of
    /// their (unconstrained) subtypes, `rec(a(3 downto 0), s(1 to 3))`.
    fn record_constraint(
        &mut self,
        r: RegionId,
        fields: &[(String, TypeId)],
        groups: &[Vec<ast::Assoc>],
        span: ast::Span,
    ) -> Option<HConstraint> {
        let [group] = groups else {
            self.error(
                span,
                "a record constraint is one list of element constraints",
            );
            return None;
        };
        let mut out = Vec::new();
        for a in group {
            let ast::Actual::Expr(ast::Expr {
                kind: ast::ExprKind::Name(n),
                ..
            }) = &a.actual
            else {
                self.error(a.span.clone(), "an element constraint was expected");
                return None;
            };
            // `e(c)` or `e(c)(c2)`: the element name and its constraints.
            let mut lists = Vec::new();
            let mut cur = n;
            while let ast::NameKind::Call(p, args) = &cur.kind {
                lists.push(args.clone());
                cur = p;
            }
            lists.reverse();
            let ast::NameKind::Simple(id) = &cur.kind else {
                self.error(a.span.clone(), "an element constraint was expected");
                return None;
            };
            let Some(k) = fields.iter().position(|(f, _)| *f == id.name) else {
                self.error(id.span.clone(), format!("no record element '{}'", id.name));
                return None;
            };
            let ft = fields[k].1;
            let c = self.constraint(r, ft, &ast::Constraint::Paren(lists), a.span.clone())?;
            let st = self.add_type(
                "",
                TypeKind::Subtype {
                    base: ft,
                    constraint: Some(c),
                    resolution: None,
                },
                None,
                None,
            );
            out.push((k, st));
        }
        Some(HConstraint::Record(out))
    }

    /// The elements of a record (sub)type with their subtypes: those of
    /// record constraints in place of the declared ones (§5.3.3).
    pub fn record_fields(&self, t: TypeId) -> Vec<(String, TypeId)> {
        let mut cur = t;
        let mut cons: Vec<(usize, TypeId)> = Vec::new();
        loop {
            match &self.types[cur].kind {
                TypeKind::Subtype {
                    base, constraint, ..
                } => {
                    if let Some(HConstraint::Record(c)) = constraint {
                        for (k, st) in c {
                            if !cons.iter().any(|(j, _)| j == k) {
                                cons.push((*k, *st));
                            }
                        }
                    }
                    cur = *base;
                }
                TypeKind::Record(fields) => {
                    let mut f = fields.clone();
                    for (k, st) in cons {
                        f[k].1 = st;
                    }
                    return f;
                }
                _ => return Vec::new(),
            }
        }
    }

    /// A discrete range and its type: `0 to 3`, `t'range`, `natural`,
    /// `integer range 0 to 7`.
    pub fn discrete_range(
        &mut self,
        r: RegionId,
        dr: &ast::DiscreteRange,
        expect: Option<TypeId>,
    ) -> Option<(TypeId, HRange)> {
        match dr {
            ast::DiscreteRange::Range(re) => {
                let hr = self.range_expr(r, re, expect)?;
                // §5.3.2.2: universal_integer bounds of a discrete range
                // are of type INTEGER.
                let t = match &self.types[self.base(hr.left.ty)].kind {
                    TypeKind::UniversalInteger => self.std.integer,
                    _ => hr.left.ty,
                };
                Some((t, hr))
            }
            ast::DiscreteRange::Subtype(ind) => {
                let t = self.subtype_ind(r, ind)?;
                let hr = self.type_range(t, ind.span.clone())?;
                Some((t, hr))
            }
        }
    }

    /// The range of a scalar (sub)type as an `HRange`.
    pub fn type_range(&mut self, t: TypeId, span: ast::Span) -> Option<HRange> {
        // The nearest range constraint; a non-static one is its
        // expression (`integer range 0 to a'length - 1`).
        let mut cur = t;
        loop {
            match &self.types[cur].kind {
                TypeKind::Subtype {
                    constraint: Some(HConstraint::Range(hr)),
                    ..
                } => {
                    if hr.static_val.is_none() {
                        return Some(hr.clone());
                    }
                    break;
                }
                TypeKind::Subtype { base, .. } => cur = *base,
                _ => break,
            }
        }
        let sr = self.scalar_range(t);
        match sr {
            Some(sr) => {
                let loc = self.loc(span);
                Some(HRange {
                    left: Box::new(lit_expr(sr.left.clone(), t, loc.clone())),
                    dir: sr.dir,
                    right: Box::new(lit_expr(sr.right.clone(), t, loc)),
                    static_val: Some(sr),
                    of_obj: None,
                })
            }
            None => {
                // A non-static constraint: its expression.
                let mut cur = t;
                loop {
                    match &self.types[cur].kind {
                        TypeKind::Subtype {
                            constraint: Some(HConstraint::Range(hr)),
                            ..
                        } => return Some(hr.clone()),
                        TypeKind::Subtype { base, .. } => cur = *base,
                        _ => {
                            self.error(span, "a discrete subtype was expected");
                            return None;
                        }
                    }
                }
            }
        }
    }

    /// The static range of a scalar (sub)type, if static.
    pub fn scalar_range(&self, t: TypeId) -> Option<StaticRange> {
        let mut cur = t;
        loop {
            match &self.types[cur].kind {
                TypeKind::Subtype {
                    constraint: Some(HConstraint::Range(hr)),
                    ..
                } => return hr.static_val.clone(),
                TypeKind::Subtype { base, .. } => cur = *base,
                _ => return self.types[cur].range.clone(),
            }
        }
    }

    // ---- objects ------------------------------------------------------------------

    fn object_decl(&mut self, r: RegionId, o: &ast::ObjectDecl, kind: ObjKind) -> Vec<ObjId> {
        let Some(ty) = self.subtype_ind(r, &o.ty) else {
            return Vec::new();
        };
        let init = o.value.as_ref().and_then(|v| self.expr(r, v, Some(ty)));
        let static_val = match (kind, &init) {
            (ObjKind::Constant, Some(i)) => self.eval_static(i),
            _ => None,
        };
        let mut out = Vec::new();
        for n in &o.names {
            // A deferred constant's full declaration (package body).
            if kind == ObjKind::Constant
                && let Some(prev) = self.deferred_constant(r, &n.name)
            {
                self.objects[prev].init = init.clone();
                self.objects[prev].static_val = static_val.clone();
                out.push(prev);
                continue;
            }
            let id = self.add_obj(ObjInfo {
                name: n.name.clone(),
                kind,
                ty,
                init: init.clone(),
                loc: self.loc(n.span.clone()),
                static_val: static_val.clone(),
            });
            self.declare(r, &n.name, Sym::Obj(id));
            out.push(id);
        }
        out
    }

    /// A constant declared without a value in the enclosing package.
    fn deferred_constant(&mut self, r: RegionId, name: &str) -> Option<ObjId> {
        let parent = self.regions[r].parent?;
        match self.regions[parent].syms.get(name)?.first()? {
            Sym::Obj(o)
                if self.objects[*o].kind == ObjKind::Constant
                    && self.objects[*o].init.is_none() =>
            {
                Some(*o)
            }
            _ => None,
        }
    }

    /// Generic, port or parameter list: objects declared in `r`.
    pub fn interface_list(
        &mut self,
        r: RegionId,
        list: &[ast::InterfaceDecl],
        kind: IfaceKind,
        _path: &str,
    ) -> Vec<ObjId> {
        let mut out = Vec::new();
        for d in list {
            match d {
                ast::InterfaceDecl::Object(o) => {
                    let Some(ty) = self.subtype_ind(r, &o.ty) else {
                        continue;
                    };
                    let default = o.default.as_ref().and_then(|v| self.expr(r, v, Some(ty)));
                    let mode = o.mode.unwrap_or(Mode::In);
                    let okind = match kind {
                        IfaceKind::Generic => ObjKind::Generic,
                        IfaceKind::Port => ObjKind::Port(mode),
                        IfaceKind::Param { function } => {
                            let class = match o.class {
                                Some(c) => c,
                                None if mode == Mode::In || function => ObjClass::Constant,
                                None => ObjClass::Variable,
                            };
                            ObjKind::Param(class, mode)
                        }
                    };
                    let static_val = default.as_ref().and_then(|e| self.eval(e));
                    for n in &o.names {
                        let id = self.add_obj(ObjInfo {
                            name: n.name.clone(),
                            kind: okind,
                            ty,
                            init: default.clone(),
                            loc: self.loc(n.span.clone()),
                            static_val: if okind == ObjKind::Generic {
                                static_val.clone()
                            } else {
                                None
                            },
                        });
                        self.declare(r, &n.name, Sym::Obj(id));
                        out.push(id);
                    }
                }
                // The class of a generic type (VHDL-2019) is not checked
                // against the actual yet; operations on the type resolve
                // when the unit is analysed with its actual bound.
                ast::InterfaceDecl::Type(i, _) => {
                    // A generic type (§6.5.3): the instance's actual type, or
                    // an incomplete type while there is none.
                    let t = match self.type_binding.iter().find(|(n, _)| *n == i.name) {
                        Some((_, t)) => *t,
                        None => self.add_type(
                            &i.name,
                            TypeKind::Incomplete,
                            None,
                            Some(self.loc(i.span.clone())),
                        ),
                    };
                    self.declare(r, &i.name, Sym::Type(t));
                }
                ast::InterfaceDecl::Subprogram { spec, .. } => {
                    self.error(
                        spec.span.clone(),
                        "generic subprograms are not supported yet",
                    );
                }
                ast::InterfaceDecl::Package { span, .. } => {
                    self.error(span.clone(), "generic packages are not supported yet");
                }
            }
        }
        out
    }

    // ---- subprograms --------------------------------------------------------------

    /// The key a subprogram is declared under: its name, or `"op"`.
    pub fn designator_key(d: &ast::Designator) -> String {
        match d {
            ast::Designator::Ident(i) => i.name.clone(),
            ast::Designator::Op(o, _) => format!("\"{}\"", o),
        }
    }

    /// Declare a subprogram (its specification); returns its id. The
    /// parameters live in a region of their own, child of `r`.
    pub fn subprogram_spec(
        &mut self,
        r: RegionId,
        spec: &ast::SubprogramSpec,
        path: &str,
    ) -> Option<SubId> {
        let (id, _) = self.subprogram_spec_region(r, spec, path)?;
        Some(id)
    }

    fn subprogram_spec_region(
        &mut self,
        r: RegionId,
        spec: &ast::SubprogramSpec,
        path: &str,
    ) -> Option<(SubId, RegionId)> {
        if !spec.generics.is_empty() {
            self.error(
                spec.span.clone(),
                "generic subprograms are not supported yet",
            );
            return None;
        }
        let pr = self.new_region(Some(r));
        let (is_function, pure, ret) = match &spec.kind {
            ast::SubprogramKind::Function { pure, ret } => {
                (true, *pure, Some(self.type_mark(r, ret)?))
            }
            ast::SubprogramKind::Procedure => (false, true, None),
        };
        let mut params = self.interface_list(
            pr,
            &spec.params,
            IfaceKind::Param {
                function: is_function,
            },
            path,
        );
        let name = Self::designator_key(&spec.designator);
        // A method of a protected type: the object is a hidden first
        // parameter (a VHDL name cannot end with '_').
        let method = self.cur_prot;
        if let Some(t) = method {
            let o = self.add_obj(ObjInfo {
                name: "self_".into(),
                kind: ObjKind::Param(ObjClass::Variable, Mode::In),
                ty: t,
                init: None,
                loc: self.loc(spec.designator.span()),
                static_val: None,
            });
            self.declare(pr, "self_", Sym::Obj(o));
            params.insert(0, o);
        }
        let id = self.add_sub(SubInfo {
            name: name.clone(),
            is_function,
            pure,
            params,
            ret,
            builtin: None,
            body: None,
            loc: Some(self.loc(spec.designator.span())),
            path: format!("{}.{}", path, name),
        });
        // std.env / std.textio / std.standard subprograms without VHDL bodies
        // are native.
        if path.starts_with("std.") {
            self.subprograms[id].builtin = super::predefined::native_builtin(path, &name);
        }
        if let Some(t) = method {
            self.method_of.insert(id, t);
            self.method_keys
                .entry(format!("<m{}:{}>", t, name))
                .or_default()
                .push(id);
        }
        self.declare(r, &name, Sym::Sub(id));
        Some((id, pr))
    }

    /// Whether two subprograms have the same parameter and result type
    /// profile (§4.5.1).
    pub(super) fn same_profile(&self, a: SubId, b: SubId) -> bool {
        let (sa, sb) = (&self.subprograms[a], &self.subprograms[b]);
        sa.is_function == sb.is_function
            && sa.params.len() == sb.params.len()
            && sa.ret.map(|t| self.base(t)) == sb.ret.map(|t| self.base(t))
            && sa
                .params
                .iter()
                .zip(&sb.params)
                .all(|(x, y)| self.base(self.objects[*x].ty) == self.base(self.objects[*y].ty))
    }

    pub(super) fn subprogram_body(
        &mut self,
        r: RegionId,
        b: &ast::SubprogramBody,
        path: &str,
    ) -> Option<SubId> {
        let key = Self::designator_key(&b.spec.designator);
        // The specification this body completes: same profile, declared in
        // this region or the enclosing package declaration.
        let (new_id, pr) = self.subprogram_spec_region(r, &b.spec, path)?;
        let mut target = new_id;
        let mut cands: Vec<SubId> = Vec::new();
        let mut reg = Some(r);
        for _ in 0..2 {
            let Some(rr) = reg else { break };
            if let Some(v) = self.regions[rr].syms.get(&key) {
                cands.extend(v.iter().filter_map(|s| match s {
                    Sym::Sub(id) if *id != new_id => Some(*id),
                    _ => None,
                }));
            }
            reg = self.regions[rr].parent;
        }
        if let Some(prev) = cands
            .into_iter()
            .find(|&c| self.same_profile(c, new_id) && self.subprograms[c].body.is_none())
        {
            // Use the declaration's parameter objects in the body.
            let decl_params = self.subprograms[prev].params.clone();
            for (p, dp) in self.subprograms[new_id]
                .params
                .clone()
                .into_iter()
                .zip(&decl_params)
            {
                let name = self.objects[p].name.clone();
                if let Some(v) = self.regions[pr].syms.get_mut(&name) {
                    *v = vec![Sym::Obj(*dp)];
                }
            }
            // Remove the duplicate declaration of the body's specification.
            if let Some(v) = self.regions[r].syms.get_mut(&key) {
                v.retain(|s| *s != Sym::Sub(new_id));
            }
            if let Some(t) = self.method_of.remove(&new_id)
                && let Some(v) = self.method_keys.get_mut(&format!("<m{}:{}>", t, key))
            {
                v.retain(|s| *s != new_id);
            }
            target = prev;
        }
        let sub_path = format!("{}.{}", path, key);
        // Subprograms of the standard libraries are analysed when the design
        // calls them (`analyze_reachable_bodies`): unused library code — some
        // of it needing features not supported yet — never blocks a design.
        if matches!(self.cur_lib.as_str(), "std" | "ieee") {
            self.lazy_bodies.insert(
                target,
                super::LazyBody {
                    body: b.clone(),
                    region: pr,
                    path: sub_path,
                    lib: self.cur_lib.clone(),
                    file: self.cur_file,
                },
            );
            return Some(target);
        }
        self.analyze_body(target, pr, b, &sub_path);
        Some(target)
    }

    /// Analyse a subprogram body in its parameter region.
    pub fn analyze_body(
        &mut self,
        target: SubId,
        pr: RegionId,
        b: &ast::SubprogramBody,
        sub_path: &str,
    ) {
        let body_r = self.new_region(Some(pr));
        let mut locals = Vec::new();
        let mut subs = Vec::new();
        // Subprograms declared in a method's body are not methods.
        let saved = self.cur_prot.take();
        self.decls(body_r, &b.decls, &mut locals, &mut subs, sub_path);
        self.cur_prot = saved;
        let ret = self.subprograms[target].ret;
        let stmts = self.seq_stmts(body_r, &b.stmts, &stmt_ctx_fn(ret));
        self.subprograms[target].body = Some(Body { locals, stmts });
    }

    // ---- architectures -------------------------------------------------------------

    pub fn architecture(
        &mut self,
        r: RegionId,
        ent: &EntityInfo,
        a: &ast::ArchBody,
    ) -> Architecture {
        let path = format!("{}.{}.{}", ent.library, ent.name, a.name.name);
        let mut objs = Vec::new();
        let mut subs = Vec::new();
        self.decls(r, &a.decls, &mut objs, &mut subs, &path);
        let mut arch = Architecture {
            entity: ent.name.clone(),
            name: a.name.name.clone(),
            library: ent.library.clone(),
            generics: ent.generics.clone(),
            ports: ent.ports.clone(),
            signals: objs
                .iter()
                .copied()
                .filter(|&o| self.objects[o].kind == ObjKind::Signal)
                .collect(),
            constants: objs
                .iter()
                .copied()
                .filter(|&o| self.objects[o].kind != ObjKind::Signal)
                .collect(),
            processes: Vec::new(),
            instances: Vec::new(),
            nested: false,
            foreign: Vec::new(),
            loc: self.loc(a.name.span.clone()),
        };
        for s in &a.stmts {
            self.conc_stmt(r, s, &mut arch);
        }
        arch
    }
}

/// Statement context of a subprogram body: its result type (`None` for a
/// procedure).
pub fn stmt_ctx_fn(ret: Option<TypeId>) -> super::stmt::StmtCtx {
    super::stmt::StmtCtx {
        in_process: false,
        sensitized: false,
        ret,
    }
}

/// `x(3 downto 0)`'s association actual as a discrete range.
pub fn expr_to_discrete_range(e: &ast::Expr) -> ast::DiscreteRange {
    match &e.kind {
        ast::ExprKind::Range(r) => ast::DiscreteRange::Range((**r).clone()),
        ast::ExprKind::Name(n) => match &n.kind {
            ast::NameKind::Attribute(..) => {
                ast::DiscreteRange::Range(ast::RangeExpr::Attr(n.clone()))
            }
            _ => ast::DiscreteRange::Subtype(ast::SubtypeInd {
                resolution: None,
                mark: n.clone(),
                constraint: None,
                span: n.span.clone(),
            }),
        },
        _ => ast::DiscreteRange::Range(ast::RangeExpr::Explicit {
            left: Box::new(e.clone()),
            dir: Dir::To,
            right: Box::new(e.clone()),
            span: e.span.clone(),
        }),
    }
}

pub fn name_text(n: &ast::Name) -> String {
    match &n.kind {
        ast::NameKind::Simple(i) => i.name.clone(),
        ast::NameKind::Selected(p, s) => format!(
            "{}.{}",
            name_text(p),
            match s {
                ast::Suffix::Ident(i) => i.name.clone(),
                ast::Suffix::Char(c, _) => format!("'{}'", *c as char),
                ast::Suffix::Op(o, _) => format!("\"{}\"", o),
                ast::Suffix::All(_) => "all".into(),
            }
        ),
        ast::NameKind::Op(o) => format!("\"{}\"", o.to_ascii_lowercase()),
        ast::NameKind::Char(c) => format!("'{}'", *c as char),
        ast::NameKind::Call(p, _) => name_text(p),
        ast::NameKind::Attribute(p, a, _) => format!("{}'{}", name_text(p), a.name),
        ast::NameKind::External { path, .. } => path.clone(),
    }
}

/// The object a name denotes, through indexing, slicing and selection.
pub fn root_obj(h: &HExpr) -> Option<ObjId> {
    match &h.kind {
        HExprKind::Obj(o) => Some(*o),
        HExprKind::Index(b, _) | HExprKind::Slice(b, _) | HExprKind::Field(b, _) => root_obj(b),
        _ => None,
    }
}

pub fn lit_expr(v: Value, ty: TypeId, loc: Loc) -> HExpr {
    HExpr {
        kind: HExprKind::Lit(v),
        ty,
        loc,
    }
}

pub fn to_f64(v: &Value) -> f64 {
    match v {
        Value::Real(r) => *r,
        Value::Int(i) | Value::Phys(i) => *i as f64,
        Value::Enum(e) => *e as f64,
        _ => 0.0,
    }
}
