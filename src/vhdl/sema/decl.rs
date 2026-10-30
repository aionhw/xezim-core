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
            ast::Decl::View(vd) => self.view_decl(r, vd),
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
        if let ast::NameKind::Attribute(prefix, attr, param) = &n.kind {
            return self.type_attribute(r, prefix, &attr.name, param.as_deref(), n.span.clone());
        }
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

    /// A type mark that is an attribute: `x'subtype` (§16.2.2, of an object
    /// or a type), `t'base`, `a'element`, and VHDL-2019's
    /// `p'designated_subtype` (an access type's) and `a'index(n)` (the
    /// index subtype of dimension n, 1 by default).
    fn type_attribute(
        &mut self,
        r: RegionId,
        prefix: &ast::Name,
        attr: &str,
        param: Option<&ast::Expr>,
        span: ast::Span,
    ) -> Option<TypeId> {
        // The prefix: a type or subtype, else an object (its subtype).
        let n = self.errors.len();
        let t = match self.name_sym(r, prefix) {
            Some(Sym::Type(t)) => t,
            _ => {
                self.errors.truncate(n);
                let e = ast::Expr {
                    kind: ast::ExprKind::Name(prefix.clone()),
                    span: prefix.span.clone(),
                };
                self.expr(r, &e, None)?.ty
            }
        };
        let base = self.base(t);
        match attr {
            "subtype" => Some(t),
            "base" => Some(base),
            "element" => match self.element_subtype(t) {
                Some(e) => Some(e),
                None => {
                    self.error(span, "'element needs an array type");
                    None
                }
            },
            "designated_subtype" => match self.types[base].kind {
                TypeKind::Access(d) => Some(d),
                _ => {
                    self.error(span, "'designated_subtype needs an access type");
                    None
                }
            },
            "index" => {
                let TypeKind::Array { index, .. } = self.types[base].kind.clone() else {
                    self.error(span, "'index needs an array type");
                    return None;
                };
                let dim = match param {
                    None => 1,
                    Some(p) => {
                        let h = self.expr(r, p, Some(self.std.integer))?;
                        match self.eval(&h).and_then(|v| v.as_i64()) {
                            Some(d) => d,
                            None => {
                                self.error(p.span.clone(), "the dimension of 'index must be static");
                                return None;
                            }
                        }
                    }
                };
                match usize::try_from(dim - 1).ok().and_then(|i| index.get(i)) {
                    Some(t) => Some(*t),
                    None => {
                        self.error(span, format!("the array has no dimension {}", dim));
                        None
                    }
                }
            }
            _ => {
                self.error(span, format!("'{} is not a type", attr));
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
                let mut params = self.subprograms[*id].params.clone();
                // A method's hidden object parameter is not in a signature.
                if self.method_of.contains_key(id) && !params.is_empty() {
                    params.remove(0);
                }
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
            // A generic protected type (VHDL-2019 §5.6.2): its declaration is
            // analysed for each instance, with the generics bound; with a
            // generic map it is its own instance.
            Some(ast::TypeDef::Protected {
                generics,
                generic_map,
                decls,
            }) if !generics.is_empty() => {
                let g = self.add_type(&name, TypeKind::Protected, None, loc.clone());
                self.generic_prots.insert(
                    g,
                    super::generics::GenericProt {
                        name: name.clone(),
                        region: r,
                        generics: generics.clone(),
                        decls: decls.clone(),
                        lib: self.cur_lib.clone(),
                        file: self.cur_file,
                        body: None,
                        pending: Vec::new(),
                    },
                );
                match generic_map {
                    Some(gm) => {
                        self.protected_instance(r, &name, g, gm, loc, path);
                    }
                    None => self.declare(r, &name, Sym::Type(g)),
                }
                return;
            }
            Some(ast::TypeDef::Protected { decls, .. }) => {
                self.protected_decl(r, &name, decls, loc, path);
                return;
            }
            Some(ast::TypeDef::ProtectedInst { base, generic_map }) => {
                let Some(g) = self.type_mark(r, base) else {
                    return;
                };
                if !self.generic_prots.contains_key(&g) {
                    self.error(base.span.clone(), "not a generic protected type");
                    return;
                }
                self.protected_instance(r, &name, g, generic_map, loc, path);
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
            ast::TypeDef::Protected { .. }
            | ast::TypeDef::ProtectedBody(_)
            | ast::TypeDef::ProtectedInst { .. } => return,
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
        // Completing an incomplete type declaration (§5.4.2): its id.
        let prev = match self.regions[r].syms.get(name).and_then(|v| v.first()) {
            Some(Sym::Type(p)) if matches!(self.types[*p].kind, TypeKind::Incomplete) => Some(*p),
            _ => None,
        };
        let t = match prev {
            Some(p) => {
                self.types[p].kind = TypeKind::Protected;
                p
            }
            None => {
                let t = self.add_type(name, TypeKind::Protected, None, loc);
                self.declare(r, name, Sym::Type(t));
                t
            }
        };
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
        let decls = self.private_method_aliases(r, t, decls);
        self.decls(
            pr,
            &decls,
            &mut objs,
            &mut subs,
            &format!("{}.{}", path, name),
        );
        self.cur_prot = saved;
        // Private variables (VHDL-2019 §5.6.2): variables of each object of
        // the type, like the body's, visible to the body and to the
        // declaration's aliases but not outside.
        let private: Vec<ObjId> = objs
            .into_iter()
            .filter(|o| matches!(self.objects[*o].kind, ObjKind::Variable))
            .collect();
        for v in &private {
            self.prot_vars.insert(*v, t);
        }
        if let Some(p) = self.protected.get_mut(&t) {
            p.vars = private;
        }
    }

    /// The declarations of a protected type declaration with each alias of
    /// a method of one of its private variables (`alias get is v.get
    /// [return integer]`, VHDL-2019) as a method of the type that calls it
    /// (its body goes to `prot_forwards`, for the type's body): calling the
    /// alias on an object calls the method of that object's variable.
    fn private_method_aliases(&mut self, r: RegionId, t: TypeId, decls: &[ast::Decl]) -> Vec<ast::Decl> {
        let mut out = Vec::new();
        for d in decls {
            let ast::Decl::Alias {
                name,
                target,
                signature: Some(sig),
                span,
                ..
            } = d
            else {
                out.push(d.clone());
                continue;
            };
            let ast::NameKind::Selected(prefix, ast::Suffix::Ident(method)) = &target.kind else {
                out.push(d.clone());
                continue;
            };
            let ast::NameKind::Simple(var) = &prefix.kind else {
                out.push(d.clone());
                continue;
            };
            let var_ty = decls.iter().find_map(|x| match x {
                ast::Decl::Variable { obj, .. } if obj.names.iter().any(|n| n.name == var.name) => {
                    Some(obj.ty.mark.clone())
                }
                _ => None,
            });
            let Some(mark) = var_ty else {
                out.push(d.clone());
                continue;
            };
            let Some(vt) = self.type_mark(r, &mark) else {
                continue;
            };
            let Some(info) = self.protected.get(&vt).cloned() else {
                out.push(d.clone());
                continue;
            };
            let cands: Vec<Sym> = self.regions[info.decl_region]
                .syms
                .get(&method.name)
                .cloned()
                .unwrap_or_default();
            let mut chosen = None;
            for c in cands {
                if self.signature_matches(r, &c, Some(sig)) {
                    chosen = Some(c);
                    break;
                }
            }
            let Some(Sym::Sub(target_sub)) = chosen else {
                self.error(span.clone(), "no method matches the alias signature");
                continue;
            };
            // Without the method's hidden object parameter.
            let params = self.subprograms[target_sub].params[1..].to_vec();
            let mut formals = Vec::new();
            let mut actuals = Vec::new();
            for (i, (p, mark)) in params.iter().zip(&sig.params).enumerate() {
                let (class, mode) = match self.objects[*p].kind {
                    ObjKind::Param(c, m) => (c, m),
                    _ => (ast::ObjClass::Constant, Mode::In),
                };
                let pname = ast::Ident {
                    name: format!("vh_fwd{}", i),
                    span: span.clone(),
                };
                formals.push(ast::InterfaceDecl::Object(ast::InterfaceObject {
                    class: Some(class),
                    names: vec![pname.clone()],
                    mode: Some(mode),
                    ty: ast::SubtypeInd {
                        resolution: None,
                        mark: mark.clone(),
                        constraint: None,
                        span: span.clone(),
                    },
                    bus: false,
                    default: None,
                    view: None,
                    span: span.clone(),
                }));
                actuals.push(ast::Assoc {
                    formal: None,
                    actual: ast::Actual::Expr(ast::Expr {
                        kind: ast::ExprKind::Name(ast::Name {
                            kind: ast::NameKind::Simple(pname),
                            span: span.clone(),
                        }),
                        span: span.clone(),
                    }),
                    span: span.clone(),
                });
            }
            let kind = match &sig.ret {
                Some(ret) => ast::SubprogramKind::Function {
                    pure: false,
                    ret: ret.clone(),
                },
                None => ast::SubprogramKind::Procedure,
            };
            let spec = ast::SubprogramSpec {
                kind,
                designator: name.clone(),
                generics: Vec::new(),
                params: formals,
                ret_id: None,
                span: span.clone(),
            };
            let callee = if actuals.is_empty() {
                target.clone()
            } else {
                ast::Name {
                    kind: ast::NameKind::Call(Box::new(target.clone()), actuals),
                    span: span.clone(),
                }
            };
            let stmt = if sig.ret.is_some() {
                ast::SeqKind::Return(Some(ast::Expr {
                    kind: ast::ExprKind::Name(callee),
                    span: span.clone(),
                }))
            } else {
                ast::SeqKind::ProcCall(callee)
            };
            self.prot_forwards
                .entry(t)
                .or_default()
                .push(ast::Decl::SubprogramBody(ast::SubprogramBody {
                    spec: spec.clone(),
                    decls: Vec::new(),
                    stmts: vec![ast::SeqStmt {
                        label: None,
                        kind: stmt,
                        span: span.clone(),
                    }],
                    span: span.clone(),
                }));
            out.push(ast::Decl::SubprogramDecl(spec));
        }
        out
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
        // The body of a generic protected type (VHDL-2019): kept for its
        // instances, and given to those made before it.
        if let Some(gp) = self.generic_prots.get_mut(&t) {
            gp.body = Some((r, decls.to_vec()));
            let pending = std::mem::take(&mut gp.pending);
            for (inst, ir, ipath) in pending {
                self.instance_body(t, inst, ir, &ipath);
            }
            return;
        }
        self.protected_body_in(t, r, decls, &format!("{}.{}", path, name), &[]);
    }

    /// Analyse the body of protected type `t` in region `r`: the variables
    /// each object has and its methods' bodies. `extra` are symbols the
    /// body sees besides `r`'s (a generic body's package body, for an
    /// instance).
    fn protected_body_in(
        &mut self,
        t: TypeId,
        r: RegionId,
        decls: &[ast::Decl],
        path: &str,
        extra: &[(String, Vec<Sym>)],
    ) {
        let Some(info) = self.protected.get(&t).cloned() else {
            return;
        };
        // The body sees its own context and the declaration's methods.
        let br = self.new_region(Some(r));
        for (k, v) in extra {
            for sym in v {
                self.declare(br, k, sym.clone());
            }
        }
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
        let mut decls = decls.to_vec();
        decls.extend(self.prot_forwards.remove(&t).unwrap_or_default());
        self.decls(br, &decls, &mut objs, &mut subs, path);
        self.cur_prot = saved;
        let vars: Vec<ObjId> = objs
            .into_iter()
            .filter(|o| matches!(self.objects[*o].kind, ObjKind::Variable))
            .collect();
        for v in &vars {
            self.prot_vars.insert(*v, t);
        }
        if let Some(p) = self.protected.get_mut(&t) {
            p.vars.extend(vars);
            p.has_body = true;
        }
    }

    /// An instance of generic protected type `g` named `name` (VHDL-2019
    /// §5.6.4): its declaration analysed with the generics bound to the
    /// actuals of `gmap` (in a region of the generic's context); the
    /// generic constants are variables of each object, set to the actuals.
    fn protected_instance(
        &mut self,
        r: RegionId,
        name: &str,
        g: TypeId,
        gmap: &[ast::Assoc],
        loc: Option<Loc>,
        path: &str,
    ) {
        let Some(gp) = self.generic_prots.get(&g).cloned() else {
            return;
        };
        let actx = super::generics::ActualCtx {
            region: r,
            lib: self.cur_lib.clone(),
            file: self.cur_file,
        };
        let ipath = format!("{}.{}", path, name);
        let saved = (
            std::mem::replace(&mut self.cur_lib, gp.lib.clone()),
            self.cur_file,
        );
        self.cur_file = gp.file;
        let ir = self.new_region(Some(gp.region));
        let consts = self.bind_generics(ir, &gp.generics, gmap, &actx, &ipath);
        self.protected_decl(ir, &gp.name, &gp.decls, loc, &ipath);
        self.cur_lib = saved.0;
        self.cur_file = saved.1;
        let Some(Sym::Type(t)) = self.regions[ir].syms.get(&gp.name).and_then(|v| v.first()).cloned()
        else {
            return;
        };
        self.types[t].name = name.to_string();
        for c in &consts {
            self.objects[*c].kind = ObjKind::Variable;
            self.prot_vars.insert(*c, t);
        }
        if let Some(p) = self.protected.get_mut(&t) {
            let mut vars = consts;
            vars.append(&mut p.vars);
            p.vars = vars;
        }
        self.declare(r, name, Sym::Type(t));
        match &gp.body {
            Some(_) => self.instance_body(g, t, ir, &ipath),
            None => {
                if let Some(gp) = self.generic_prots.get_mut(&g) {
                    gp.pending.push((t, ir, ipath));
                }
            }
        }
    }

    /// The body of instance `t` of generic protected type `g`: the
    /// generic's body analysed with the instance's generics (region `ir`),
    /// seeing the declarations of the package body it is written in.
    fn instance_body(&mut self, g: TypeId, t: TypeId, ir: RegionId, path: &str) {
        let Some(gp) = self.generic_prots.get(&g).cloned() else {
            return;
        };
        let Some((rb, decls)) = gp.body else {
            return;
        };
        let extra: Vec<(String, Vec<Sym>)> = self.regions[rb]
            .syms
            .iter()
            .filter(|(k, _)| **k != gp.name)
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        let saved = (
            std::mem::replace(&mut self.cur_lib, gp.lib.clone()),
            self.cur_file,
        );
        self.cur_file = gp.file;
        self.protected_body_in(t, ir, &decls, path, &extra);
        self.cur_lib = saved.0;
        self.cur_file = saved.1;
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
        // VHDL-2019 §5.5.2: the state, mode, position and size of a file,
        // and moving in it (positions in bytes).
        if self.revision == crate::vhdl::VhdlStd::V2019 && std.file_open_state != 0 {
            let native = |n: &str| Builtin::Native(format!("file.{}", n));
            let origin = (
                "origin",
                ObjClass::Constant,
                Mode::In,
                std.file_origin_kind,
                Some(lit_expr(Value::Enum(0), std.file_origin_kind, loc.clone())),
            );
            let offset = ("offset", ObjClass::Constant, Mode::In, std.integer, None);
            let size = ("size", ObjClass::Constant, Mode::In, std.integer, None);
            subs.push(("file_state", vec![f.clone()], Some(std.file_open_state), native("state")));
            subs.push(("file_mode", vec![f.clone()], Some(std.file_open_kind), native("mode")));
            subs.push(("file_position", vec![f.clone()], Some(std.natural), native("position")));
            subs.push(("file_size", vec![f.clone()], Some(std.natural), native("size")));
            subs.push(("file_canseek", vec![f.clone()], Some(std.boolean), native("canseek")));
            subs.push(("file_rewind", vec![f.clone()], None, native("rewind")));
            subs.push((
                "file_seek",
                vec![f.clone(), offset, origin.clone()],
                None,
                native("seek"),
            ));
            subs.push(("file_truncate", vec![f.clone(), size, origin], None, native("truncate")));
        }
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
        // VHDL-2019 (§6.4.2.3, §6.4.2.4): a variable or signal of an
        // unconstrained array subtype takes the bounds of its initial value.
        let ty = match &init {
            Some(i)
                if self.revision == crate::vhdl::VhdlStd::V2019
                    && matches!(
                        kind,
                        ObjKind::Variable | ObjKind::SharedVariable | ObjKind::Signal
                    ) =>
            {
                self.inferred_subtype(ty, i).unwrap_or(ty)
            }
            _ => ty,
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

    /// The subtype an unconstrained one-dimensional array subtype `ty` takes
    /// from a static initial value: its bounds (`None` when `ty` is
    /// constrained or the value is not static).
    fn inferred_subtype(&mut self, ty: TypeId, init: &HExpr) -> Option<TypeId> {
        if self.constrained(ty) {
            return None;
        }
        let TypeKind::Array { index, elem } = self.types[self.base(ty)].kind.clone() else {
            return None;
        };
        if index.len() != 1 || !self.constrained(elem) {
            return None;
        }
        let Some(Value::Array(av)) = self.eval_static(init) else {
            return None;
        };
        let it = index[0];
        let is_enum = matches!(self.types[self.base(it)].kind, TypeKind::Enum(_));
        let val = |v: i64| {
            if is_enum {
                Value::Enum(v as u32)
            } else {
                Value::Int(v)
            }
        };
        let lit = |v: i64| HExpr {
            kind: HExprKind::Lit(val(v)),
            ty: it,
            loc: init.loc.clone(),
        };
        let hr = HRange {
            left: Box::new(lit(av.left)),
            dir: av.dir,
            right: Box::new(lit(av.right)),
            static_val: Some(StaticRange {
                left: val(av.left),
                dir: av.dir,
                right: val(av.right),
            }),
            of_obj: None,
        };
        Some(self.add_type(
            "",
            TypeKind::Subtype {
                base: ty,
                constraint: Some(HConstraint::Index(vec![Some(hr)], None)),
                resolution: None,
            },
            None,
            None,
        ))
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
                    // A mode view (VHDL-2019): the type and the view.
                    let (ty, view) = match &o.view {
                        Some(vi) => match self.view_indication(r, vi, &o.ty, kind, o) {
                            Some((t, v)) => (t, Some(v)),
                            None => continue,
                        },
                        None => match self.subtype_ind(r, &o.ty) {
                            Some(t) => (t, None),
                            None => continue,
                        },
                    };
                    let default = o.default.as_ref().and_then(|v| self.expr(r, v, Some(ty)));
                    // A port or parameter with a view is driven and read
                    // through its elements: it associates as `inout`, and
                    // an element's own mode applies where a formal part
                    // names it (`map_ports`).
                    let mode = if view.is_some() {
                        Mode::InOut
                    } else {
                        o.mode.unwrap_or(Mode::In)
                    };
                    let okind = match kind {
                        IfaceKind::Generic => ObjKind::Generic,
                        IfaceKind::Port => ObjKind::Port(mode),
                        IfaceKind::Param { function } => {
                            let class = match o.class {
                                Some(c) => c,
                                None if view.is_some() => ObjClass::Signal,
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
                        if let Some(v) = view {
                            self.port_views.insert(id, v);
                        }
                        out.push(id);
                    }
                }
                // Operations on a generic type resolve when the unit is
                // analysed with its actual bound; the actual must be of the
                // type's class (VHDL-2019).
                ast::InterfaceDecl::Type(i, class) => {
                    // A generic type (§6.5.3): the instance's actual type, or
                    // an incomplete type while there is none.
                    let t = match self.type_binding.iter().find(|(n, _)| *n == i.name) {
                        Some((_, t)) => {
                            let t = *t;
                            if let Some(c) = class {
                                self.check_type_class(t, c, i);
                            }
                            t
                        }
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
        // A return identifier (VHDL-2019 §4.2.1): the subtype of the result
        // the call's context expects, given by a hidden last parameter
        // whose value has that subtype (a null array without one).
        let mut ret_param = None;
        if let (Some(rid), Some(rt)) = (&spec.ret_id, ret) {
            let TypeKind::Array { index, .. } = self.types[self.base(rt)].kind.clone() else {
                self.error(rid.span.clone(), "a return identifier of a non-array type is not supported yet");
                return None;
            };
            let loc = self.loc(rid.span.clone());
            let it = index[0];
            let null = HExpr {
                kind: HExprKind::Lit(Value::Array(Box::new(ArrayValue {
                    left: 0,
                    dir: Dir::To,
                    right: -1,
                    elems: Vec::new(),
                }))),
                ty: rt,
                loc: loc.clone(),
            };
            let o = self.add_obj(ObjInfo {
                name: "ret_".into(),
                kind: ObjKind::Param(ObjClass::Constant, Mode::In),
                ty: rt,
                init: Some(null),
                loc: loc.clone(),
                static_val: None,
            });
            params.push(o);
            let obj = HExpr {
                kind: HExprKind::Obj(o),
                ty: rt,
                loc: loc.clone(),
            };
            let ranges = (0..index.len())
                .map(|dim| {
                    let t = index.get(dim).copied().unwrap_or(it);
                    let placeholder = Box::new(HExpr {
                        kind: HExprKind::Lit(Value::Int(0)),
                        ty: t,
                        loc: loc.clone(),
                    });
                    Some(HRange {
                        left: placeholder.clone(),
                        dir: Dir::To,
                        right: placeholder,
                        static_val: None,
                        of_obj: Some((Box::new(obj.clone()), dim, false)),
                    })
                })
                .collect();
            let st = self.add_type(
                &rid.name,
                TypeKind::Subtype {
                    base: rt,
                    constraint: Some(HConstraint::Index(ranges, None)),
                    resolution: None,
                },
                None,
                Some(loc),
            );
            self.declare(pr, &rid.name, Sym::Type(st));
            ret_param = Some(o);
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
        if let Some(o) = ret_param {
            self.ret_params.insert(id, o);
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
        let saved_blocks = std::mem::take(&mut self.block_locals);
        let stmts = self.seq_stmts(body_r, &b.stmts, &stmt_ctx_fn(ret));
        locals.extend(std::mem::replace(&mut self.block_locals, saved_blocks));
        self.subprograms[target].body = Some(Body { locals, stmts });
        // A std subprogram with a VHDL body (STD.ENV's calendar functions,
        // libraries/std/env-body.vhdl) runs it rather than a native.
        if matches!(self.subprograms[target].builtin, Some(Builtin::Native(_))) {
            self.subprograms[target].builtin = None;
        }
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
