//! Generic packages and their instantiation (IEEE 1076-2008 §4.9, §6.5.6),
//! and the binding of generic types, subprograms and packages (§6.5.3,
//! §6.5.4, §6.5.5).
//!
//! A generic package is not analysed on its own. Each instantiation
//! analyses its declarations (and later its body) again in a region of its
//! own where the formal generics denote the actuals: a generic constant is
//! a constant with the actual's value, a generic type names the actual
//! type, a generic subprogram the actual subprogram and a generic package
//! the actual package instance. The instance's types and subprograms are
//! therefore distinct from every other instance's (§4.9).

use super::hir::*;
use super::{Design, PkgKey, RegionId, Sym};
use crate::vhdl::ast;

/// One formal of a generic list (an interface object declaring several
/// names gives one per name).
enum Formal<'a> {
    Obj(&'a ast::Ident, &'a ast::InterfaceObject),
    Type(&'a ast::Ident),
    Sub(&'a ast::SubprogramSpec, &'a Option<ast::SubprogramDefault>),
    Package(&'a ast::Ident),
}

impl Formal<'_> {
    fn name(&self) -> String {
        match self {
            Formal::Obj(i, _) | Formal::Type(i) | Formal::Package(i) => i.name.clone(),
            Formal::Sub(spec, _) => Design::designator_key(&spec.designator),
        }
    }
}

/// A generic subprogram (§4.2.1): its declaration, where it was declared.
#[derive(Clone, Debug)]
pub struct GenericSub {
    pub spec: ast::SubprogramSpec,
    pub body: Option<ast::SubprogramBody>,
    pub region: RegionId,
    pub lib: String,
    pub file: FileId,
    /// Instances made before the body was seen (a package declaration
    /// instantiating a subprogram of its body): name, generics region,
    /// path; completed with the body.
    pub pending: Vec<(ast::Ident, RegionId, String)>,
}

/// Where the actuals of a generic map are analysed.
#[derive(Clone)]
pub struct ActualCtx {
    pub region: RegionId,
    pub lib: String,
    pub file: FileId,
}

impl Design {
    /// Run `f` in the context the actuals are written in.
    fn in_actual<R>(&mut self, a: &ActualCtx, f: impl FnOnce(&mut Self) -> R) -> R {
        let saved = (
            std::mem::replace(&mut self.cur_lib, a.lib.clone()),
            self.cur_file,
        );
        self.cur_file = a.file;
        let r = f(self);
        self.cur_lib = saved.0;
        self.cur_file = saved.1;
        r
    }

    /// Bind the generics `formals` in region `ir` (in the current, formal
    /// context) to the actuals of `gmap` (analysed in `actx`); returns
    /// the generic constants, in order.
    pub(super) fn bind_generics(
        &mut self,
        ir: RegionId,
        formals: &[ast::InterfaceDecl],
        gmap: &[ast::Assoc],
        actx: &ActualCtx,
        path: &str,
    ) -> Vec<ObjId> {
        let mut flat = Vec::new();
        for f in formals {
            match f {
                ast::InterfaceDecl::Object(o) => {
                    for n in &o.names {
                        flat.push(Formal::Obj(n, o));
                    }
                }
                ast::InterfaceDecl::Type(i) => flat.push(Formal::Type(i)),
                ast::InterfaceDecl::Subprogram { spec, default } => {
                    flat.push(Formal::Sub(spec, default))
                }
                ast::InterfaceDecl::Package { name, .. } => flat.push(Formal::Package(name)),
            }
        }
        // The actual of each formal: by name, else by position.
        let mut actuals: Vec<Option<&ast::Assoc>> = vec![None; flat.len()];
        for (i, a) in gmap.iter().enumerate() {
            let k = match &a.formal {
                None => Some(i).filter(|&i| i < flat.len()),
                Some(n) => {
                    let name = match &n.kind {
                        ast::NameKind::Simple(id) => id.name.clone(),
                        _ => super::decl::name_text(n),
                    };
                    flat.iter().position(|f| f.name() == name)
                }
            };
            match k {
                Some(k) => actuals[k] = Some(a),
                None => {
                    let fl: Vec<String> = flat.iter().map(|f| f.name()).collect();
                    self.in_actual(actx, |d| {
                        d.error(
                            a.span.clone(),
                            format!("no such generic in this generic list ({})", fl.join(", ")),
                        )
                    })
                }
            }
        }
        let mut objs = Vec::new();
        for (f, a) in flat.iter().zip(actuals) {
            let actual = a.and_then(|a| match &a.actual {
                ast::Actual::Expr(e) => Some(e),
                ast::Actual::Open(_) => None,
            });
            match f {
                Formal::Obj(n, o) => {
                    let Some(ty) = self.subtype_ind(ir, &o.ty) else {
                        continue;
                    };
                    let init = match actual {
                        Some(e) => self.in_actual(actx, |d| d.expr(actx.region, e, Some(ty))),
                        None => match &o.default {
                            Some(e) => self.expr(ir, e, Some(ty)),
                            None => {
                                self.error(
                                    n.span.clone(),
                                    format!("generic '{}' has no actual", n.name),
                                );
                                None
                            }
                        },
                    };
                    let static_val = init.as_ref().and_then(|e| self.eval_static(e));
                    let id = self.add_obj(ObjInfo {
                        name: n.name.clone(),
                        kind: ObjKind::Constant,
                        ty,
                        init,
                        loc: self.loc(n.span.clone()),
                        static_val,
                    });
                    self.declare(ir, &n.name, Sym::Obj(id));
                    objs.push(id);
                }
                Formal::Type(i) => {
                    let t = match actual {
                        Some(ast::Expr {
                            kind: ast::ExprKind::Name(nm),
                            ..
                        }) => self.in_actual(actx, |d| d.type_mark(actx.region, nm)),
                        Some(e) => {
                            self.error(
                                e.span.clone(),
                                "the actual of a generic type must be a subtype",
                            );
                            None
                        }
                        None => {
                            self.error(
                                i.span.clone(),
                                format!("generic type '{}' has no actual", i.name),
                            );
                            None
                        }
                    };
                    if let Some(t) = t {
                        self.declare(ir, &i.name, Sym::Type(t));
                    }
                }
                Formal::Sub(spec, default) => {
                    // The formal's profile, from a specification analysed
                    // in a scratch region.
                    let scratch = self.new_region(Some(ir));
                    let Some(formal) = self.subprogram_spec(scratch, spec, path) else {
                        continue;
                    };
                    let key = Self::designator_key(&spec.designator);
                    let cands: Vec<Sym> = match (actual, default) {
                        (
                            Some(ast::Expr {
                                kind: ast::ExprKind::Name(nm),
                                ..
                            }),
                            _,
                        ) => self.in_actual(actx, |d| d.overloads(actx.region, nm)),
                        (Some(e), _) => {
                            self.error(
                                e.span.clone(),
                                "the actual of a generic subprogram must be a subprogram name",
                            );
                            continue;
                        }
                        // `is <>`: a subprogram of the same designator
                        // visible where the package is instantiated.
                        (None, Some(ast::SubprogramDefault::Box)) => {
                            self.in_actual(actx, |d| d.lookup(actx.region, &key))
                        }
                        (None, Some(ast::SubprogramDefault::Name(nm))) => self.overloads(ir, nm),
                        (None, None) => Vec::new(),
                    };
                    let found = cands.into_iter().find_map(|s| match s {
                        Sym::Sub(c) if self.same_profile(c, formal) => Some(c),
                        _ => None,
                    });
                    match found {
                        Some(c) => self.declare(ir, &key, Sym::Sub(c)),
                        None => self.error(
                            spec.span.clone(),
                            format!("no subprogram matching generic subprogram {}", key),
                        ),
                    }
                }
                Formal::Package(i) => {
                    let p = match actual {
                        Some(ast::Expr {
                            kind: ast::ExprKind::Name(nm),
                            ..
                        }) => self.in_actual(actx, |d| d.resolve_static_name(actx.region, nm)),
                        _ => None,
                    };
                    match p {
                        Some(Sym::Package(k)) => self.declare(ir, &i.name, Sym::Package(k)),
                        _ => self.error(
                            i.span.clone(),
                            format!(
                                "generic package '{}' needs a package instance as actual",
                                i.name
                            ),
                        ),
                    }
                }
            }
        }
        objs
    }

    /// Declare a generic subprogram (its specification, or its body
    /// completing an earlier specification).
    pub(super) fn declare_generic_sub(
        &mut self,
        r: RegionId,
        spec: &ast::SubprogramSpec,
        body: Option<&ast::SubprogramBody>,
    ) {
        let key = Self::designator_key(&spec.designator);
        if let Some(b) = body {
            // The specification may be in an enclosing region (a package
            // declaration, completed in its body).
            let existing = self.lookup(r, &key);
            for s in existing {
                if let Sym::GenericSub(g) = s
                    && self.generic_subs[g].body.is_none()
                {
                    self.generic_subs[g].body = Some(b.clone());
                    for (name, ir, path) in std::mem::take(&mut self.generic_subs[g].pending) {
                        let mut ib = b.clone();
                        ib.spec.generics.clear();
                        ib.spec.designator = ast::Designator::Ident(name);
                        self.subprogram_body(ir, &ib, &path);
                    }
                    return;
                }
            }
        }
        self.generic_subs.push(GenericSub {
            spec: spec.clone(),
            body: body.cloned(),
            region: r,
            lib: self.cur_lib.clone(),
            file: self.cur_file,
            pending: Vec::new(),
        });
        let g = self.generic_subs.len() - 1;
        self.declare(r, &key, Sym::GenericSub(g));
    }

    /// `function f is new g generic map (...)` (§4.4): the generic
    /// subprogram analysed with its generics bound, declared as `name`.
    pub(super) fn instantiate_sub(
        &mut self,
        r: RegionId,
        name: &ast::Ident,
        uninst: &ast::Name,
        gmap: &[ast::Assoc],
        span: ast::Span,
        path: &str,
    ) -> Option<SubId> {
        let g = self.overloads(r, uninst).into_iter().find_map(|s| match s {
            Sym::GenericSub(g) => Some(g),
            _ => None,
        });
        let Some(g) = g else {
            self.error(span, "no generic subprogram of this name");
            return None;
        };
        let gs = self.generic_subs[g].clone();
        let _ = span;
        let actx = ActualCtx {
            region: r,
            lib: self.cur_lib.clone(),
            file: self.cur_file,
        };
        let path = path.to_string();
        let id = self.in_unit(&gs.lib.clone(), gs.file, |d| {
            let ir = d.new_region(Some(gs.region));
            d.bind_generics(ir, &gs.spec.generics, gmap, &actx, &path);
            match gs.body {
                Some(mut b) => {
                    b.spec.generics.clear();
                    b.spec.designator = ast::Designator::Ident(name.clone());
                    d.subprogram_body(ir, &b, &path)
                }
                // The body comes later (`declare_generic_sub`).
                None => {
                    let mut spec = gs.spec.clone();
                    spec.generics.clear();
                    spec.designator = ast::Designator::Ident(name.clone());
                    let id = d.subprogram_spec(ir, &spec, &path);
                    d.generic_subs[g]
                        .pending
                        .push((name.clone(), ir, path.clone()));
                    id
                }
            }
        })?;
        self.declare(r, &name.name, Sym::Sub(id));
        Some(id)
    }

    /// The declarations a (possibly selected) name denotes, every overload.
    pub(super) fn overloads(&mut self, r: RegionId, n: &ast::Name) -> Vec<Sym> {
        match &n.kind {
            ast::NameKind::Simple(i) => self.lookup(r, &i.name),
            ast::NameKind::Selected(prefix, suffix) => {
                let key = match suffix {
                    ast::Suffix::Ident(i) => i.name.clone(),
                    ast::Suffix::Op(o, _) => format!("\"{}\"", o),
                    _ => return Vec::new(),
                };
                match self.resolve_static_name(r, prefix) {
                    Some(Sym::Package(pk)) => self.pkg_syms(&pk, &key),
                    _ => Vec::new(),
                }
            }
            _ => Vec::new(),
        }
    }

    /// The name of a package as written: an instance declared in a unit
    /// is keyed `<name>_inst<n>`.
    pub(super) fn inst_name_of(&self, k: &PkgKey) -> String {
        match (self.inst_of.contains_key(k), k.1.rfind("_inst")) {
            (true, Some(i))
                if k.1[i + 5..].bytes().all(|b| b.is_ascii_digit()) && i + 5 < k.1.len() =>
            {
                k.1[..i].to_string()
            }
            _ => k.1.clone(),
        }
    }

    /// Instantiate a generic package (§4.9) as package `key`, with the
    /// generic map's actuals analysed in `actx`.
    pub(super) fn instantiate_package(
        &mut self,
        actx: &ActualCtx,
        inst: &ast::PackageInst,
        key: PkgKey,
    ) -> Option<RegionId> {
        let gk = match self.in_actual(actx, |d| d.resolve_static_name(actx.region, &inst.package)) {
            Some(Sym::Package(k)) => k,
            _ => {
                self.error(inst.package.span.clone(), "no such package");
                return None;
            }
        };
        self.ensure_library(&gk.0);
        let src = self.units.get(&gk.0).and_then(|u| u.get(&gk.1)).cloned()?;
        let du = self.unit_ast(&src)?.clone();
        let ast::LibraryUnit::Package(p) = &du.unit else {
            self.error(inst.package.span.clone(), "not a generic package");
            return None;
        };
        if p.generics.is_empty() {
            self.error(
                inst.package.span.clone(),
                format!("package '{}' is not a generic package", gk.1),
            );
            return None;
        }
        let path = format!("{}.{}", key.0, key.1);
        let ir = self.in_unit(&gk.0.clone(), src.file, |d| {
            let ctx = d.context_region(&du.context);
            let ir = d.new_region(Some(ctx));
            d.pkg_regions.insert(key.clone(), ir);
            // Within the instance, the generic package's name denotes it.
            d.declare(ir, &gk.1, Sym::Package(key.clone()));
            let mut objs = d.bind_generics(ir, &p.generics, &inst.generic_map, actx, &path);
            let mut subs = Vec::new();
            d.decls(ir, &p.decls, &mut objs, &mut subs, &path);
            d.packages.insert(
                key.clone(),
                (
                    Package {
                        library: key.0.clone(),
                        name: key.1.clone(),
                        objects: objs,
                        subprograms: subs,
                    },
                    ir,
                ),
            );
            ir
        });
        self.inst_of.insert(key, gk);
        Some(ir)
    }
}
