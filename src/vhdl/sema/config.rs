//! Component binding (IEEE 1076-2008 §7.3) and configurations (§3.4):
//! which design entity a component instance stands for, and how the
//! entity's generics and ports are associated through the component's.
//!
//! A component instance is bound by a component configuration of the
//! configuration being applied, else by a configuration specification of an
//! enclosing declarative part, else by default to the entity of the same
//! name (§7.3.3). The binding is resolved during analysis: the instance
//! records the entity's formals with the actuals of the instance, so
//! elaboration sees a direct entity instance.

use super::hir::*;
use super::{Design, RegionId, Sym};
use crate::vhdl::ast;

/// A block configuration being applied, with the region and library its
/// names are resolved in.
#[derive(Clone, Debug)]
pub struct BlockCfg {
    pub block: ast::BlockConfig,
    pub region: RegionId,
    pub lib: String,
    pub file: FileId,
}

/// A binding indication with where it was written.
struct Binding {
    ind: Option<ast::BindingInd>,
    region: RegionId,
    lib: String,
    file: FileId,
    /// The block configuration of a component configuration.
    block: Option<ast::BlockConfig>,
}

impl Design {
    /// Register a block configuration (once per source position).
    pub fn add_block_cfg(&mut self, c: BlockCfg) -> usize {
        if let Some(i) = self
            .block_configs
            .iter()
            .position(|x| x.file == c.file && x.block.span == c.block.span)
        {
            return i;
        }
        self.block_configs.push(c);
        self.block_configs.len() - 1
    }

    /// The entity a name denotes: `lib.e`, or `e` (visible, else in the
    /// working library).
    pub fn entity_name(&mut self, r: RegionId, n: &ast::Name) -> Option<(String, String)> {
        match &n.kind {
            ast::NameKind::Selected(p, ast::Suffix::Ident(e)) => match self.name_sym(r, p) {
                Some(Sym::Library(l)) => Some((l, e.name.clone())),
                _ => {
                    self.error(n.span.clone(), "an entity name lib.entity was expected");
                    None
                }
            },
            ast::NameKind::Simple(e) => match self.lookup(r, &e.name).first() {
                Some(Sym::Entity(l, en)) => Some((l.clone(), en.clone())),
                _ => Some((self.cur_lib.clone(), e.name.clone())),
            },
            _ => {
                self.error(n.span.clone(), "an entity name was expected");
                None
            }
        }
    }

    /// A configuration declaration named `lib.cfg` or `cfg`: its entity,
    /// the architecture its block configuration names, and that block
    /// configuration.
    pub fn config_unit(
        &mut self,
        r: RegionId,
        n: &ast::Name,
    ) -> Option<(String, String, Option<String>, Option<usize>)> {
        let (lib, name) = match &n.kind {
            ast::NameKind::Selected(p, ast::Suffix::Ident(c)) => match self.name_sym(r, p) {
                Some(Sym::Library(l)) => (l, c.name.clone()),
                _ => {
                    self.error(n.span.clone(), "a configuration name was expected");
                    return None;
                }
            },
            ast::NameKind::Simple(c) => (self.cur_lib.clone(), c.name.clone()),
            _ => {
                self.error(n.span.clone(), "a configuration name was expected");
                return None;
            }
        };
        let r = self.config_by_name(&lib, &name);
        if r.is_none() {
            self.error(
                n.span.clone(),
                format!("no configuration '{}' in library '{}'", name, lib),
            );
        }
        r
    }

    /// The configuration declaration `name` of library `lib`.
    pub fn config_by_name(
        &mut self,
        lib: &str,
        name: &str,
    ) -> Option<(String, String, Option<String>, Option<usize>)> {
        self.ensure_library(lib);
        let src = self.units.get(lib)?.get(name)?.clone();
        let du = self.unit_ast(&src)?.clone();
        let ast::LibraryUnit::Configuration(c) = &du.unit else {
            return None;
        };
        self.in_unit(lib, src.file, |d| {
            let ctx = d.context_region(&du.context);
            let (elib, ename) = d.entity_name(ctx, &c.entity)?;
            let Some(block) = c.block.clone() else {
                return Some((elib, ename, None, None));
            };
            let arch = match &block.spec.kind {
                ast::NameKind::Simple(a) => Some(a.name.clone()),
                _ => None,
            };
            let cfg = d.add_block_cfg(BlockCfg {
                block,
                region: ctx,
                lib: lib.to_string(),
                file: src.file,
            });
            Some((elib, ename, arch, Some(cfg)))
        })
    }

    /// The block configuration, within block configuration `cfg`, of the
    /// block or generate block `label` (iteration `index`, alternative
    /// `alt`), §3.4.2.
    pub fn sub_block_cfg(
        &mut self,
        cfg: usize,
        label: &str,
        index: Option<&Value>,
        alt: Option<&str>,
    ) -> Option<usize> {
        let bc = self.block_configs[cfg].clone();
        let mut general = None;
        for item in &bc.block.items {
            let ast::ConfigItem::Block(b) = item else {
                continue;
            };
            let hit = match &b.spec.kind {
                ast::NameKind::Simple(i) if i.name == label => {
                    general.get_or_insert(b.clone());
                    false
                }
                ast::NameKind::Call(p, args) if matches!(&p.kind, ast::NameKind::Simple(i) if i.name == label) => {
                    match args.as_slice() {
                        [
                            ast::Assoc {
                                formal: None,
                                actual: ast::Actual::Expr(e),
                                ..
                            },
                        ] => self.in_unit(&bc.lib.clone(), bc.file, |d| {
                            d.spec_index_matches(bc.region, e, index, alt)
                        }),
                        _ => false,
                    }
                }
                _ => false,
            };
            if hit {
                return Some(self.add_block_cfg(BlockCfg {
                    block: b.clone(),
                    ..bc.clone()
                }));
            }
        }
        general.map(|b| self.add_block_cfg(BlockCfg { block: b, ..bc }))
    }

    /// Whether the index of a generate block specification (a value, a
    /// range or an alternative label) selects this block.
    fn spec_index_matches(
        &mut self,
        r: RegionId,
        e: &ast::Expr,
        index: Option<&Value>,
        alt: Option<&str>,
    ) -> bool {
        if let (ast::ExprKind::Name(n), Some(a)) = (&e.kind, alt)
            && let ast::NameKind::Simple(i) = &n.kind
        {
            return i.name == a;
        }
        let Some(v) = index.and_then(|v| v.as_i64()) else {
            return false;
        };
        if let ast::ExprKind::Range(re) = &e.kind {
            let dr = ast::DiscreteRange::Range((**re).clone());
            return match self
                .discrete_range(r, &dr, None)
                .and_then(|(_, h)| h.static_val)
            {
                Some(sr) => {
                    let (a, z) = (
                        sr.left.as_i64().unwrap_or(0),
                        sr.right.as_i64().unwrap_or(0),
                    );
                    match sr.dir {
                        ast::Dir::To => a <= v && v <= z,
                        ast::Dir::Downto => z <= v && v <= a,
                    }
                }
                None => false,
            };
        }
        match self.expr(r, e, None).and_then(|h| self.eval(&h)) {
            Some(x) => x.as_i64() == Some(v),
            None => false,
        }
    }

    /// The component configuration of block configuration `cfg` for
    /// instance `label` of component `comp` (§3.4.3).
    fn component_config(&self, cfg: usize, label: &str, comp: &str) -> Option<Binding> {
        let bc = &self.block_configs[cfg];
        let mut fallback = None;
        for item in &bc.block.items {
            let ast::ConfigItem::Component(cc) = item else {
                continue;
            };
            if super::last_ident(&cc.spec.comp).map(|i| i.name.as_str()) != Some(comp) {
                continue;
            }
            let b = Binding {
                ind: cc.binding.clone(),
                region: bc.region,
                lib: bc.lib.clone(),
                file: bc.file,
                block: cc.block.clone(),
            };
            match &cc.spec.insts {
                ast::InstList::Labels(ls) if ls.iter().any(|l| l.name == label) => return Some(b),
                ast::InstList::Labels(_) => {}
                ast::InstList::All | ast::InstList::Others => {
                    fallback.get_or_insert(b);
                }
            }
        }
        fallback
    }

    /// The configuration specification for instance `label` of component
    /// `comp`, from the innermost declarative part with one (§7.3.1).
    fn config_spec(&self, mut r: RegionId, label: &str, comp: &str) -> Option<Binding> {
        loop {
            let mut fallback = None;
            for (sr, spec, lib, file) in &self.cfg_specs {
                if *sr != r
                    || super::last_ident(&spec.spec.comp).map(|i| i.name.as_str()) != Some(comp)
                {
                    continue;
                }
                let b = Binding {
                    ind: Some(spec.binding.clone()),
                    region: r,
                    lib: lib.clone(),
                    file: *file,
                    block: None,
                };
                match &spec.spec.insts {
                    ast::InstList::Labels(ls) if ls.iter().any(|l| l.name == label) => {
                        return Some(b);
                    }
                    ast::InstList::Labels(_) => {}
                    _ => {
                        fallback.get_or_insert(b);
                    }
                }
            }
            if fallback.is_some() {
                return fallback;
            }
            r = self.regions[r].parent?;
        }
    }

    /// A component instantiation statement: the bound entity's instance,
    /// or nothing for an unbound instance (§7.3.3: no default entity, or
    /// `use open`).
    #[allow(clippy::too_many_arguments)]
    pub fn component_instance(
        &mut self,
        r: RegionId,
        label: &str,
        n: &ast::Name,
        generic_map: &[ast::Assoc],
        port_map: &[ast::Assoc],
        arch: &mut Architecture,
        loc: Loc,
    ) {
        let cid = match self.name_sym(r, n) {
            Some(Sym::Component(c)) => c,
            _ => {
                self.error(
                    n.span.clone(),
                    format!("'{}' is not a component", super::decl::name_text(n)),
                );
                return;
            }
        };
        let comp = self.components[cid].clone();
        let cg = self.map_formals_ex(r, &comp.generics, generic_map, true);
        let (cp, cconv) = self.map_ports(r, &comp.ports, port_map, arch, &loc);
        // Local generics without an actual take their defaults (§6.5.6.2).
        let cg: Vec<(ObjId, Option<HExpr>)> = cg
            .into_iter()
            .map(|(f, a, _)| {
                let d = self.objects[f].init.clone();
                (f, a.or(d))
            })
            .collect();
        let cp: Vec<(ObjId, Option<HExpr>)> = cp.into_iter().map(|(f, a, _)| (f, a)).collect();
        let cfg_binding = self
            .cur_cfg
            .and_then(|c| self.component_config(c, label, &comp.name));
        // A component configuration without a binding indication keeps
        // the configuration specification's (§7.3.2.1).
        let spec = self.config_spec(r, label, &comp.name);
        let binding = match cfg_binding {
            Some(b) if b.ind.as_ref().is_some_and(|i| i.aspect.is_some()) => Some(b),
            Some(b) => Some(Binding {
                ind: spec.as_ref().and_then(|s| s.ind.clone()).or(b.ind),
                ..b
            }),
            None => spec,
        };
        let (blib, bfile) = binding
            .as_ref()
            .map(|b| (b.lib.clone(), b.file))
            .unwrap_or((self.cur_lib.clone(), self.cur_file));
        let bregion = binding.as_ref().map(|b| b.region).unwrap_or(r);
        let ind = binding.as_ref().and_then(|b| b.ind.clone());
        let entity = self.in_unit(&blib.clone(), bfile, |d| {
            match ind.as_ref().and_then(|i| i.aspect.clone()) {
                Some(ast::EntityAspect::Open) => None,
                Some(ast::EntityAspect::Entity(en, a)) => {
                    let (l, e) = d.entity_name(bregion, &en)?;
                    Some((l, e, a.map(|a| a.name), None))
                }
                Some(ast::EntityAspect::Configuration(cn)) => d.config_unit(bregion, &cn),
                None => {
                    // The default binding: the entity of the component's name,
                    // visible or in the working library (§7.3.3).
                    let lib = match d.lookup(r, &comp.name).first() {
                        Some(Sym::Entity(l, _)) => l.clone(),
                        _ => d.cur_lib.clone(),
                    };
                    d.ensure_library(&lib);
                    let is_entity = d
                        .units
                        .get(&lib)
                        .and_then(|u| u.get(&comp.name))
                        .cloned()
                        .and_then(|s| d.unit_kind(&s));
                    matches!(is_entity, Some(super::UnitKind::Entity))
                        .then(|| (lib, comp.name.clone(), None, None))
                }
            }
        });
        let Some((lib, ename, mut archn, mut cfg)) = entity else {
            // Unbound: the instance is absent (GHDL warns at elaboration).
            return;
        };
        // A component configuration's block configuration configures the
        // bound architecture.
        if let Some(block) = binding.as_ref().and_then(|b| b.block.clone()) {
            if archn.is_none()
                && let ast::NameKind::Simple(a) = &block.spec.kind
            {
                archn = Some(a.name.clone());
            }
            let b = binding.as_ref().unwrap();
            cfg = Some(self.add_block_cfg(BlockCfg {
                block,
                region: b.region,
                lib: b.lib.clone(),
                file: b.file,
            }));
        }
        let Some(info) = self.analyze_entity(&lib, &ename) else {
            self.error(
                loc.span.clone(),
                format!("no entity '{}' in library '{}'", ename, lib),
            );
            return;
        };
        // The binding's maps see the component's generics and ports as
        // actuals (§7.3.2.2, §7.3.2.3).
        let br = self.new_region(Some(bregion));
        for o in comp.generics.iter().chain(&comp.ports) {
            let name = self.objects[*o].name.clone();
            self.declare(br, &name, Sym::Obj(*o));
        }
        // A map aspect of the binding associates exactly what it names;
        // without one, the formals are associated with the locals of the
        // same name (§7.3.2.2, §7.3.3).
        let gm = ind
            .as_ref()
            .map(|i| i.generic_map.clone())
            .unwrap_or_default();
        let pm = ind.as_ref().map(|i| i.port_map.clone()).unwrap_or_default();
        let bg = self.in_unit(&blib.clone(), bfile, |d| {
            d.map_formals_ex(br, &info.generics, &gm, true)
        });
        let bp = self.in_unit(&blib.clone(), bfile, |d| {
            d.map_formals_ex(br, &info.ports, &pm, false)
        });
        let mut gmap = Vec::new();
        for (f, a, _) in bg {
            let actual = if gm.is_empty() {
                self.same_name_actual(f, &cg)
            } else {
                a.and_then(|a| self.subst_locals(&a, &cg, &loc))
            };
            if let Some(a) = actual {
                gmap.push((f, a));
            }
        }
        let mut pmap = Vec::new();
        // The entity port each local port is associated with.
        let mut local_of: Vec<(ObjId, ObjId)> = Vec::new();
        for (f, a, _) in bp {
            let local = if pm.is_empty() {
                let name = &self.objects[f].name;
                cp.iter()
                    .map(|(l, _)| *l)
                    .find(|l| self.objects[*l].name == *name)
            } else {
                match a.as_ref().map(|a| &a.kind) {
                    Some(HExprKind::Obj(o)) if cp.iter().any(|(l, _)| l == o) => Some(*o),
                    _ => None,
                }
            };
            if let Some(l) = local {
                local_of.push((l, f));
            }
            let actual = if pm.is_empty() {
                self.same_name_actual(f, &cp)
            } else {
                a.and_then(|a| self.subst_locals(&a, &cp, &loc))
            };
            pmap.push((f, actual));
        }
        // Conversions and partial formals of the local ports apply to the
        // entity ports bound to them.
        let mut port_conv = Vec::new();
        for mut pc in cconv {
            let Some(&(_, to)) = local_of.iter().find(|(l, _)| *l == pc.formal) else {
                self.errors.push((
                    loc.clone(),
                    "a converted or partial component port must be bound to an entity port".into(),
                ));
                continue;
            };
            let objs = &self.objects;
            let side = if pc.mode == ast::Mode::In {
                &mut pc.target
            } else {
                &mut pc.value
            };
            *side = map_objs(side, &mut |o| {
                (o == pc.formal).then(|| HExpr {
                    kind: HExprKind::Obj(to),
                    ty: objs[to].ty,
                    loc: objs[to].loc.clone(),
                })
            });
            pc.formal = to;
            port_conv.push(pc);
        }
        arch.instances.push(Instance {
            label: label.to_string(),
            library: lib,
            entity: ename,
            arch: archn,
            arch_index: None,
            generic_map: gmap,
            port_map: pmap,
            port_conv,
            generic_types: Vec::new(),
            config: cfg,
            loc,
        });
    }

    /// The actual of the local generic or port named like entity formal
    /// `f` (default binding, §7.3.3).
    fn same_name_actual(&self, f: ObjId, locals: &[(ObjId, Option<HExpr>)]) -> Option<HExpr> {
        let name = &self.objects[f].name;
        locals
            .iter()
            .find(|(l, _)| self.objects[*l].name == *name)
            .and_then(|(_, a)| a.clone())
    }

    /// A binding map actual with the local generics and ports replaced by
    /// their actuals in the instance; `None` when it is an open local.
    fn subst_locals(
        &mut self,
        h: &HExpr,
        locals: &[(ObjId, Option<HExpr>)],
        loc: &Loc,
    ) -> Option<HExpr> {
        if let HExprKind::Obj(o) = &h.kind
            && let Some((_, a)) = locals.iter().find(|(l, _)| l == o)
        {
            return a.clone();
        }
        let mut open = false;
        let out = map_objs(h, &mut |o| {
            locals.iter().find(|(l, _)| *l == o).map(|(_, a)| match a {
                Some(a) => a.clone(),
                None => {
                    open = true;
                    lit_placeholder(h)
                }
            })
        });
        if open {
            self.errors.push((
                loc.clone(),
                "an open component port or generic is used in a binding expression".into(),
            ));
            return None;
        }
        Some(out)
    }
}

fn lit_placeholder(h: &HExpr) -> HExpr {
    HExpr {
        kind: HExprKind::Lit(Value::Int(0)),
        ty: h.ty,
        loc: h.loc.clone(),
    }
}

/// `h` with object names replaced where `f` gives a replacement.
pub fn map_objs(h: &HExpr, f: &mut dyn FnMut(ObjId) -> Option<HExpr>) -> HExpr {
    let kind = match &h.kind {
        HExprKind::Obj(o) => match f(*o) {
            Some(x) => return x,
            None => HExprKind::Obj(*o),
        },
        HExprKind::Call(s, args) => {
            HExprKind::Call(*s, args.iter().map(|a| map_objs(a, f)).collect())
        }
        HExprKind::Index(b, i) => HExprKind::Index(
            Box::new(map_objs(b, f)),
            i.iter().map(|a| map_objs(a, f)).collect(),
        ),
        HExprKind::Slice(b, r) => HExprKind::Slice(Box::new(map_objs(b, f)), map_range(r, f)),
        HExprKind::Field(b, i) => HExprKind::Field(Box::new(map_objs(b, f)), *i),
        HExprKind::ArrayAgg(items) => HExprKind::ArrayAgg(
            items
                .iter()
                .map(|(cs, v)| {
                    let cs = cs
                        .iter()
                        .map(|c| match c {
                            HChoice::Expr(x) => HChoice::Expr(map_objs(x, f)),
                            HChoice::Range(r) => HChoice::Range(map_range(r, f)),
                            HChoice::Others => HChoice::Others,
                        })
                        .collect();
                    (cs, map_objs(v, f))
                })
                .collect(),
        ),
        HExprKind::RecordAgg(v) => HExprKind::RecordAgg(v.iter().map(|a| map_objs(a, f)).collect()),
        HExprKind::Convert(x) => HExprKind::Convert(Box::new(map_objs(x, f))),
        HExprKind::Qualified(x) => HExprKind::Qualified(Box::new(map_objs(x, f))),
        HExprKind::Deref(x) => HExprKind::Deref(Box::new(map_objs(x, f))),
        HExprKind::Attr(n, p, a) => HExprKind::Attr(
            n.clone(),
            Box::new(match p.as_ref() {
                AttrPrefix::Expr(x) => AttrPrefix::Expr(map_objs(x, f)),
                AttrPrefix::Type(t) => AttrPrefix::Type(*t),
            }),
            a.as_ref().map(|x| Box::new(map_objs(x, f))),
        ),
        HExprKind::New(x) => HExprKind::New(x.as_ref().map(|x| Box::new(map_objs(x, f)))),
        k => k.clone(),
    };
    HExpr {
        kind,
        ty: h.ty,
        loc: h.loc.clone(),
    }
}

fn map_range(r: &HRange, f: &mut dyn FnMut(ObjId) -> Option<HExpr>) -> HRange {
    HRange {
        left: Box::new(map_objs(&r.left, f)),
        dir: r.dir,
        right: Box::new(map_objs(&r.right, f)),
        static_val: r.static_val.clone(),
        of_obj: r
            .of_obj
            .as_ref()
            .map(|(o, d, rev)| (Box::new(map_objs(o, f)), *d, *rev)),
    }
}
