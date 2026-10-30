//! Mode views (VHDL-2019 §6.5.2): the modes of the elements of a record
//! port or signal parameter.
//!
//! A port with a view associates as an `inout` port: its elements are read
//! and driven through the one association, each from the side its mode
//! says. An element's own mode applies where a formal part names it
//! (`bus.ack => a`, `map_ports`). `v'converse` swaps `in` and `out`.

use super::hir::*;
use super::{Design, RegionId, Sym};
use crate::vhdl::ast::{self, Mode};

use super::decl::IfaceKind;

/// The converse of a mode (§6.5.2): `in` and `out` swap, `buffer` becomes
/// `in`, `inout` and `linkage` stay.
pub fn converse(m: Mode) -> Mode {
    match m {
        Mode::In => Mode::Out,
        Mode::Out | Mode::Buffer => Mode::In,
        m => m,
    }
}

impl Design {
    /// A mode view declaration: its record type and each element's mode.
    pub(super) fn view_decl(&mut self, r: RegionId, vd: &ast::ViewDecl) {
        let Some(ty) = self.subtype_ind(r, &vd.ty) else {
            return;
        };
        let TypeKind::Record(fields) = self.types[self.base(ty)].kind.clone() else {
            self.error(vd.ty.span.clone(), "the subtype of a mode view must be a record type");
            return;
        };
        let mut elems: Vec<Option<ElemView>> = vec![None; fields.len()];
        for (names, m) in &vd.elems {
            let mode = match m {
                ast::ElemMode::Mode(Mode::Linkage) => {
                    self.error(names[0].span.clone(), "an element of a mode view cannot be of mode linkage");
                    continue;
                }
                ast::ElemMode::Mode(m) => Some(ElemView::Mode(*m)),
                ast::ElemMode::View(n) | ast::ElemMode::ArrayView(n) => {
                    let array = matches!(m, ast::ElemMode::ArrayView(_));
                    self.view_name(r, n).map(|(view, converse)| {
                        ElemView::View(PortView {
                            view,
                            converse,
                            array,
                        })
                    })
                }
            };
            for n in names {
                let Some(i) = fields.iter().position(|(f, _)| *f == n.name) else {
                    self.error(
                        n.span.clone(),
                        format!("'{}' is not an element of the record type of the view", n.name),
                    );
                    continue;
                };
                if elems[i].is_some() {
                    self.error(n.span.clone(), format!("element '{}' has a mode in the view already", n.name));
                    continue;
                }
                let Some(mode) = mode else {
                    continue;
                };
                if let ElemView::View(pv) = mode
                    && !self.view_fits(pv, fields[i].1)
                {
                    self.error(
                        n.span.clone(),
                        format!("the view of element '{}' is not a view of its type", n.name),
                    );
                    continue;
                }
                elems[i] = Some(mode);
            }
        }
        let mut out = Vec::new();
        for (i, e) in elems.into_iter().enumerate() {
            match e {
                Some(e) => out.push(e),
                None => {
                    self.error(
                        vd.name.span.clone(),
                        format!("element '{}' has no mode in the view", fields[i].0),
                    );
                    return;
                }
            }
        }
        let id = self.views.len();
        self.views.push(ViewInfo {
            name: vd.name.name.clone(),
            ty,
            elems: out,
        });
        self.declare(r, &vd.name.name, Sym::View(id));
    }

    /// A view name, possibly `v'converse` (any number of times).
    fn view_name(&mut self, r: RegionId, n: &ast::Name) -> Option<(usize, bool)> {
        if let ast::NameKind::Attribute(prefix, attr, None) = &n.kind
            && attr.name == "converse"
        {
            return self.view_name(r, prefix).map(|(v, c)| (v, !c));
        }
        match self.name_sym(r, n) {
            Some(Sym::View(v)) => Some((v, false)),
            _ => {
                self.error(n.span.clone(), "a mode view name was expected");
                None
            }
        }
    }

    /// Whether a view applies to objects of type `ty`: the view's record
    /// type, or (`array`) an array of it.
    fn view_fits(&self, pv: PortView, ty: TypeId) -> bool {
        let vt = self.base(self.views[pv.view].ty);
        let t = self.base(ty);
        if !pv.array {
            return t == vt;
        }
        matches!(&self.types[t].kind, TypeKind::Array { elem, .. } if self.base(*elem) == vt)
    }

    /// The type and view of an interface object with a mode view
    /// indication (`p : view v [of t]`, `p : view (v) of t`).
    pub(super) fn view_indication(
        &mut self,
        r: RegionId,
        vi: &ast::ViewInd,
        ty: &ast::SubtypeInd,
        kind: IfaceKind,
        o: &ast::InterfaceObject,
    ) -> Option<(TypeId, PortView)> {
        match kind {
            IfaceKind::Port => {}
            IfaceKind::Param { function: false }
                if matches!(o.class, None | Some(ast::ObjClass::Signal)) => {}
            _ => {
                self.error(
                    o.span.clone(),
                    "a mode view is allowed for ports and signal parameters of procedures only",
                );
                return None;
            }
        }
        let (view, converse) = self.view_name(r, &vi.name)?;
        let pv = PortView {
            view,
            converse,
            array: vi.array,
        };
        let t = if vi.of {
            self.subtype_ind(r, ty)?
        } else if vi.array {
            self.error(o.span.clone(), "an array mode view needs the subtype of the array (of ...)");
            return None;
        } else {
            self.views[view].ty
        };
        if !self.view_fits(pv, t) {
            self.error(ty.span.clone(), "the subtype is not of the type of the mode view");
            return None;
        }
        Some((t, pv))
    }

    /// The mode of the part of a port with a view that a formal part names:
    /// the mode of the element it is (or is in), or `None` for a part that
    /// is itself a record with a view (whose elements have different modes).
    pub(super) fn view_mode_at(&self, pv: PortView, formal: &HExpr) -> Option<Mode> {
        let mut steps = Vec::new();
        let mut h = formal;
        loop {
            match &h.kind {
                HExprKind::Obj(_) => break,
                HExprKind::Field(b, i) => {
                    steps.push(Some(*i));
                    h = b;
                }
                HExprKind::Index(b, _) | HExprKind::Slice(b, _) => {
                    steps.push(None);
                    h = b;
                }
                HExprKind::Call(_, a) if a.len() == 1 => h = &a[0],
                HExprKind::Convert(x) => h = x,
                _ => return None,
            }
        }
        steps.reverse();
        let mut cur = pv;
        let mut steps = steps.into_iter();
        loop {
            if cur.array {
                // An index or slice of the array; each element has the view.
                match steps.next() {
                    Some(None) => cur.array = false,
                    _ => return None,
                }
            }
            let Some(Some(i)) = steps.next() else {
                return None;
            };
            match self.views[cur.view].elems.get(i)? {
                ElemView::Mode(m) => return Some(if cur.converse { converse(*m) } else { *m }),
                ElemView::View(inner) => {
                    cur = PortView {
                        view: inner.view,
                        converse: cur.converse != inner.converse,
                        array: inner.array,
                    };
                }
            }
        }
    }
}
