//! §3.12.1: a compilation-unit variable or net is one object. Its
//! declaration is elaborated once, in the hierarchy root, and a reference
//! from any other definition names that storage.

use super::{stmt_list_declared_names, stmt_local_declared, substitute_bare_idents_stmt};
use crate::ast::Span;
use crate::ast::binding::Bound;
use crate::ast::decl::{ClassDeclaration, ClassItem, ClassMethodKind, FunctionPort};
use crate::ast::expr::{ExprKind, Expression, HierarchicalIdentifier};
use crate::ast::stmt::{Statement, StatementKind};
use crate::hasher::HashMap;

/// Where one unit declaration is stored.
#[derive(Clone, Debug)]
pub(crate) struct Target {
    /// The flat name in the root: the plain name, or the reserved
    /// `$unit::<name>` when the root declares the name itself.
    pub storage: String,
    /// Another definition declares the plain name, so a reference by it
    /// from below such an instance has to be rooted.
    pub contested: bool,
}

thread_local! {
    static TABLE: std::cell::RefCell<HashMap<String, Target>> =
        std::cell::RefCell::new(HashMap::default());
}

/// Record where each unit variable and net of the design being elaborated
/// is stored. An empty table leaves every reference as written.
pub(crate) fn set(targets: HashMap<String, Target>) {
    TABLE.with(|t| *t.borrow_mut() = targets);
}

/// Whether the root declares `name` as the unit's variable or net.
pub(crate) fn declares(name: &str) -> bool {
    TABLE.with(|t| t.borrow().contains_key(name))
}

/// The storage of `name` for a reference in the body of the instance
/// `prefix`. The root's own body (no prefix) names its declarations directly.
fn target(name: &str, prefix: &str) -> Option<Target> {
    if prefix.is_empty() {
        return None;
    }
    TABLE.with(|t| t.borrow().get(name).cloned())
}

fn reference(
    hier: &HierarchicalIdentifier,
    target: &Target,
    plain: &str,
    span: Span,
    select: &dyn Fn(&Expression) -> Expression,
) -> Expression {
    let mut h = hier.clone();
    h.path[0].name.name = target.storage.clone();
    for seg in &mut h.path {
        for sel in &mut seg.selects {
            *sel = select(sel);
        }
    }
    // The reserved name is declared nowhere else. The plain name may be: an
    // enclosing instance's own declaration would take a relative reference.
    if target.storage == plain && target.contested {
        h.root = Some(crate::ast::expr::HierRoot::Root);
    }
    h.cached_signal_id = crate::ast::cache::SignalCache::new(None);
    h.cached_resolved_name = crate::ast::cache::NameCache::new();
    Expression::new(ExprKind::Ident(h), span)
}

/// `$unit::name` in an instance body: the unit's storage, whatever the
/// instance's module declares under the plain name.
pub(crate) fn qualified(
    hier: &HierarchicalIdentifier,
    plain: &str,
    prefix: &str,
    span: Span,
    select: &dyn Fn(&Expression) -> Expression,
) -> Option<Expression> {
    // A pass over a body before its instance is known keeps the qualifier
    // for the pass that knows it.
    if prefix.is_empty() && declares(plain) {
        return Some(Expression::new(ExprKind::Ident(hier.clone()), span));
    }
    let mut t = target(plain, prefix)?;
    // The qualified name passes every local declaration of the plain one.
    t.contested = true;
    Some(reference(hier, &t, plain, span, select))
}

/// A simple name in an instance body that no declaration of the module, of
/// its generate blocks or of the enclosing statements takes: the unit's
/// storage, when its flat name differs from the name or could be taken by
/// an enclosing instance. `None` leaves the name as written.
pub(crate) fn bare(
    hier: &HierarchicalIdentifier,
    prefix: &str,
    span: Span,
    select: &dyn Fn(&Expression) -> Expression,
) -> Option<Expression> {
    let name = hier.path.first()?.name.name.as_str();
    if hier.bound.as_decl().is_some() || hier.bound == Bound::GENVAR || stmt_local_declared(name) {
        return None;
    }
    let t = target(name, prefix)?;
    if t.storage == name && !t.contested {
        return None;
    }
    Some(reference(hier, &t, name, span, select))
}

/// §3.12.1: a compilation-unit class is declared in unit scope, so a name
/// in its body that no member, formal or local declares is the unit's, not
/// a declaration of the module whose process happens to run the method.
/// `map` gives each such name its qualified spelling; `members` are the
/// names the classes of the design declare, which hide a unit name.
pub(crate) fn qualify_class_body(
    c: &mut ClassDeclaration,
    map: &std::collections::HashMap<String, String>,
    members: &dyn Fn(&ClassDeclaration) -> std::collections::HashSet<String>,
) {
    let hidden = members(c);
    let map: std::collections::HashMap<String, String> = map
        .iter()
        .filter(|(name, _)| !hidden.contains(*name))
        .map(|(a, b)| (a.clone(), b.clone()))
        .collect();
    if map.is_empty() {
        return;
    }
    let body = |items: &[Statement], ports: &[FunctionPort]| -> Option<Vec<Statement>> {
        let mut map = map.clone();
        for p in ports {
            map.remove(&p.name.name);
        }
        for n in stmt_list_declared_names(items) {
            map.remove(n);
        }
        (!map.is_empty()).then(|| {
            items
                .iter()
                .map(|s| substitute_bare_idents_stmt(s, &map))
                .collect()
        })
    };
    for item in &mut c.items {
        match item {
            ClassItem::Property(p) => {
                for d in &mut p.declarators {
                    if let Some(init) = &mut d.init {
                        let stmt =
                            Statement::new(StatementKind::Expr(init.as_ref().clone()), init.span);
                        if let StatementKind::Expr(e) =
                            substitute_bare_idents_stmt(&stmt, &map).kind
                        {
                            **init = e;
                        }
                    }
                }
            }
            ClassItem::Method(m) => match &mut m.kind {
                ClassMethodKind::Function(f) | ClassMethodKind::Extern(f) => {
                    if let Some(items) = body(&f.items, &f.ports) {
                        f.items = items.into();
                    }
                }
                ClassMethodKind::Task(t) => {
                    if let Some(items) = body(&t.items, &t.ports) {
                        t.items = items.into();
                    }
                }
                ClassMethodKind::PureVirtual(_) => {}
            },
            _ => {}
        }
    }
}
