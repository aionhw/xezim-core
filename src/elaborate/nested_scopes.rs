use super::*;

/// Inline module instantiations: replace instances with their continuous assigns and always blocks.
/// §8.23 nested class declarations: hoist each `class Inner` found inside a
/// class body into the class table, keyed BOTH as `Outer::Inner` (the
/// qualified reference form) and — first declaration wins — as the bare
/// inner name. Records the enclosing class so methods of the inner class
/// can resolve the outer class's statics. Without this the inner class was
/// silently invisible: `Outer::Inner x = new;` produced a null handle.
///
/// Returns every fully-qualified key inserted (`Outer::Inner`, and
/// recursively `Outer::Inner::Deep`, ...), so a caller that also needs an
/// alternate leading scope — e.g. the package-qualified `pkg::Outer::Inner`
/// — can alias the SAME `Arc` onto those keys instead of re-elaborating the
/// whole nested subtree once per outer spelling.
pub(super) fn register_nested_classes(
    c: &crate::ast::decl::ClassDeclaration,
    outer: &str,
    elab: &mut ElaboratedModule,
) -> Vec<String> {
    let mut all_scoped: Vec<String> = Vec::new();
    for item in &c.items {
        if let ClassItem::Class(inner) = item {
            let with_outer;
            let inner = if c.params.is_empty() {
                inner
            } else {
                with_outer = with_enclosing_params(c, inner);
                &with_outer
            };
            register_class_enum_members(inner, elab);
            let mut cls = elaborate_class_with_params(inner, Some(&elab.parameters));
            cls.enclosing = Some(outer.to_string());
            // pkg_scope may already have qualified a colliding inner name.
            // Do not repeat the enclosing scope: package aliases must remain
            // spellable as `pkg::Outer#(...)::Inner` (#842).
            let scoped = nested_class_owner(Some(outer), inner);
            let cls = std::sync::Arc::new(cls);
            elab.classes.insert(scoped.clone(), cls.clone());
            elab.classes.entry(inner.name.name.clone()).or_insert(cls);
            all_scoped.push(scoped.clone());
            // delve deeper; prepend each descendant key with its parents.
            all_scoped.extend(register_nested_classes(inner, &scoped, elab));
        }
    }
    all_scoped
}

/// §8.23/§8.25: a class nested in a parameterized class sees the enclosing
/// class's parameters, which differ per specialization of the enclosing
/// class. The nested class is elaborated with those parameters prepended to
/// its own (minus any it redeclares), so its members sized or typed by them
/// follow the specialization each object is built in (the runtime binds them
/// from the enclosing object, see `instantiate_class_with_type_args`).
fn with_enclosing_params(
    outer: &crate::ast::decl::ClassDeclaration,
    inner: &crate::ast::decl::ClassDeclaration,
) -> crate::ast::decl::ClassDeclaration {
    use crate::ast::decl::ParameterKind;
    let mut own: HashSet<String> = HashSet::default();
    for p in &inner.params {
        match &p.kind {
            ParameterKind::Data { assignments, .. } => {
                own.extend(assignments.iter().map(|a| a.name.name.clone()))
            }
            ParameterKind::Type { assignments } => {
                own.extend(assignments.iter().map(|a| a.name.name.clone()))
            }
        }
    }
    for it in &inner.items {
        match it {
            ClassItem::Typedef(td) => {
                own.insert(td.name.name.clone());
            }
            ClassItem::Class(nc) => {
                own.insert(nc.name.name.clone());
            }
            _ => {}
        }
    }
    let mut params = Vec::new();
    for p in &outer.params {
        let mut p = p.clone();
        let keep = match &mut p.kind {
            ParameterKind::Data { assignments, .. } => {
                assignments.retain(|a| !own.contains(&a.name.name));
                !assignments.is_empty()
            }
            ParameterKind::Type { assignments } => {
                assignments.retain(|a| !own.contains(&a.name.name));
                !assignments.is_empty()
            }
        };
        if keep {
            params.push(p);
        }
    }
    let mut out = inner.clone();
    params.append(&mut out.params);
    out.params = params;
    out
}

/// §16.8, §16.12: record the default actual arguments of the named sequence
/// or property registered as `key`. A redeclaration without any drops the
/// ones an earlier declaration of the name left.
pub(super) fn register_sva_port_defaults(
    elab: &mut ElaboratedModule,
    key: &str,
    defaults: &[Option<Expression>],
) {
    if defaults.iter().any(|d| d.is_some()) {
        elab.property_param_defaults
            .insert(key.to_string(), defaults.to_vec());
    } else {
        elab.property_param_defaults.remove(key);
    }
}
