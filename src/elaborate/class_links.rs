use super::*;

/// LRM §6.20.3 / §8.4: any signal whose declared `type_name` resolves to a
/// known class default-initialises to 0 (the null handle) rather than X.
/// Without this, untouched class handle declarations read as X, defeating
/// `if (h == null)` and similar guards. Runs for the root module and again
/// after inlining, which is where instance-scoped handles appear.
pub fn null_init_class_handles(elab: &mut ElaboratedModule) {
    let cls_names: std::collections::HashSet<String> = elab.classes.keys().cloned().collect();
    for sig in elab.signals.values_mut() {
        if let Some(tn) = &sig.type_name {
            if cls_names.contains(tn) {
                sig.value = Value::zero(sig.width);
            }
        }
    }
}

/// Link out-of-class method bodies (`function ClassName::m(); ... endfunction`)
/// into their classes, replacing the `extern` prototype with the real body.
/// Run after `inline_instantiations`, which (re)populates `elab.classes` from
/// the AST and would otherwise clobber any earlier linking.
pub fn link_extern_methods(elab: &mut ElaboratedModule, definitions: &HashMap<String, Definition>) {
    use crate::ast::decl::{ClassMethod, ClassMethodKind, PackageItem};
    // Attach a single out-of-body method body to its class (replacing the
    // `extern`/pure prototype, or inserting if none). Returns true if it was
    // an out-of-body method (had a `ClassName::` scope).
    let mut attach = |class_name: String, method_name: String, kind: ClassMethodKind, span: _| {
        // §8.24/§8.23: `outer::inner::m` names the nested class, which is
        // registered both under its chain and its own name: attach to each.
        // The bare key may hold another class — a top-level `class inner`
        // (`pkg_scope` then renames this one `outer::inner`) or a `B::inner`
        // registered first — so attach there only when it is enclosed by
        // the same class as the chained one.
        let mut keys: Vec<String> = vec![class_name.clone()];
        if let Some((_, last)) = class_name.rsplit_once("::") {
            let enclosing = |key: &str| elab.classes.get(key).map(|c| c.enclosing.clone());
            if let Some(Some(outer)) = enclosing(&class_name)
                && enclosing(last) == Some(Some(outer))
            {
                keys.push(last.to_string());
            }
        }
        for key in keys {
            let Some(shared) = elab.classes.get(&key) else {
                continue;
            };
            // §8.24 / §26.3: imported and package-qualified spellings name
            // the same class. Preserve that identity when attaching an extern
            // body: mutating only one Arc entry leaves the other spelling's
            // prototype unlinked (including constructors reached via aliases).
            let aliases: Vec<String> = elab
                .classes
                .iter()
                .filter(|(_, cls)| std::sync::Arc::ptr_eq(cls, shared))
                .map(|(name, _)| name.clone())
                .collect();
            // Take every alias entry out first, so the class's Arc is unique
            // and `make_mut` edits it in place: cloning it per extern body
            // deep-copied the class and its methods for every body.
            let mut linked = elab.classes.remove(&key).expect("present");
            for alias in aliases.iter().filter(|a| **a != key) {
                elab.classes.remove(alias);
            }
            let cls = std::sync::Arc::make_mut(&mut linked);
            let methods = std::sync::Arc::make_mut(&mut cls.methods);
            if let Some(existing) = methods.get_mut(&method_name) {
                existing.kind = kind.clone();
            } else {
                methods.insert(
                    method_name.clone(),
                    ClassMethod {
                        qualifiers: Vec::new(),
                        kind: kind.clone(),
                        span,
                    },
                );
            }
            for alias in aliases {
                elab.classes.insert(alias, linked.clone());
            }
        }
    };
    for def in definitions.values() {
        // Out-of-body method definitions (`function Class::m(); ...`) appear
        // in these places depending on where the source wrote them:
        //   * `Definition::Package` items (a function inside a `package ... endpackage`),
        //   * `Definition::Module/Interface/Program` items — compilation-unit-
        //     scope (`$unit`) functions are injected into EVERY module by the
        //     driver (see lib.rs), and UVM's `uvm_sequencer::new` etc. are
        //     written this way. Scanning only packages (the old behaviour)
        //     left `$unit` out-of-body bodies unlinked, so `new`/methods kept
        //     their empty `extern` prototype and field initializers like
        //     `seq_item_export = new(...)` never ran — every handle field
        //     stayed null, surfacing as "Cannot connect to null port handle".
        //   * class bodies: the declaration scope of nested classes (#842).
        match def {
            Definition::Package(p) => {
                for item in &p.items {
                    match item {
                        PackageItem::Function(f) if f.name.has_scope() => {
                            let scope = f
                                .name
                                .scopes
                                .iter()
                                .map(|s| s.name.name.as_str())
                                .collect::<Vec<_>>()
                                .join("::");
                            attach(
                                scope,
                                f.name.name.name.clone(),
                                ClassMethodKind::Function(f.clone()),
                                f.span,
                            );
                        }
                        PackageItem::Task(t) if t.name.has_scope() => {
                            let scope = t
                                .name
                                .scopes
                                .iter()
                                .map(|s| s.name.name.as_str())
                                .collect::<Vec<_>>()
                                .join("::");
                            attach(
                                scope,
                                t.name.name.name.clone(),
                                ClassMethodKind::Task(t.clone()),
                                t.span,
                            );
                        }
                        PackageItem::Class(c) => {
                            let owner = nested_class_owner(Some(&p.name.name), c);
                            link_class_items(c, &owner, &mut attach);
                        }
                        _ => {}
                    }
                }
            }
            Definition::Module(m) => link_module_items(&m.items, &mut attach),
            Definition::Interface(i) => link_module_items(&i.items, &mut attach),
            Definition::Program(p) => link_module_items(&p.items, &mut attach),
            Definition::Class(c) => link_class_items(c, &c.name.name, &mut attach),
            _ => {}
        }
    }
}

/// §8.23/§26.3: colliding class names have already been qualified by
/// `pkg_scope`; otherwise extend the lexical enclosing class/package.
pub(super) fn nested_class_owner(enclosing: Option<&str>, c: &ClassDeclaration) -> String {
    let name = &c.name.name;
    match enclosing {
        Some(outer) => nested_scope_name(outer, name),
        _ => name.clone(),
    }
}

/// A class-scoped name may already include its enclosing class chain but
/// omit the package prefix (`Outer::Inner` inside `pkg::Outer`). Retain the
/// longest existing overlap instead of repeating that chain.
pub(super) fn nested_scope_name(enclosing: &str, name: &str) -> String {
    let matches = |scope: &str| name == scope || name.starts_with(&format!("{scope}::"));
    if matches(enclosing) {
        return name.to_string();
    }
    for (at, _) in enclosing.match_indices("::") {
        if matches(&enclosing[at + 2..]) {
            return format!("{}::{name}", &enclosing[..at]);
        }
    }
    format!("{enclosing}::{name}")
}

/// §8.24 (#842): the enclosing class body is the declaration scope of a
/// nested class's out-of-block methods. Reuse the ordinary extern linker
/// so constructors, qualifiers and the class table's aliases stay intact.
fn link_class_items<F>(class: &ClassDeclaration, owner: &str, attach: &mut F)
where
    F: FnMut(String, String, crate::ast::decl::ClassMethodKind, crate::ast::Span),
{
    let target =
        |name: &crate::ast::types::TypeName| nested_scope_name(owner, &name.scope_prefix());
    for item in &class.items {
        match item {
            ClassItem::Method(method) => match &method.kind {
                ClassMethodKind::Function(f) if f.name.has_scope() => attach(
                    target(&f.name),
                    f.name.name.name.clone(),
                    ClassMethodKind::Function(f.clone()),
                    f.span,
                ),
                ClassMethodKind::Task(t) if t.name.has_scope() => attach(
                    target(&t.name),
                    t.name.name.name.clone(),
                    ClassMethodKind::Task(t.clone()),
                    t.span,
                ),
                _ => {}
            },
            ClassItem::Class(inner) => {
                let inner_owner = nested_class_owner(Some(owner), inner);
                link_class_items(inner, &inner_owner, attach);
            }
            _ => {}
        }
    }
}

/// Helper for `link_extern_methods`: scan a module/interface/program body's
/// items for out-of-body class method definitions (`ModuleItem::Function` /
/// `Task` whose name carries a `ClassName::` scope) and attach each to its
/// class. Mirrors the package-item path; `ModuleItem` and `PackageItem` wrap
/// the same `FunctionDeclaration`/`TaskDeclaration` types.
fn link_module_items<F>(items: &[crate::ast::decl::ModuleItem], attach: &mut F)
where
    F: FnMut(String, String, crate::ast::decl::ClassMethodKind, crate::ast::Span),
{
    use crate::ast::decl::{ClassMethodKind, ModuleItem};
    for item in items {
        match item {
            ModuleItem::FunctionDeclaration(f) if f.name.has_scope() => {
                let scope = f
                    .name
                    .scopes
                    .iter()
                    .map(|s| s.name.name.as_str())
                    .collect::<Vec<_>>()
                    .join("::");
                attach(
                    scope,
                    f.name.name.name.clone(),
                    ClassMethodKind::Function(f.clone()),
                    f.span,
                );
            }
            ModuleItem::TaskDeclaration(t) if t.name.has_scope() => {
                let scope = t
                    .name
                    .scopes
                    .iter()
                    .map(|s| s.name.name.as_str())
                    .collect::<Vec<_>>()
                    .join("::");
                attach(
                    scope,
                    t.name.name.name.clone(),
                    ClassMethodKind::Task(t.clone()),
                    t.span,
                );
            }
            ModuleItem::ClassDeclaration(c) => link_class_items(c, &c.name.name, attach),
            _ => {}
        }
    }
}
