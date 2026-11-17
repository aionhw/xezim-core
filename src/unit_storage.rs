//! §3.12.1 / §6.7 / §6.8: the variables and nets of the compilation unit
//! are declared once, in the hierarchy root, so every module, interface,
//! program, unit subroutine and unit class names the same object.

use crate::ast::decl::{
    ClassDeclaration, ClassItem, ClassMethodKind, DataDeclaration, ModuleItem, NetDeclaration,
    ParameterDeclaration, ParameterKind,
};
use crate::ast::stmt::{Statement, StatementKind};
use crate::elaborate::unit_storage::Target;
use crate::hasher::HashMap;
use crate::{SourceDefinition, design_declared_names, elaborate, scope_tree, sv_parser};
use std::rc::Rc;

/// Declare the unit's storage in `root` and record where each name lives.
/// `single` is false when no hierarchy root can hold it: each definition
/// then keeps the declarations it received.
pub(crate) fn settle(
    definitions: &mut HashMap<String, SourceDefinition>,
    single: bool,
    root: &str,
    vars: &[DataDeclaration],
    nets: &[NetDeclaration],
    params: &[ParameterDeclaration],
    shadowed_classes: &mut HashMap<String, Rc<ClassDeclaration>>,
) {
    let mut targets: HashMap<String, Target> = HashMap::default();
    if !single || (vars.is_empty() && nets.is_empty()) {
        elaborate::unit_storage::set(targets);
        return;
    }
    let Some((ports, own_params, items)) = (match definitions.get_mut(root) {
        Some(SourceDefinition::Module(m)) => {
            let m = Rc::make_mut(m);
            Some((&m.ports, &m.params, &mut m.items))
        }
        Some(SourceDefinition::Program(p)) => {
            let p = Rc::make_mut(p);
            Some((&p.ports, &p.params, &mut p.items))
        }
        Some(SourceDefinition::Interface(i)) => {
            let i = Rc::make_mut(i);
            Some((&i.ports, &i.params, &mut i.items))
        }
        _ => None,
    }) else {
        elaborate::unit_storage::set(targets);
        return;
    };
    // A declaration of the root shadows the unit's (§3.12.1): the unit
    // object keeps the reserved name `$unit::<name>` there.
    let local = design_declared_names(ports, own_params, items);
    let shadowed = |name: &str| local.contains(name);
    let mut renames: std::collections::HashMap<String, String> = vars
        .iter()
        .flat_map(|d| d.declarators.iter().map(|v| &v.name.name))
        .chain(
            nets.iter()
                .flat_map(|n| n.declarators.iter().map(|v| &v.name.name)),
        )
        .filter(|name| shadowed(name))
        .map(|name| (name.clone(), sv_parser::unit_scope_name(name)))
        .collect();
    for name in vars
        .iter()
        .flat_map(|d| d.declarators.iter().map(|v| &v.name.name))
        .chain(
            nets.iter()
                .flat_map(|n| n.declarators.iter().map(|v| &v.name.name)),
        )
    {
        let storage = renames.get(name).cloned().unwrap_or_else(|| name.clone());
        targets.insert(
            name.clone(),
            Target {
                storage,
                contested: false,
            },
        );
    }
    renames.extend(params.iter().flat_map(|p| {
        match &p.kind {
            ParameterKind::Data { assignments, .. } => assignments
                .iter()
                .filter(|a| shadowed(&a.name.name))
                .map(|a| {
                    (
                        a.name.name.clone(),
                        sv_parser::unit_scope_name(&a.name.name),
                    )
                })
                .collect::<Vec<_>>(),
            _ => Vec::new(),
        }
    }));
    for d in vars.iter().rev() {
        if !d.declarators.iter().any(|v| shadowed(&v.name.name)) {
            items.insert(0, ModuleItem::DataDeclaration(d.clone()));
            continue;
        }
        // `int a, b;` where only `b` is shadowed: each declarator lands
        // under its own name.
        let (hidden, plain): (Vec<_>, Vec<_>) = d
            .declarators
            .iter()
            .cloned()
            .partition(|v| shadowed(&v.name.name));
        let mut dd = d.clone();
        dd.declarators = hidden;
        for v in dd.declarators.iter_mut() {
            v.name.name = sv_parser::unit_scope_name(&v.name.name);
        }
        items.insert(0, ModuleItem::DataDeclaration(dd));
        if !plain.is_empty() {
            let mut dd = d.clone();
            dd.declarators = plain;
            items.insert(0, ModuleItem::DataDeclaration(dd));
        }
    }
    // A unit net's driver expression is written in unit scope.
    for net in nets.iter().rev() {
        let mut net = net.clone();
        for decl in &mut net.declarators {
            if shadowed(&decl.name.name) {
                decl.name.name = sv_parser::unit_scope_name(&decl.name.name);
            }
            if let Some(init) = &mut decl.init {
                let stmt = Statement::new(StatementKind::Expr(init.clone()), init.span);
                if let StatementKind::Expr(expr) =
                    elaborate::substitute_bare_idents_stmt(&stmt, &renames).kind
                {
                    *init = expr;
                }
            }
        }
        items.insert(0, ModuleItem::NetDeclaration(net));
    }
    // A plain name that another scope of the design declares can be taken
    // by an enclosing instance of a reference: those references are rooted.
    for (name, def) in definitions.iter() {
        let own = match def {
            SourceDefinition::Module(m) => design_declared_names(&m.ports, &m.params, &m.items),
            SourceDefinition::Program(p) => design_declared_names(&p.ports, &p.params, &p.items),
            SourceDefinition::Interface(i) => design_declared_names(&i.ports, &i.params, &i.items),
            _ => continue,
        };
        if name != root {
            for n in &own {
                if let Some(t) = targets.get_mut(n) {
                    t.contested = true;
                }
            }
        }
        if let Some(tree) = scope_tree::tree_of(name) {
            for d in &tree.decls {
                if name == root && d.scope == tree.root {
                    continue;
                }
                if let Some(t) = targets.get_mut(&d.name) {
                    t.contested = true;
                }
            }
        }
    }
    // §3.12.1: a unit class body names the unit's storage past any module
    // declaration of the same name.
    let qualified: std::collections::HashMap<String, String> = targets
        .iter()
        .filter(|(name, t)| t.contested || t.storage != **name)
        .map(|(name, _)| (name.clone(), sv_parser::unit_scope_name(name)))
        .collect();
    if !qualified.is_empty() {
        let classes: HashMap<String, Rc<ClassDeclaration>> = definitions
            .iter()
            .filter_map(|(name, def)| match def {
                SourceDefinition::Class(c) => Some((name.clone(), Rc::clone(c))),
                _ => None,
            })
            .chain(
                shadowed_classes
                    .iter()
                    .map(|(n, c)| (n.clone(), Rc::clone(c))),
            )
            .collect();
        let all: std::collections::HashSet<String> = qualified.keys().cloned().collect();
        let members = |c: &ClassDeclaration| class_scope_names(c, &classes, &all);
        for def in definitions.values_mut() {
            if let SourceDefinition::Class(c) = def {
                elaborate::unit_storage::qualify_class_body(Rc::make_mut(c), &qualified, &members);
            }
        }
        for c in shadowed_classes.values_mut() {
            elaborate::unit_storage::qualify_class_body(Rc::make_mut(c), &qualified, &members);
        }
    }
    elaborate::unit_storage::set(targets);
}

/// The names a class body sees before unit scope: its own members and
/// parameters, nested declarations and those of its base classes. A base
/// that is not a unit class may declare any name: `all` hides them all.
fn class_scope_names(
    c: &ClassDeclaration,
    classes: &HashMap<String, Rc<ClassDeclaration>>,
    all: &std::collections::HashSet<String>,
) -> std::collections::HashSet<String> {
    let mut names = std::collections::HashSet::new();
    let mut at = Some(c);
    let mut depth = 0;
    while let Some(c) = at {
        for p in &c.params {
            match &p.kind {
                ParameterKind::Data { assignments, .. } => {
                    names.extend(assignments.iter().map(|a| a.name.name.clone()))
                }
                ParameterKind::Type { assignments } => {
                    names.extend(assignments.iter().map(|a| a.name.name.clone()))
                }
            }
        }
        for item in &c.items {
            match item {
                ClassItem::Property(p) => {
                    names.extend(p.declarators.iter().map(|d| d.name.name.clone()))
                }
                ClassItem::Method(m) => match &m.kind {
                    ClassMethodKind::Function(f)
                    | ClassMethodKind::PureVirtual(f)
                    | ClassMethodKind::Extern(f) => {
                        names.insert(f.name.name.name.clone());
                    }
                    ClassMethodKind::Task(t) => {
                        names.insert(t.name.name.name.clone());
                    }
                },
                ClassItem::Parameter(p) => {
                    if let ParameterKind::Data { assignments, .. } = &p.kind {
                        names.extend(assignments.iter().map(|a| a.name.name.clone()));
                    }
                }
                ClassItem::Typedef(t) => {
                    names.insert(t.name.name.clone());
                }
                ClassItem::Class(i) => {
                    names.insert(i.name.name.clone());
                }
                _ => {}
            }
        }
        at = match &c.extends {
            None => None,
            Some(e) => match classes.get(&e.name.name).filter(|_| e.scopes.is_empty()) {
                Some(base) if depth < 64 => Some(&**base),
                _ => return all.clone(),
            },
        };
        depth += 1;
    }
    names
}
