//! §6.21: accepting an implicit static initializer preserves static lifetime.
//! Normalize accepted declarations before instance rewriting and bytecode
//! preparation, so all execution paths see the same explicit lifetime.

use super::{
    ElaboratedModule, StaticInitScope, collect_expr_idents, relax_implicit_static, span_location_of,
};
use crate::SourceDefinition;
use crate::ast::decl::{ClassDeclaration, ClassItem, ClassMethodKind, ModuleItem, PackageItem};
use crate::ast::stmt::{ForInit, Statement, StatementKind};
use crate::ast::types::Lifetime;
use crate::hasher::{HashMap, HashSet};
use std::rc::Rc;

pub(crate) fn normalize(definitions: &mut HashMap<String, SourceDefinition>) {
    if !relax_implicit_static() {
        return;
    }
    // Source maps are already published; an empty elaboration context uses
    // those maps while the original declaration offsets are still intact.
    let source = ElaboratedModule::new(String::new());
    for definition in definitions.values_mut() {
        match definition {
            SourceDefinition::Module(m) => {
                let m = Rc::make_mut(m);
                items(
                    &mut m.items,
                    m.lifetime != Some(Lifetime::Automatic),
                    Scope::new(&source, "module", &m.name.name),
                );
            }
            SourceDefinition::Interface(m) => {
                let m = Rc::make_mut(m);
                items(
                    &mut m.items,
                    m.lifetime != Some(Lifetime::Automatic),
                    Scope::new(&source, "interface", &m.name.name),
                );
            }
            SourceDefinition::Program(m) => {
                let m = Rc::make_mut(m);
                items(
                    &mut m.items,
                    m.lifetime != Some(Lifetime::Automatic),
                    Scope::new(&source, "program", &m.name.name),
                );
            }
            SourceDefinition::Package(p) => {
                let p = Rc::make_mut(p);
                let default_static = p.lifetime != Some(Lifetime::Automatic);
                for item in &mut p.items {
                    match item {
                        // §8.6/§8.24: an out-of-block class method (`C::m`)
                        // is automatic whatever the package's default (#621).
                        PackageItem::Function(f)
                            if is_static(f.lifetime, default_static)
                                && f.name.scopes.is_empty() =>
                        {
                            statements(
                                &mut f.items,
                                &HashSet::default(),
                                Scope::new(&source, "package", &p.name.name)
                                    .subroutine("function", &f.name.name.name),
                            );
                        }
                        PackageItem::Task(t)
                            if is_static(t.lifetime, default_static)
                                && t.name.scopes.is_empty() =>
                        {
                            statements(
                                &mut t.items,
                                &HashSet::default(),
                                Scope::new(&source, "package", &p.name.name)
                                    .subroutine("task", &t.name.name.name),
                            );
                        }
                        PackageItem::Class(c) => {
                            class(c, Scope::new(&source, "package", &p.name.name))
                        }
                        _ => {}
                    }
                }
            }
            SourceDefinition::Class(c) => {
                let owner = c.name.name.clone();
                class(Rc::make_mut(c), Scope::new(&source, "class", &owner));
            }
            _ => {}
        }
    }
}

#[derive(Clone, Copy)]
struct Scope<'a> {
    source: &'a ElaboratedModule,
    file_owner: &'a str,
    details: StaticInitScope<'a>,
}

impl<'a> Scope<'a> {
    fn new(source: &'a ElaboratedModule, owner_kind: &'a str, owner: &'a str) -> Self {
        Self {
            source,
            file_owner: owner,
            details: StaticInitScope {
                kind: "block",
                name: owner,
                owner_kind,
                owner,
            },
        }
    }

    fn subroutine(self, kind: &'a str, name: &'a str) -> Self {
        Self {
            details: StaticInitScope {
                kind,
                name,
                ..self.details
            },
            ..self
        }
    }
}

fn is_static(lifetime: Option<Lifetime>, default_static: bool) -> bool {
    match lifetime {
        Some(Lifetime::Static) => true,
        Some(Lifetime::Automatic) => false,
        None => default_static,
    }
}

fn class(c: &mut ClassDeclaration, scope: Scope<'_>) {
    let scope = Scope {
        details: StaticInitScope {
            owner_kind: "class",
            owner: &c.name.name,
            ..scope.details
        },
        ..scope
    };
    for item in &mut c.items {
        match item {
            // A static method qualifier does not change the automatic
            // lifetime of its variables (§8.6); only a lifetime does.
            ClassItem::Method(m) => match &mut m.kind {
                ClassMethodKind::Function(f) if is_static(f.lifetime, false) => {
                    statements(
                        &mut f.items,
                        &HashSet::default(),
                        scope.subroutine("function", &f.name.name.name),
                    );
                }
                ClassMethodKind::Task(t) if is_static(t.lifetime, false) => {
                    statements(
                        &mut t.items,
                        &HashSet::default(),
                        scope.subroutine("task", &t.name.name.name),
                    );
                }
                _ => {}
            },
            ClassItem::Class(nested) => class(nested, scope),
            _ => {}
        }
    }
}

fn items(body: &mut [ModuleItem], default_static: bool, scope: Scope<'_>) {
    for item in body {
        match item {
            ModuleItem::FunctionDeclaration(f)
                if is_static(f.lifetime, default_static) && f.name.scopes.is_empty() =>
            {
                statements(
                    &mut f.items,
                    &HashSet::default(),
                    scope.subroutine("function", &f.name.name.name),
                );
            }
            ModuleItem::TaskDeclaration(t)
                if is_static(t.lifetime, default_static) && t.name.scopes.is_empty() =>
            {
                statements(
                    &mut t.items,
                    &HashSet::default(),
                    scope.subroutine("task", &t.name.name.name),
                );
            }
            ModuleItem::InitialConstruct(i) if default_static => {
                statement(&mut i.stmt, &mut HashSet::default(), scope);
            }
            ModuleItem::AlwaysConstruct(a) if default_static => {
                statement(&mut a.stmt, &mut HashSet::default(), scope);
            }
            ModuleItem::FinalConstruct(f) if default_static => {
                statement(&mut f.stmt, &mut HashSet::default(), scope);
            }
            ModuleItem::GenerateRegion(g) => items(&mut g.items, default_static, scope),
            ModuleItem::GenerateFor(g) => items(&mut g.items, default_static, scope),
            ModuleItem::GenerateIf(g) => {
                for (_, branch) in &mut g.branches {
                    items(branch, default_static, scope);
                }
            }
            ModuleItem::GenerateCase(g) => {
                for arm in &mut g.arms {
                    items(&mut arm.items, default_static, scope);
                }
            }
            ModuleItem::ClassDeclaration(c) => class(c, scope),
            ModuleItem::NestedModule(m) => {
                items(
                    &mut m.items,
                    m.lifetime != Some(Lifetime::Automatic),
                    Scope::new(scope.source, "module", &m.name.name),
                );
            }
            _ => {}
        }
    }
}

fn statements(body: &mut [Statement], automatic: &HashSet<String>, scope: Scope<'_>) {
    let mut automatic = automatic.clone();
    for s in body {
        statement(s, &mut automatic, scope);
    }
}

fn statement(s: &mut Statement, automatic: &mut HashSet<String>, scope: Scope<'_>) {
    match &mut s.kind {
        StatementKind::VarDecl {
            lifetime,
            declarators,
            ..
        } => {
            if *lifetime == Some(Lifetime::Automatic) {
                automatic.extend(declarators.iter().map(|d| d.name.name.clone()));
            } else if lifetime.is_none() && declarators.iter().any(|d| d.init.is_some()) {
                // Keep the permissive behavior for an initializer reading an
                // automatic loop/block variable; a static initializer cannot
                // legally refer to that variable (§6.21).
                let captures_automatic =
                    declarators.iter().filter_map(|d| d.init.as_ref()).any(|e| {
                        let mut names = HashSet::default();
                        collect_expr_idents(e, &mut names);
                        names.iter().any(|name| automatic.contains(name))
                    });
                if !captures_automatic {
                    *lifetime = Some(Lifetime::Static);
                    for d in declarators.iter().filter(|d| d.init.is_some()) {
                        crate::log_eprintln(&format!(
                            "[xezim][warning] variable '{}' is implicitly static (§6.21); \
                             accepted because --relax-implicit-static is in effect\n  \
                             in {} '{}' of {} '{}'{}",
                            d.name.name,
                            scope.details.kind,
                            scope.details.name,
                            scope.details.owner_kind,
                            scope.details.owner,
                            span_location_of(scope.source, d.name.span, scope.file_owner)
                                .map(|loc| format!(" at {}", loc))
                                .unwrap_or_default()
                        ));
                    }
                }
            }
        }
        StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
            statements(stmts, automatic, scope);
        }
        StatementKind::For { init, body, .. } => {
            let mut loop_automatic = automatic.clone();
            for i in init {
                if let ForInit::VarDecl { name, .. } = i {
                    loop_automatic.insert(name.name.clone());
                }
            }
            statement(body, &mut loop_automatic, scope);
        }
        StatementKind::Foreach { vars, body, .. } => {
            let mut loop_automatic = automatic.clone();
            loop_automatic.extend(vars.iter().flatten().map(|v| v.name.clone()));
            statement(body, &mut loop_automatic, scope);
        }
        StatementKind::If {
            then_stmt,
            else_stmt,
            ..
        } => {
            statement(then_stmt, &mut automatic.clone(), scope);
            if let Some(e) = else_stmt {
                statement(e, &mut automatic.clone(), scope);
            }
        }
        StatementKind::Case { items, .. } => {
            for i in items {
                statement(&mut i.stmt, &mut automatic.clone(), scope);
            }
        }
        StatementKind::While { body, .. }
        | StatementKind::DoWhile { body, .. }
        | StatementKind::Repeat { body, .. }
        | StatementKind::Forever { body }
        | StatementKind::TimingControl { stmt: body, .. }
        | StatementKind::Wait { stmt: body, .. } => statement(body, automatic, scope),
        _ => {}
    }
}
