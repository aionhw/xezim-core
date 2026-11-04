//! IEEE 1800-2023 §8.17: constructor argument forwarding.
//!
//! * `function new(default);` takes the argument list of the nearest base
//!   constructor that declares one (an empty list when no base does) and,
//!   when the class has a base, opens with `super.new` of those arguments
//!   unless its body calls `super.new` itself.
//! * `extends Base(default)` on a class with an explicit constructor opens
//!   that constructor the same way; a class with no constructor of its own
//!   already hands its `new` arguments to the base at run time.
//! * `super.new(default)` in a constructor body is `super.new` with the
//!   constructor's formals, in order.
//!
//! Rewrites the parsed descriptions before they are registered, so every
//! registry sees one declaration and the formals exist by the time a
//! constructor body is checked for undeclared names. A formal is copied
//! whole, so its declared type and default value travel with it.

use crate::ast::{Description, Identifier};
use crate::ast::decl::{
    ClassDeclaration, ClassItem, ClassMethodKind, FunctionDeclaration, FunctionPort, ModuleItem,
    PackageItem,
};
use crate::ast::expr::{ExprKind, Expression, HierPathSegment, HierarchicalIdentifier};
use crate::ast::stmt::{Statement, StatementKind};
use crate::hasher::HashMap;

/// A constructor declaration: in its class, or an out-of-body
/// `function C::new(...)` (`class` names the class).
enum Site<'a> {
    Class(&'a mut ClassDeclaration),
    OutOfBody {
        class: String,
        func: &'a mut FunctionDeclaration,
    },
}

#[derive(Clone, Default)]
struct Ctor {
    ports: Vec<FunctionPort>,
    default_args: bool,
}

/// The constructor declared in the class body, if any.
fn class_ctor(c: &mut ClassDeclaration) -> Option<&mut FunctionDeclaration> {
    c.items.iter_mut().find_map(|it| match it {
        ClassItem::Method(m) => match &mut m.kind {
            ClassMethodKind::Function(f) | ClassMethodKind::Extern(f)
                if f.name.scopes.is_empty() && f.name.name.name == "new" =>
            {
                Some(f)
            }
            _ => None,
        },
        _ => None,
    })
}

fn out_of_body_ctor(f: &FunctionDeclaration) -> Option<String> {
    (f.name.name.name == "new")
        .then(|| f.name.scopes.last().map(|s| s.name.name.clone()))
        .flatten()
}

fn package_item(item: &mut PackageItem, f: &mut dyn FnMut(Site<'_>)) {
    match item {
        PackageItem::Class(c) => class(c, f),
        PackageItem::Function(fd) => {
            if let Some(class) = out_of_body_ctor(fd) {
                f(Site::OutOfBody { class, func: fd });
            }
        }
        _ => {}
    }
}

fn walk(descriptions: &mut [Description], f: &mut dyn FnMut(Site<'_>)) {
    for d in descriptions.iter_mut() {
        match d {
            Description::Module(m) => items(&mut m.items, f),
            Description::Interface(m) => items(&mut m.items, f),
            Description::Program(m) => items(&mut m.items, f),
            Description::Package(p) => {
                for item in &mut p.items {
                    package_item(item, f);
                }
            }
            Description::Class(c) => class(c, f),
            Description::PackageItem(item) => package_item(item, f),
            _ => {}
        }
    }
}

fn class(c: &mut ClassDeclaration, f: &mut dyn FnMut(Site<'_>)) {
    for it in &mut c.items {
        if let ClassItem::Class(nested) = it {
            class(nested, f);
        }
    }
    f(Site::Class(c));
}

fn items(body: &mut [ModuleItem], f: &mut dyn FnMut(Site<'_>)) {
    for item in body {
        match item {
            ModuleItem::ClassDeclaration(c) => class(c, f),
            ModuleItem::FunctionDeclaration(fd) => {
                if let Some(class) = out_of_body_ctor(fd) {
                    f(Site::OutOfBody { class, func: fd });
                }
            }
            ModuleItem::GenerateRegion(g) => items(&mut g.items, f),
            ModuleItem::GenerateFor(g) => items(&mut g.items, f),
            ModuleItem::GenerateIf(g) => {
                for (_, branch) in &mut g.branches {
                    items(branch, f);
                }
            }
            ModuleItem::GenerateCase(g) => {
                for arm in &mut g.arms {
                    items(&mut arm.items, f);
                }
            }
            ModuleItem::NestedModule(m) => items(&mut m.items, f),
            _ => {}
        }
    }
}

fn ident(path: &[&str], span: crate::ast::Span) -> Expression {
    Expression::new(
        ExprKind::Ident(HierarchicalIdentifier {
            root: None,
            path: path
                .iter()
                .map(|n| HierPathSegment {
                    name: Identifier {
                        name: n.to_string(),
                        span,
                    },
                    selects: Vec::new(),
                })
                .collect(),
            span,
            cached_signal_id: std::cell::Cell::new(None),
            cached_resolved_name: std::cell::OnceCell::new(),
        }),
        span,
    )
}

fn is_default_ident(e: &Expression) -> bool {
    matches!(&e.kind, ExprKind::Ident(h)
        if h.root.is_none()
            && h.path.len() == 1
            && h.path[0].name.name == "default"
            && h.path[0].selects.is_empty())
}

/// The argument list of a `super.new(...)` call expression.
fn super_new_args(e: &mut Expression) -> Option<&mut Vec<Expression>> {
    let ExprKind::Call { func, args } = &mut e.kind else {
        return None;
    };
    let is_super_new = match &func.kind {
        ExprKind::Ident(h) => {
            h.path.len() == 2 && h.path[0].name.name == "super" && h.path[1].name.name == "new"
        }
        ExprKind::MemberAccess { expr, member } => {
            member.name == "new"
                && matches!(&expr.kind, ExprKind::Ident(h)
                    if h.path.len() == 1 && h.path[0].name.name == "super")
        }
        _ => false,
    };
    is_super_new.then_some(args)
}

/// Expands `super.new(default)` in a constructor body; reports whether the
/// body calls `super.new` at all.
fn rewrite(stmts: &mut [Statement], formals: &[Expression], saw: &mut bool) {
    for s in stmts.iter_mut() {
        match &mut s.kind {
            StatementKind::Expr(e) => {
                if let Some(args) = super_new_args(e) {
                    *saw = true;
                    if args.len() == 1 && is_default_ident(&args[0]) {
                        *args = formals.to_vec();
                    }
                }
            }
            StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
                rewrite(stmts, formals, saw)
            }
            StatementKind::If {
                then_stmt,
                else_stmt,
                ..
            } => {
                rewrite(std::slice::from_mut(then_stmt), formals, saw);
                if let Some(e) = else_stmt {
                    rewrite(std::slice::from_mut(e), formals, saw);
                }
            }
            _ => {}
        }
    }
}

/// Rewrites one constructor: fills a `new(default)` argument list in,
/// expands `super.new(default)`, and opens a forwarding constructor with
/// the `super.new` call.
fn apply(f: &mut FunctionDeclaration, formals: &[FunctionPort], forwards: bool, has_base: bool) {
    if f.default_args {
        f.ports = formals.to_vec();
    }
    let span = f.span;
    let actuals: Vec<Expression> = formals
        .iter()
        .map(|p| ident(&[p.name.name.as_str()], p.span))
        .collect();
    let mut saw_super_new = false;
    rewrite(&mut f.items, &actuals, &mut saw_super_new);
    if forwards && has_base && !saw_super_new {
        let call = Expression::new(
            ExprKind::Call {
                func: Box::new(ident(&["super", "new"], span)),
                args: actuals,
            },
            span,
        );
        f.items.insert(0, Statement::new(StatementKind::Expr(call), span));
    }
}

pub(crate) fn forward(descriptions: &mut [Description]) {
    // Pass 1: every class's base and constructor argument list.
    let mut ctors: HashMap<String, Ctor> = HashMap::default();
    let mut bases: HashMap<String, (Option<String>, bool)> = HashMap::default();
    let mut any = false;
    walk(descriptions, &mut |site| match site {
        Site::Class(c) => {
            let name = c.name.name.clone();
            let ext = c.extends.as_ref();
            any |= ext.is_some_and(|e| e.default_args);
            bases.insert(
                name.clone(),
                (
                    ext.map(|e| e.name.name.clone()),
                    ext.is_some_and(|e| e.default_args),
                ),
            );
            if let Some(f) = class_ctor(c) {
                any |= f.default_args;
                let slot = ctors.entry(name).or_default();
                // An out-of-body definition seen first keeps its list.
                if slot.ports.is_empty() && !slot.default_args {
                    *slot = Ctor {
                        ports: f.ports.clone(),
                        default_args: f.default_args,
                    };
                }
            }
        }
        Site::OutOfBody { class, func } => {
            any |= func.default_args;
            let slot = ctors.entry(class).or_default();
            if slot.ports.is_empty() || func.default_args {
                *slot = Ctor {
                    ports: func.ports.clone(),
                    default_args: func.default_args,
                };
            }
        }
    });
    // `super.new(default)` alone also needs the rewrite, so the second walk
    // runs even when no declaration forwards.
    let _ = any;
    // The argument list a constructor of `name` takes: its own when it
    // declares one, else the nearest base constructor's.
    let effective = |name: &str| -> Vec<FunctionPort> {
        let mut cur = Some(name.to_string());
        let mut depth = 0;
        while let Some(cn) = cur {
            depth += 1;
            if depth > 64 {
                break;
            }
            if let Some(c) = ctors.get(&cn)
                && !c.default_args
            {
                return c.ports.clone();
            }
            cur = bases.get(&cn).and_then(|(b, _)| b.clone());
        }
        Vec::new()
    };
    // Pass 2: rewrite the constructors.
    walk(descriptions, &mut |site| match site {
        Site::Class(c) => {
            let name = c.name.name.clone();
            let has_base = c.extends.is_some();
            let ext_default = c.extends.as_ref().is_some_and(|e| e.default_args);
            if let Some(f) = class_ctor(c) {
                let formals = if f.default_args {
                    effective(&name)
                } else {
                    f.ports.clone()
                };
                apply(f, &formals, f.default_args || ext_default, has_base);
            }
        }
        Site::OutOfBody { class, func } => {
            let (base, ext_default) = bases.get(&class).cloned().unwrap_or((None, false));
            let formals = if func.default_args {
                effective(&class)
            } else {
                func.ports.clone()
            };
            apply(func, &formals, func.default_args || ext_default, base.is_some());
        }
    });
}
