//! §8.25.1, §6.20.3: a typedef of a parameterized class that names a member
//! type of one of the class's type parameters (`class E #(type T); typedef
//! T::hw_t hw_t; endclass`). The type tables key a class-scoped typedef by
//! `E::hw_t`, which is the default specialization, where `T` names no class.
//! Used through a specialization (`E#(cfg_t)::hw_t`), the typedef is the
//! argument's member type (`cfg_t::hw_t`). A type parameter or typedef used
//! as a class scope (`C::hw_t` with `parameter type C = cfg_t`) names the
//! class it is bound to.

use super::{TYPEDEF_SHAPES_TLS, member_access_chain_as_scopes};
use crate::ast::Description;
use crate::ast::Identifier;
use crate::ast::decl::{ClassDeclaration, ClassItem, ModuleItem, PackageItem, ParameterKind};
use crate::ast::expr::{ExprKind, Expression};
use crate::ast::types::{DataType, TypeName, TypeScope};
use crate::hasher::HashMap;
use std::cell::RefCell;
use std::rc::Rc;

/// The type parameters of one parameterized class, and its typedefs that
/// name one of them.
struct ClassTypeScope {
    /// Every header parameter, type and value, in declaration order: the
    /// positions of `#(...)` arguments.
    param_order: Vec<String>,
    /// The type parameters.
    type_params: Vec<String>,
    /// Each type parameter's default, when it has one.
    type_defaults: HashMap<String, DataType>,
    /// Typedef name -> the type parameter it names and the member path after
    /// it (`typedef T::a::m t;` keeps `a::m`; `typedef T t;` keeps none).
    typedefs: HashMap<String, (String, Option<TypeName>)>,
}

thread_local! {
    /// The design's parameterized classes that have such typedefs, by class
    /// name (and `pkg::class` for a package's class). Installed once per
    /// elaboration by [`install`].
    static CLASS_TYPE_SCOPES: RefCell<Rc<HashMap<String, Rc<ClassTypeScope>>>> =
        RefCell::new(Rc::new(HashMap::default()));
}

/// Collect the parameterized classes of `descriptions` whose typedefs name a
/// type parameter, replacing what an earlier elaboration installed.
pub(crate) fn install(descriptions: &[Description]) {
    let mut map: HashMap<String, Rc<ClassTypeScope>> = HashMap::default();
    let mut add = |c: &ClassDeclaration, pkg: Option<&str>| {
        let Some(scope) = class_type_scope(c) else {
            return;
        };
        let scope = Rc::new(scope);
        if let Some(pkg) = pkg {
            map.insert(format!("{pkg}::{}", c.name.name), scope.clone());
        }
        map.entry(c.name.name.clone()).or_insert(scope);
    };
    let module_items =
        |items: &[ModuleItem], add: &mut dyn FnMut(&ClassDeclaration, Option<&str>)| {
            for item in items {
                if let ModuleItem::ClassDeclaration(c) = item {
                    add(c, None);
                }
            }
        };
    for d in descriptions {
        match d {
            Description::Class(c) => add(c, None),
            Description::PackageItem(PackageItem::Class(c)) => add(c, None),
            Description::Package(p) => {
                for item in &p.items {
                    if let PackageItem::Class(c) = item {
                        add(c, Some(&p.name.name));
                    }
                }
            }
            Description::Module(m) => module_items(&m.items, &mut add),
            Description::Interface(i) => module_items(&i.items, &mut add),
            Description::Program(p) => module_items(&p.items, &mut add),
            _ => {}
        }
    }
    CLASS_TYPE_SCOPES.with(|c| *c.borrow_mut() = Rc::new(map));
}

fn class_type_scope(c: &ClassDeclaration) -> Option<ClassTypeScope> {
    let mut param_order = Vec::new();
    let mut type_defaults = HashMap::default();
    let mut type_params: Vec<&str> = Vec::new();
    for p in &c.params {
        match &p.kind {
            ParameterKind::Type { assignments } => {
                for a in assignments {
                    param_order.push(a.name.name.clone());
                    type_params.push(&a.name.name);
                    if let Some(dt) = &a.init {
                        type_defaults.insert(a.name.name.clone(), dt.clone());
                    }
                }
            }
            ParameterKind::Data { assignments, .. } => {
                param_order.extend(assignments.iter().map(|a| a.name.name.clone()));
            }
        }
    }
    if type_params.is_empty() {
        return None;
    }
    let mut typedefs = HashMap::default();
    for item in &c.items {
        let ClassItem::Typedef(td) = item else {
            continue;
        };
        let DataType::TypeReference {
            name,
            dimensions,
            type_args,
            ..
        } = &td.data_type
        else {
            continue;
        };
        if !td.dimensions.is_empty() || !dimensions.is_empty() || !type_args.is_empty() {
            continue;
        }
        let entry = match name.scopes.split_first() {
            None if type_params.contains(&name.name.name.as_str()) => {
                (name.name.name.clone(), None)
            }
            Some((head, rest))
                if head.type_args.is_empty() && type_params.contains(&head.name.name.as_str()) =>
            {
                let member = TypeName {
                    scopes: rest.to_vec(),
                    name: name.name.clone(),
                    span: name.span,
                    bound: Default::default(),
                };
                (head.name.name.clone(), Some(member))
            }
            _ => continue,
        };
        // The class's typedefs may already carry its name (`cls::t`).
        let leaf = td.name.name.rsplit("::").next().unwrap_or(&td.name.name);
        typedefs.insert(leaf.to_string(), entry);
    }
    let type_params = type_params.into_iter().map(str::to_string).collect();
    (!typedefs.is_empty()).then_some(ClassTypeScope {
        param_order,
        type_params,
        type_defaults,
        typedefs,
    })
}

/// `Cls#(args)::t`, where the class's typedef `t` names its type parameter
/// `T` or a member of it, as the type it names in that specialization:
/// `cfg_t::hw_t` for `E#(cfg_t)::hw_t`. `None` for every other name, and
/// when the argument is not a type name.
pub(crate) fn specialized(name: &TypeName) -> Option<TypeName> {
    let link = name.scopes.last()?;
    let scopes = CLASS_TYPE_SCOPES.with(|c| c.borrow().clone());
    if scopes.is_empty() {
        return None;
    }
    let class = (name.scopes.len() > 1)
        .then(|| scopes.get(&name.scope_prefix()))
        .flatten()
        .or_else(|| scopes.get(&link.name.name))?;
    let (param, member) = class.typedefs.get(&name.name.name)?;
    let (arg_name, arg_args) = bind_type_param(class, &link.type_args, param, 0)?;
    let Some(member) = member else {
        // `typedef T t;`: the argument itself, when it names a type without
        // specialization arguments of its own.
        return arg_args.is_empty().then_some(arg_name);
    };
    let mut scopes = arg_name.scopes;
    scopes.push(TypeScope {
        name: arg_name.name,
        type_args: arg_args,
    });
    scopes.extend(member.scopes.iter().cloned());
    Some(TypeName {
        scopes,
        name: member.name.clone(),
        span: name.span,
        bound: Default::default(),
    })
}

/// `C::t`, where `C` is a type parameter or typedef bound to a class type
/// (`parameter type C = cfg_t`, `typedef E#(cfg_t) e_t;`), as the name it
/// stands for: `cfg_t::t`, `E#(cfg_t)::t`. `None` when the first scope link
/// is no such name.
pub(crate) fn through_alias(name: &TypeName) -> Option<TypeName> {
    let (head, rest) = name.scopes.split_first()?;
    if !head.type_args.is_empty() {
        return None;
    }
    let (bound, bound_args) =
        TYPEDEF_SHAPES_TLS.with(|c| match c.borrow().0.get(&head.name.name) {
            Some(DataType::TypeReference {
                name,
                dimensions,
                type_args,
                ..
            }) if dimensions.is_empty() => Some((name.clone(), type_args.clone())),
            _ => None,
        })?;
    if bound.scopes.is_empty() && bound.name.name == head.name.name {
        return None;
    }
    let mut scopes = bound.scopes;
    scopes.push(TypeScope {
        name: bound.name,
        type_args: bound_args,
    });
    scopes.extend(rest.iter().cloned());
    Some(TypeName {
        scopes,
        name: name.name.clone(),
        span: name.span,
        bound: Default::default(),
    })
}

/// The type the type parameter `param` takes in the specialization with
/// `args`: its argument by name or position, else its default. A default
/// that names an earlier type parameter (`type U = T`, `type U = T::m`)
/// takes that parameter's own binding (§8.25).
fn bind_type_param(
    class: &ClassTypeScope,
    args: &[Expression],
    param: &str,
    depth: usize,
) -> Option<(TypeName, Vec<Expression>)> {
    if depth > class.type_params.len() {
        return None;
    }
    let position = class.param_order.iter().position(|p| p == param)?;
    let named = args.iter().find_map(|a| match &a.kind {
        ExprKind::NamedArg { name, expr } if name.name == param => Some(expr.as_deref()),
        _ => None,
    });
    let explicit = match named {
        Some(e) => e,
        None => args
            .iter()
            .filter(|a| !matches!(a.kind, ExprKind::NamedArg { .. }))
            .nth(position),
    };
    if let Some(e) = explicit {
        return arg_type_name(e);
    }
    let (default, default_args) = default_type_name(class, param)?;
    let earlier = |n: &str| {
        class.type_params.iter().any(|t| t == n)
            && class.param_order.iter().position(|p| p == n) < Some(position)
    };
    if default.scopes.is_empty() && earlier(&default.name.name) {
        return default_args
            .is_empty()
            .then(|| bind_type_param(class, args, &default.name.name, depth + 1))
            .flatten();
    }
    match default.scopes.split_first() {
        Some((head, rest)) if head.type_args.is_empty() && earlier(&head.name.name) => {
            let (bound, bound_args) = bind_type_param(class, args, &head.name.name, depth + 1)?;
            let mut scopes = bound.scopes;
            scopes.push(TypeScope {
                name: bound.name,
                type_args: bound_args,
            });
            scopes.extend(rest.iter().cloned());
            Some((
                TypeName {
                    scopes,
                    name: default.name,
                    span: default.span,
                    bound: Default::default(),
                },
                default_args,
            ))
        }
        _ => Some((default, default_args)),
    }
}

fn default_type_name(class: &ClassTypeScope, param: &str) -> Option<(TypeName, Vec<Expression>)> {
    match class.type_defaults.get(param)? {
        DataType::TypeReference {
            name,
            dimensions,
            type_args,
            ..
        } if dimensions.is_empty() => Some((name.clone(), type_args.clone())),
        _ => None,
    }
}

/// The keyword types a `#(...)` argument may spell as an identifier.
const BUILTIN_TYPE_KEYWORDS: &[&str] = &[
    "bit",
    "logic",
    "reg",
    "byte",
    "shortint",
    "int",
    "longint",
    "integer",
    "time",
    "real",
    "shortreal",
    "realtime",
    "string",
    "chandle",
    "event",
];

/// A `#(...)` type argument that names a type: `cfg_t`, `pkg::cfg_t`, or a
/// type literal of a named type (with its own specialization arguments).
fn arg_type_name(e: &Expression) -> Option<(TypeName, Vec<Expression>)> {
    match &e.kind {
        ExprKind::Paren(inner) => arg_type_name(inner),
        ExprKind::TypeLiteral(dt) => match dt.as_ref() {
            DataType::TypeReference {
                name,
                dimensions,
                type_args,
                ..
            } if dimensions.is_empty() => Some((name.clone(), type_args.clone())),
            _ => None,
        },
        // A built-in type keyword argument (`#(byte)`) is no type name.
        ExprKind::Ident(h)
            if h.root.is_none()
                && h.path.len() == 1
                && h.path[0].selects.is_empty()
                && !BUILTIN_TYPE_KEYWORDS.contains(&h.path[0].name.name.as_str()) =>
        {
            Some((
                TypeName {
                    scopes: Vec::new(),
                    name: Identifier {
                        name: h.path[0].name.name.clone(),
                        span: h.span,
                    },
                    span: h.span,
                    bound: Default::default(),
                },
                Vec::new(),
            ))
        }
        ExprKind::MemberAccess { .. } => {
            let (scopes, leaf) = member_access_chain_as_scopes(e)?;
            Some((
                TypeName {
                    scopes,
                    name: leaf,
                    span: e.span,
                    bound: Default::default(),
                },
                Vec::new(),
            ))
        }
        _ => None,
    }
}
