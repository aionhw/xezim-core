//! §8.3 / §23.6: module-instance class names belong to their lexical scope.

use super::*;

/// Retain scoped-member shape while rebasing the owner of `C#(...)`.
/// Flattening only the owner produces a hybrid package path that the
/// specialization value reader cannot interpret as a static property.
pub(super) fn specialized_receiver(
    e: &Expression,
    prefix: &str,
    bindings: &HashMap<String, Expression>,
    local_names: &std::collections::HashSet<String>,
    interfaces: &HashMap<String, String>,
) -> Expression {
    if let ExprKind::MemberAccess { expr, member } = &e.kind {
        Expression::new(
            ExprKind::MemberAccess {
                expr: Box::new(specialized_receiver(
                    expr,
                    prefix,
                    bindings,
                    local_names,
                    interfaces,
                )),
                member: member.clone(),
            },
            e.span,
        )
    } else {
        rewrite_expr_impl(e, prefix, bindings, local_names, interfaces)
    }
}

fn receiver_text(e: &Expression) -> Option<String> {
    match &e.kind {
        ExprKind::Ident(h) if h.root.is_none() && h.path.iter().all(|p| p.selects.is_empty()) => {
            Some(
                h.path
                    .iter()
                    .map(|p| p.name.name.as_str())
                    .collect::<Vec<_>>()
                    .join("::"),
            )
        }
        ExprKind::MemberAccess { expr, member } => {
            Some(format!("{}::{}", receiver_text(expr)?, member.name))
        }
        ExprKind::Specialization {
            base,
            type_args_text,
        } => Some(format!("{}#({})", receiver_text(base)?, type_args_text)),
        _ => None,
    }
}

/// §6.20.3: expression parsing keeps `C#(...)` as a specialization node.
/// Reparse only that uncommon override shape in a type context, preserving
/// builtin type arguments, named arguments and package/nested qualifiers.
pub(super) fn type_override(e: &Expression) -> Option<DataType> {
    let text = receiver_text(e)?;
    if !text.contains("#(") {
        return None;
    }
    let source = format!("module __type_override; typedef {text} __bound_type; endmodule");
    let parsed = crate::parse(&source);
    if !parsed.errors.is_empty() {
        return None;
    }
    let crate::ast::Description::Module(module) = parsed.source.descriptions.into_iter().next()?
    else {
        return None;
    };
    module.items.into_iter().find_map(|item| match item {
        ModuleItem::TypedefDeclaration(t) => Some(t.data_type),
        _ => None,
    })
}

fn argument_text(e: &Expression) -> String {
    if let ExprKind::TypeLiteral(dt) = &e.kind {
        if let Some(receiver) = receiver(dt) {
            if let Some(text) = receiver_text(&receiver) {
                return text;
            }
        }
        if let Some(text) = data_type_to_spec_fragment(dt) {
            return text;
        }
    }
    expr_to_arg_string(e)
}

/// §6.20.3 / §8.23: preserve the class specialization when a module type
/// parameter becomes a scoped receiver in an inlined subroutine or process.
pub(super) fn receiver(dt: &DataType) -> Option<Expression> {
    let DataType::TypeReference {
        name, type_args, ..
    } = dt
    else {
        return None;
    };
    let mut result = None;
    for (name, args) in name
        .scopes
        .iter()
        .map(|s| (&s.name, &s.type_args))
        .chain(std::iter::once((&name.name, type_args)))
    {
        let base = if let Some(expr) = result {
            Expression::new(
                ExprKind::MemberAccess {
                    expr: Box::new(expr),
                    member: name.clone(),
                },
                name.span,
            )
        } else {
            make_ident_expr(&name.name)
        };
        result = Some(if args.is_empty() {
            base
        } else {
            Expression::new(
                ExprKind::Specialization {
                    base: Box::new(base),
                    type_args_text: args.iter().map(argument_text).collect::<Vec<_>>().join(","),
                },
                name.span,
            )
        });
    }
    result
}

fn target<'a>(
    name: &str,
    prefix: &str,
    bindings: &'a HashMap<String, Expression>,
) -> Option<&'a str> {
    let ExprKind::Ident(h) = &bindings.get(name)?.kind else {
        return None;
    };
    let [segment] = h.path.as_slice() else {
        return None;
    };
    (h.root.is_none()
        && segment.selects.is_empty()
        && segment.name.name.strip_prefix(prefix) == Some(name))
    .then_some(segment.name.name.as_str())
}

pub(super) fn data_type(
    dt: &DataType,
    prefix: &str,
    bindings: &HashMap<String, Expression>,
) -> DataType {
    match dt {
        DataType::TypeReference {
            name,
            dimensions,
            type_args,
            span,
        } => {
            let mut name = name.clone();
            if let Some(scope) = name.scopes.first_mut() {
                if let Some(to) = target(&scope.name.name, prefix, bindings) {
                    scope.name.name = to.to_string();
                }
            } else if let Some(to) = target(&name.name.name, prefix, bindings) {
                name.name.name = to.to_string();
            }
            DataType::TypeReference {
                name,
                dimensions: dimensions.clone(),
                type_args: type_args.clone(),
                span: *span,
            }
        }
        DataType::Struct(s) => {
            let mut s = s.clone();
            for member in &mut s.members {
                member.data_type = data_type(&member.data_type, prefix, bindings);
            }
            DataType::Struct(s)
        }
        DataType::Enum(e) => {
            let mut e = e.clone();
            if let Some(base) = &e.base_type {
                e.base_type = Some(Box::new(data_type(base, prefix, bindings)));
            }
            DataType::Enum(e)
        }
        _ => dt.clone(),
    }
}

/// §23.9: a nearer declaration of `name` hides it and every block key it
/// heads (`name.k`, `name[0].k`).
fn hide(bindings: &mut HashMap<String, Expression>, name: &str) {
    bindings.retain(|k, _| k.split(['.', '[']).next() != Some(name));
}

pub(super) fn class(
    cd: &ClassDeclaration,
    prefix: &str,
    bindings: &HashMap<String, Expression>,
) -> ClassDeclaration {
    let mut result = cd.clone();
    result.name.name = cat2(prefix, &cd.name.name);
    // §8.25: a class parameter shadows an enclosing class with the same name.
    let mut bindings = bindings.clone();
    for parameter in &cd.params {
        match &parameter.kind {
            ParameterKind::Type { assignments } => {
                for a in assignments {
                    hide(&mut bindings, &a.name.name);
                }
            }
            ParameterKind::Data { assignments, .. } => {
                for a in assignments {
                    hide(&mut bindings, &a.name.name);
                }
            }
        }
    }
    let bindings = &bindings;
    if let Some(base) = &mut result.extends {
        if base.scopes.is_empty() {
            if let Some(to) = target(&base.name.name, prefix, bindings) {
                base.name.name = to.to_string();
            }
        } else if let Some(scope) = base.scopes.first_mut() {
            if let Some(to) = target(&scope.name, prefix, bindings) {
                scope.name = to.to_string();
            }
        }
    }
    // Body-local types shadow module types, just as class parameters do.
    // Their unqualified spellings are resolved by the class context.
    let outer_bindings = bindings;
    let mut body_bindings = outer_bindings.clone();
    for item in &cd.items {
        match item {
            ClassItem::Typedef(t) => {
                hide(&mut body_bindings, &t.name.name);
            }
            ClassItem::Class(c) => {
                hide(&mut body_bindings, &c.name.name);
            }
            // §8.3: a property hides a block's data of its name (`cfg.depth`).
            ClassItem::Property(p) => {
                for d in &p.declarators {
                    hide(&mut body_bindings, &d.name.name);
                }
            }
            _ => {}
        }
    }
    let bindings = &body_bindings;
    let empty_names = std::collections::HashSet::new();
    let empty_interfaces = HashMap::default();
    for item in &mut result.items {
        match item {
            ClassItem::Property(p) => {
                p.data_type = data_type(&p.data_type, prefix, bindings);
                for d in &mut p.declarators {
                    if let Some(e) = &d.init {
                        d.init = Some(rewrite_expr(
                            e,
                            "",
                            bindings,
                            &empty_names,
                            &empty_interfaces,
                        ));
                    }
                }
            }
            ClassItem::Typedef(t) => t.data_type = data_type(&t.data_type, prefix, outer_bindings),
            ClassItem::Method(m) => {
                let (ports, body) = match &mut m.kind {
                    ClassMethodKind::Function(f)
                    | ClassMethodKind::Extern(f)
                    | ClassMethodKind::PureVirtual(f) => {
                        f.return_type = data_type(&f.return_type, prefix, bindings);
                        (&mut f.ports, &mut f.items)
                    }
                    ClassMethodKind::Task(t) => (&mut t.ports, &mut t.items),
                };
                let mut method_bindings = bindings.clone();
                for port in ports {
                    port.data_type = data_type(&port.data_type, prefix, bindings);
                    hide(&mut method_bindings, &port.name.name);
                    if let Some(e) = &port.default {
                        port.default = Some(rewrite_expr(
                            e,
                            "",
                            bindings,
                            &empty_names,
                            &empty_interfaces,
                        ));
                    }
                }
                for name in stmt_list_declared_names(body) {
                    hide(&mut method_bindings, name);
                }
                // §8.3/§13.4: rewrite from the shared source directly. Mutating
                // the cloned body first would copy every statement before the
                // rewriter builds a second copy.
                *body = crate::ast::cache::without_scope_caches(|| body.iter().map(|s| {
                    // Prefix only class aliases, keeping existing ownership
                    // rules for ordinary method locals and module variables.
                    rewrite_stmt(s, prefix, &method_bindings, &empty_names, &empty_interfaces)
                }).collect());
            }
            _ => {}
        }
    }
    result
}
