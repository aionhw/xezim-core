use super::*;

pub(super) fn set_type_bind_tls(ctx: &RewriteCtx) {
    // §23.8: a body materialized after elaboration (possibly on another
    // thread) resolves its upward names against the design's scope tree.
    install_upward_scopes(&ctx.upward);
    // Always assign — an instance WITHOUT type parameters must clear
    // whatever an enclosing instance left, or its `$bits(T)` on a typedef
    // named `T` would fold to the parent's parameter width.
    let w = &ctx.type_bind_widths;
    TYPE_BIND_WIDTHS_TLS.with(|c| {
        *c.borrow_mut() = if w.is_empty() { None } else { Some(w.clone()) };
    });
    let q = &ctx.type_bind_queries;
    TYPE_BIND_QUERIES_TLS.with(|c| {
        *c.borrow_mut() = if q.is_empty() { None } else { Some(q.clone()) };
    });
    let t = &ctx.type_binds;
    TYPE_BIND_TYPES_TLS.with(|c| {
        *c.borrow_mut() = if t.is_empty() { None } else { Some(t.clone()) };
    });
}

pub(super) fn clear_type_bind_tls() {
    TYPE_BIND_WIDTHS_TLS.with(|c| *c.borrow_mut() = None);
    TYPE_BIND_QUERIES_TLS.with(|c| *c.borrow_mut() = None);
    TYPE_BIND_TYPES_TLS.with(|c| *c.borrow_mut() = None);
}

pub(super) fn with_type_bind_tls<R>(ctx: &RewriteCtx, f: impl FnOnce() -> R) -> R {
    struct Restore {
        upward: Option<Rc<std::cell::RefCell<UpwardScopes>>>,
        widths: Option<Rc<HashMap<String, u32>>>,
        queries: Option<Rc<HashMap<String, TypeQueryDims>>>,
        types: Option<Rc<HashMap<String, DataType>>>,
    }
    impl Drop for Restore {
        fn drop(&mut self) {
            UPWARD_SCOPES_TLS.with(|c| *c.borrow_mut() = self.upward.take());
            TYPE_BIND_WIDTHS_TLS.with(|c| *c.borrow_mut() = self.widths.take());
            TYPE_BIND_QUERIES_TLS.with(|c| *c.borrow_mut() = self.queries.take());
            TYPE_BIND_TYPES_TLS.with(|c| *c.borrow_mut() = self.types.take());
        }
    }
    let _restore = Restore {
        upward: UPWARD_SCOPES_TLS.with(|c| c.borrow().as_ref().map(Rc::clone)),
        widths: TYPE_BIND_WIDTHS_TLS.with(|c| c.borrow().as_ref().map(Rc::clone)),
        queries: TYPE_BIND_QUERIES_TLS.with(|c| c.borrow().as_ref().map(Rc::clone)),
        types: TYPE_BIND_TYPES_TLS.with(|c| c.borrow().as_ref().map(Rc::clone)),
    };
    set_type_bind_tls(ctx);
    f()
}

/// §10.9: the type of a typed pattern `T'{...}` in the instance being
/// rewritten: a bound type parameter's type, a local typedef under its
/// instance name, else `T` with its bounds rescoped.
pub(super) fn rewrite_typed_pattern_type(
    ty: &DataType,
    prefix: &str,
    port_map: &HashMap<String, Expression>,
    local_names: &std::collections::HashSet<String>,
    interface_map: &HashMap<String, String>,
) -> DataType {
    if let DataType::TypeReference {
        name,
        dimensions,
        type_args,
        ..
    } = ty
        && name.scopes.is_empty()
        && dimensions.is_empty()
        && type_args.is_empty()
    {
        let bound = TYPE_BIND_TYPES_TLS.with(|c| {
            c.borrow()
                .as_ref()
                .and_then(|m| m.get(&name.name.name).cloned())
        });
        if let Some(dt) = bound {
            return dt;
        }
        if !prefix.is_empty() && local_names.contains(&name.name.name) {
            return scope_local_typerefs(ty, local_names, prefix);
        }
    }
    module_class_scope::data_type(
        &rewrite_data_type_scoped(ty, prefix, port_map, local_names, interface_map),
        prefix,
        port_map,
    )
}

/// `$bits(T)` or a §20.7 array query (`$left(T)`, `$size(T, 2)`, …) with `T`
/// a type parameter of the instance being materialized: its value, or None
/// when the call is anything else or the dimension does not exist.
pub(super) fn query_of_bound_type_param(name: &str, args: &[Expression]) -> Option<i64> {
    let is_query = matches!(
        name,
        "$left"
            | "$right"
            | "$high"
            | "$low"
            | "$size"
            | "$increment"
            | "$dimensions"
            | "$unpacked_dimensions"
    );
    if !(name == "$bits" && args.len() == 1 || is_query && (1..=2).contains(&args.len())) {
        return None;
    }
    let ExprKind::Ident(h) = &args[0].kind else {
        return None;
    };
    if h.path.len() != 1 || !h.path[0].selects.is_empty() || h.root.is_some() {
        return None;
    }
    let t = &h.path[0].name.name;
    if name == "$bits" {
        return TYPE_BIND_WIDTHS_TLS
            .with(|c| c.borrow().as_ref().and_then(|m| m.get(t).copied()))
            .map(i64::from);
    }
    let dim = match args.get(1) {
        Some(d) => usize::try_from(const_eval_i64_with_params(d, None)?).ok()?,
        None => 1,
    };
    TYPE_BIND_QUERIES_TLS.with(|c| {
        let c = c.borrow();
        type_query_bound(name, c.as_ref()?.get(t)?, dim)
    })
}

/// §6.20.3, §7.4.1: `T [1:0] tmp;` with `T` bound to `bound` declares a packed
/// array of `bound`: its own packed dimensions stay innermost and `dims` go
/// outside them (`logic [7:0]` becomes `logic [1:0][7:0]`). `None` for a
/// type that cannot carry packed dimensions here (an atom such as `int`, an
/// unpacked aggregate, a class), which keeps the declaration as written.
fn with_outer_packed_dims(bound: &DataType, dims: &[PackedDimension]) -> Option<DataType> {
    if dims.is_empty() {
        return Some(bound.clone());
    }
    let mut out = bound.clone();
    let inner = match &mut out {
        DataType::IntegerVector { dimensions, .. }
        | DataType::Implicit { dimensions, .. }
        | DataType::TypeReference { dimensions, .. } => dimensions,
        DataType::Struct(su) if su.packed => &mut su.dimensions,
        DataType::Enum(e) => &mut e.dimensions,
        _ => return None,
    };
    let mut all = dims.to_vec();
    all.append(inner);
    *inner = all;
    Some(out)
}

/// `substitute_type_params_stmt` over a subroutine body.
pub(super) fn substitute_type_params_stmts(
    stmts: Vec<Statement>,
    binds: &HashMap<String, DataType>,
    prefix: &str,
) -> Vec<Statement> {
    if binds.is_empty() {
        return stmts;
    }
    substitute_type_params_block(stmts, binds, prefix)
}

/// §6.18, §6.20.3: the statements of one block or subroutine body. A typedef
/// declared there (`typedef logic [3:0] T;`) hides a type parameter of the
/// same name for the whole block, so its declarations keep naming the local
/// type.
fn substitute_type_params_block(
    stmts: Vec<Statement>,
    binds: &HashMap<String, DataType>,
    prefix: &str,
) -> Vec<Statement> {
    let shadowed: Vec<&str> = stmts
        .iter()
        .filter_map(|st| match &st.kind {
            StatementKind::Typedef(td) if binds.contains_key(&td.name.name) => {
                Some(td.name.name.as_str())
            }
            _ => None,
        })
        .collect();
    let narrowed;
    let binds = if shadowed.is_empty() {
        binds
    } else {
        narrowed = binds
            .iter()
            .filter(|(k, _)| !shadowed.contains(&k.as_str()))
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect::<HashMap<String, DataType>>();
        &narrowed
    };
    stmts
        .into_iter()
        .map(|st| substitute_type_params_stmt(st, binds, prefix))
        .collect()
}

/// Substitute an instance's TYPE-PARAMETER bindings into the declarations of
/// a cloned behavioral statement — see `RewriteCtx::type_binds`. Only a
/// `VarDecl` or `ParamDecl` whose type is a `TypeReference` naming a bound
/// parameter is rewritten (to the full resolved concrete DataType, with any
/// packed dimensions written after the name placed outside the bound type's
/// own, §7.4.1); everything else passes through untouched, recursing into
/// compound statements. No-op (identity, no clone churn beyond the move) when
/// the binding map is empty.
fn subst_type_param_dt(
    data_type: DataType,
    binds: &HashMap<String, DataType>,
    prefix: &str,
) -> DataType {
    match &data_type {
        DataType::TypeReference {
            name,
            dimensions,
            type_args,
            span,
        } if type_args.is_empty()
            && name.scopes.is_empty()
            && binds.contains_key(&name.name.name) =>
        {
            let bound = &binds[&name.name.name];
            // §7.4.1: `T [1:0] tmp;` with `T` bound to an integer atom
            // (`int`) or an enum is a packed array of two `int` or enum
            // elements, whose elements keep the atom's signedness and the
            // enum's type. Neither is a vector with dimensions of its own, so
            // name the instance's alias of the parameter (`u.T`), which
            // outlives the inlining, as a typedef of that type is named.
            let alias_bound = !dimensions.is_empty()
                && !prefix.is_empty()
                && matches!(bound, DataType::IntegerAtom { .. } | DataType::Enum(_));
            let packed = if alias_bound {
                None
            } else {
                with_outer_packed_dims(bound, dimensions)
            };
            packed.unwrap_or_else(|| {
                if alias_bound {
                    let mut alias = name.clone();
                    alias.name.name = cat2(prefix, &name.name.name);
                    DataType::TypeReference {
                        name: alias,
                        dimensions: dimensions.clone(),
                        type_args: Vec::new(),
                        span: *span,
                    }
                } else {
                    data_type.clone()
                }
            })
        }
        // §6.18, §6.20.3: a block typedef of a class scope whose prefix is a
        // type parameter bound to a class (`typedef C::hw_t l_t;`) names
        // that class's member type.
        DataType::TypeReference { name, .. }
            if name.scopes.first().is_some_and(|head| {
                head.type_args.is_empty()
                    && matches!(binds.get(&head.name.name), Some(DataType::TypeReference { dimensions, .. }) if dimensions.is_empty())
            }) =>
        {
            let DataType::TypeReference {
                mut name,
                dimensions,
                type_args,
                span,
            } = data_type
            else {
                unreachable!()
            };
            let Some(DataType::TypeReference {
                name: bound,
                type_args: bound_args,
                ..
            }) = binds.get(&name.scopes[0].name.name)
            else {
                unreachable!()
            };
            let mut scopes = bound.scopes.clone();
            scopes.push(crate::ast::types::TypeScope {
                name: bound.name.clone(),
                type_args: bound_args.clone(),
            });
            scopes.extend(name.scopes.drain(1..));
            name.scopes = scopes;
            DataType::TypeReference {
                name,
                dimensions,
                type_args,
                span,
            }
        }
        // §6.20.3, §7.2: a struct or union written in the declaration
        // (`struct packed { T a; T b; } s;`) or an enum on a type parameter
        // (`enum T {A, B} e;`) names the parameter in its members.
        DataType::Struct(_) | DataType::Enum(_) if names_bound_type_param(&data_type, binds) => {
            match data_type {
                DataType::Struct(mut su) => {
                    for m in &mut su.members {
                        m.data_type = subst_type_param_dt(
                            std::mem::replace(&mut m.data_type, DataType::Void(m.span)),
                            binds,
                            prefix,
                        );
                    }
                    DataType::Struct(su)
                }
                DataType::Enum(mut e) => {
                    if let Some(b) = e.base_type.take() {
                        e.base_type = Some(Box::new(subst_type_param_dt(*b, binds, prefix)));
                    }
                    DataType::Enum(e)
                }
                other => other,
            }
        }
        _ => data_type,
    }
}

/// Whether `subst_type_param_dt` would change a struct, union or enum type:
/// a member, nested at any depth, or the enum base names a bound parameter.
fn names_bound_type_param(dt: &DataType, binds: &HashMap<String, DataType>) -> bool {
    match dt {
        DataType::TypeReference {
            name, type_args, ..
        } => type_args.is_empty() && name.scopes.is_empty() && binds.contains_key(&name.name.name),
        DataType::Struct(su) => su
            .members
            .iter()
            .any(|m| names_bound_type_param(&m.data_type, binds)),
        DataType::Enum(e) => e
            .base_type
            .as_deref()
            .is_some_and(|b| names_bound_type_param(b, binds)),
        _ => false,
    }
}

pub(super) fn substitute_type_params_stmt(
    stmt: Statement,
    binds: &HashMap<String, DataType>,
    prefix: &str,
) -> Statement {
    if binds.is_empty() {
        return stmt;
    }
    let Statement { kind, span } = stmt;
    let sub = |st: Box<Statement>| Box::new(substitute_type_params_stmt(*st, binds, prefix));
    let kind = match kind {
        StatementKind::VarDecl {
            data_type,
            lifetime,
            declarators,
        } => StatementKind::VarDecl {
            data_type: subst_type_param_dt(data_type, binds, prefix),
            lifetime,
            declarators,
        },
        StatementKind::ParamDecl {
            is_local,
            data_type,
            declarators,
        } => StatementKind::ParamDecl {
            is_local,
            data_type: subst_type_param_dt(data_type, binds, prefix),
            declarators,
        },
        // §6.18: a block typedef built on a type parameter
        // (`typedef T [1:0] pair_t;`) names its binding, as a declaration
        // does. One that declares the parameter's own name has already taken
        // it out of `binds` (`substitute_type_params_block`).
        StatementKind::Typedef(mut td) => {
            td.data_type = subst_type_param_dt(
                std::mem::replace(&mut td.data_type, DataType::Void(span)),
                binds,
                prefix,
            );
            StatementKind::Typedef(td)
        }
        StatementKind::If {
            unique_priority,
            condition,
            then_stmt,
            else_stmt,
        } => StatementKind::If {
            unique_priority,
            condition,
            then_stmt: sub(then_stmt),
            else_stmt: else_stmt.map(sub),
        },
        StatementKind::Case {
            unique_priority,
            kind,
            expr,
            items,
        } => StatementKind::Case {
            unique_priority,
            kind,
            expr,
            items: items
                .into_iter()
                .map(|it| CaseItem {
                    stmt: substitute_type_params_stmt(it.stmt, binds, prefix),
                    ..it
                })
                .collect(),
        },
        StatementKind::For {
            init,
            condition,
            step,
            body,
        } => StatementKind::For {
            // §12.7.1: a loop variable declared with a type parameter.
            init: init
                .into_iter()
                .map(|it| match it {
                    ForInit::VarDecl {
                        data_type,
                        name,
                        init,
                    } => ForInit::VarDecl {
                        data_type: subst_type_param_dt(data_type, binds, prefix),
                        name,
                        init,
                    },
                    other => other,
                })
                .collect(),
            condition,
            step,
            body: sub(body),
        },
        StatementKind::Foreach { array, vars, body } => StatementKind::Foreach {
            array,
            vars,
            body: sub(body),
        },
        StatementKind::While { condition, body } => StatementKind::While {
            condition,
            body: sub(body),
        },
        StatementKind::DoWhile { body, condition } => StatementKind::DoWhile {
            body: sub(body),
            condition,
        },
        StatementKind::Repeat { count, body } => StatementKind::Repeat {
            count,
            body: sub(body),
        },
        StatementKind::Forever { body } => StatementKind::Forever { body: sub(body) },
        StatementKind::SeqBlock { name, stmts } => StatementKind::SeqBlock {
            name,
            stmts: substitute_type_params_block(stmts.into_vec(), binds, prefix).into(),
        },
        StatementKind::ParBlock {
            name,
            join_type,
            stmts,
        } => StatementKind::ParBlock {
            name,
            join_type,
            stmts: substitute_type_params_block(stmts.into_vec(), binds, prefix).into(),
        },
        StatementKind::TimingControl { control, stmt } => StatementKind::TimingControl {
            control,
            stmt: sub(stmt),
        },
        StatementKind::Wait { condition, stmt } => StatementKind::Wait {
            condition,
            stmt: sub(stmt),
        },
        // Same missing-arm class as rewrite_stmt's Assertion gap: recurse
        // into the remaining compound kinds so a VarDecl of a bound type
        // param inside them still resolves.
        StatementKind::Assertion(mut a) => {
            a.action = a.action.map(sub);
            a.else_action = a.else_action.map(sub);
            StatementKind::Assertion(a)
        }
        StatementKind::RandCase { items } => StatementKind::RandCase {
            items: items
                .into_iter()
                .map(|(w, st)| (w, substitute_type_params_stmt(st, binds, prefix)))
                .collect(),
        },
        StatementKind::WaitOrder {
            events,
            pass,
            fail,
            armed,
            idx,
            span,
        } => StatementKind::WaitOrder {
            events,
            pass: pass.map(sub),
            fail: fail.map(sub),
            armed,
            idx,
            span,
        },
        StatementKind::RsAction { body } => StatementKind::RsAction { body: sub(body) },
        other => other,
    };
    Statement { kind, span }
}

/// §6.21: alpha-rename a PROCESS body's top-level block locals that shadow a
/// module-scope name. The process executor flattens the body for suspension
/// (ProcCont), so no block-scope boundary survives to runtime — a frameless
/// local landed on the module signal itself and the block's writes clobbered
/// it (`initial begin logic [7:0] v; v = 8'hF0; end` overwrote module `v`).
/// Renaming the local (and every reference, via the port-map rewriter, which
/// handles selects, member tails and event controls) removes the collision
/// entirely. `salt` keeps two processes' same-named locals distinct.
///
/// Named blocks are left alone: their locals are hierarchically referenceable
/// (§23.9) and must keep their spelling. Returns None when there is nothing
/// to rename.
/// Substitute bare identifier references (`name` → `replacement`) throughout a
/// statement, using the inlining rewriter (selects, member tails and event
/// controls all handled). Used for §3.12.1: a $unit subroutine injected into a
/// module that SHADOWS a $unit variable must keep its body's references bound
/// to the $unit copy, not the module's shadow.
pub fn substitute_bare_idents_stmt(
    stmt: &Statement,
    map: &std::collections::HashMap<String, String>,
) -> Statement {
    let port_map = bare_ident_map(map, stmt.span);
    let empty_locals: std::collections::HashSet<String> = std::collections::HashSet::new();
    let empty_iface: HashMap<String, String> = HashMap::default();
    rewrite_stmt(stmt, "", &port_map, &empty_locals, &empty_iface)
}

fn bare_ident_map(
    map: &std::collections::HashMap<String, String>,
    span: Span,
) -> HashMap<String, Expression> {
    let mut port_map: HashMap<String, Expression> = HashMap::default();
    for (from, to) in map {
        let hier = crate::ast::expr::HierarchicalIdentifier {
            root: None,
            path: vec![crate::ast::expr::HierPathSegment {
                name: crate::ast::Identifier {
                    name: to.clone(),
                    span,
                },
                selects: Vec::new(),
            }],
            span,
            cached_signal_id: crate::ast::cache::SignalCache::new(None),
            cached_resolved_name: crate::ast::cache::NameCache::new(),
            bound: crate::ast::binding::Bound::UNSET,
        };
        port_map.insert(from.clone(), Expression::new(ExprKind::Ident(hier), span));
    }
    port_map
}

/// §3.12.1: an injected compilation-unit constant keeps the scope of its
/// initializer and declared ranges, even when the receiving module shadows
/// another compilation-unit declaration they reference.
pub fn substitute_bare_idents_param(
    param: &ParameterDeclaration,
    map: &std::collections::HashMap<String, String>,
) -> ParameterDeclaration {
    let mut out = param.clone();
    let ports = bare_ident_map(map, param.span);
    let locals = Default::default();
    let interfaces = HashMap::default();
    if let ParameterKind::Data {
        data_type,
        assignments,
    } = &mut out.kind
    {
        *data_type = rewrite_data_type_scoped(data_type, "", &ports, &locals, &interfaces);
        for assignment in assignments {
            assignment.dimensions = rewrite_unpacked_dims_scoped(
                &assignment.dimensions,
                "",
                &ports,
                &locals,
                &interfaces,
            );
            if let Some(value) = &mut assignment.init {
                *value = rewrite_expr(value, "", &ports, &locals, &interfaces);
            }
        }
    }
    out
}
