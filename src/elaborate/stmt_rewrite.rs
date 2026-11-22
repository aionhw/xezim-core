use super::*;

thread_local! {
    /// Set by `flatten_pkg_member_refs`: the package names whose `P::m`
    /// member accesses fold to `Ident([P, m])`; every other member access
    /// is left as it is.
    pub(super) static PKG_FLATTEN_ONLY: std::cell::RefCell<Option<std::collections::HashSet<String>>> =
        const { std::cell::RefCell::new(None) };
}

/// §26.3: spell every `P::m` (P a package) in a subroutine body the way the
/// process bodies get it from the inliner — `Ident([P, m])` rather than a
/// `MemberAccess` on the package name. Module tasks and functions are not
/// inlined, so their package references kept the member-access shape that
/// the collection paths (`P::q.push_back`, `P::d = new[n]`, `P::aa[k].x`)
/// do not resolve. Nothing else in the body changes.
pub fn flatten_pkg_member_refs(
    stmt: &Statement,
    pkgs: &std::collections::HashSet<String>,
) -> Statement {
    PKG_FLATTEN_ONLY.with(|s| *s.borrow_mut() = Some(pkgs.clone()));
    let empty_map: HashMap<String, Expression> = HashMap::default();
    let empty_locals: std::collections::HashSet<String> = std::collections::HashSet::new();
    let empty_iface: HashMap<String, String> = HashMap::default();
    let out = rewrite_stmt(stmt, "", &empty_map, &empty_locals, &empty_iface);
    PKG_FLATTEN_ONLY.with(|s| *s.borrow_mut() = None);
    out
}

pub fn rename_process_shadowed_locals(
    stmt: &Statement,
    module_names: &std::collections::HashSet<String>,
    salt: &str,
) -> Option<Statement> {
    let StatementKind::SeqBlock { name, stmts } = &stmt.kind else {
        return None;
    };
    // A LABELED block's locals are hierarchically addressable (`tb.p1.v`), so
    // they are salted with the label itself (`p1.v`) rather than the opaque
    // process salt: the stored name IS the hierarchical name, so references
    // from other processes keep resolving, while two processes' same-named
    // locals (or a local shadowing a module variable) no longer share one
    // slot. Labeled blocks used to be skipped here entirely, which left
    // exactly those collisions in place.
    let label: Option<&str> = name.as_ref().map(|n| n.name.as_str());
    let mut map: HashMap<String, Expression> = HashMap::default();
    let mut renames: HashMap<String, String> = HashMap::default();
    for s in stmts.iter() {
        if let StatementKind::VarDecl { declarators, .. }
        | StatementKind::ParamDecl { declarators, .. } = &s.kind
        {
            for d in declarators {
                if module_names.contains(&d.name.name) && !renames.contains_key(&d.name.name) {
                    let fresh = match label {
                        Some(l) => format!("{}.{}", l, d.name.name),
                        None => format!("{}__shadow_{}", d.name.name, salt),
                    };
                    let hier = crate::ast::expr::HierarchicalIdentifier {
                        root: None,
                        path: vec![crate::ast::expr::HierPathSegment {
                            name: crate::ast::Identifier {
                                name: fresh.clone(),
                                span: d.name.span,
                            },
                            selects: Vec::new(),
                        }],
                        span: d.name.span,
                        cached_signal_id: crate::ast::cache::SignalCache::new(None),
                        cached_resolved_name: crate::ast::cache::NameCache::new(),
                        bound: crate::ast::binding::Bound::UNSET,
                    };
                    map.insert(
                        d.name.name.clone(),
                        Expression::new(ExprKind::Ident(hier), d.name.span),
                    );
                    renames.insert(d.name.name.clone(), fresh);
                }
            }
        }
    }
    if renames.is_empty() {
        return None;
    }
    // A NESTED block redeclaring one of these names introduces its own
    // variable — the blanket reference rewrite below would capture it. Drop
    // such names from the rename set (their nested uses keep the §6.21
    // shadow-frame handling instead).
    fn nested_redeclares(
        s: &Statement,
        names: &HashMap<String, String>,
        hits: &mut Vec<String>,
        top: bool,
    ) {
        match &s.kind {
            StatementKind::VarDecl { declarators, .. }
            | StatementKind::ParamDecl { declarators, .. }
                if !top =>
            {
                for d in declarators {
                    if names.contains_key(&d.name.name) {
                        hits.push(d.name.name.clone());
                    }
                }
            }
            StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
                for c in stmts {
                    nested_redeclares(c, names, hits, false);
                }
            }
            StatementKind::If {
                then_stmt,
                else_stmt,
                ..
            } => {
                nested_redeclares(then_stmt, names, hits, false);
                if let Some(e) = else_stmt {
                    nested_redeclares(e, names, hits, false);
                }
            }
            StatementKind::Case { items, .. } => {
                for it in items {
                    nested_redeclares(&it.stmt, names, hits, false);
                }
            }
            StatementKind::For { body, .. }
            | StatementKind::While { body, .. }
            | StatementKind::DoWhile { body, .. }
            | StatementKind::Repeat { body, .. }
            | StatementKind::Forever { body }
            | StatementKind::Foreach { body, .. } => {
                nested_redeclares(body, names, hits, false);
            }
            StatementKind::TimingControl { stmt, .. } | StatementKind::Wait { stmt, .. } => {
                nested_redeclares(stmt, names, hits, false);
            }
            _ => {}
        }
    }
    let mut hits: Vec<String> = Vec::new();
    for s in stmts.iter() {
        match &s.kind {
            StatementKind::VarDecl { .. } | StatementKind::ParamDecl { .. } => {}
            _ => nested_redeclares(s, &renames, &mut hits, false),
        }
    }
    for h in hits {
        renames.remove(&h);
        map.remove(&h);
    }
    if renames.is_empty() {
        return None;
    }
    let empty_locals: std::collections::HashSet<String> = std::collections::HashSet::new();
    let empty_iface: HashMap<String, String> = HashMap::default();
    let mut out = rewrite_stmt(stmt, "", &map, &empty_locals, &empty_iface);
    // §6.21 / §20.7: ranges read the renamed local too. A declaration's
    // packed or unpacked dimensions must follow the same binding as its body,
    // including a declaration in a nested block reading an outer local array.
    fn declarations(
        stmt: &mut Statement,
        renames: &HashMap<String, String>,
        map: &HashMap<String, Expression>,
        own: bool,
    ) {
        let empty = std::collections::HashSet::new();
        let interfaces = HashMap::default();
        match &mut stmt.kind {
            StatementKind::VarDecl {
                data_type,
                declarators,
                ..
            }
            | StatementKind::ParamDecl {
                data_type,
                declarators,
                ..
            } => {
                *data_type = rewrite_data_type_scoped(data_type, "", map, &empty, &interfaces);
                for d in declarators {
                    if own && let Some(fresh) = renames.get(&d.name.name) {
                        d.name.name = fresh.clone();
                    }
                    d.dimensions =
                        rewrite_unpacked_dims_scoped(&d.dimensions, "", map, &empty, &interfaces);
                }
            }
            StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
                for child in stmts {
                    declarations(child, renames, map, false);
                }
            }
            StatementKind::If {
                then_stmt,
                else_stmt,
                ..
            } => {
                declarations(then_stmt, renames, map, false);
                if let Some(child) = else_stmt {
                    declarations(child, renames, map, false);
                }
            }
            StatementKind::Case { items, .. } => {
                for item in items {
                    declarations(&mut item.stmt, renames, map, false);
                }
            }
            StatementKind::For { body, .. }
            | StatementKind::While { body, .. }
            | StatementKind::DoWhile { body, .. }
            | StatementKind::Repeat { body, .. }
            | StatementKind::Forever { body }
            | StatementKind::Foreach { body, .. }
            | StatementKind::TimingControl { stmt: body, .. }
            | StatementKind::Wait { stmt: body, .. } => declarations(body, renames, map, false),
            _ => {}
        }
    }
    if let StatementKind::SeqBlock { stmts, .. } = &mut out.kind {
        for stmt in stmts {
            declarations(stmt, &renames, &map, true);
        }
    }
    Some(out)
}

/// `local_names` minus the names a loop declares itself (a for-init
/// `integer i`, foreach loop variables). A declared name that also exists at
/// the child's module scope (`integer i, j;` next to `for (integer i = 0;
/// ...)`) used to have its USES prefixed to the module variable while the
/// declaration stayed bare, so the loop tested an x-valued `inst.i` and never
/// ran. `None` when nothing collides (the common case). Block-local
/// declarations (`begin integer k; ... end`) are deliberately NOT stripped:
/// the runtime's process-context block locals are not yet consistent enough
/// to stand on their own, and the prefixed form keeps today's behaviour.
/// Names declared by the top-level `VarDecl` statements of a statement list
/// (a subroutine body or a block). §6.21: such a declaration shadows the
/// module's own names for the statements that follow it, so the inliner must
/// not prefix its uses with the instance path — `begin int u; u = 5; end`
/// clobbered the module-level `u`, a task-local `core` next to an instance
/// `core` read `core.c` as x, and a block-local handle named like the
/// enclosing instance read null.
pub(super) fn stmt_list_declared_names(stmts: &[Statement]) -> Vec<&str> {
    let mut out = Vec::new();
    for st in stmts {
        if let StatementKind::VarDecl { declarators, .. }
        | StatementKind::ParamDecl { declarators, .. } = &st.kind
        {
            for d in declarators {
                out.push(d.name.name.as_str());
            }
        }
    }
    out
}

/// A process local's type: class and type keys of the instance, then in a
/// generate rename the block's parameters and types (§6.21, §23.9).
fn rewrite_local_type(
    dt: &DataType,
    prefix: &str,
    port_map: &HashMap<String, Expression>,
) -> DataType {
    let dt = module_class_scope::data_type(dt, prefix, port_map);
    match gen_renames_local_types(prefix) {
        true => with_gen_part(local_type_takes, || gen_type(&dt)),
        false => dt,
    }
}

/// §6.18, §23.9: the types a statement list declares.
pub(super) fn stmt_list_typedef_names(stmts: &[Statement]) -> impl Iterator<Item = &str> {
    stmts.iter().filter_map(|st| match &st.kind {
        StatementKind::Typedef(td) => Some(td.name.name.as_str()),
        _ => None,
    })
}

/// Rewrite a statement list where each `VarDecl` shadows the module names
/// for the statements AFTER it (its own initialiser still sees the outer
/// set).
pub(super) fn rewrite_stmt_list_scoped(
    stmts: &[Statement],
    prefix: &str,
    port_map: &HashMap<String, Expression>,
    local_names: &std::collections::HashSet<String>,
    interface_map: &HashMap<String, String>,
) -> Vec<Statement> {
    let mut cur: Option<std::collections::HashSet<String>> = None;
    let mut cur_ports: Option<HashMap<String, Expression>> = None;
    // §6.21: the list's own declarations are not scopes (`upward_scope_rewrite`).
    let _stmt_locals = push_stmt_locals(
        stmts
            .iter()
            .filter_map(|st| match &st.kind {
                StatementKind::VarDecl { declarators, .. }
                | StatementKind::ParamDecl { declarators, .. } => Some(declarators),
                _ => None,
            })
            .flatten()
            .map(|d| d.name.name.clone())
            .collect(),
    );
    let mut out = Vec::with_capacity(stmts.len());
    for st in stmts {
        let names = cur.as_ref().unwrap_or(local_names);
        let ports = cur_ports.as_ref().unwrap_or(port_map);
        out.push(rewrite_stmt(st, prefix, ports, names, interface_map));
        if let StatementKind::VarDecl { declarators, .. }
        | StatementKind::ParamDecl { declarators, .. } = &st.kind
        {
            if let Some(reduced) =
                without_declared(names, declarators.iter().map(|d| d.name.name.as_str()))
            {
                cur = Some(reduced);
            }
            for d in declarators {
                // An empty prefix is an explicit alpha-renaming pass:
                // its mapping names this declaration itself, not an outer
                // module binding that the declaration shadows.
                if !prefix.is_empty()
                    && cur_ports
                        .as_ref()
                        .unwrap_or(port_map)
                        .contains_key(&d.name.name)
                {
                    cur_ports
                        .get_or_insert_with(|| port_map.clone())
                        .remove(&d.name.name);
                }
            }
        }
    }
    out
}

pub(super) fn without_declared<'a>(
    local_names: &std::collections::HashSet<String>,
    declared: impl Iterator<Item = &'a str>,
) -> Option<std::collections::HashSet<String>> {
    let mut reduced: Option<std::collections::HashSet<String>> = None;
    for n in declared {
        if local_names.contains(n) {
            reduced.get_or_insert_with(|| local_names.clone()).remove(n);
        }
    }
    reduced
}

fn rewrite_decl_list(
    declarators: &[crate::ast::stmt::VarDeclarator],
    prefix: &str,
    port_map: &HashMap<String, Expression>,
    local_names: &std::collections::HashSet<String>,
    interface_map: &HashMap<String, String>,
) -> Vec<crate::ast::stmt::VarDeclarator> {
    let renaming = gen_renames_local_types(prefix);
    declarators
        .iter()
        .map(|d| crate::ast::stmt::VarDeclarator {
            decl: d.decl,
            name: d.name.clone(),
            dimensions: match renaming {
                true => with_gen_part(local_type_takes, || gen_dims(&d.dimensions)),
                false => d.dimensions.clone(),
            },
            init: d.init.as_deref().map(|e| {
                Box::new(rewrite_expr(
                    e,
                    prefix,
                    port_map,
                    local_names,
                    interface_map,
                ))
            }),
            span: d.span,
        })
        .collect()
}

pub(super) fn rewrite_stmt(
    stmt: &Statement,
    prefix: &str,
    port_map: &HashMap<String, Expression>,
    local_names: &std::collections::HashSet<String>,
    interface_map: &HashMap<String, String>,
) -> Statement {
    // A changed enclosing block may still contain unchanged block lists.
    // Reuse only proven root identities; clone keeps explicit Fresh and
    // Disabled cache ownership in force for every nested statement.
    if matches!(
        stmt.kind,
        StatementKind::SeqBlock { .. } | StatementKind::ParBlock { .. }
    ) && prefix.is_empty()
        && port_map.is_empty()
        && interface_map.is_empty()
        && identity_rewrite::can_preserve_root_stmt(stmt)
    {
        return stmt.clone();
    }
    let new_kind = match &stmt.kind {
        StatementKind::BlockingAssign { lvalue, rvalue } => StatementKind::BlockingAssign {
            lvalue: rewrite_expr(lvalue, prefix, port_map, local_names, interface_map),
            rvalue: rewrite_expr(rvalue, prefix, port_map, local_names, interface_map),
        },
        StatementKind::NonblockingAssign {
            lvalue,
            delay,
            rvalue,
        } => StatementKind::NonblockingAssign {
            lvalue: rewrite_expr(lvalue, prefix, port_map, local_names, interface_map),
            delay: delay
                .as_ref()
                .map(|d| Box::new(rewrite_expr(d, prefix, port_map, local_names, interface_map))),
            rvalue: rewrite_expr(rvalue, prefix, port_map, local_names, interface_map),
        },
        StatementKind::Expr(expr) => StatementKind::Expr(rewrite_expr(
            expr,
            prefix,
            port_map,
            local_names,
            interface_map,
        )),
        StatementKind::If {
            unique_priority,
            condition,
            then_stmt,
            else_stmt,
        } => StatementKind::If {
            unique_priority: *unique_priority,
            condition: rewrite_expr(condition, prefix, port_map, local_names, interface_map),
            then_stmt: Box::new(rewrite_stmt(
                then_stmt,
                prefix,
                port_map,
                local_names,
                interface_map,
            )),
            else_stmt: else_stmt.as_ref().map(|s| {
                Box::new(rewrite_stmt(
                    s,
                    prefix,
                    port_map,
                    local_names,
                    interface_map,
                ))
            }),
        },
        StatementKind::Case {
            unique_priority,
            kind,
            expr,
            items,
        } => StatementKind::Case {
            unique_priority: *unique_priority,
            kind: *kind,
            expr: rewrite_expr(expr, prefix, port_map, local_names, interface_map),
            items: items
                .iter()
                .map(|item| CaseItem {
                    patterns: item
                        .patterns
                        .iter()
                        .map(|p| rewrite_expr(p, prefix, port_map, local_names, interface_map))
                        .collect(),
                    is_default: item.is_default,
                    stmt: rewrite_stmt(&item.stmt, prefix, port_map, local_names, interface_map),
                    span: item.span,
                    // §12.6: rewrite constant-expression sub-patterns and the
                    // `&&&` guard; tags and `.v` binding names are not signals.
                    pattern: item.pattern.as_deref().map(|p| {
                        Box::new(rewrite_pattern(
                            p,
                            prefix,
                            port_map,
                            local_names,
                            interface_map,
                        ))
                    }),
                    guard: item.guard.as_deref().map(|g| {
                        Box::new(rewrite_expr(
                            g,
                            prefix,
                            port_map,
                            local_names,
                            interface_map,
                        ))
                    }),
                })
                .collect(),
        },
        StatementKind::For {
            init,
            condition,
            step,
            body,
        } => {
            // The loop variables shadow same-named child-scope variables in
            // the condition, step and body; the init expressions are
            // evaluated before the declaration and keep the outer set.
            let bound: Vec<&str> = init
                .iter()
                .filter_map(|fi| match fi {
                    ForInit::VarDecl { name, .. } => Some(name.name.as_str()),
                    _ => None,
                })
                .collect();
            with_shadowed(&bound, port_map, local_names, |inner_ports, inner| {
                StatementKind::For {
                    init: init
                        .iter()
                        .map(|fi| match fi {
                            ForInit::VarDecl {
                                data_type,
                                name,
                                init,
                            } => ForInit::VarDecl {
                                data_type: rewrite_local_type(data_type, prefix, port_map),
                                name: name.clone(),
                                init: rewrite_expr(
                                    init,
                                    prefix,
                                    port_map,
                                    local_names,
                                    interface_map,
                                ),
                            },
                            ForInit::Assign { lvalue, rvalue } => ForInit::Assign {
                                lvalue: rewrite_expr(
                                    lvalue,
                                    prefix,
                                    port_map,
                                    local_names,
                                    interface_map,
                                ),
                                rvalue: rewrite_expr(
                                    rvalue,
                                    prefix,
                                    port_map,
                                    local_names,
                                    interface_map,
                                ),
                            },
                        })
                        .collect(),
                    condition: condition
                        .as_ref()
                        .map(|c| rewrite_expr(c, prefix, inner_ports, inner, interface_map)),
                    step: step
                        .iter()
                        .map(|s| rewrite_expr(s, prefix, inner_ports, inner, interface_map))
                        .collect(),
                    body: Box::new(rewrite_stmt(
                        body,
                        prefix,
                        inner_ports,
                        inner,
                        interface_map,
                    )),
                }
            })
        }
        StatementKind::While { condition, body } => StatementKind::While {
            condition: rewrite_expr(condition, prefix, port_map, local_names, interface_map),
            body: Box::new(rewrite_stmt(
                body,
                prefix,
                port_map,
                local_names,
                interface_map,
            )),
        },
        // §12.7.3: a `foreach` in an inlined child. Without an arm here the
        // statement passed through UNREWRITTEN, so both the array expression
        // and every name in the body kept the child's bare form. The runtime's
        // scope-hint fallbacks rescued the loop bounds and the writes, which is
        // why the loop ran and the array filled correctly — but a READ of the
        // array inside the body resolves through the base name, which no hint
        // reaches, so it returned x while the identical read outside the loop
        // was fine. The loop VARIABLES stay untouched: they are declared by the
        // foreach itself, not inherited from the child's scope.
        StatementKind::Foreach { array, vars, body } => {
            let bound: Vec<&str> = vars.iter().flatten().map(|v| v.name.as_str()).collect();
            with_shadowed(&bound, port_map, local_names, |inner_ports, inner| {
                StatementKind::Foreach {
                    array: rewrite_expr(array, prefix, port_map, local_names, interface_map),
                    vars: vars.clone(),
                    body: Box::new(rewrite_stmt(
                        body,
                        prefix,
                        inner_ports,
                        inner,
                        interface_map,
                    )),
                }
            })
        }
        // Sibling of the missing-Assertion-arm bug: these kinds also fell
        // through `other => other.clone()` un-rewritten, so a dotted
        // reference inside them stayed a raw MemberAccess (and, in prefix
        // mode, skipped prefixing/port substitution). Observed live on
        // `force tgt = host.sig;` in a bound module: the un-collapsed
        // rvalue broke continuous-force tracking. The rest are the same
        // class, fixed for uniformity.
        StatementKind::DoWhile { body, condition } => StatementKind::DoWhile {
            body: Box::new(rewrite_stmt(
                body,
                prefix,
                port_map,
                local_names,
                interface_map,
            )),
            condition: rewrite_expr(condition, prefix, port_map, local_names, interface_map),
        },
        StatementKind::Wait { condition, stmt } => StatementKind::Wait {
            condition: rewrite_expr(condition, prefix, port_map, local_names, interface_map),
            stmt: Box::new(rewrite_stmt(
                stmt,
                prefix,
                port_map,
                local_names,
                interface_map,
            )),
        },
        StatementKind::ProceduralContinuous(pc) => {
            use crate::ast::stmt::ProceduralContinuous as PC;
            StatementKind::ProceduralContinuous(match pc {
                PC::Assign { lvalue, rvalue } => PC::Assign {
                    lvalue: rewrite_expr(lvalue, prefix, port_map, local_names, interface_map),
                    rvalue: rewrite_expr(rvalue, prefix, port_map, local_names, interface_map),
                },
                PC::Deassign(lv) => PC::Deassign(rewrite_expr(
                    lv,
                    prefix,
                    port_map,
                    local_names,
                    interface_map,
                )),
                PC::Force { lvalue, rvalue } => PC::Force {
                    lvalue: rewrite_expr(lvalue, prefix, port_map, local_names, interface_map),
                    rvalue: rewrite_expr(rvalue, prefix, port_map, local_names, interface_map),
                },
                PC::Release(lv) => PC::Release(rewrite_expr(
                    lv,
                    prefix,
                    port_map,
                    local_names,
                    interface_map,
                )),
            })
        }
        // Declared names stay untouched (the declaration introduces them).
        // §6.21, §23.9: in a generate rename the type and dimensions read the
        // block's parameters and types; elsewhere only the initializer reads
        // outer names.
        // Block data there keeps its bare name, which the instance resolves.
        StatementKind::VarDecl {
            data_type,
            lifetime,
            declarators,
        } => StatementKind::VarDecl {
            data_type: rewrite_local_type(data_type, prefix, port_map),
            lifetime: *lifetime,
            declarators: rewrite_decl_list(declarators, prefix, port_map, local_names, interface_map),
        },
        StatementKind::ParamDecl {
            is_local,
            data_type,
            declarators,
        } => StatementKind::ParamDecl {
            is_local: *is_local,
            data_type: rewrite_local_type(data_type, prefix, port_map),
            declarators: rewrite_decl_list(declarators, prefix, port_map, local_names, interface_map),
        },
        // A process-local typedef's type reads as a local's does.
        StatementKind::Typedef(td) if prefix.is_empty() => {
            let mut td = td.clone();
            if gen_renames_local_types(prefix) {
                with_gen_part(local_type_takes, || {
                    td.data_type = gen_type(&td.data_type);
                    td.dimensions = gen_dims(&td.dimensions);
                });
            }
            StatementKind::Typedef(td)
        }
        StatementKind::RandCase { items } => StatementKind::RandCase {
            items: items
                .iter()
                .map(|(w, st)| {
                    (
                        rewrite_expr(w, prefix, port_map, local_names, interface_map),
                        rewrite_stmt(st, prefix, port_map, local_names, interface_map),
                    )
                })
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
            events: events.clone(),
            pass: pass.as_ref().map(|s| {
                Box::new(rewrite_stmt(
                    s,
                    prefix,
                    port_map,
                    local_names,
                    interface_map,
                ))
            }),
            fail: fail.as_ref().map(|s| {
                Box::new(rewrite_stmt(
                    s,
                    prefix,
                    port_map,
                    local_names,
                    interface_map,
                ))
            }),
            armed: *armed,
            idx: *idx,
            span: *span,
        },
        StatementKind::RsAction { body } => StatementKind::RsAction {
            body: Box::new(rewrite_stmt(
                body,
                prefix,
                port_map,
                local_names,
                interface_map,
            )),
        },
        StatementKind::Repeat { count, body } => StatementKind::Repeat {
            count: rewrite_expr(count, prefix, port_map, local_names, interface_map),
            body: Box::new(rewrite_stmt(
                body,
                prefix,
                port_map,
                local_names,
                interface_map,
            )),
        },
        StatementKind::Forever { body } => StatementKind::Forever {
            body: Box::new(rewrite_stmt(
                body,
                prefix,
                port_map,
                local_names,
                interface_map,
            )),
        },
        // §16.3/§16.4: an immediate assertion's condition and action blocks
        // are ordinary procedural code. This arm was missing, so the whole
        // statement fell through `other => other.clone()` un-rewritten: a
        // dotted reference in the condition (`sub.sig`, parsed as
        // MemberAccess) never collapsed to a hierarchical Ident, and the
        // interpreter read it as a (nonexistent) object property — 0. An
        // `assert (sub.sig >= lo) else $error(...)` in a bound checker
        // module falsely fired while the same read in a plain `if` (which
        // IS rewritten) resolved fine.
        StatementKind::Assertion(a) => {
            StatementKind::Assertion(crate::ast::stmt::AssertionStatement {
                kind: a.kind,
                expr: rewrite_expr(&a.expr, prefix, port_map, local_names, interface_map),
                action: a.action.as_ref().map(|s| {
                    Box::new(rewrite_stmt(
                        s,
                        prefix,
                        port_map,
                        local_names,
                        interface_map,
                    ))
                }),
                else_action: a.else_action.as_ref().map(|s| {
                    Box::new(rewrite_stmt(
                        s,
                        prefix,
                        port_map,
                        local_names,
                        interface_map,
                    ))
                }),
                is_property: a.is_property,
                is_sequence: a.is_sequence,
                deferred: a.deferred,
                label: a.label.clone(),
                procedural: a.procedural,
                inferred_clock: a
                    .inferred_clock
                    .as_ref()
                    .map(|ev| {
                        Box::new(crate::ast::stmt::EventExpr {
                            edge: ev.edge,
                            expr: rewrite_expr(&ev.expr, prefix, port_map, local_names, interface_map),
                            iff: ev.iff.as_ref().map(|g| {
                                rewrite_expr(g, prefix, port_map, local_names, interface_map)
                            }),
                            span: ev.span,
                        })
                    }),
                span: a.span,
            })
        }
        StatementKind::TimingControl {
            control,
            stmt: body,
        } => StatementKind::TimingControl {
            control: match control {
                TimingControl::Delay(e) => TimingControl::Delay(rewrite_expr(
                    e,
                    prefix,
                    port_map,
                    local_names,
                    interface_map,
                )),
                TimingControl::Event(ev) => TimingControl::Event(rewrite_event_control(
                    ev,
                    prefix,
                    port_map,
                    local_names,
                    interface_map,
                )),
            },
            stmt: Box::new(rewrite_stmt(
                body,
                prefix,
                port_map,
                local_names,
                interface_map,
            )),
        },
        StatementKind::SeqBlock { name, stmts } => StatementKind::SeqBlock {
            name: name.clone(),
            stmts: rewrite_stmt_list_scoped(stmts, prefix, port_map, local_names, interface_map).into(),
        },
        StatementKind::EventTrigger {
            nonblocking,
            name,
            target,
            span,
        } => StatementKind::EventTrigger {
            nonblocking: *nonblocking,
            name: Identifier {
                name: if let Some(mapped) = port_map.get(&name.name) {
                    whole_net_ident_name(mapped).unwrap_or_else(|| name.name.clone())
                } else if local_names.contains(&name.name) {
                    cat2(prefix, &name.name)
                } else if let Some(k) = target.as_deref().and_then(|t| match &t.kind {
                    // The parser's name of a one-name target (§15.5.1).
                    ExprKind::Ident(h) if h.path.len() == 1 && h.path[0].name.name == name.name => {
                        gen_renamed(h.bound, &name.name, |_| true)
                    }
                    _ => None,
                }) {
                    k
                } else {
                    name.name.clone()
                },
                span: name.span,
            },
            target: target.as_ref().map(|t| {
                Box::new(rewrite_expr(
                    t,
                    prefix,
                    port_map,
                    local_names,
                    interface_map,
                ))
            }),
            span: *span,
        },
        StatementKind::ParBlock {
            name,
            stmts,
            join_type,
        } => StatementKind::ParBlock {
            name: name.clone(),
            stmts: rewrite_stmt_list_scoped(stmts, prefix, port_map, local_names, interface_map).into(),
            join_type: *join_type,
        },

        // A subroutine body usually ENDS in `return <expr>` — leaving it
        // unrewritten silently bound the returned name to the wrong scope
        // (an inlined instance's function returned the caller-scope variable;
        // a $unit subroutine returned the module's shadow).
        StatementKind::Return(Some(expr)) => StatementKind::Return(Some(rewrite_expr(
            expr,
            prefix,
            port_map,
            local_names,
            interface_map,
        ))),
        StatementKind::Disable(h) => {
            StatementKind::Disable(rewrite_disable(h, prefix, local_names))
        }
        other => other.clone(),
    };
    Statement::new(new_kind, stmt.span)
}

/// §9.6.2: a `disable` of a task names the task's key, as a call does: the
/// generate rename unless the name binds elsewhere (§23.9), then the instance
/// prefix, or the key found upward (§23.8.1). A block keeps its label, by
/// which it is matched.
fn rewrite_disable(
    h: &HierarchicalIdentifier,
    prefix: &str,
    local_names: &std::collections::HashSet<String>,
) -> HierarchicalIdentifier {
    let [seg] = &h.path[..] else {
        return h.clone();
    };
    if h.root.is_some() || !seg.selects.is_empty() {
        return h.clone();
    }
    let name = seg.name.name.as_str();
    let key = gen_renamed(h.bound, name, |_| true)
        .or_else(|| {
            (h.bound.as_decl().is_some() && local_names.contains(name)).then(|| cat2(prefix, name))
        })
        .or_else(|| upward_subroutine_key(h, prefix));
    let mut out = h.clone();
    if let Some(k) = key {
        out.path[0].name.name = k;
    }
    out
}

fn rewrite_event_control(
    ev: &EventControl,
    prefix: &str,
    port_map: &HashMap<String, Expression>,
    local_names: &std::collections::HashSet<String>,
    interface_map: &HashMap<String, String>,
) -> EventControl {
    match ev {
        EventControl::Identifier(id) => {
            let name = if let Some(mapped) = port_map.get(&id.name) {
                whole_net_ident_name(mapped).unwrap_or_else(|| id.name.clone())
            } else if local_names.contains(&id.name) {
                cat2(prefix, &id.name)
            } else {
                id.name.clone()
            };
            EventControl::Identifier(Identifier {
                name,
                span: id.span,
            })
        }
        EventControl::HierIdentifier(expr) => EventControl::HierIdentifier(rewrite_expr(
            expr,
            prefix,
            port_map,
            local_names,
            interface_map,
        )),
        EventControl::EventExpr(exprs) => EventControl::EventExpr(
            exprs
                .iter()
                .map(|e| EventExpr {
                    edge: e.edge,
                    expr: rewrite_expr(&e.expr, prefix, port_map, local_names, interface_map),
                    iff: e
                        .iff
                        .as_ref()
                        .map(|i| rewrite_expr(i, prefix, port_map, local_names, interface_map)),
                    span: e.span,
                })
                .collect(),
        ),
        other => other.clone(),
    }
}
