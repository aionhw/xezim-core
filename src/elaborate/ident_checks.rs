use super::*;

/// Names bound by a §12.6 pattern's `.v` sub-patterns.
pub(super) fn collect_pattern_bindings(p: &crate::ast::stmt::Pattern, out: &mut Vec<String>) {
    use crate::ast::stmt::Pattern as P;
    match p {
        P::Binding(id) => out.push(id.name.clone()),
        P::Tagged { inner: Some(i), .. } => collect_pattern_bindings(i, out),
        P::Struct(ms) => {
            for (_, sp) in ms {
                collect_pattern_bindings(sp, out);
            }
        }
        _ => {}
    }
}

/// §27.6: every `begin : label` name introduced by a generate construct, at
/// any nesting depth. These are SCOPES in the hierarchical namespace
/// (`gblk.u.ID`, `g[0].u.ID`), not values, and validation runs before generate
/// inlining creates the flattened keys — so they are registered up front as
/// placeholder names, exactly as instance names already are.
/// §27.6: register every labelled generate block as a placeholder name so the
/// undeclared-identifier validator accepts it as a SCOPE root. `gblk.u.ID` and
/// `g[0].u.ID` are legal hierarchical references, but validation runs before
/// generate inlining creates the flattened keys, so the bare root (`gblk`, `g`)
/// was rejected and the whole enclosing block failed to elaborate — even though
/// the generate itself was correct, and a non-generate `u1.ID` worked because
/// instance names are registered the same way.
pub(super) fn register_generate_labels(items: &[ModuleItem], elab: &mut ElaboratedModule) {
    let mut labels = Vec::new();
    collect_generate_labels(items, &mut labels);
    for l in labels {
        if !elab.signals.contains_key(&l) {
            signals_insert_traced(
                &mut elab.signals,
                line!(),
                l.clone(),
                Signal {
                    is_const: false,
                    name: l.into(),
                    width: 1,
                    is_signed: false,
                    is_real: false,
                    direction: None,
                    value: Value::new(1),
                    type_name: Some("$genblock".to_string()),
                },
            );
        }
    }
}

fn collect_generate_labels(items: &[ModuleItem], out: &mut Vec<String>) {
    for item in items {
        match item {
            ModuleItem::GenerateRegion(gr) => collect_generate_labels(&gr.items, out),
            ModuleItem::GenerateFor(gf) => {
                if let Some(n) = &gf.name {
                    out.push(n.clone());
                }
                collect_generate_labels(&gf.items, out);
            }
            ModuleItem::GenerateIf(gi) => {
                for l in gi.branch_labels.iter().flatten() {
                    out.push(l.clone());
                }
                for (_, items) in &gi.branches {
                    collect_generate_labels(items, out);
                }
            }
            ModuleItem::GenerateCase(gc) => {
                for arm in &gc.arms {
                    if let Some(l) = &arm.label {
                        out.push(l.clone());
                    }
                    collect_generate_labels(&arm.items, out);
                }
            }
            _ => {}
        }
    }
}

pub(super) fn validate_stmt_idents(
    stmt: &Statement,
    elab: &ElaboratedModule,
    locals: &mut HashSet<String>,
) -> Result<(), String> {
    match &stmt.kind {
        StatementKind::BlockingAssign { lvalue, rvalue }
        | StatementKind::NonblockingAssign { lvalue, rvalue, .. } => {
            if let ExprKind::Ident(hier) = &lvalue.kind {
                let name = if hier.path.len() == 1 {
                    Some(hier.path[0].name.name.clone())
                } else {
                    // Hierarchical name: join segments
                    Some(
                        hier.path
                            .iter()
                            .map(|s| s.name.name.as_str())
                            .collect::<Vec<_>>()
                            .join("."),
                    )
                };
                if let Some(n) = name {
                    if let Some(sig) = elab.signals.get(&n) {
                        if sig.is_const && !elab.const_decl_inits.contains(&n) {
                            return Err(format!("Illegal write to constant identifier '{}'", n));
                        }
                        if sig.direction == Some(PortDirection::Input) {
                            return Err(format!("Illegal write to input identifier '{}'", n));
                        }
                    }
                }
            }
            if let ExprKind::MemberAccess { expr, member } = &lvalue.kind {
                if let ExprKind::Ident(hier) = &expr.kind {
                    if hier.path.len() == 1 {
                        let base = &hier.path[0].name.name;
                        if let Some(view) = elab.modport_views.get(base) {
                            if view.get(&member.name) == Some(&PortDirection::Input) {
                                return Err(format!(
                                    "Illegal write to input identifier '{}.{}'",
                                    base, member.name
                                ));
                            }
                        }
                        if let Some(dirs) = elab.clocking_signal_dirs.get(base) {
                            if dirs.get(&member.name) == Some(&PortDirection::Input) {
                                return Err(format!(
                                    "Illegal write to input identifier '{}.{}'",
                                    base, member.name
                                ));
                            }
                        }
                    }
                }
            }
            validate_expr_idents(lvalue, elab, locals)?;
            validate_expr_idents(rvalue, elab, locals)?;
        }
        StatementKind::If {
            condition,
            then_stmt,
            else_stmt,
            ..
        } => {
            validate_expr_idents(condition, elab, locals)?;
            // §12.6.2: `if (e matches p)` declares the pattern's `.v` bindings
            // for the then-branch (not the else-branch).
            let mut bound: Vec<String> = Vec::new();
            if let ExprKind::Matches { pattern, .. } = &condition.kind {
                collect_pattern_bindings(pattern, &mut bound);
            }
            let fresh: Vec<String> = bound
                .iter()
                .filter(|b| locals.insert((*b).clone()))
                .cloned()
                .collect();
            let r = validate_stmt_idents(then_stmt, elab, locals);
            for b in fresh {
                locals.remove(&b);
            }
            r?;
            if let Some(eb) = else_stmt {
                validate_stmt_idents(eb, elab, locals)?;
            }
        }
        StatementKind::Case { expr, items, .. } => {
            validate_expr_idents(expr, elab, locals)?;
            for item in items {
                for p in &item.patterns {
                    validate_expr_idents(p, elab, locals)?;
                }
                // §12.6.1: a pattern item's `.v` bindings are declared for the
                // scope of that item's statement (and its `&&&` guard). Add
                // them, validate, then remove so they don't leak to siblings.
                let mut bound: Vec<String> = Vec::new();
                if let Some(pat) = &item.pattern {
                    collect_pattern_bindings(pat, &mut bound);
                }
                let fresh: Vec<String> = bound
                    .iter()
                    .filter(|b| locals.insert((*b).clone()))
                    .cloned()
                    .collect();
                if let Some(g) = &item.guard {
                    validate_expr_idents(g, elab, locals)?;
                }
                let r = validate_stmt_idents(&item.stmt, elab, locals);
                for b in fresh {
                    locals.remove(&b);
                }
                r?;
            }
        }
        StatementKind::For {
            init,
            condition,
            step,
            body,
        } => {
            let mut for_locals = Vec::new();
            for fi in init {
                match fi {
                    ForInit::VarDecl { name, init: e, .. } => {
                        validate_expr_idents(e, elab, locals)?;
                        // §12.7.1/§12.7.3: a loop variable shadows a
                        // same-named local only inside the loop; the local
                        // stays declared after it.
                        if locals.insert(name.name.clone()) {
                            for_locals.push(name.name.clone());
                        }
                    }
                    ForInit::Assign { lvalue, rvalue } => {
                        validate_expr_idents(lvalue, elab, locals)?;
                        validate_expr_idents(rvalue, elab, locals)?;
                    }
                }
            }
            if let Some(c) = condition {
                validate_expr_idents(c, elab, locals)?;
            }
            for s in step {
                validate_expr_idents(s, elab, locals)?;
            }
            validate_stmt_idents(body, elab, locals)?;
            for n in for_locals {
                locals.remove(&n);
            }
        }
        StatementKind::Foreach { array, body, vars } => {
            validate_expr_idents(array, elab, locals)?;
            let mut foreach_locals = Vec::new();
            for id in vars.iter().flatten() {
                if locals.insert(id.name.clone()) {
                    foreach_locals.push(id.name.clone());
                }
            }
            validate_stmt_idents(body, elab, locals)?;
            for n in foreach_locals {
                locals.remove(&n);
            }
        }
        StatementKind::While { condition, body } | StatementKind::DoWhile { body, condition } => {
            validate_expr_idents(condition, elab, locals)?;
            validate_stmt_idents(body, elab, locals)?;
        }
        StatementKind::Repeat { count, body } => {
            validate_expr_idents(count, elab, locals)?;
            validate_stmt_idents(body, elab, locals)?;
        }
        StatementKind::Forever { body } => validate_stmt_idents(body, elab, locals)?,
        StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
            for s in stmts {
                validate_stmt_idents(s, elab, locals)?;
            }
        }
        StatementKind::TimingControl { control, stmt } => {
            match control {
                TimingControl::Delay(e) => validate_expr_idents(e, elab, locals)?,
                TimingControl::Event(ev) => validate_event_idents(ev, elab, locals)?,
            }
            validate_stmt_idents(stmt, elab, locals)?;
        }
        StatementKind::Expr(e) => validate_expr_idents(e, elab, locals)?,
        StatementKind::Wait { condition, stmt } => {
            validate_expr_idents(condition, elab, locals)?;
            validate_stmt_idents(stmt, elab, locals)?;
        }
        StatementKind::Assertion(a) => {
            validate_expr_idents(&a.expr, elab, locals)?;
            if let Some(s) = &a.action {
                validate_stmt_idents(s, elab, locals)?;
            }
            if let Some(s) = &a.else_action {
                validate_stmt_idents(s, elab, locals)?;
            }
        }
        StatementKind::Return(Some(expr)) => {
            validate_expr_idents(expr, elab, locals)?;
        }
        StatementKind::VarDecl { declarators, .. }
        | StatementKind::ParamDecl { declarators, .. } => {
            for d in declarators {
                if let Some(init) = &d.init {
                    validate_expr_idents(init, elab, locals)?;
                }
                locals.insert(d.name.name.clone());
            }
        }
        // §6.18: a block-local typedef introduces a type name later statements
        // may use as a scope (`loc_t::static_method(...)`) or declare with.
        StatementKind::Typedef(td) => {
            locals.insert(td.name.name.clone());
        }
        _ => {}
    }
    Ok(())
}

/// §6.7.1: a net's data type is 4-state integral or an aggregate of such; a
/// class handle, `string`, `chandle` or `event` can never be a net.
pub(super) fn check_net_data_type(
    nd: &crate::ast::decl::NetDeclaration,
    elab: &ElaboratedModule,
) -> Result<(), String> {
    let bad = match &nd.data_type {
        DataType::TypeReference { name, .. }
            if elab.classes.contains_key(&name.name.name)
                && elab
                    .typedef_types
                    .get(&name.name.name)
                    .is_none_or(|dt| matches!(dt, DataType::Void(_))) =>
        {
            Some(format!("class type '{}'", name.name.name))
        }
        DataType::Simple { kind, .. } => Some(format!("{:?}", kind).to_lowercase()),
        _ => None,
    };
    match bad {
        Some(what) => Err(span_error(
            elab,
            nd.span,
            &format!("illegal net data type: {} (IEEE 1800-2017 §6.7.1)", what),
        )),
        None => Ok(()),
    }
}

pub(super) fn validate_expr_idents(
    expr: &Expression,
    elab: &ElaboratedModule,
    locals: &HashSet<String>,
) -> Result<(), String> {
    validate_expr_idents_as(expr, elab, locals, HeadRole::Value)
}

/// `validate_expr_idents` for an expression whose head is written as `role`.
fn validate_expr_idents_as(
    expr: &Expression,
    elab: &ElaboratedModule,
    locals: &HashSet<String>,
    role: HeadRole,
) -> Result<(), String> {
    fn root_ident_name(expr: &Expression) -> Option<&str> {
        match &expr.kind {
            ExprKind::Ident(hier) if hier.path.len() == 1 => Some(hier.path[0].name.name.as_str()),
            ExprKind::MemberAccess { expr, .. } => root_ident_name(expr),
            _ => None,
        }
    }

    fn generated_subroutine_name(
        expr: &Expression,
        params: &HashMap<String, Value>,
    ) -> Option<String> {
        let ExprKind::MemberAccess { expr: base, member } = &expr.kind else {
            return None;
        };
        let ExprKind::Index { expr: scope, index } = &base.kind else {
            return None;
        };
        let ExprKind::Ident(h) = &scope.kind else {
            return None;
        };
        if h.path.len() != 1 || !h.path[0].selects.is_empty() {
            return None;
        }
        let idx = const_eval_i64_with_params(index, Some(params))?;
        Some(format!("{}[{}].{}", h.path[0].name.name, idx, member.name))
    }

    match &expr.kind {
        ExprKind::Ident(hier)
            // Only check plain identifiers for now (hierarchical might be valid across modules)
            if hier.path.len() == 1 => {
                let name = &hier.path[0].name.name;
                // `std` is the built-in package (§18.12 std::randomize,
                // std::mailbox, std::semaphore, …) — always a legal root.
                // `process` is the built-in class of §9.7 — `process::self()`
                // plus its §18.14 random-stability methods (srandom,
                // get_randstate, set_randstate). It is never user-declared, so
                // its use as a scope root must not be flagged undeclared.
                if name == "new" || name.starts_with('$') || name == "super" || name == "this"
                    || name == "std" || name == "process"
                {
                    return Ok(());
                }
                // A built-in type keyword captured as an Ident — only the
                // parser's `$bits(<type>)` / `$size(<type>)` type-argument path
                // produces these, so it's a type reference, not a signal.
                if is_builtin_type_keyword(name) || name == "void" {
                    return Ok(());
                }
                // §26.3: `pkg::name` is the storage spelling `pkg_scope`
                // gives a variable several packages declare; it is
                // registered with the package, after this check runs.
                if name
                    .split_once("::")
                    .is_some_and(|(p, _)| elab.packages.contains(p))
                {
                    return Ok(());
                }
                match head_verdict(hier, role) {
                    HeadVerdict::Declared => return Ok(()),
                    HeadVerdict::Unbound => {}
                    // §23.8.1: the top has no upward scope to find a call in.
                    HeadVerdict::Undeclared | HeadVerdict::UpwardCall => {
                        return Err(span_error(
                            elab,
                            expr.span,
                            &format!("Undeclared identifier '{}'", name),
                        ));
                    }
                }
                if !elab.signals.contains_key(name) && !elab.parameters.contains_key(name) &&
                   !elab.functions.contains_key(name) && !elab.tasks.contains_key(name) &&
                   !elab.dpi_imports.contains_key(name) &&
                   !elab.arrays.contains_key(name) && !elab.associative_arrays.contains_key(name) &&
                   !elab.arrays_2d.contains_key(name) && !elab.arrays_nd.contains_key(name) &&
                   !elab.classes.contains_key(name) && !elab.typedefs.contains_key(name) &&
                   !elab.clocking_blocks.contains_key(name) && !elab.lets.contains_key(name) &&
                   !elab.sequences.contains(name) &&
                   // §19.7.1 `cg::type_option.f` scopes on the covergroup name.
                   !elab.covergroups.contains_key(name) &&
                   // §23.11: an instance a compilation-unit bind adds to
                   // this top. Another top cannot name it (§23.8).
                   !(role == HeadRole::Path && is_unit_bind_instance_of(&elab.name, name)) &&
                   !locals.contains(name) {
                   return Err(span_error(
                       elab,
                       expr.span,
                       &format!("Undeclared identifier '{}'", name),
                   ));
                }            }
        ExprKind::Ident(hier) => {
            if let HeadVerdict::Undeclared = head_verdict(hier, role) {
                return Err(span_error(
                    elab,
                    expr.span,
                    &format!("Undeclared identifier '{}'", hier.path[0].name.name),
                ));
            }
        }
        ExprKind::Unary { operand, .. } => validate_expr_idents(operand, elab, locals)?,
        ExprKind::Binary { left, right, .. } => { validate_expr_idents(left, elab, locals)?; validate_expr_idents(right, elab, locals)?; }
        ExprKind::Conditional { condition, then_expr, else_expr } => {
            validate_expr_idents(condition, elab, locals)?;
            validate_expr_idents(then_expr, elab, locals)?;
            validate_expr_idents(else_expr, elab, locals)?;
        }
        ExprKind::Concatenation(parts) => { for p in parts { validate_expr_idents(p, elab, locals)?; } }
        ExprKind::Replication { count, exprs } => {
            validate_expr_idents(count, elab, locals)?;
            for e in exprs { validate_expr_idents(e, elab, locals)?; }
        }
        ExprKind::Index { expr, index } => {
            if let ExprKind::Ident(hier) = &expr.kind {
                if hier.path.len() == 1 {
                    let nm = &hier.path[0].name.name;
                    // §6.12.2 forbids a bit-select OF a real, but `r[i]` on an
                    // ARRAY of reals is an ELEMENT select, not a bit-select.
                    // The check keyed only on "the signal is real", so
                    // `real r_aa[int]; r_aa[7]` was rejected outright and any
                    // module holding a real associative/unpacked array failed
                    // to elaborate.
                    let is_indexable_collection = elab.arrays.contains_key(nm)
                        || elab.associative_arrays.contains_key(nm)
                        || elab.arrays_2d.contains_key(nm)
                        || elab.arrays_nd.contains_key(nm)
                        || elab.dynamic_arrays.contains(nm);
                    if !is_indexable_collection {
                        if let Some(sig) = elab.signals.get(nm) {
                            if sig.is_real {
                                return Err(format!("Bit-select of real variable '{}' is not allowed", sig.name));
                            }
                        }
                    }
                }
            }
            if let ExprKind::Ident(hier) = &index.kind {
                if hier.path.len() == 1 {
                    if let Some(sig) = elab.signals.get(&hier.path[0].name.name) {
                        if sig.is_real {
                            return Err(format!("Real variable '{}' cannot be used as bit-select index", sig.name));
                        }
                    }
                }
            }
            let base = match role {
                HeadRole::Path => HeadRole::Path,
                _ => HeadRole::Value,
            };
            validate_expr_idents_as(expr, elab, locals, base)?;
            validate_expr_idents(index, elab, locals)?;
        }
        ExprKind::RangeSelect { expr, left, right, .. } => {
            if let ExprKind::Ident(hier) = &expr.kind {
                if hier.path.len() == 1 {
                    if let Some(sig) = elab.signals.get(&hier.path[0].name.name) {
                        if sig.is_real {
                            return Err(format!("Part-select of real variable '{}' is not allowed", sig.name));
                        }
                    }
                }
            }
            validate_expr_idents(expr, elab, locals)?;
            validate_expr_idents(left, elab, locals)?;
            validate_expr_idents(right, elab, locals)?;
        }
        ExprKind::Paren(inner) => validate_expr_idents(inner, elab, locals)?,
        ExprKind::Call { func, args } => {
            let generated = generated_subroutine_name(func, &elab.parameters)
                .is_some_and(|name| {
                    elab.functions.contains_key(&name) || elab.tasks.contains_key(&name)
                });
            if !generated {
                validate_expr_idents(func, elab, locals)?;
            }
            // §18.11: the arguments of `obj.randomize(a, b)` name MEMBERS of
            // the object's class, not identifiers of the enclosing scope, so
            // validating them here rejected perfectly legal code outright
            // ("Undeclared identifier 'a'") and aborted the whole run. The
            // members are resolved against the object at call time instead.
            let randomize_members = matches!(&func.kind,
                ExprKind::MemberAccess { member, .. } if member.name == "randomize");
            if !randomize_members {
                for a in args { validate_expr_idents(a, elab, locals)?; }
            }
        }
        ExprKind::SystemCall { name, args } => {
            // Args can be scope/module/instance references (not value lookups)
            // for dump/coverage/scope-info system tasks.
            let skip = matches!(
                name.as_str(),
                "$dumpvars" | "$dumpfile" | "$dumpports" | "$dumpportsoff"
                    | "$dumpportson" | "$dumpportsflush" | "$dumpportsall"
                    | "$dumpportslimit" | "$printtimescale" | "$timeformat"
                    | "$coverage_control" | "$coverage_get" | "$coverage_get_max"
                    | "$coverage_merge" | "$coverage_save" | "$get_coverage"
                    | "$set_coverage_db_name" | "$load_coverage_db"
                    // FSDB/VPD waveform tasks: scope args like $dumpvars.
                    | "$fsdbDumpvars" | "$fsdbDumpfile" | "$vcdpluson" | "$vcdplusoff"
                    // SHM + SST2 waveform tasks: the first
                    // argument of $shm_probe/$recordvars/$probe is a SCOPE
                    // (`$shm_probe(testbench, "AC")`), so validating it as a
                    // value lookup failed whole-testbench elaboration with
                    // "Undeclared identifier '<top>'".
                    | "$shm_open" | "$shm_probe" | "$shm_close" | "$shm_save"
                    | "$recordfile" | "$recordvars" | "$recordon" | "$recordoff"
                    | "$recordsetup" | "$recordclose"
                    | "$probe" | "$probe_close" | "$probe_off" | "$probe_on"
                    // §20.16: second argument is an instance scope.
                    | "$sdf_annotate"
                    // §20.12 assertion controls: `$assertoff(0, testbench)`
                    // during reset is a staple of vendor testbenches — the
                    // trailing args are scopes/hierarchical refs, not values.
                    | "$assertoff" | "$asserton" | "$assertkill" | "$assertcontrol"
                    | "$assertpasson" | "$assertpassoff" | "$assertfailon"
                    | "$assertfailoff" | "$assertnonvacuouson" | "$assertvacuousoff"
                    // Legacy scope/listing tasks (§21 of 1364): scope args too.
                    | "$scope" | "$list" | "$showvars" | "$showscopes"
            )
            // Vendor debug/waveform families take scope args throughout and
            // are runtime-ignored anyway; match by PREFIX so each vendor's
            // next task name ($xm* Verisium/vwdb dumping, $indago*, ...)
            // doesn't re-break elaboration one name at a time. None collide
            // with an LRM-defined task name.
            || ["$shm", "$xm", "$fsdb", "$vcdplus", "$vwdb", "$indago", "$record", "$probe"]
                .iter()
                .any(|p| name.starts_with(p));
            if !skip {
                for a in args { validate_expr_idents(a, elab, locals)?; }
            }
        }
        ExprKind::MemberAccess { expr, .. } => {
            // Skip validation for package scopes (`pkg::name`) and for
            // hierarchical references rooted at the current top module name
            // (e.g. `tb.x_soc...` inside the testbench).
            if let Some(root) = root_ident_name(expr) {
                if root == elab.name || elab.packages.contains(root) {
                    // scope / hierarchy reference, not a value lookup
                } else {
                    validate_expr_idents_as(expr, elab, locals, HeadRole::Path)?;
                }
            } else {
                validate_expr_idents_as(expr, elab, locals, HeadRole::Path)?;
            }
        }
        ExprKind::WithClause { expr, filter } => {
            // The Call's args inside an array-method `with` clause are
            // iterator-name bindings (e.g. `find(item, idx)` introduces
            // `item` and `idx`), not value references. Validate the
            // method receiver but skip the iterator-name args, and add
            // those names to the filter's scope.
            let mut with_locals = locals.clone();
            with_locals.insert("item".to_string());
            match &expr.kind {
                ExprKind::Call { func, args } => {
                    validate_expr_idents(func, elab, locals)?;
                    for a in args {
                        if let ExprKind::Ident(h) = &a.kind {
                            if h.path.len() == 1 && h.path[0].selects.is_empty() {
                                with_locals.insert(h.path[0].name.name.clone());
                                continue;
                            }
                        }
                        validate_expr_idents(a, elab, locals)?;
                    }
                }
                _ => validate_expr_idents(expr, elab, locals)?,
            }
            validate_expr_idents(filter, elab, &with_locals)?;
        }
        _ => {}
    }
    Ok(())
}

fn validate_event_idents(
    ev: &EventControl,
    elab: &ElaboratedModule,
    locals: &HashSet<String>,
) -> Result<(), String> {
    match ev {
        EventControl::EventExpr(exprs) => {
            for ee in exprs {
                if ee.edge.is_some() {
                    if let ExprKind::Ident(hier) = &ee.expr.kind {
                        if hier.path.len() == 1 {
                            if let Some(sig) = elab.signals.get(&hier.path[0].name.name) {
                                if sig.is_real {
                                    return Err(format!("Edge event on real variable '{}' is not allowed", sig.name));
                                }
                            }
                        }
                    }
                }
                validate_expr_idents(&ee.expr, elab, locals)?;
            }
        }
        // §14.11: `##N` desugars to the reserved `__xz_default_clocking`
        // marker. It is only legal when a `default clocking` block exists —
        // a clocking block declared WITHOUT `default` does not qualify.
        EventControl::Identifier(id)
            if (id.name == "__xz_default_clocking" || id.name == "__xz_default_clocking0")
                && !elab.clocking_blocks.values().any(|cd| cd.is_default) =>
        {
            let loc = span_location(elab, id.span)
                .map(|l| format!(" at {}", l))
                .unwrap_or_default();
            return Err(format!(
                "A default clocking block must be specified to use the ##n \
                 timing statement{}",
                loc
            ));
        }
        EventControl::Identifier(id)
            // §14.3/§14.11: `@(cb)` may name a clocking block, and the parser
            // desugars procedural `##N` to a wait on the reserved
            // `__xz_default_clocking` marker — both resolve at simulation
            // time to the block's clock event, not to a declared signal.
            if !elab.signals.contains_key(&id.name) && !elab.parameters.contains_key(&id.name)
                && !elab.sequences.contains(&id.name) && !locals.contains(&id.name)
                && !elab.clocking_blocks.contains_key(&id.name)
                && id.name != "__xz_default_clocking"
                && id.name != "__xz_default_clocking0"
            => {
                return Err(span_error(
                    elab,
                    id.span,
                    &format!("Undeclared identifier '{}'", id.name),
                ));
            }
        EventControl::HierIdentifier(e) => validate_expr_idents(e, elab, locals)?,
        _ => {}
    }
    Ok(())
}
