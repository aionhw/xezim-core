use super::*;

/// §6.21 escape hatch: accept implicitly-static initializers (warn instead of
/// erroring). Real designs carry the pattern and other simulators let it be
/// suppressed, so a user hitting it mid-flow needs a way forward that is not
/// "edit a vendor's source tree".
static RELAX_IMPLICIT_STATIC: std::sync::atomic::AtomicBool =
    std::sync::atomic::AtomicBool::new(false);

pub fn set_relax_implicit_static(on: bool) {
    RELAX_IMPLICIT_STATIC.store(on, std::sync::atomic::Ordering::Relaxed);
}

/// Whether accepted implicit initializers retain static lifetime (§6.21).
/// Consumers include this semantic mode in their elaborated-design cache key.
pub fn relax_implicit_static() -> bool {
    if RELAX_IMPLICIT_STATIC.load(std::sync::atomic::Ordering::Relaxed) {
        return true;
    }
    static ENV: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENV.get_or_init(|| std::env::var("XEZIM_ALLOW_IMPLICIT_STATIC").ok().as_deref() == Some("1"))
}

/// Where a §6.21 violation was found, for the diagnostic.
#[derive(Clone, Copy)]
pub(crate) struct StaticInitScope<'a> {
    /// "function" / "task"
    pub kind: &'a str,
    /// subroutine name
    pub name: &'a str,
    /// "package" / "module"
    pub owner_kind: &'a str,
    /// enclosing package / module name
    pub owner: &'a str,
}

pub(super) fn check_implicit_static_inits(
    stmts: &[crate::ast::stmt::Statement],
    elab: &ElaboratedModule,
    scope: StaticInitScope<'_>,
) -> Result<(), String> {
    use crate::ast::stmt::StatementKind as SK;
    fn walk(s: &crate::ast::stmt::Statement) -> Option<(String, Span)> {
        match &s.kind {
            SK::VarDecl {
                lifetime: None,
                declarators,
                ..
            } => {
                for d in declarators {
                    if d.init.is_some() {
                        return Some((d.name.name.clone(), d.name.span));
                    }
                }
                None
            }
            SK::SeqBlock { stmts, .. } | SK::ParBlock { stmts, .. } => stmts.iter().find_map(walk),
            SK::If {
                then_stmt,
                else_stmt,
                ..
            } => walk(then_stmt).or_else(|| else_stmt.as_ref().and_then(|eb| walk(eb))),
            SK::For { body, .. }
            | SK::While { body, .. }
            | SK::DoWhile { body, .. }
            | SK::Repeat { body, .. }
            | SK::Forever { body }
            | SK::Foreach { body, .. } => walk(body),
            SK::TimingControl { stmt, .. } | SK::Wait { stmt, .. } => walk(stmt),
            SK::Case { items, .. } => items.iter().find_map(|it| walk(&it.stmt)),
            _ => None,
        }
    }
    let Some((var, span)) = stmts.iter().find_map(walk) else {
        return Ok(());
    };

    // The location is the whole point of this diagnostic: without it a user
    // hitting the rule in a large multi-file design has no way to find the
    // declaration. Hint the file with the OWNER (package/module), whose span
    // space the subroutine body lives in.
    let where_ = match span_location_of(elab, span, scope.owner) {
        Some(loc) => format!(
            "  in {} '{}' of {} '{}' at {}",
            scope.kind, scope.name, scope.owner_kind, scope.owner, loc
        ),
        None => format!(
            "  in {} '{}' of {} '{}'",
            scope.kind, scope.name, scope.owner_kind, scope.owner
        ),
    };

    if relax_implicit_static() {
        crate::log_eprintln(&format!(
            "[xezim][warning] variable '{}' is implicitly static (§6.21); accepted because \
             --relax-implicit-static is in effect\n{}",
            var, where_
        ));
        return Ok(());
    }

    Err(format!(
        "Variable '{}' is implicitly static; declare it explicitly static or automatic (§6.21)\n\
         {}\n  \
         fix: `static <type> {} = ...;` (one copy, initialized once before time 0) or \
         `automatic <type> {} = ...;` (a fresh copy per call)\n  \
         or accept it as-is: --relax-implicit-static (env XEZIM_ALLOW_IMPLICIT_STATIC=1)",
        var, where_, var, var
    ))
}

pub(super) fn validate_enum_assignments(elab: &ElaboratedModule) -> Result<(), String> {
    use crate::ast::expr::{ExprKind, Expression};
    use crate::ast::stmt::{Statement, StatementKind};
    fn try_const_u64(e: &Expression, elab: &ElaboratedModule) -> Option<u64> {
        // Only fold pure constant rvalues. Anything with an Ident or
        // function call is conservatively skipped.
        match &e.kind {
            ExprKind::Number(_) => Some(eval_const_expr(e, &elab.parameters)),
            ExprKind::Paren(inner) => try_const_u64(inner, elab),
            _ => None,
        }
    }
    // §23.9: resolve the nearest declaration before consulting module signals.
    // None is a local declaration whose type is not a named enum.
    type Scope = HashMap<String, Option<String>>;
    fn bind(scope: &mut Scope, name: &str, dt: &DataType, elab: &ElaboratedModule) {
        let enum_name = match dt {
            DataType::TypeReference { name, .. } => {
                let full = name.qualified();
                if elab.enum_members.contains_key(&full) {
                    Some(full)
                } else {
                    elab.enum_members
                        .contains_key(&name.name.name)
                        .then(|| name.name.name.clone())
                }
            }
            _ => None,
        };
        scope.insert(name.to_string(), enum_name);
    }
    fn declarations(stmts: &[Statement], elab: &ElaboratedModule) -> Scope {
        let mut scope = Scope::default();
        for stmt in stmts {
            match &stmt.kind {
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
                    for decl in declarators {
                        bind(&mut scope, &decl.name.name, data_type, elab);
                    }
                }
                _ => {}
            }
        }
        scope
    }
    fn check_assign(
        lvalue: &Expression,
        rvalue: &Expression,
        elab: &ElaboratedModule,
        scopes: &[Scope],
    ) -> Result<(), String> {
        if let ExprKind::Ident(h) = &lvalue.kind {
            if h.path.len() == 1 {
                let name = &h.path[0].name.name;
                let tname = match scopes.iter().rev().find_map(|scope| scope.get(name)) {
                    Some(local) => local.as_deref(),
                    None => elab
                        .signals
                        .get(name)
                        .and_then(|sig| sig.type_name.as_deref()),
                };
                if let Some(tname) = tname
                    && let Some(members) = elab.enum_members.get(tname)
                    && let Some(v) = try_const_u64(rvalue, elab)
                    && !members.iter().any(|(_, mv)| *mv == v)
                {
                    return Err(format!(
                        "Assignment of {} to enum '{}' variable '{}' is not a declared member (IEEE 1800-2017 §6.19.3)",
                        v, tname, name
                    ));
                }
            }
        }
        Ok(())
    }
    fn walk_stmt(
        s: &Statement,
        elab: &ElaboratedModule,
        scopes: &mut Vec<Scope>,
    ) -> Result<(), String> {
        match &s.kind {
            StatementKind::BlockingAssign { lvalue, rvalue }
            | StatementKind::NonblockingAssign { lvalue, rvalue, .. } => {
                check_assign(lvalue, rvalue, elab, scopes)?;
            }
            StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
                scopes.push(declarations(stmts, elab));
                for s in stmts {
                    walk_stmt(s, elab, scopes)?;
                }
                scopes.pop();
            }
            StatementKind::If {
                then_stmt,
                else_stmt,
                ..
            } => {
                walk_stmt(then_stmt, elab, scopes)?;
                if let Some(e) = else_stmt {
                    walk_stmt(e, elab, scopes)?;
                }
            }
            StatementKind::For { init, body, .. } => {
                let mut scope = Scope::default();
                for init in init {
                    if let crate::ast::stmt::ForInit::VarDecl {
                        name, data_type, ..
                    } = init
                    {
                        bind(&mut scope, &name.name, data_type, elab);
                    }
                }
                scopes.push(scope);
                walk_stmt(body, elab, scopes)?;
                scopes.pop();
            }
            StatementKind::Foreach { vars, body, .. } => {
                let scope = vars
                    .iter()
                    .flatten()
                    .map(|v| (v.name.clone(), None))
                    .collect();
                scopes.push(scope);
                walk_stmt(body, elab, scopes)?;
                scopes.pop();
            }
            StatementKind::While { body, .. }
            | StatementKind::DoWhile { body, .. }
            | StatementKind::Forever { body }
            | StatementKind::Repeat { body, .. } => walk_stmt(body, elab, scopes)?,
            StatementKind::Case { items, .. } => {
                for it in items {
                    walk_stmt(&it.stmt, elab, scopes)?;
                }
            }
            StatementKind::TimingControl { stmt, .. } => walk_stmt(stmt, elab, scopes)?,
            _ => {}
        }
        Ok(())
    }
    for ib in &elab.initial_blocks {
        walk_stmt(&ib.stmt, elab, &mut Vec::new())?;
    }
    for ab in &elab.always_blocks {
        walk_stmt(&ab.stmt, elab, &mut Vec::new())?;
    }
    for f in elab.functions.values() {
        let mut scope = declarations(&f.items, elab);
        bind(&mut scope, &f.name.name.name, &f.return_type, elab);
        for port in &f.ports {
            bind(&mut scope, &port.name.name, &port.data_type, elab);
        }
        let mut scopes = vec![scope];
        for s in &f.items {
            walk_stmt(s, elab, &mut scopes)?;
        }
    }
    for t in elab.tasks.values() {
        let mut scope = declarations(&t.items, elab);
        for port in &t.ports {
            bind(&mut scope, &port.name.name, &port.data_type, elab);
        }
        let mut scopes = vec![scope];
        for s in &t.items {
            walk_stmt(s, elab, &mut scopes)?;
        }
    }
    Ok(())
}

fn is_lvalue_expr(e: &crate::ast::expr::Expression) -> bool {
    use crate::ast::expr::ExprKind;
    matches!(
        &e.kind,
        ExprKind::Ident(_)
            | ExprKind::Index { .. }
            | ExprKind::RangeSelect { .. }
            | ExprKind::MemberAccess { .. }
            | ExprKind::Concatenation(_)
    )
}

pub(super) fn validate_ref_arg_lvalues(elab: &ElaboratedModule) -> Result<(), String> {
    use crate::ast::expr::{ExprKind, Expression};
    use crate::ast::stmt::{Statement, StatementKind};
    // §26.3: package subroutines have both qualified registrations and bare
    // aliases. An alias still belongs to its declaration's package, even
    // when another package supplied the bare entry for a callee in its body.
    fn declaring_package<'a>(
        key: &'a str,
        span: crate::ast::Span,
        is_task: bool,
        elab: &'a ElaboratedModule,
    ) -> Option<&'a str> {
        if let Some((pkg, _)) = key.split_once("::")
            && elab.packages.contains(pkg)
        {
            return Some(pkg);
        }
        elab.packages.iter().find_map(|pkg| {
            let qualified = format!("{pkg}::{key}");
            let registered_span = if is_task {
                elab.tasks.get(&qualified).map(|t| t.span)
            } else {
                elab.functions.get(&qualified).map(|f| f.span)
            };
            (registered_span == Some(span)).then_some(pkg.as_str())
        })
    }
    fn callee_key(
        func: &Expression,
        package: Option<&str>,
        locals: &HashMap<String, DataType>,
        elab: &ElaboratedModule,
    ) -> Option<String> {
        // §23.8 / §26.3: `p.route(...)` can name an object variable p,
        // even when a package p exists. Never borrow the package signature
        // for a receiver declared in this call's scope.
        let is_package = |name: &str| {
            elab.packages.contains(name)
                && !locals.contains_key(name)
                && !elab.signals.contains_key(name)
        };
        match &func.kind {
            ExprKind::Ident(h) if h.path.iter().all(|s| s.selects.is_empty()) => {
                let first = h.path.first()?.name.name.as_str();
                if h.path.len() == 1 {
                    if let Some(pkg) = package {
                        let key = format!("{pkg}::{first}");
                        if elab.functions.contains_key(&key) || elab.tasks.contains_key(&key) {
                            return Some(key);
                        }
                    }
                    return Some(first.to_string());
                }
                // A qualified call must never borrow an unrelated bare
                // function's signature (§13.5.2 / §26.3 / §23.8).
                let sep = if is_package(first) {
                    "::"
                } else {
                    "."
                };
                Some(
                    h.path
                        .iter()
                        .map(|s| s.name.name.as_str())
                        .collect::<Vec<_>>()
                        .join(sep),
                )
            }
            ExprKind::MemberAccess { expr, member } => {
                let base = callee_key(expr, None, locals, elab)?;
                let sep = if is_package(&base) {
                    "::"
                } else {
                    "."
                };
                Some(format!("{base}{sep}{}", member.name))
            }
            _ => None,
        }
    }
    fn check_call(
        callee_name: &str,
        args: &[Expression],
        elab: &ElaboratedModule,
    ) -> Result<(), String> {
        let formals: Option<&[crate::ast::decl::FunctionPort]> =
            if let Some(t) = elab.tasks.get(callee_name) {
                Some(t.ports.as_slice())
            } else if let Some(f) = elab.functions.get(callee_name) {
                Some(f.ports.as_slice())
            } else {
                None
            };
        if let Some(ports) = formals {
            // §13.5.3: actuals may be named (`.r(x)`) or omitted (`f(a, , c)`),
            // so map each actual to ITS formal instead of assuming pure
            // positional order — the old positional check flagged the wrong
            // formal (or a NamedArg wrapper) as a non-lvalue ref argument.
            let mut pos = 0usize;
            for a in args {
                let (formal, actual): (Option<&crate::ast::decl::FunctionPort>, &Expression) =
                    match &a.kind {
                        ExprKind::NamedArg { name, expr } => {
                            let f = ports.iter().find(|p| p.name.name == name.name);
                            match expr {
                                Some(e) => (f, e.as_ref()),
                                None => continue,
                            }
                        }
                        ExprKind::Empty => {
                            pos += 1;
                            continue;
                        }
                        _ => {
                            let f = ports.get(pos);
                            pos += 1;
                            (f, a)
                        }
                    };
                if let Some(p) = formal {
                    if matches!(p.direction, crate::ast::types::PortDirection::Ref)
                        && !is_lvalue_expr(actual)
                    {
                        return Err(format!(
                            "Argument to `ref` formal '{}' of '{}' must be a variable (IEEE 1800-2017 §13.5.2)",
                            p.name.name, callee_name
                        ));
                    }
                }
            }
        }
        Ok(())
    }
    fn walk_expr(
        e: &Expression,
        elab: &ElaboratedModule,
        package: Option<&str>,
        locals: &HashMap<String, DataType>,
    ) -> Result<(), String> {
        if let ExprKind::Call { func, args } = &e.kind {
            if let Some(key) = callee_key(func, package, locals, elab) {
                check_call(&key, args, elab)?;
            }
            for a in args {
                walk_expr(a, elab, package, locals)?;
            }
            return Ok(());
        }
        Ok(())
    }
    fn walk_stmt(
        s: &Statement,
        elab: &ElaboratedModule,
        package: Option<&str>,
        locals: &HashMap<String, DataType>,
    ) -> Result<(), String> {
        match &s.kind {
            StatementKind::Expr(e) => walk_expr(e, elab, package, locals)?,
            StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
                for s in stmts {
                    walk_stmt(s, elab, package, locals)?;
                }
            }
            StatementKind::If {
                then_stmt,
                else_stmt,
                condition: _,
                ..
            } => {
                walk_stmt(then_stmt, elab, package, locals)?;
                if let Some(e) = else_stmt {
                    walk_stmt(e, elab, package, locals)?;
                }
            }
            StatementKind::For { body, .. }
            | StatementKind::While { body, .. }
            | StatementKind::DoWhile { body, .. }
            | StatementKind::Forever { body }
            | StatementKind::Repeat { body, .. }
            | StatementKind::Foreach { body, .. } => walk_stmt(body, elab, package, locals)?,
            StatementKind::Case { items, .. } => {
                for it in items {
                    walk_stmt(&it.stmt, elab, package, locals)?;
                }
            }
            StatementKind::TimingControl { stmt, .. } => walk_stmt(stmt, elab, package, locals)?,
            _ => {}
        }
        Ok(())
    }
    for ib in &elab.initial_blocks {
        let mut locals = HashMap::default();
        collect_stmt_declared_types(&ib.stmt, &mut locals);
        walk_stmt(&ib.stmt, elab, None, &locals)?;
    }
    for ab in &elab.always_blocks {
        let mut locals = HashMap::default();
        collect_stmt_declared_types(&ab.stmt, &mut locals);
        walk_stmt(&ab.stmt, elab, None, &locals)?;
    }
    for (key, f) in elab.functions.iter() {
        let package = declaring_package(key, f.span, false, elab);
        let mut locals = HashMap::default();
        for p in &f.ports {
            locals.insert(p.name.name.clone(), p.data_type.clone());
        }
        for s in &f.items {
            collect_stmt_declared_types(s, &mut locals);
        }
        for s in &f.items {
            walk_stmt(s, elab, package, &locals)?;
        }
    }
    for (key, t) in &elab.tasks {
        let package = declaring_package(key, t.span, true, elab);
        let mut locals = HashMap::default();
        for p in &t.ports {
            locals.insert(p.name.name.clone(), p.data_type.clone());
        }
        for s in &t.items {
            collect_stmt_declared_types(s, &mut locals);
        }
        for s in &t.items {
            walk_stmt(s, elab, package, &locals)?;
        }
    }
    Ok(())
}

/// LRM §25.4 modport direction enforcement (static check).
///
/// `modport_views: Map<signal_name, Map<member_name, PortDirection>>` is
/// populated when an interface instance signal is bound through a particular
/// modport. The *writing* side may only target members the modport tags as
/// `Output` or `Inout`. Writes to `Input` members violate the contract.
///
/// We catch the common static cases: continuous assigns and procedural
/// blocking/non-blocking assigns whose LHS is `iface_signal.member`. Dynamic
/// paths (passing the modport handle through tasks, virtual interfaces,
/// indexed selects) fall through silently — those need runtime tagging,
/// which is out of scope for this check.
/// LRM §25.4 modport direction enforcement (AST-level walk).
///
/// Two passes:
///   1. Build a map `iface_name -> modport_name -> {input members}` by
///      walking every `Definition::Interface` and collecting each modport's
///      `input`-direction members.
///   2. For every `Definition::Module`, find ports whose data type is a
///      modport-bound interface (`bus_if.slave foo`), then walk the
///      module body looking for assigns to `foo.<member>`. If `<member>`
///      appears in the input-set for that modport, error.
///
/// Dynamic paths (modport handles passed through tasks, virtual interfaces,
/// indexed selects) are out of scope for this check — they'd need runtime
/// tagging. The static walk catches the common direct-write cases.
pub(super) fn validate_modport_writes_at_ast(
    defs: &HashMap<String, Definition>,
) -> Result<(), String> {
    use crate::ast::expr::{ExprKind, Expression};
    use crate::ast::stmt::{Statement, StatementKind};
    use crate::ast::types::{DataType, PortDirection};

    // (1) iface_name -> modport_name -> set of `input` member names.
    let mut input_sets: HashMap<String, HashMap<String, HashSet<String>>> = HashMap::default();
    for def in defs.values() {
        if let Definition::Interface(iface) = def {
            let mut per_modport: HashMap<String, HashSet<String>> = HashMap::default();
            for item in &iface.items {
                if let ModuleItem::ModportDeclaration(md) = item {
                    for mp in &md.items {
                        let mut inputs: HashSet<String> = HashSet::default();
                        for p in &mp.ports {
                            if matches!(p.direction, PortDirection::Input) {
                                inputs.insert(p.name.name.clone());
                            }
                        }
                        per_modport.insert(mp.name.name.clone(), inputs);
                    }
                }
            }
            if !per_modport.is_empty() {
                input_sets.insert(iface.name.name.clone(), per_modport);
            }
        }
    }
    if input_sets.is_empty() {
        return Ok(()); // nothing to check
    }

    // Helper: from a Module's port list, extract `(port_name, input_member_set)`
    // for every port that's a modport-bound interface.
    fn module_modport_ports(
        m: &ModuleDeclaration,
        input_sets: &HashMap<String, HashMap<String, HashSet<String>>>,
    ) -> HashMap<String, HashSet<String>> {
        let mut out: HashMap<String, HashSet<String>> = HashMap::default();
        if let PortList::Ansi(ports) = &m.ports {
            for port in ports {
                if let Some(DataType::Interface {
                    name,
                    modport: Some(mp),
                    ..
                }) = port.data_type.as_ref()
                {
                    if let Some(per_mp) = input_sets.get(&name.name) {
                        if let Some(inputs) = per_mp.get(&mp.name) {
                            out.insert(port.name.name.clone(), inputs.clone());
                        }
                    }
                }
            }
        }
        out
    }

    fn check_lvalue(
        lv: &Expression,
        port_inputs: &HashMap<String, HashSet<String>>,
        mod_name: &str,
        context: &str,
    ) -> Result<(), String> {
        if let ExprKind::MemberAccess { expr, member } = &lv.kind {
            if let ExprKind::Ident(h) = &expr.kind {
                if h.path.len() == 1 {
                    let base = h.path[0].name.name.as_str();
                    if let Some(inputs) = port_inputs.get(base) {
                        if inputs.contains(member.name.as_str()) {
                            return Err(format!(
                                "module '{}' {}: cannot write to modport-input member '{}.{}' (IEEE 1800-2017 §25.4)",
                                mod_name, context, base, member.name
                            ));
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn walk_stmt(
        s: &Statement,
        port_inputs: &HashMap<String, HashSet<String>>,
        mod_name: &str,
    ) -> Result<(), String> {
        match &s.kind {
            StatementKind::BlockingAssign { lvalue, .. }
            | StatementKind::NonblockingAssign { lvalue, .. } => {
                check_lvalue(lvalue, port_inputs, mod_name, "procedural assignment")
            }
            StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
                for s in stmts {
                    walk_stmt(s, port_inputs, mod_name)?;
                }
                Ok(())
            }
            StatementKind::If {
                then_stmt,
                else_stmt,
                ..
            } => {
                walk_stmt(then_stmt, port_inputs, mod_name)?;
                if let Some(e) = else_stmt {
                    walk_stmt(e, port_inputs, mod_name)?;
                }
                Ok(())
            }
            StatementKind::Case { items, .. } => {
                for it in items {
                    walk_stmt(&it.stmt, port_inputs, mod_name)?;
                }
                Ok(())
            }
            StatementKind::For { body, .. }
            | StatementKind::While { body, .. }
            | StatementKind::DoWhile { body, .. }
            | StatementKind::Repeat { body, .. }
            | StatementKind::Forever { body, .. }
            | StatementKind::Foreach { body, .. } => walk_stmt(body, port_inputs, mod_name),
            StatementKind::TimingControl { stmt, .. } => walk_stmt(stmt, port_inputs, mod_name),
            _ => Ok(()),
        }
    }

    // (2) Walk every module Definition.
    for def in defs.values() {
        if let Definition::Module(m) = def {
            let port_inputs = module_modport_ports(m, &input_sets);
            if port_inputs.is_empty() {
                continue;
            }
            for item in &m.items {
                match item {
                    ModuleItem::ContinuousAssign(ca) => {
                        for (lhs, _rhs) in &ca.assignments {
                            check_lvalue(lhs, &port_inputs, &m.name.name, "continuous assign")?;
                        }
                    }
                    ModuleItem::AlwaysConstruct(ac) => {
                        walk_stmt(&ac.stmt, &port_inputs, &m.name.name)?;
                    }
                    ModuleItem::InitialConstruct(ic) => {
                        walk_stmt(&ic.stmt, &port_inputs, &m.name.name)?;
                    }
                    _ => {}
                }
            }
        }
    }
    Ok(())
}

#[allow(dead_code)]
fn validate_modport_writes(elab: &ElaboratedModule) -> Result<(), String> {
    // NOTE — kept for future per-module hook. Not currently invoked: the
    // ElaboratedModule visible at the validator call site is the *top* module
    // and its modport_views map is empty (per-instance modport binds happen
    // during sub-module elaboration and are not aggregated back up). To
    // actually enforce this, validate_modport_writes needs to run inside
    // `elaborate_module_with_defs` for every module that has modport ports,
    // not once on the top elab. That hook is the L-tier follow-up.
    use crate::ast::expr::{ExprKind, Expression};
    use crate::ast::stmt::{Statement, StatementKind};
    use crate::ast::types::PortDirection;

    fn check_lvalue(lv: &Expression, elab: &ElaboratedModule, context: &str) -> Result<(), String> {
        if let ExprKind::MemberAccess { expr, member } = &lv.kind {
            if let ExprKind::Ident(h) = &expr.kind {
                let base = h.path.last().map(|s| s.name.name.as_str()).unwrap_or("");
                if let Some(view) = elab.modport_views.get(base) {
                    if let Some(dir) = view.get(member.name.as_str()) {
                        if matches!(dir, PortDirection::Input) {
                            return Err(format!(
                                "{}: cannot write to modport-input member '{}.{}' (IEEE 1800-2017 §25.4)",
                                context, base, member.name
                            ));
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn walk_stmt(s: &Statement, elab: &ElaboratedModule) -> Result<(), String> {
        match &s.kind {
            StatementKind::BlockingAssign { lvalue, .. }
            | StatementKind::NonblockingAssign { lvalue, .. } => {
                check_lvalue(lvalue, elab, "procedural assignment")
            }
            StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
                for s in stmts {
                    walk_stmt(s, elab)?;
                }
                Ok(())
            }
            StatementKind::If {
                then_stmt,
                else_stmt,
                ..
            } => {
                walk_stmt(then_stmt, elab)?;
                if let Some(e) = else_stmt {
                    walk_stmt(e, elab)?;
                }
                Ok(())
            }
            StatementKind::Case { items, .. } => {
                for it in items {
                    walk_stmt(&it.stmt, elab)?;
                }
                Ok(())
            }
            StatementKind::For { body, .. }
            | StatementKind::While { body, .. }
            | StatementKind::DoWhile { body, .. }
            | StatementKind::Repeat { body, .. }
            | StatementKind::Forever { body, .. }
            | StatementKind::Foreach { body, .. } => walk_stmt(body, elab),
            StatementKind::TimingControl { stmt, .. } => walk_stmt(stmt, elab),
            _ => Ok(()),
        }
    }

    for ca in &elab.continuous_assigns {
        check_lvalue(&ca.lhs, elab, "continuous assign")?;
    }
    for ab in &elab.always_blocks {
        walk_stmt(&ab.stmt, elab)?;
    }
    for ib in &elab.initial_blocks {
        walk_stmt(&ib.stmt, elab)?;
    }
    Ok(())
}

/// IEEE 1800-2017 §9.2.2: legality of `always_comb` / `always_latch` /
/// `always_ff` bodies, and §9.2.2.1 the "an always process must advance
/// simulation time" (no zero-delay infinite loop) rule for a plain `always`.
///
///  * §9.2.2.2 always_comb / §9.2.2.3 always_latch: the body may contain no
///    blocking delay control (`#…`), no event control (`@…`), and no `wait`
///    statement — the sensitivity list is inferred, not written.
///  * §9.2.2.3 always_latch: the inferred sensitivity list must be non-empty
///    (a latch with no inputs has "no event control").
///  * §9.2.2.4 always_ff: the first statement must be a single event control;
///    no further event/delay/wait controls may appear in the body.
///  * §9.2.2.1 plain always: the process must be guaranteed to advance
///    simulation time on every iteration, else it is a zero-delay livelock
///    (a reference simulator: "always process does not have any delay").
/// IEEE 1800-2017 §11.5.1: the bounds of a constant part-select `[l:r]`
/// must be constant expressions; only the indexed forms (`+:` / `-:`) take
/// a variable base (their WIDTH must still be constant). Every engine used
/// to evaluate such a bound at run time from the variable's current value.
pub(super) fn validate_constant_part_select_bounds(elab: &ElaboratedModule) -> Result<(), String> {
    use crate::ast::expr::{ExprKind, Expression, RangeKind};
    use crate::ast::stmt::{Statement, StatementKind};

    fn bound_is_const(e: &Expression, elab: &ElaboratedModule) -> bool {
        const_eval_i64_with_params(e, Some(&elab.parameters)).is_some()
    }
    /// The rule applies to a PACKED vector only. A queue, dynamic, unpacked
    /// or associative array, and a string, take variable slice bounds
    /// (§7.10.4, §7.5.2, §6.16), and a base that is not a plain identifier
    /// (an element or a member) has no type here to decide by, so it is
    /// left alone.
    fn packed_base(expr: &Expression, elab: &ElaboratedModule) -> bool {
        let ExprKind::Ident(h) = &expr.kind else {
            return false;
        };
        if h.path.len() != 1 || !h.path[0].selects.is_empty() {
            return false;
        }
        let n = h.path[0].name.name.as_str();
        !(elab.queue_vars.contains(n)
            || elab.dynamic_arrays.contains(n)
            || elab.arrays.contains_key(n)
            || elab.arrays_2d.contains_key(n)
            || elab.arrays_nd.contains_key(n)
            || elab.associative_arrays.contains_key(n)
            || elab.string_signals.contains(n))
            && elab.signals.contains_key(n)
    }
    fn walk_expr(e: &Expression, elab: &ElaboratedModule) -> Result<(), String> {
        match &e.kind {
            ExprKind::RangeSelect {
                expr,
                kind,
                left,
                right,
            } => {
                walk_expr(expr, elab)?;
                walk_expr(left, elab)?;
                walk_expr(right, elab)?;
                if !packed_base(expr, elab) {
                    return Ok(());
                }
                match kind {
                    RangeKind::Constant => {
                        if !bound_is_const(left, elab) || !bound_is_const(right, elab) {
                            return Err(span_error(
                                elab,
                                e.span,
                                "the bounds of a part-select `[l:r]` must be constant \
                                 expressions; use `[base +: width]` or `[base -: width]` for a \
                                 variable base (IEEE 1800-2017 §11.5.1)",
                            ));
                        }
                    }
                    RangeKind::IndexedUp | RangeKind::IndexedDown => {
                        if !bound_is_const(right, elab) {
                            return Err(span_error(
                                elab,
                                e.span,
                                "the width of an indexed part-select must be a constant \
                                 expression (IEEE 1800-2017 §11.5.1)",
                            ));
                        }
                    }
                }
                Ok(())
            }
            ExprKind::Unary { operand, .. } => walk_expr(operand, elab),
            ExprKind::Binary { left, right, .. } => {
                walk_expr(left, elab)?;
                walk_expr(right, elab)
            }
            ExprKind::Conditional {
                condition,
                then_expr,
                else_expr,
            } => {
                walk_expr(condition, elab)?;
                walk_expr(then_expr, elab)?;
                walk_expr(else_expr, elab)
            }
            ExprKind::Concatenation(v) => v.iter().try_for_each(|x| walk_expr(x, elab)),
            ExprKind::Replication { count, exprs } => {
                walk_expr(count, elab)?;
                exprs.iter().try_for_each(|x| walk_expr(x, elab))
            }
            ExprKind::Call { func, args } => {
                walk_expr(func, elab)?;
                args.iter().try_for_each(|x| walk_expr(x, elab))
            }
            ExprKind::SystemCall { args, .. } => args.iter().try_for_each(|x| walk_expr(x, elab)),
            ExprKind::Inside { expr, ranges } => {
                walk_expr(expr, elab)?;
                ranges.iter().try_for_each(|x| walk_expr(x, elab))
            }
            ExprKind::MemberAccess { expr, .. } => walk_expr(expr, elab),
            ExprKind::Index { expr, index } => {
                walk_expr(expr, elab)?;
                walk_expr(index, elab)
            }
            ExprKind::Range(a, b) => {
                walk_expr(a, elab)?;
                walk_expr(b, elab)
            }
            ExprKind::Paren(x) => walk_expr(x, elab),
            _ => Ok(()),
        }
    }
    fn walk_stmt(st: &Statement, elab: &ElaboratedModule) -> Result<(), String> {
        match &st.kind {
            StatementKind::BlockingAssign { lvalue, rvalue }
            | StatementKind::NonblockingAssign { lvalue, rvalue, .. } => {
                walk_expr(lvalue, elab)?;
                walk_expr(rvalue, elab)
            }
            StatementKind::Expr(e) => walk_expr(e, elab),
            StatementKind::If {
                condition,
                then_stmt,
                else_stmt,
                ..
            } => {
                walk_expr(condition, elab)?;
                walk_stmt(then_stmt, elab)?;
                if let Some(e) = else_stmt {
                    walk_stmt(e, elab)?;
                }
                Ok(())
            }
            StatementKind::Case { expr, items, .. } => {
                walk_expr(expr, elab)?;
                for it in items {
                    it.patterns.iter().try_for_each(|x| walk_expr(x, elab))?;
                    walk_stmt(&it.stmt, elab)?;
                }
                Ok(())
            }
            StatementKind::For {
                condition,
                step,
                body,
                ..
            } => {
                if let Some(c) = condition {
                    walk_expr(c, elab)?;
                }
                step.iter().try_for_each(|x| walk_expr(x, elab))?;
                walk_stmt(body, elab)
            }
            StatementKind::Foreach { array, body, .. } => {
                walk_expr(array, elab)?;
                walk_stmt(body, elab)
            }
            StatementKind::While { condition, body }
            | StatementKind::DoWhile { body, condition } => {
                walk_expr(condition, elab)?;
                walk_stmt(body, elab)
            }
            StatementKind::Repeat { count, body } => {
                walk_expr(count, elab)?;
                walk_stmt(body, elab)
            }
            StatementKind::Forever { body } | StatementKind::ForeverTail { body } => {
                walk_stmt(body, elab)
            }
            StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
                stmts.iter().try_for_each(|x| walk_stmt(x, elab))
            }
            StatementKind::TimingControl { stmt, .. } => walk_stmt(stmt, elab),
            _ => Ok(()),
        }
    }
    for ca in &elab.continuous_assigns {
        walk_expr(&ca.lhs, elab)?;
        walk_expr(&ca.rhs, elab)?;
    }
    for ab in &elab.always_blocks {
        walk_stmt(&ab.stmt, elab)?;
    }
    for pa in &elab.pending_always {
        walk_stmt(&pa.source, elab)?;
    }
    for ib in elab.initial_blocks.iter().chain(elab.final_blocks.iter()) {
        walk_stmt(&ib.stmt, elab)?;
    }
    Ok(())
}

pub(super) fn validate_always_ff_event_controls(elab: &ElaboratedModule) -> Result<(), String> {
    use crate::ast::decl::AlwaysKind;
    use crate::ast::expr::{ExprKind, NumberLiteral};
    use crate::ast::stmt::{JoinType, Statement, StatementKind, TimingControl};

    fn kw(k: AlwaysKind) -> &'static str {
        match k {
            AlwaysKind::AlwaysComb => "always_comb",
            AlwaysKind::AlwaysLatch => "always_latch",
            AlwaysKind::AlwaysFf => "always_ff",
            AlwaysKind::Always => "always",
        }
    }

    // §9.2.2.2/§9.2.2.3/§9.2.2.4: no delay/event/wait control anywhere in the
    // body (for always_ff this is called on the body AFTER its single leading
    // event control has been peeled off).
    fn walk_forbid(s: &Statement, k: AlwaysKind) -> Result<(), String> {
        match &s.kind {
            StatementKind::TimingControl { control, .. } => match control {
                TimingControl::Delay(_) => Err(format!(
                    "error: a blocking delay is not allowed in an {} process \
                     (IEEE 1800-2017 §9.2.2)",
                    kw(k)
                )),
                TimingControl::Event(_) => Err(format!(
                    "error: an event control is not allowed in an {} process \
                     (IEEE 1800-2017 §9.2.2)",
                    kw(k)
                )),
            },
            StatementKind::Wait { .. } | StatementKind::WaitFork => Err(format!(
                "error: a wait statement is not allowed in an {} process \
                 (IEEE 1800-2017 §9.2.2)",
                kw(k)
            )),
            StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
                for st in stmts {
                    walk_forbid(st, k)?;
                }
                Ok(())
            }
            StatementKind::If {
                then_stmt,
                else_stmt,
                ..
            } => {
                walk_forbid(then_stmt, k)?;
                if let Some(e) = else_stmt {
                    walk_forbid(e, k)?;
                }
                Ok(())
            }
            StatementKind::Case { items, .. } => {
                for it in items {
                    walk_forbid(&it.stmt, k)?;
                }
                Ok(())
            }
            StatementKind::For { body, .. }
            | StatementKind::While { body, .. }
            | StatementKind::DoWhile { body, .. }
            | StatementKind::Forever { body }
            | StatementKind::Repeat { body, .. }
            | StatementKind::Foreach { body, .. } => walk_forbid(body, k),
            _ => Ok(()),
        }
    }

    // §9.2.2.3: does the body read at least one identifier (its inferred
    // sensitivity)? A latch with an empty sensitivity list is illegal.
    fn expr_reads_ident(e: &crate::ast::expr::Expression) -> bool {
        match &e.kind {
            ExprKind::Ident(_) => true,
            ExprKind::Paren(x) | ExprKind::Unary { operand: x, .. } => expr_reads_ident(x),
            ExprKind::Binary { left, right, .. } => {
                expr_reads_ident(left) || expr_reads_ident(right)
            }
            ExprKind::Conditional {
                condition,
                then_expr,
                else_expr,
            } => {
                expr_reads_ident(condition)
                    || expr_reads_ident(then_expr)
                    || expr_reads_ident(else_expr)
            }
            ExprKind::Index { expr, index } => expr_reads_ident(expr) || expr_reads_ident(index),
            ExprKind::RangeSelect {
                expr, left, right, ..
            } => expr_reads_ident(expr) || expr_reads_ident(left) || expr_reads_ident(right),
            ExprKind::Concatenation(xs) => xs.iter().any(expr_reads_ident),
            ExprKind::Replication { count, exprs } => {
                expr_reads_ident(count) || exprs.iter().any(expr_reads_ident)
            }
            ExprKind::Call { func, args } => {
                // A function call's return generally depends on its arguments
                // AND on whatever module vars it reads — either way the latch
                // has a live sensitivity. Treat any call as a read.
                expr_reads_ident(func) || args.iter().any(expr_reads_ident) || true
            }
            ExprKind::MemberAccess { expr, .. } => expr_reads_ident(expr),
            _ => false,
        }
    }
    fn stmt_reads_ident(s: &Statement) -> bool {
        match &s.kind {
            StatementKind::BlockingAssign { rvalue, .. }
            | StatementKind::NonblockingAssign { rvalue, .. } => expr_reads_ident(rvalue),
            StatementKind::If {
                condition,
                then_stmt,
                else_stmt,
                ..
            } => {
                expr_reads_ident(condition)
                    || stmt_reads_ident(then_stmt)
                    || else_stmt.as_ref().is_some_and(|e| stmt_reads_ident(e))
            }
            StatementKind::Case { expr, items, .. } => {
                expr_reads_ident(expr) || items.iter().any(|it| stmt_reads_ident(&it.stmt))
            }
            StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
                stmts.iter().any(stmt_reads_ident)
            }
            StatementKind::For { body, .. }
            | StatementKind::While { body, .. }
            | StatementKind::DoWhile { body, .. }
            | StatementKind::Forever { body }
            | StatementKind::Repeat { body, .. }
            | StatementKind::Foreach { body, .. } => stmt_reads_ident(body),
            StatementKind::Expr(e) => expr_reads_ident(e),
            _ => false,
        }
    }

    // §9.2.2.1: CAN this statement block the always thread (advance simulation
    // time or wait on an event) before it loops? Deliberately OPTIMISTIC —
    // returns true whenever we cannot PROVE the statement completes in zero
    // time. Two things force optimism: (1) intra-assignment timing
    // (`x = #10 y`, `q <= #1 d`) is discarded by the parser, so an assignment
    // may carry a hidden delay; (2) an `always task();` may block inside the
    // (un-inlined) task body. We therefore reject only the structural cases we
    // can prove are zero-delay livelocks — chiefly `fork … join_none` and a
    // `join_any`/`join` whose parent unblocks at time 0 — which is exactly
    // what a reference simulator flags as "always process does not have any delay".
    fn is_literal_zero(e: &crate::ast::expr::Expression) -> bool {
        match &e.kind {
            ExprKind::Paren(x) => is_literal_zero(x),
            ExprKind::Number(NumberLiteral::Integer { value, .. }) => {
                value.chars().filter(|c| *c != '_').all(|c| c == '0')
            }
            ExprKind::Number(NumberLiteral::Real(v)) | ExprKind::Number(NumberLiteral::Time(v)) => {
                *v == 0.0
            }
            _ => false,
        }
    }
    fn can_block(s: &Statement) -> bool {
        match &s.kind {
            StatementKind::TimingControl { control, .. } => match control {
                // `#0` is a zero delay (same time slot) — does not advance.
                TimingControl::Delay(e) => !is_literal_zero(e),
                TimingControl::Event(_) => true,
            },
            StatementKind::Wait { .. } | StatementKind::WaitFork => true,
            StatementKind::SeqBlock { stmts, .. } => stmts.iter().any(can_block),
            StatementKind::ParBlock {
                join_type, stmts, ..
            } => match join_type {
                // join: parent unblocks when the LAST child finishes.
                JoinType::Join => stmts.iter().any(can_block),
                // join_any: parent unblocks when the FIRST child finishes, so
                // every child must consume time for the parent to advance.
                JoinType::JoinAny => !stmts.is_empty() && stmts.iter().all(can_block),
                // join_none: parent never blocks on the children.
                JoinType::JoinNone => false,
            },
            StatementKind::Forever { body }
            | StatementKind::DoWhile { body, .. }
            | StatementKind::Repeat { body, .. }
            | StatementKind::While { body, .. }
            | StatementKind::For { body, .. }
            | StatementKind::Foreach { body, .. } => can_block(body),
            StatementKind::If {
                then_stmt,
                else_stmt,
                ..
            } => can_block(then_stmt) || else_stmt.as_ref().is_some_and(|e| can_block(e)),
            StatementKind::Case { items, .. } => items.iter().any(|it| can_block(&it.stmt)),
            // Assignments may carry (parser-discarded) intra-assignment timing;
            // an expression statement may be a time-consuming task call.
            StatementKind::BlockingAssign { .. }
            | StatementKind::NonblockingAssign { .. }
            | StatementKind::Expr(_) => true,
            _ => false,
        }
    }

    // Only fork-based bodies are flagged as no-delay livelocks here: a plain
    // `always` whose non-advancement comes from a bare zero-delay loop
    // (`always begin #0; end`, `always assign x = y;`) is left to the
    // runtime's zero-delay livelock guard, matching prior behavior. The
    // fork/join_none / min-zero-join_any cases (always4A / always4B) cannot be
    // caught at runtime the same way (they spawn children), so we reject them
    // at elaboration exactly as a reference simulator does.
    fn contains_fork(s: &Statement) -> bool {
        match &s.kind {
            StatementKind::ParBlock { .. } => true,
            StatementKind::SeqBlock { stmts, .. } => stmts.iter().any(contains_fork),
            StatementKind::TimingControl { stmt, .. } => contains_fork(stmt),
            StatementKind::If {
                then_stmt,
                else_stmt,
                ..
            } => contains_fork(then_stmt) || else_stmt.as_ref().is_some_and(|e| contains_fork(e)),
            StatementKind::Case { items, .. } => items.iter().any(|it| contains_fork(&it.stmt)),
            StatementKind::For { body, .. }
            | StatementKind::While { body, .. }
            | StatementKind::DoWhile { body, .. }
            | StatementKind::Forever { body }
            | StatementKind::Repeat { body, .. }
            | StatementKind::Foreach { body, .. }
            | StatementKind::Wait { stmt: body, .. } => contains_fork(body),
            _ => false,
        }
    }

    for ab in &elab.always_blocks {
        match ab.kind {
            AlwaysKind::AlwaysFf => {
                // §9.2.2.4: exactly ONE event control, and it must be the first
                // statement. Two legal spellings:
                //   (1) `always_ff @(posedge clk) begin … end`
                //         → the outer statement IS the event control; every
                //           statement in its body must be free of timing.
                //   (2) `always_ff begin @(posedge clk) …; … end`
                //         → the FIRST statement inside the block is the event
                //           control; the remaining statements must be free of
                //           timing.
                // Any further `@…`/`#…`/`wait` in the body is illegal.
                match &ab.stmt.kind {
                    StatementKind::TimingControl {
                        control: TimingControl::Event(_),
                        stmt,
                    } => {
                        walk_forbid(stmt, AlwaysKind::AlwaysFf)?;
                    }
                    StatementKind::SeqBlock { stmts, .. }
                        if matches!(
                            stmts.first().map(|s| &s.kind),
                            Some(StatementKind::TimingControl {
                                control: TimingControl::Event(_),
                                ..
                            })
                        ) =>
                    {
                        for (i, st) in stmts.iter().enumerate() {
                            if i == 0 {
                                // the required leading event control — peel it,
                                // its inner statement is the real body head.
                                if let StatementKind::TimingControl { stmt, .. } = &st.kind {
                                    walk_forbid(stmt, AlwaysKind::AlwaysFf)?;
                                }
                            } else {
                                walk_forbid(st, AlwaysKind::AlwaysFf)?;
                            }
                        }
                    }
                    _ => {
                        return Err(
                            "error: the first statement of an always_ff process must be an \
                             event control statement (IEEE 1800-2017 §9.2.2.4)"
                                .into(),
                        );
                    }
                }
            }
            AlwaysKind::AlwaysComb => {
                walk_forbid(&ab.stmt, AlwaysKind::AlwaysComb)?;
            }
            AlwaysKind::AlwaysLatch => {
                walk_forbid(&ab.stmt, AlwaysKind::AlwaysLatch)?;
                if !stmt_reads_ident(&ab.stmt) {
                    return Err(
                        "error: always_latch process has no event control — its inferred \
                         sensitivity list is empty (IEEE 1800-2017 §9.2.2.3)"
                            .into(),
                    );
                }
            }
            AlwaysKind::Always => {
                if !can_block(&ab.stmt) && contains_fork(&ab.stmt) {
                    return Err(
                        "error: always process does not have any delay; a zero-delay infinite \
                         loop will occur (IEEE 1800-2017 §9.2.2.1)"
                            .into(),
                    );
                }
            }
        }
    }
    Ok(())
}

/// IEEE 1800-2023 §8.20.5: enforcement of the `:final` specifier.
///
/// Two checks:
///   1. `class :final X` — no class may declare `extends X`.
///   2. `function :final foo` — no derived class may declare a method
///      named `foo` anywhere in its ancestor chain.
pub(super) fn validate_final_method_overrides(elab: &ElaboratedModule) -> Result<(), String> {
    for (cname, cdef) in &elab.classes {
        // Direct-parent class-level :final check.
        if let Some(parent_name) = &cdef.extends {
            if let Some(parent) = elab.classes.get(parent_name) {
                if parent.is_final {
                    return Err(format!(
                        "Class '{}' extends `final` class '{}' (IEEE 1800-2023 §8.20.5)",
                        cname, parent_name
                    ));
                }
            }
        }
        // Walk every strict ancestor for `:final` methods.
        let mut cur = cdef.extends.clone();
        while let Some(parent_name) = cur {
            let Some(parent) = elab.classes.get(&parent_name) else {
                break;
            };
            for (mname, pmethod) in parent.methods.iter() {
                if method_is_final(pmethod) && cdef.methods.contains_key(mname) {
                    return Err(format!(
                        "Class '{}' overrides `:final` method '{}' from ancestor '{}' (IEEE 1800-2023 §8.20.5)",
                        cname, mname, parent_name
                    ));
                }
            }
            cur = parent.extends.clone();
        }
    }
    Ok(())
}
