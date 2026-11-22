use super::*;

pub(super) fn resolve_interface_modport_view(
    interface_name: &str,
    modport_name: &str,
    all_defs: Option<&HashMap<String, Definition>>,
) -> Option<HashMap<String, PortDirection>> {
    let defs = all_defs?;
    let idef = match defs.get(interface_name) {
        Some(Definition::Interface(i)) => i,
        _ => return None,
    };
    for item in &idef.items {
        if let ModuleItem::ModportDeclaration(md) = item {
            for mp in &md.items {
                if mp.name.name == modport_name {
                    let mut dirs = HashMap::default();
                    for p in &mp.ports {
                        dirs.insert(p.name.name.clone(), p.direction);
                    }
                    return Some(dirs);
                }
            }
        }
    }
    None
}

fn validate_class_constraint_expr(
    expr: &Expression,
    names: &ConstraintNames,
    locals: &[&str],
) -> Result<(), String> {
    match &expr.kind {
        ExprKind::Ident(hier) if hier.path.len() == 1 => {
            let n = &hier.path[0].name.name;
            if n != "this" && n != "super" && n != "new" && !names.contains(n, locals) {
                return Err(format!("Undeclared identifier '{}' in class constraint", n));
            }
        }
        ExprKind::Unary { operand, .. } => validate_class_constraint_expr(operand, names, locals)?,
        ExprKind::Binary { left, right, .. } => {
            validate_class_constraint_expr(left, names, locals)?;
            validate_class_constraint_expr(right, names, locals)?;
        }
        ExprKind::Conditional {
            condition,
            then_expr,
            else_expr,
        } => {
            validate_class_constraint_expr(condition, names, locals)?;
            validate_class_constraint_expr(then_expr, names, locals)?;
            validate_class_constraint_expr(else_expr, names, locals)?;
        }
        ExprKind::Concatenation(parts) => {
            for p in parts {
                validate_class_constraint_expr(p, names, locals)?;
            }
        }
        ExprKind::Replication { count, exprs } => {
            validate_class_constraint_expr(count, names, locals)?;
            for e in exprs {
                validate_class_constraint_expr(e, names, locals)?;
            }
        }
        ExprKind::Index { expr, index } => {
            validate_class_constraint_expr(expr, names, locals)?;
            validate_class_constraint_expr(index, names, locals)?;
        }
        ExprKind::RangeSelect {
            expr, left, right, ..
        } => {
            validate_class_constraint_expr(expr, names, locals)?;
            validate_class_constraint_expr(left, names, locals)?;
            validate_class_constraint_expr(right, names, locals)?;
        }
        ExprKind::Inside { expr, ranges } => {
            validate_class_constraint_expr(expr, names, locals)?;
            for r in ranges {
                validate_class_constraint_expr(r, names, locals)?;
            }
        }
        ExprKind::Range(lo, hi) => {
            validate_class_constraint_expr(lo, names, locals)?;
            validate_class_constraint_expr(hi, names, locals)?;
        }
        ExprKind::Paren(inner) => validate_class_constraint_expr(inner, names, locals)?,
        ExprKind::Call { func: _, args } => {
            // Don't validate the callee identifier: it resolves to a function/method
            // (including class methods, package functions, built-ins) that may not be
            // in the property-name allowed set.
            for a in args {
                validate_class_constraint_expr(a, names, locals)?;
            }
        }
        ExprKind::SystemCall { args, .. } => {
            for a in args {
                validate_class_constraint_expr(a, names, locals)?;
            }
        }
        ExprKind::MemberAccess { expr, .. } => validate_class_constraint_expr(expr, names, locals)?,
        _ => {}
    }
    Ok(())
}

fn validate_constraint_item_names(
    item: &ConstraintItem,
    names: &ConstraintNames,
    locals: &[&str],
) -> Result<(), String> {
    match item {
        ConstraintItem::Expr(expr) => validate_class_constraint_expr(expr, names, locals)?,
        ConstraintItem::Inside { expr, range, .. } => {
            validate_class_constraint_expr(expr, names, locals)?;
            for r in range {
                match r {
                    ConstraintRange::Value(e) => validate_class_constraint_expr(e, names, locals)?,
                    ConstraintRange::Range { lo, hi } => {
                        validate_class_constraint_expr(lo, names, locals)?;
                        validate_class_constraint_expr(hi, names, locals)?;
                    }
                }
            }
        }
        ConstraintItem::Implication {
            condition,
            constraint,
            ..
        } => {
            validate_class_constraint_expr(condition, names, locals)?;
            validate_constraint_item_names(constraint, names, locals)?;
        }
        ConstraintItem::IfElse {
            condition,
            then_item,
            else_item,
            ..
        } => {
            validate_class_constraint_expr(condition, names, locals)?;
            validate_constraint_item_names(then_item, names, locals)?;
            if let Some(ei) = else_item {
                validate_constraint_item_names(ei, names, locals)?;
            }
        }
        ConstraintItem::Foreach {
            array, vars, item, ..
        } => {
            validate_class_constraint_expr(array, names, locals)?;
            // §18.5.8.1: the loop variables are a scope of their own over
            // the enclosing one, not a copy of every name.
            let inner: Vec<&str> = locals
                .iter()
                .copied()
                .chain(vars.iter().flatten().map(|id| id.name.as_str()))
                .collect();
            validate_constraint_item_names(item, names, &inner)?;
        }
        ConstraintItem::Soft(inner) => validate_constraint_item_names(inner, names, locals)?,
        ConstraintItem::Unique { exprs, .. } => {
            for e in exprs {
                validate_class_constraint_expr(e, names, locals)?;
            }
        }
        ConstraintItem::Block(items) => {
            for it in items {
                validate_constraint_item_names(it, names, locals)?;
            }
        }
        ConstraintItem::Solve { before, after, .. } => {
            for id in before {
                if !names.contains(&id.name, locals) {
                    return Err(format!(
                        "Undeclared identifier '{}' in class constraint",
                        id.name
                    ));
                }
            }
            for id in after {
                if !names.contains(&id.name, locals) {
                    return Err(format!(
                        "Undeclared identifier '{}' in class constraint",
                        id.name
                    ));
                }
            }
        }
    }
    Ok(())
}

fn collect_class_member_names(
    c: &ClassDeclaration,
    all_defs: Option<&HashMap<String, Definition>>,
    body_classes: &[&ClassDeclaration],
    allowed: &mut HashSet<String>,
    seen: &mut HashSet<String>,
) {
    if !seen.insert(c.name.name.clone()) {
        return;
    }
    for item in &c.items {
        match item {
            ClassItem::Property(p) => {
                for d in &p.declarators {
                    allowed.insert(d.name.name.clone());
                }
            }
            ClassItem::Parameter(pd) => match &pd.kind {
                ParameterKind::Data { assignments, .. } => {
                    for a in assignments {
                        allowed.insert(a.name.name.clone());
                    }
                }
                ParameterKind::Type { assignments } => {
                    for a in assignments {
                        allowed.insert(a.name.name.clone());
                    }
                }
            },
            ClassItem::Method(m) => {
                let name = match &m.kind {
                    ClassMethodKind::Function(f) => &f.name.name.name,
                    ClassMethodKind::Task(t) => &t.name.name.name,
                    ClassMethodKind::PureVirtual(f) => &f.name.name.name,
                    ClassMethodKind::Extern(f) => &f.name.name.name,
                };
                allowed.insert(name.clone());
            }
            ClassItem::Typedef(td) => {
                allowed.insert(td.name.name.clone());
                if let DataType::Enum(et) = &td.data_type {
                    for m in &et.members {
                        allowed.insert(m.name.name.clone());
                    }
                }
            }
            _ => {}
        }
    }
    for p in &c.params {
        match &p.kind {
            ParameterKind::Data { assignments, .. } => {
                for a in assignments {
                    allowed.insert(a.name.name.clone());
                }
            }
            ParameterKind::Type { assignments } => {
                for a in assignments {
                    allowed.insert(a.name.name.clone());
                }
            }
        }
    }
    if let Some(ext) = &c.extends
        && let Some(defs) = all_defs
    {
        // §8.16/§26.3: the base of a class declared in a MODULE body (or
        // another package) may live INSIDE an imported package
        // (`mypacket extends packet` where `packet` is `packet_pkg`'s
        // class) rather than as a top-level Class definition. Packages
        // are kept whole in `all_defs` (Definition::Package), so a bare
        // `defs.get(base)` lookup misses package members and an inherited
        // property reference in a derived constraint is wrongly rejected
        // as undeclared. Fall back to searching every package's classes.
        let parent = body_classes
            .iter()
            .copied()
            .find(|p| p.name.name == ext.name.name)
            .or_else(|| match defs.get(&ext.name.name) {
                Some(Definition::Class(p)) => Some(p),
                Some(Definition::Package(_)) | None => {
                    find_base_class_in_packages(defs, &ext.name.name)
                }
                _ => None,
            });
        if let Some(parent) = parent {
            collect_class_member_names(parent, all_defs, body_classes, allowed, seen);
        }
    }
}

/// Search every package in `defs` for a class named `name`, used to resolve
/// a bare base-class name over which a module/package class `extends` when
/// the base lives inside an imported package (not as a top-level Class def).
fn find_base_class_in_packages<'a>(
    defs: &'a HashMap<String, Definition<'a>>,
    name: &str,
) -> Option<&'a ClassDeclaration> {
    for def in defs.values() {
        if let Definition::Package(pkg) = def {
            for item in &pkg.items {
                if let crate::ast::decl::PackageItem::Class(c) = item {
                    if c.name.name == name {
                        return Some(c);
                    }
                }
            }
        }
    }
    None
}

/// Add the enum constant names introduced by an enum typedef to `allowed`.
fn collect_enum_member_names(td: &TypedefDeclaration, allowed: &mut HashSet<String>) {
    if let DataType::Enum(et) = &td.data_type {
        for m in &et.members {
            allowed.insert(m.name.name.clone());
        }
    }
}

/// Collect identifier names that are legal to reference from any class
/// constraint regardless of class membership: package- and top-level enum
/// constants, class names, parameters/localparams, and `const` data declarations.
/// Without these, a constraint such as `reg != ZERO` (where `ZERO` is a package enum
/// literal) is wrongly rejected as an undeclared identifier.
fn collect_global_constraint_names(
    all_defs: &HashMap<String, Definition>,
    allowed: &mut HashSet<String>,
) {
    for def in all_defs.values() {
        // Package and class names are legal roots of scoped constraint
        // references (`pkg::CONST`, `ClassName::STATIC`).
        allowed.insert(def.name().to_string());
        match def {
            Definition::Typedef(td) => collect_enum_member_names(td, allowed),
            Definition::Package(p) => {
                for item in &p.items {
                    match item {
                        // §8.23 / §18.3 / §26.3: a package class is a legal
                        // root of a scoped reference (`codes::REQUEST`), just
                        // like a class recorded as a top-level definition.
                        crate::ast::decl::PackageItem::Class(c) => {
                            allowed.insert(c.name.name.clone());
                        }
                        crate::ast::decl::PackageItem::Typedef(td) => {
                            allowed.insert(td.name.name.clone());
                            collect_enum_member_names(td, allowed);
                        }
                        crate::ast::decl::PackageItem::Parameter(pd) => {
                            if let ParameterKind::Data { assignments, .. } = &pd.kind {
                                for a in assignments {
                                    allowed.insert(a.name.name.clone());
                                }
                            }
                        }
                        crate::ast::decl::PackageItem::Data(d) => {
                            for decl in &d.declarators {
                                allowed.insert(decl.name.name.clone());
                            }
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        }
    }
}

/// §8.20/§18.5: the definition map a class declared in a MODULE body must be
/// validated against. A nested class's base is a `ModuleItem::ClassDeclaration`
/// of the same body, not a top-level definition, so resolving `extends` through
/// `all_defs` alone never found it: the base's properties never joined the
/// allowed set and a derived constraint referring to an INHERITED property was
/// rejected outright ("Undeclared identifier"), aborting the whole simulation.
/// The identical code at $unit or package scope was accepted, which is what
/// made it look like a constraint bug rather than a scoping one.
pub(super) fn defs_with_local_classes<'a>(
    items: &'a [ModuleItem],
    all_defs: Option<&HashMap<String, Definition<'a>>>,
) -> Option<HashMap<String, Definition<'a>>> {
    let mut local: Vec<(&'a str, &'a crate::ast::decl::ClassDeclaration)> = Vec::new();
    for it in items {
        if let ModuleItem::ClassDeclaration(cd) = it {
            local.push((cd.name.name.as_str(), cd));
        }
    }
    if local.is_empty() {
        return None;
    }
    let mut merged: HashMap<String, Definition<'a>> = all_defs.cloned().unwrap_or_default();
    for (n, cd) in local {
        // §23.9: the nearest lexical class hides an enclosing declaration.
        merged.insert(n.to_string(), Definition::Class(cd));
    }
    Some(merged)
}

pub(super) fn validate_class_constraints(
    c: &ClassDeclaration,
    all_defs: Option<&HashMap<String, Definition>>,
    module_enums: Option<&HashMap<String, Vec<(String, u64)>>>,
    scope: Option<&ElaboratedModule>,
    inst_prefix: Option<&str>,
) -> Result<(), String> {
    validate_class_constraints_in_body(c, all_defs, &[], module_enums, scope, inst_prefix)
}

/// §8.3/§18.5: an instantiated module's own classes participate in base
/// lookup and scoped constraint names. Borrow its prepared body rather than
/// copying the design-wide definition table for each instance.
pub(super) fn validate_class_constraints_in_body(
    c: &ClassDeclaration,
    all_defs: Option<&HashMap<String, Definition>>,
    body_classes: &[&ClassDeclaration],
    module_enums: Option<&HashMap<String, Vec<(String, u64)>>>,
    scope: Option<&ElaboratedModule>,
    inst_prefix: Option<&str>,
) -> Result<(), String> {
    // A class without a constraint has nothing to check (aionhw/xezim#871).
    if !c
        .items
        .iter()
        .any(|it| matches!(it, ClassItem::Constraint(_)))
    {
        return Ok(());
    }
    let mut allowed = HashSet::default();
    let mut seen = HashSet::default();
    collect_class_member_names(c, all_defs, body_classes, &mut allowed, &mut seen);
    allowed.extend(body_classes.iter().map(|c| c.name.name.clone()));
    if let Some(defs) = all_defs {
        collect_global_constraint_names(defs, &mut allowed);
    }
    // Enum typedefs declared at MODULE scope (before the class) are legal
    // constraint references too — `constraint c { m != R0; }` where `reg_t`
    // is a module-local typedef. `collect_global_constraint_names` only sees
    // top-level/package typedefs, so fold in the elaborating module's
    // already-registered enum types and member names.
    if let Some(ems) = module_enums {
        for (tname, members) in ems {
            allowed.insert(tname.clone());
            for (mname, _) in members {
                allowed.insert(mname.clone());
            }
        }
    }
    let names = ConstraintNames {
        own: allowed,
        scope,
        inst_prefix,
        leaves: std::cell::OnceCell::new(),
    };
    for item in &c.items {
        if let ClassItem::Constraint(con) = item {
            for it in &con.items {
                validate_constraint_item_names(it, &names, &[])?;
            }
        }
    }
    Ok(())
}

/// The names a class constraint may read (§18.3): the class's own members,
/// the global names and the enum names in `own`, and the variables and
/// parameters of the scope the class is declared in, looked up in the
/// elaborated design as a constraint reads them. For a class inlined from an
/// instance the instance's signals are registered under prefixed names while
/// the constraint says the bare one, so the leaf spelling of any signal is
/// accepted too. Copying every signal and parameter name of the design
/// inlined so far into a set for every class made elaboration grow with the
/// square of the instances (aionhw/xezim#871); the accepted names are the
/// same.
struct ConstraintNames<'a> {
    own: HashSet<String>,
    scope: Option<&'a ElaboratedModule>,
    /// The prefix of the instance the class was inlined from (`g[0].u.`).
    inst_prefix: Option<&'a str>,
    /// The last segment of every dotted signal key, built on first use.
    leaves: std::cell::OnceCell<HashSet<String>>,
}

impl ConstraintNames<'_> {
    /// Whether `n` is a name a constraint may read; `locals` are the loop
    /// variables of the enclosing `foreach` constraints (§18.5.8.1).
    fn contains(&self, n: &str, locals: &[&str]) -> bool {
        if locals.contains(&n) || self.own.contains(n) {
            return true;
        }
        let Some(elab) = self.scope else {
            return false;
        };
        if elab.signals.contains_key(n) || elab.parameters.contains_key(n) {
            return true;
        }
        // The instance prefix carries its trailing dot (`g[0].u.`).
        if !n.contains('.')
            && self.inst_prefix.is_some_and(|p| {
                let key = if p.ends_with('.') {
                    format!("{p}{n}")
                } else {
                    format!("{p}.{n}")
                };
                elab.signals.contains_key(&key)
            })
        {
            return true;
        }
        self.leaves
            .get_or_init(|| {
                elab.signals
                    .keys()
                    .filter_map(|k| k.rsplit_once('.').map(|(_, leaf)| leaf.to_string()))
                    .collect()
            })
            .contains(n)
    }
}

/// §6.21 (measured): a local variable WITH an initializer inside a
/// STATIC-lifetime task/function must carry an explicit `static` or
/// `automatic` keyword — the reference rejects the implicit form at compile
/// time ("implicitly static"), even under an explicit `task static`, and in
/// package scope too. Measured exemptions: for-header declarations,
/// initial/always block locals, no-init locals, automatic subroutines,
/// `module automatic` scope, and class methods.
/// §8.4/§6.20: `return null` is only meaningful for class-handle (or
/// chandle) return types. A function whose return type is an integral
/// vector — including the IMPLICIT logic return of `function f();` —
/// cannot return null (ivtest br_gh440; the reference rejects it).
pub(super) fn check_non_class_null_return(
    fd: &crate::ast::decl::FunctionDeclaration,
) -> Result<(), String> {
    let integral_ret = matches!(
        fd.return_type,
        DataType::Implicit { .. } | DataType::IntegerVector { .. } | DataType::IntegerAtom { .. }
    );
    if !integral_ret {
        return Ok(());
    }
    fn walk(s: &crate::ast::stmt::Statement, fname: &str) -> Result<(), String> {
        use crate::ast::stmt::StatementKind as SK;
        match &s.kind {
            SK::Return(Some(e)) if matches!(e.kind, ExprKind::Null) => Err(format!(
                "function '{}' has a non-class return type and cannot return null (§8.4)",
                fname
            )),
            SK::SeqBlock { stmts, .. } | SK::ParBlock { stmts, .. } => {
                for st in stmts {
                    walk(st, fname)?;
                }
                Ok(())
            }
            SK::If {
                then_stmt,
                else_stmt,
                ..
            } => {
                walk(then_stmt, fname)?;
                if let Some(e) = else_stmt {
                    walk(e, fname)?;
                }
                Ok(())
            }
            SK::For { body, .. }
            | SK::Foreach { body, .. }
            | SK::While { body, .. }
            | SK::DoWhile { body, .. }
            | SK::Repeat { body, .. }
            | SK::Forever { body, .. } => walk(body, fname),
            SK::Case { items, .. } => {
                for it in items {
                    walk(&it.stmt, fname)?;
                }
                Ok(())
            }
            SK::TimingControl { stmt, .. } => walk(stmt, fname),
            _ => Ok(()),
        }
    }
    for st in &fd.items {
        walk(st, &fd.name.name.name)?;
    }
    Ok(())
}
