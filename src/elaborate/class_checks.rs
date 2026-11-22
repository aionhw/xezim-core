use super::*;

pub(super) fn method_is_final(m: &crate::ast::decl::ClassMethod) -> bool {
    method_specifier(m) == Some(crate::ast::decl::MethodSpecifier::Final)
}

fn method_specifier(
    m: &crate::ast::decl::ClassMethod,
) -> Option<crate::ast::decl::MethodSpecifier> {
    use crate::ast::decl::ClassMethodKind;
    match &m.kind {
        ClassMethodKind::Function(f) => f.specifier,
        ClassMethodKind::Task(t) => t.specifier,
        ClassMethodKind::PureVirtual(f) => f.specifier,
        ClassMethodKind::Extern(f) => f.specifier,
    }
}

/// IEEE 1800-2023 §8.20.5 enforcement for the `:extends` and `:initial`
/// method-override markers (the `:final` rule lives in
/// `validate_final_method_overrides` above).
///
/// - `:extends foo` — `foo` MUST be defined in some ancestor.
/// - `:initial foo` — `foo` must NOT be defined in any ancestor.
///
/// These markers exist precisely to catch refactor-induced silent shadowing
/// or accidental redeclaration; without enforcement they are visual noise.
pub(super) fn validate_method_override_markers(elab: &ElaboratedModule) -> Result<(), String> {
    use crate::ast::decl::MethodSpecifier;
    for (cname, cdef) in &elab.classes {
        for (mname, m) in cdef.methods.iter() {
            let spec = method_specifier(m);
            if !matches!(
                spec,
                Some(MethodSpecifier::Extends) | Some(MethodSpecifier::Initial)
            ) {
                continue;
            }
            // Walk strict ancestors looking for a same-named method.
            let mut found_in_ancestor = false;
            let mut cur = cdef.extends.clone();
            while let Some(parent_name) = cur {
                let Some(parent) = elab.classes.get(&parent_name) else {
                    break;
                };
                if parent.methods.contains_key(mname) {
                    found_in_ancestor = true;
                    break;
                }
                cur = parent.extends.clone();
            }
            match spec {
                Some(MethodSpecifier::Extends) if !found_in_ancestor => {
                    return Err(format!(
                        "Class '{}' method '{}' is marked `:extends` but no ancestor declares it (IEEE 1800-2023 §8.20.5)",
                        cname, mname
                    ));
                }
                Some(MethodSpecifier::Initial) if found_in_ancestor => {
                    return Err(format!(
                        "Class '{}' method '{}' is marked `:initial` but an ancestor already declares it (IEEE 1800-2023 §8.20.5)",
                        cname, mname
                    ));
                }
                _ => {}
            }
        }
    }
    Ok(())
}

fn expr_is_new(expr: &Expression) -> bool {
    match &expr.kind {
        ExprKind::Ident(hier) => hier.path.len() == 1 && hier.path[0].name.name == "new",
        ExprKind::Call { func, .. } => {
            if let ExprKind::Ident(hier) = &func.kind {
                return hier.path.len() == 1 && hier.path[0].name.name == "new";
            }
            false
        }
        _ => false,
    }
}

fn check_new_assignment(
    lvalue: &Expression,
    rvalue: &Expression,
    elab: &ElaboratedModule,
) -> Result<(), String> {
    if !expr_is_new(rvalue) {
        return Ok(());
    }
    let name = match simple_lhs_name(lvalue) {
        Some(n) => n,
        None => return Ok(()),
    };
    let type_name = elab.signals.get(&name).and_then(|s| s.type_name.clone());
    if let Some(tn) = type_name {
        if let Some(cls) = elab.classes.get(&tn) {
            if cls.is_interface {
                return Err(format!("Cannot instantiate interface class '{}'", tn));
            }
            if cls.is_virtual || cls.has_pure_virtual {
                return Err(format!("Cannot instantiate abstract class '{}'", tn));
            }
        }
    }
    Ok(())
}

fn walk_stmt_for_class_new(stmt: &Statement, elab: &ElaboratedModule) -> Result<(), String> {
    match &stmt.kind {
        StatementKind::BlockingAssign { lvalue, rvalue }
        | StatementKind::NonblockingAssign { lvalue, rvalue, .. } => {
            check_new_assignment(lvalue, rvalue, elab)?;
        }
        StatementKind::If {
            then_stmt,
            else_stmt,
            ..
        } => {
            walk_stmt_for_class_new(then_stmt, elab)?;
            if let Some(eb) = else_stmt {
                walk_stmt_for_class_new(eb, elab)?;
            }
        }
        StatementKind::Case { items, .. } => {
            for it in items {
                walk_stmt_for_class_new(&it.stmt, elab)?;
            }
        }
        StatementKind::For { body, .. }
        | StatementKind::Foreach { body, .. }
        | StatementKind::While { body, .. }
        | StatementKind::DoWhile { body, .. }
        | StatementKind::Repeat { body, .. }
        | StatementKind::Forever { body } => walk_stmt_for_class_new(body, elab)?,
        StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
            for s in stmts {
                walk_stmt_for_class_new(s, elab)?;
            }
        }
        StatementKind::TimingControl { stmt, .. } | StatementKind::Wait { stmt, .. } => {
            walk_stmt_for_class_new(stmt, elab)?
        }
        _ => {}
    }
    Ok(())
}

/// Typedef names declared OUTSIDE any class — in a module/interface/program
/// (generate blocks included), a package, or `$unit`. Class-local typedefs
/// also land in the bare `elab.typedefs` table, so that table cannot tell
/// whether a name is visible to a class from its enclosing scopes.
pub(super) fn non_class_typedef_names(
    defs: &HashMap<String, Definition>,
    module: &Definition,
) -> HashSet<String> {
    fn items(its: &[ModuleItem], out: &mut HashSet<String>) {
        for it in its {
            match it {
                ModuleItem::TypedefDeclaration(t) => {
                    out.insert(t.name.name.clone());
                }
                ModuleItem::GenerateRegion(g) => items(&g.items, out),
                ModuleItem::GenerateIf(g) => g.branches.iter().for_each(|(_, b)| items(b, out)),
                ModuleItem::GenerateFor(g) => items(&g.items, out),
                ModuleItem::GenerateCase(g) => g.arms.iter().for_each(|a| items(&a.items, out)),
                ModuleItem::NestedModule(m) => items(&m.items, out),
                _ => {}
            }
        }
    }
    let mut out = HashSet::default();
    for def in defs.values().chain(std::iter::once(module)) {
        match def {
            Definition::Module(_) | Definition::Interface(_) | Definition::Program(_) => {
                items(def.items(), &mut out)
            }
            Definition::Package(p) => {
                for it in &p.items {
                    if let PackageItem::Typedef(t) = it {
                        out.insert(t.name.name.clone());
                    }
                }
            }
            Definition::Typedef(t) => {
                out.insert(t.name.name.clone());
            }
            _ => {}
        }
    }
    out
}

pub(super) fn validate_class_usage(
    elab: &ElaboratedModule,
    scope_typedefs: Option<&HashSet<String>>,
) -> Result<(), String> {
    // §8.26.4: `implements T` where T is a class type parameter is illegal.
    for cls in elab.classes.values() {
        for imp in &cls.implements {
            if cls.type_param_names.iter().any(|n| n == imp) {
                return Err(format!(
                    "Class '{}' cannot implement type parameter '{}'",
                    cls.name, imp
                ));
            }
        }
    }
    // §8.26.6.1: multiple interface-class implementations that declare the same
    // method name with conflicting return types cannot be satisfied by a
    // single concrete method.
    for cls in elab.classes.values() {
        if cls.implements.len() < 2 {
            continue;
        }
        let mut seen: HashMap<String, String> = HashMap::default();
        for iname in &cls.implements {
            let iface = match elab.classes.get(iname) {
                Some(c) => c,
                None => continue,
            };
            for (mname, m) in iface.methods.iter() {
                let ret = match &m.kind {
                    ClassMethodKind::Function(f)
                    | ClassMethodKind::PureVirtual(f)
                    | ClassMethodKind::Extern(f) => data_type_kind_name(&f.return_type),
                    ClassMethodKind::Task(_) => "task".to_string(),
                };
                match seen.get(mname) {
                    Some(prev) if prev != &ret => {
                        return Err(format!(
                            "Class '{}' has conflicting return types for inherited method '{}'",
                            cls.name, mname
                        ));
                    }
                    None => {
                        seen.insert(mname.clone(), ret);
                    }
                    _ => {}
                }
            }
        }
    }
    // §8.21/§8.26.5: reject instantiating an abstract or interface class.
    for ib in &elab.initial_blocks {
        walk_stmt_for_class_new(&ib.stmt, elab)?;
    }
    for ab in &elab.always_blocks {
        walk_stmt_for_class_new(&ab.stmt, elab)?;
    }

    // §8.26.3: typedefs declared in an interface class are NOT inherited by
    // classes that implement it. Flag a method signature that references a
    // bare typedef that only exists inside an implemented interface class.
    for cls in elab.classes.values() {
        if cls.implements.is_empty() {
            continue;
        }
        // Gather typedef names contributed only by implemented interfaces.
        let mut iface_only_typedefs: HashSet<String> = HashSet::default();
        for iname in &cls.implements {
            if let Some(iface) = elab.classes.get(iname) {
                for t in &iface.typedef_names {
                    iface_only_typedefs.insert(t.clone());
                }
            }
        }
        // Remove anything the class itself (or its extends chain) defines,
        // plus names reachable through module-level typedefs.
        for t in &cls.typedef_names {
            iface_only_typedefs.remove(t);
        }
        let mut cur = cls.extends.clone();
        let mut guard = 0;
        while let Some(base) = cur {
            guard += 1;
            if guard > 32 {
                break;
            }
            if let Some(b) = elab.classes.get(&base) {
                for t in &b.typedef_names {
                    iface_only_typedefs.remove(t);
                }
                cur = b.extends.clone();
            } else {
                break;
            }
        }
        match scope_typedefs {
            Some(names) => iface_only_typedefs.retain(|t| !names.contains(t)),
            None => {
                for t in elab.typedefs.keys() {
                    iface_only_typedefs.remove(t);
                }
            }
        }
        if iface_only_typedefs.is_empty() {
            continue;
        }
        for m in cls.methods.values() {
            let func = match &m.kind {
                ClassMethodKind::Function(f)
                | ClassMethodKind::PureVirtual(f)
                | ClassMethodKind::Extern(f) => Some(f),
                _ => None,
            };
            if let Some(f) = func {
                for p in &f.ports {
                    if let DataType::TypeReference { name, .. } = &p.data_type {
                        if name.has_scope() {
                            continue;
                        }
                        if iface_only_typedefs.contains(&name.name.name) {
                            return Err(format!(
                                "Class '{}' method '{}' references type '{}' — typedefs from implemented interfaces are not inherited",
                                cls.name, f.name.name.name, name.name.name
                            ));
                        }
                    }
                }
            }
        }
    }

    // §18.6.3, §18.8, §18.9: `randomize`, `rand_mode`, and `constraint_mode`
    // are built-in methods and cannot be overridden by a user class.
    const RESERVED_METHODS: &[&str] = &["randomize", "rand_mode", "constraint_mode"];
    for cls in elab.classes.values() {
        for reserved in RESERVED_METHODS {
            if cls.methods.contains_key(*reserved) {
                return Err(format!(
                    "Class '{}' cannot override built-in method '{}'",
                    cls.name, reserved
                ));
            }
        }
    }

    // §18.5.1: `extern constraint c;` must be accompanied by an out-of-class
    // definition `constraint ClassName::c { ... }`.
    for cls in elab.classes.values() {
        for (cname, con) in &cls.constraints {
            if con.is_extern && !con.has_body {
                let defined = elab
                    .out_of_class_constraints
                    .contains(&(cls.name.clone(), cname.clone()));
                if !defined {
                    return Err(format!(
                        "Class '{}' declares extern constraint '{}' with no external definition",
                        cls.name, cname
                    ));
                }
            }
        }
    }

    // §18.5.4, §18.5.10, §18.5.14: randc variables cannot appear in dist
    // expressions, solve..before lists, or soft constraints.
    for cls in elab.classes.values() {
        for con in cls.constraints.values() {
            for item in &con.items {
                check_randc_restrictions(item, &cls.randc_properties, &cls.name)?;
            }
        }
    }

    Ok(())
}

fn check_randc_restrictions(
    item: &ConstraintItem,
    randc: &HashSet<String>,
    cls: &str,
) -> Result<(), String> {
    if randc.is_empty() {
        return Ok(());
    }
    match item {
        ConstraintItem::Inside {
            expr,
            is_dist: true,
            ..
        } => {
            if let Some(n) = simple_expr_name(expr) {
                if randc.contains(&n) {
                    return Err(format!(
                        "Class '{}': dist constraint cannot be applied to randc variable '{}'",
                        cls, n
                    ));
                }
            }
        }
        ConstraintItem::Solve { before, after, .. } => {
            for id in before.iter().chain(after.iter()) {
                if randc.contains(&id.name) {
                    return Err(format!(
                        "Class '{}': randc variable '{}' cannot appear in solve..before",
                        cls, id.name
                    ));
                }
            }
        }
        ConstraintItem::Soft(inner) => {
            collect_soft_randc(inner, randc, cls)?;
        }
        ConstraintItem::Block(items) => {
            for i in items {
                check_randc_restrictions(i, randc, cls)?;
            }
        }
        ConstraintItem::Implication { constraint, .. } => {
            check_randc_restrictions(constraint, randc, cls)?;
        }
        ConstraintItem::IfElse {
            then_item,
            else_item,
            ..
        } => {
            check_randc_restrictions(then_item, randc, cls)?;
            if let Some(e) = else_item {
                check_randc_restrictions(e, randc, cls)?;
            }
        }
        ConstraintItem::Foreach { item, .. } => {
            check_randc_restrictions(item, randc, cls)?;
        }
        _ => {}
    }
    Ok(())
}

fn collect_soft_randc(
    item: &ConstraintItem,
    randc: &HashSet<String>,
    cls: &str,
) -> Result<(), String> {
    // Any randc variable referenced inside a soft constraint is illegal.
    let mut names: HashSet<String> = HashSet::default();
    collect_constraint_idents(item, &mut names);
    for n in &names {
        if randc.contains(n) {
            return Err(format!(
                "Class '{}': soft constraint cannot reference randc variable '{}'",
                cls, n
            ));
        }
    }
    Ok(())
}

fn collect_constraint_idents(item: &ConstraintItem, out: &mut HashSet<String>) {
    match item {
        ConstraintItem::Expr(e) => collect_expr_idents(e, out),
        ConstraintItem::Inside { expr, range, .. } => {
            collect_expr_idents(expr, out);
            for r in range {
                match r {
                    ConstraintRange::Value(v) => collect_expr_idents(v, out),
                    ConstraintRange::Range { lo, hi } => {
                        collect_expr_idents(lo, out);
                        collect_expr_idents(hi, out);
                    }
                }
            }
        }
        ConstraintItem::Implication {
            condition,
            constraint,
            ..
        } => {
            collect_expr_idents(condition, out);
            collect_constraint_idents(constraint, out);
        }
        ConstraintItem::IfElse {
            condition,
            then_item,
            else_item,
            ..
        } => {
            collect_expr_idents(condition, out);
            collect_constraint_idents(then_item, out);
            if let Some(e) = else_item {
                collect_constraint_idents(e, out);
            }
        }
        ConstraintItem::Foreach { item, .. } => collect_constraint_idents(item, out),
        ConstraintItem::Soft(inner) => collect_constraint_idents(inner, out),
        ConstraintItem::Unique { exprs, .. } => {
            for e in exprs {
                collect_expr_idents(e, out);
            }
        }
        ConstraintItem::Block(items) => {
            for i in items {
                collect_constraint_idents(i, out);
            }
        }
        ConstraintItem::Solve { .. } => {}
    }
}

pub(super) fn collect_expr_idents(expr: &Expression, out: &mut HashSet<String>) {
    use crate::ast::expr::ExprKind;
    match &expr.kind {
        ExprKind::Ident(h) => {
            if let Some(s) = h.path.first() {
                out.insert(s.name.name.clone());
            }
        }
        ExprKind::Binary { left, right, .. } => {
            collect_expr_idents(left, out);
            collect_expr_idents(right, out);
        }
        ExprKind::Unary { operand, .. } => collect_expr_idents(operand, out),
        ExprKind::Paren(e) => collect_expr_idents(e, out),
        ExprKind::Conditional {
            condition,
            then_expr,
            else_expr,
        } => {
            collect_expr_idents(condition, out);
            collect_expr_idents(then_expr, out);
            collect_expr_idents(else_expr, out);
        }
        _ => {}
    }
}

fn simple_expr_name(expr: &Expression) -> Option<String> {
    use crate::ast::expr::ExprKind;
    match &expr.kind {
        ExprKind::Ident(h) if h.path.len() == 1 => Some(h.path[0].name.name.clone()),
        ExprKind::Paren(e) => simple_expr_name(e),
        _ => None,
    }
}
