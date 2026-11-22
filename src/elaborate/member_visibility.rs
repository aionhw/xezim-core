use super::*;

/// Resolve the DECLARED (static) class type name of an expression, if it can
/// be determined from elaboration-time type information alone.
///
/// `current_class` is `Some(C)` while inside a method of class `C`;
/// `locals` maps a method-local variable (or `this`-member) name to its
/// declared `DataType`. Returns `None` (leave unchecked) when the class type
/// cannot be statically pinned, so the member-visibility pass never rejects a
/// legal access it cannot prove illegal.
fn static_base_class(
    e: &Expression,
    current_class: Option<&str>,
    locals: &HashMap<String, crate::ast::types::DataType>,
    elab: &ElaboratedModule,
) -> Option<String> {
    match &e.kind {
        ExprKind::This => current_class.map(|c| c.to_string()),
        ExprKind::Ident(h) if h.path.len() == 1 => {
            let name = crate::sv_parser::strip_unit_scope_name(&h.path[0].name.name)
                .unwrap_or(&h.path[0].name.name);
            resolve_name_class(name, current_class, locals, elab)
        }
        ExprKind::MemberAccess { expr: base, member } => {
            let base_cls = static_base_class(base, current_class, locals, elab)?;
            let cd = elab.classes.get(&base_cls)?;
            // A property of a class-typed base with a declared class type.
            let dt = cd.property_types.get(&member.name)?;
            let tn = get_type_name(dt)?;
            resolve_known_class(elab, &tn)
        }
        _ => None,
    }
}

/// Return the class name if `name` (possibly a parameterized specialization
/// like `foo#(bar)` or a type parameter) maps to a real class in `elab.classes`
/// or a real base-class chain root. Only such names are safe to enforce on.
fn resolve_known_class(elab: &ElaboratedModule, name: &str) -> Option<String> {
    if elab.classes.contains_key(name) {
        return Some(name.to_string());
    }
    let base = name.split('#').next().unwrap_or(name);
    if elab.classes.contains_key(base) {
        return Some(base.to_string());
    }
    None
}

/// Search up the `extends` chain from `start` for the class that declares a
/// member named `mname` (a property OR a method). Returns the declaring
/// class's name. LRM §8.2 visibility is declared-type-based, so inherited
/// `local`/`protected` members keep the declaring class's visibility.
fn member_declaring_class(elab: &ElaboratedModule, start: &str, mname: &str) -> Option<String> {
    let mut cur = Some(start.to_string());
    let mut guard = 0;
    while let Some(cname) = cur {
        guard += 1;
        if guard > 64 {
            break;
        }
        let cd = elab.classes.get(&cname)?;
        if cd.properties.contains_key(mname) || cd.methods.contains_key(mname) {
            return Some(cname);
        }
        cur = cd.extends.clone();
    }
    None
}

/// True if `candidate` is `base` or derives from it (walks `extends` up).
fn class_is_or_extends(elab: &ElaboratedModule, candidate: &str, base: &str) -> bool {
    let mut cur = Some(candidate.to_string());
    let mut guard = 0;
    while let Some(c) = cur {
        guard += 1;
        if guard > 64 {
            break;
        }
        if c == base {
            return true;
        }
        cur = elab.classes.get(&c).and_then(|cd| cd.extends.clone());
    }
    false
}

/// The `local`/`protected` member-visibility check for a single
/// `base.member` access.
///
/// `access_scope` is `None` for module-level (top / procedural / continuous
/// assign) code — which can never sit inside a class and therefore can never
/// legally reach a `local`/`protected` member — and `Some(C)` inside a method
/// of class `C`.
fn check_member_visibility(
    elab: &ElaboratedModule,
    base_class: Option<String>,
    member_name: &str,
    access_scope: Option<&str>,
    span: Span,
) -> Result<(), String> {
    // We only reject accesses we can prove are on a real class's member.
    let Some(base_class) = base_class else {
        return Ok(());
    };
    let Some(declaring) = member_declaring_class(elab, &base_class, member_name) else {
        return Ok(());
    };
    let Some(cd) = elab.classes.get(&declaring) else {
        return Ok(());
    };

    if cd.local_properties.contains(member_name) || cd.protected_properties.contains(member_name) {
        let allowed = match access_scope {
            None => false,
            Some(cc) => {
                if cd.local_properties.contains(member_name) {
                    cc == declaring
                } else if cd.protected_properties.contains(member_name) {
                    class_is_or_extends(elab, cc, &declaring)
                } else {
                    false
                }
            }
        };
        if !allowed {
            let kw = if cd.local_properties.contains(member_name) {
                "local"
            } else {
                "protected"
            };
            let loc = span_location(elab, span)
                .map(|l| format!(" at {}", l))
                .unwrap_or_default();
            return Err(format!(
                "Illegal access to {} member '{}'{} (member of class '{}')",
                kw, member_name, loc, declaring
            ));
        }
    }
    Ok(())
}

/// Collect the declared `DataType` of every variable declared in a statement
/// subtree (a method body or a module block). Local class-typed variables are
/// how a method names an instance of another class; knowing their declared
/// type is what lets the member-visibility pass resolve `other.local_member`.
pub(super) fn collect_stmt_declared_types(
    stmt: &Statement,
    out: &mut HashMap<String, crate::ast::types::DataType>,
) {
    match &stmt.kind {
        StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
            for s in stmts {
                collect_stmt_declared_types(s, out);
            }
        }
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
            let dt = data_type.clone();
            for d in declarators {
                out.insert(d.name.name.clone(), dt.clone());
            }
        }
        StatementKind::If {
            then_stmt,
            else_stmt,
            ..
        } => {
            collect_stmt_declared_types(then_stmt, out);
            if let Some(e) = else_stmt {
                collect_stmt_declared_types(e, out);
            }
        }
        StatementKind::Case { items, .. } => {
            for it in items {
                collect_stmt_declared_types(&it.stmt, out);
            }
        }
        StatementKind::For { init, body, .. } => {
            // for-loop init VarDecl carries (name, init); record the loop var
            // type too for completeness (loop vars are rarely class-typed).
            for i in init {
                if let crate::ast::stmt::ForInit::VarDecl { name, .. } = i {
                    let _ = name;
                }
            }
            collect_stmt_declared_types(body, out);
        }
        StatementKind::Foreach { body, .. } => collect_stmt_declared_types(body, out),
        StatementKind::While { body, .. }
        | StatementKind::DoWhile { body, .. }
        | StatementKind::Repeat { body, .. }
        | StatementKind::Forever { body }
        | StatementKind::ForeverTail { body }
        | StatementKind::RsAction { body } => collect_stmt_declared_types(body, out),
        StatementKind::TimingControl { stmt, .. } | StatementKind::Wait { stmt, .. } => {
            collect_stmt_declared_types(stmt, out)
        }
        StatementKind::RandCase { items } => {
            for (_, s) in items {
                collect_stmt_declared_types(s, out);
            }
        }
        StatementKind::WaitOrder { pass, fail, .. } => {
            if let Some(p) = pass {
                collect_stmt_declared_types(p, out);
            }
            if let Some(f) = fail {
                collect_stmt_declared_types(f, out);
            }
        }
        // §16.3: an immediate assertion's pass and fail statements may
        // declare block-locals, as `collect_stmt_declared_names` collects;
        // without their types a member access through one escaped the
        // §8.18 visibility check.
        StatementKind::Assertion(a) => {
            if let Some(s) = &a.action {
                collect_stmt_declared_types(s, out);
            }
            if let Some(s) = &a.else_action {
                collect_stmt_declared_types(s, out);
            }
        }
        _ => {}
    }
}

/// The compiler-time member-visibility pass. Rejects `local`/`protected` member
/// access from outside the declaring class, exactly where the reference
/// simulators report `Illegal access to local/protected member`.
pub(super) fn validate_member_visibility(elab: &ElaboratedModule) -> Result<(), String> {
    let mut first: Option<String> = None;
    let mut record = |e: Result<(), String>| {
        if first.is_none() {
            if let Err(msg) = e {
                first = Some(msg);
            }
        }
    };

    // --- class method bodies (access_scope = the owning class) ---
    for cd in elab.classes.values() {
        for m in cd.methods.values() {
            match &m.kind {
                ClassMethodKind::Function(f) => {
                    let mut locals = HashMap::default();
                    for p in &f.ports {
                        locals.insert(p.name.name.clone(), p.data_type.clone());
                    }
                    for s in &f.items {
                        collect_stmt_declared_types(s, &mut locals);
                    }
                    for s in &f.items {
                        record(walk_stmt_member_visibility_inner(
                            s,
                            elab,
                            Some(&cd.name),
                            &locals,
                        ));
                    }
                }
                ClassMethodKind::Task(t) => {
                    let mut locals = HashMap::default();
                    for p in &t.ports {
                        locals.insert(p.name.name.clone(), p.data_type.clone());
                    }
                    for s in &t.items {
                        collect_stmt_declared_types(s, &mut locals);
                    }
                    for s in &t.items {
                        record(walk_stmt_member_visibility_inner(
                            s,
                            elab,
                            Some(&cd.name),
                            &locals,
                        ));
                    }
                }
                _ => {}
            }
        }
    }

    // --- module-level procedural and continuous-assign bodies (scope: None) ---
    // Module scope can never sit inside a class or a subclass, so any
    // `local`/`protected` access found here is illegal. `locals` is empty
    // for CROSS-block resolution; each block's own local declarations are
    // collected so class-typed block vars (the `t.events` case) resolve.
    let mod_scope: Option<&str> = None;
    for ib in &elab.initial_blocks {
        let mut locals: HashMap<String, crate::ast::types::DataType> = HashMap::default();
        collect_stmt_declared_types(&ib.stmt, &mut locals);
        record(walk_stmt_member_visibility_inner(
            &ib.stmt, elab, mod_scope, &locals,
        ));
    }
    for ab in &elab.always_blocks {
        let mut locals: HashMap<String, crate::ast::types::DataType> = HashMap::default();
        collect_stmt_declared_types(&ab.stmt, &mut locals);
        record(walk_stmt_member_visibility_inner(
            &ab.stmt, elab, mod_scope, &locals,
        ));
    }
    let empty_locals: HashMap<String, crate::ast::types::DataType> = HashMap::default();
    for ca in &elab.continuous_assigns {
        record(check_assign_member_visibility(
            &ca.lhs,
            elab,
            mod_scope,
            &empty_locals,
        ));
        record(check_assign_member_visibility(
            &ca.rhs,
            elab,
            mod_scope,
            &empty_locals,
        ));
    }
    for p in &elab.pending_initial {
        let mut locals: HashMap<String, crate::ast::types::DataType> = HashMap::default();
        collect_stmt_declared_types(&p.source, &mut locals);
        record(walk_stmt_member_visibility_inner(
            &p.source, elab, mod_scope, &locals,
        ));
    }
    for p in &elab.pending_always {
        let mut locals: HashMap<String, crate::ast::types::DataType> = HashMap::default();
        collect_stmt_declared_types(&p.source, &mut locals);
        record(walk_stmt_member_visibility_inner(
            &p.source, elab, mod_scope, &locals,
        ));
    }
    for p in &elab.pending_cont_assign {
        record(check_assign_member_visibility(
            &p.source_lhs(),
            elab,
            mod_scope,
            &empty_locals,
        ));
        record(check_assign_member_visibility(
            &p.rhs_source,
            elab,
            mod_scope,
            &empty_locals,
        ));
    }

    if let Some(msg) = first {
        return Err(msg);
    }
    Ok(())
}

/// Walk a continuous-assign side expression for illegal member accesses.
fn check_assign_member_visibility(
    expr: &crate::ast::expr::Expression,
    elab: &ElaboratedModule,
    access_scope: Option<&str>,
    locals: &HashMap<String, crate::ast::types::DataType>,
) -> Result<(), String> {
    let mut err: Option<String> = None;
    for_each_sub_expr(expr, &mut |x| {
        check_expr_member_access(x, elab, access_scope, locals, &mut err);
    });
    match err {
        Some(m) => Err(m),
        None => Ok(()),
    }
}

/// The sub-expression walk for `validate_member_visibility` (propagates errors
/// out rather than through the non-returning walk closures).
fn walk_stmt_member_visibility_inner(
    stmt: &Statement,
    elab: &ElaboratedModule,
    access_scope: Option<&str>,
    locals: &HashMap<String, crate::ast::types::DataType>,
) -> Result<(), String> {
    let mut err: Option<String> = None;
    for_each_stmt_expr(stmt, &mut |e| {
        for_each_sub_expr(e, &mut |x| {
            if err.is_some() {
                return;
            }
            check_expr_member_access(x, elab, access_scope, locals, &mut err);
        });
    });
    match err {
        Some(m) => Err(m),
        None => Ok(()),
    }
}

/// Inspect one expression for any member access (an explicit
/// `MemberAccess` node OR a hierarchical `Ident` like `a.b.c`) and reject
/// illegal `local`/`protected` accesses on ANY segment of its chain. Errors
/// are written into `err` (first wins).
fn check_expr_member_access(
    x: &Expression,
    elab: &ElaboratedModule,
    access_scope: Option<&str>,
    locals: &HashMap<String, crate::ast::types::DataType>,
    err: &mut Option<String>,
) {
    match &x.kind {
        ExprKind::MemberAccess { expr: base, member } => {
            let bc = static_base_class(base, access_scope, locals, elab);
            if err.is_none() {
                if let Err(m) =
                    check_member_visibility(elab, bc, &member.name, access_scope, x.span)
                {
                    *err = Some(m);
                }
            }
        }
        ExprKind::Ident(h) if h.path.len() >= 2 => {
            // `a.b.c` — resolve each segment's object class, checking every
            // intermediate member too (`a.b` first, then `b.c`).
            let mut obj_class =
                resolve_name_class(&h.path[0].name.name, access_scope, locals, elab);
            for i in 1..h.path.len() {
                let member = &h.path[i].name.name;
                if err.is_none() {
                    if let Err(m) = check_member_visibility(
                        elab,
                        obj_class.clone(),
                        member,
                        access_scope,
                        x.span,
                    ) {
                        *err = Some(m);
                    }
                }
                // advance the object's class to this member's declared class
                obj_class = obj_class.and_then(|oc| {
                    elab.classes
                        .get(&oc)
                        .and_then(|cd| cd.property_types.get(member))
                        .and_then(|dt| get_type_name(dt))
                        .and_then(|tn| resolve_known_class(elab, &tn))
                });
                if obj_class.is_none() {
                    // remaining chain unresolved — stop (can't prove anything)
                    break;
                }
            }
        }
        _ => {}
    }
}

/// Resolve the declared class of a simple identifier inside a scope:
/// a method-local/port, a class property of `this`, or a module signal.
fn resolve_name_class(
    name: &str,
    access_scope: Option<&str>,
    locals: &HashMap<String, crate::ast::types::DataType>,
    elab: &ElaboratedModule,
) -> Option<String> {
    match name {
        "this" => access_scope.map(|c| c.to_string()),
        "super" => {
            let cc = access_scope?;
            elab.classes.get(cc).and_then(|cd| cd.extends.clone())
        }
        _ => {
            if let Some(dt) = locals.get(name) {
                if let Some(tn) = get_type_name(dt) {
                    if let Some(r) = resolve_known_class(elab, &tn) {
                        return Some(r);
                    }
                }
            }
            if let Some(sig) = elab.signals.get(name) {
                if let Some(tn) = sig.type_name.clone() {
                    if let Some(r) = resolve_known_class(elab, &tn) {
                        return Some(r);
                    }
                }
            }
            if let Some(cc) = access_scope {
                if let Some(cd) = elab.classes.get(cc) {
                    if let Some(dt) = cd.property_types.get(name) {
                        if let Some(tn) = get_type_name(dt) {
                            if let Some(r) = resolve_known_class(elab, &tn) {
                                return Some(r);
                            }
                        }
                    }
                }
            }
            None
        }
    }
}

/// §23.9, §23.8.1, §27.6: what the binding of a name's head says to the
/// undeclared-name checks.
pub(super) enum HeadVerdict {
    /// Not bound (a synthesized or unanalysed position), or the head of an
    /// upward path: the name tables decide.
    Unbound,
    Declared,
    /// A bare call nothing declares lexically: legal if found upward.
    UpwardCall,
    Undeclared,
}

/// Where a single-segment head is written.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum HeadRole {
    Value,
    Callee,
    /// The base of a member select, `a.b` or `a[i].b`.
    Path,
}

pub(super) fn head_verdict(h: &HierarchicalIdentifier, role: HeadRole) -> HeadVerdict {
    if h.root.is_some() || h.path.is_empty() {
        return HeadVerdict::Declared;
    }
    if h.bound.is_unset() {
        return HeadVerdict::Unbound;
    }
    if !h.bound.is_upward() {
        return HeadVerdict::Declared;
    }
    let path = h.path.len() > 1 || role == HeadRole::Path;
    match role {
        // §27.6: an implicit block name is a name of its own scope only.
        _ if path && is_implicit_block_name(&h.path[0].name.name) => HeadVerdict::Undeclared,
        // §23.8: a hierarchical path, for the hierarchical-reference lint.
        _ if h.path.len() > 1 => HeadVerdict::Declared,
        HeadRole::Path => HeadVerdict::Unbound,
        HeadRole::Callee => HeadVerdict::UpwardCall,
        HeadRole::Value => HeadVerdict::Undeclared,
    }
}

/// The role of each head `for_each_sub_expr` visits, which sees a call or
/// a member select before its callee or base.
pub(super) struct HeadRoles {
    callee: *const Expression,
    base: *const Expression,
}

impl HeadRoles {
    pub(super) fn new() -> Self {
        HeadRoles {
            callee: std::ptr::null(),
            base: std::ptr::null(),
        }
    }

    pub(super) fn note(&mut self, x: &Expression) {
        match &x.kind {
            ExprKind::Call { func, .. } => self.callee = &**func,
            ExprKind::MemberAccess { expr, .. } => {
                let mut b = &**expr;
                while let ExprKind::Index { expr, .. } = &b.kind {
                    b = expr;
                }
                self.base = b;
            }
            _ => {}
        }
    }

    pub(super) fn role(&self, x: &Expression) -> HeadRole {
        if std::ptr::eq(x, self.callee) {
            HeadRole::Callee
        } else if std::ptr::eq(x, self.base) {
            HeadRole::Path
        } else {
            HeadRole::Value
        }
    }
}

/// §27.6 `genblk<n>`.
fn is_implicit_block_name(name: &str) -> bool {
    name.strip_prefix("genblk")
        .is_some_and(|n| !n.is_empty() && n.bytes().all(|c| c.is_ascii_digit()))
}

/// Add flattened declaration aliases without retaining a second owned set.
pub(super) fn extend_elaborated_decl_leaves(elab: &ElaboratedModule, names: &mut HashSet<String>) {
    // Leaf of every scoped elaboration key: `c.x`, `top.u.arr[3]` → `x`, `arr`.
    let mut add_key = |k: &str| {
        let leaf = k.rsplit('.').next().unwrap_or(k);
        let base = leaf.split('[').next().unwrap_or(leaf);
        if !names.contains(base) {
            names.insert(base.to_string());
        }
    };
    for k in elab.signals.keys() {
        add_key(k);
    }
    for k in elab.parameters.keys() {
        add_key(k);
    }
    for k in elab.arrays.keys() {
        add_key(k);
    }
    for k in elab.associative_arrays.keys() {
        add_key(k);
    }
    for k in elab.arrays_2d.keys() {
        add_key(k);
    }
    for k in elab.arrays_nd.keys() {
        add_key(k);
    }
    for k in elab.dynamic_arrays.iter() {
        add_key(k);
    }
    for k in elab.functions.keys() {
        add_key(k);
    }
    for k in elab.tasks.keys() {
        add_key(k);
    }
    for k in elab.dpi_imports.keys() {
        add_key(k);
    }
    for k in elab.classes.keys() {
        add_key(k);
    }
    for k in elab.typedefs.keys() {
        add_key(k);
    }
    for k in elab.typedef_types.keys() {
        add_key(k);
    }
    for k in elab.lets.keys() {
        add_key(k);
    }
    for k in elab.sequences.iter() {
        add_key(k);
    }
    for k in elab.clocking_blocks.keys() {
        add_key(k);
    }
    for k in elab.interfaces.iter() {
        add_key(k);
    }
    for ms in elab.enum_members.values() {
        for (n, _) in ms {
            add_key(n);
        }
    }
    for m in elab.package_enum_members.values() {
        for n in m.keys() {
            add_key(n);
        }
    }
}
