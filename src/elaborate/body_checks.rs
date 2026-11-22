use super::*;

/// An identifier or call in an inlined sub-instance body that NOTHING in the
/// design declares is an error — the reference tooling rejects it at
/// elaboration. The per-module validator only ever saw the TOP module's
/// blocks; sub-instance bodies are inlined afterwards and were never checked,
/// so `chk_always(...)` in an RTL module bound to a stale header that lacked
/// it simply never ran (assertions silently vanished), and a typo'd signal in
/// a child read x for the whole run.
///
/// §23.9, §23.8.1: the binding of a head decides (`head_verdict`). A head the
/// binder did not walk, or an upward path head, keeps the "declared nowhere"
/// bar: a bare name is accepted if the instance's own module declares it
/// (`local_names`, ports, interfaces), the body declares it, any elaborated
/// table knows it under any scope, or any definition in the design declares it.
pub(super) fn validate_inlined_bodies(
    elab: &ElaboratedModule,
    definitions: &HashMap<String, Definition>,
) -> Result<(), String> {
    let mut known = collect_design_declared_names(definitions, true);
    // §23.11: instances that compilation-unit binds add.
    UNIT_BIND_INSTANCES.with(|s| known.extend(s.borrow().names.iter().cloned()));
    extend_elaborated_decl_leaves(elab, &mut known);

    // §23.6: a named block of any process is a scope the module's other
    // processes may name (`blk.v`).
    let mut block_labels: HashSet<String> = HashSet::default();
    for p in &elab.pending_always {
        collect_block_labels(&p.source, &mut block_labels);
    }
    for p in &elab.pending_initial {
        collect_block_labels(&p.source, &mut block_labels);
    }
    let known: HashSet<String> = if block_labels.is_empty() {
        known
    } else {
        let mut k = known;
        k.extend(block_labels);
        k
    };
    // One check per distinct source body: sibling instances share the Rc.
    let mut seen: HashSet<usize> = HashSet::default();
    // Per body, its calls the binding leaves upward, checked per instance.
    let mut upward_calls: HashMap<usize, Vec<(String, Span)>> = HashMap::default();
    let mut first: Option<(String, Span, String)> = None;
    let mut check_body =
        |source_ptr: usize,
         ctx: &RewriteCtx,
         locals: &HashSet<String>,
         visit: &mut dyn FnMut(&mut dyn FnMut(&Expression))| {
            if first.is_some() {
                return;
            }
            if seen.insert(source_ptr) {
                let calls = upward_calls.entry(source_ptr).or_default();
                let mut roles = HeadRoles::new();
                let mut check_expr = |e: &Expression| {
                    for_each_sub_expr(e, &mut |x| {
                        if first.is_some() {
                            return;
                        }
                        roles.note(x);
                        let ExprKind::Ident(h) = &x.kind else { return };
                        let Some(head) = h.path.first() else { return };
                        let raw = head.name.name.as_str();
                        let name = crate::sv_parser::strip_unit_scope_name(raw).unwrap_or(raw);
                        if name.starts_with('$')
                            || name.contains('.')
                            || matches!(
                                name,
                                "new" | "super" | "this" | "randomize" | "std" | "process" | "null"
                            )
                            || is_builtin_type_keyword(name)
                        {
                            return;
                        }
                        match head_verdict(h, roles.role(x)) {
                            HeadVerdict::Declared => return,
                            HeadVerdict::UpwardCall => {
                                calls.push((name.to_string(), x.span));
                                return;
                            }
                            HeadVerdict::Undeclared => {
                                first = Some((name.to_string(), x.span, ctx.owner.clone()));
                                return;
                            }
                            HeadVerdict::Unbound => {}
                        }
                        if h.root.is_some()
                            || h.path.len() != 1
                            || ctx.local_names.contains(name)
                            || ctx.port_map.contains_key(name)
                            || ctx.interface_map.contains_key(name)
                            || ctx.type_binds.contains_key(name)
                            || locals.contains(name)
                            || known.contains(name)
                        {
                            return;
                        }
                        first = Some((name.to_string(), x.span, ctx.owner.clone()));
                    });
                };
                visit(&mut check_expr);
            }
            // §23.8.1: each instance searches upward from where it sits.
            let inst = ctx.prefix.trim_end_matches('.');
            let upward = ctx.upward.borrow();
            if let Some((name, span)) = upward_calls
                .get(&source_ptr)
                .into_iter()
                .flatten()
                .find(|(n, _)| upward.find_subroutine(inst, n).is_none())
            {
                first.get_or_insert((name.clone(), *span, ctx.owner.clone()));
            }
        };
    for p in &elab.pending_always {
        let mut locals = HashSet::default();
        collect_stmt_declared_names(&p.source, &mut locals);
        add_construct_bound_names(&p.source, &mut locals);
        let src = &p.source;
        check_body(
            std::rc::Rc::as_ptr(src) as usize,
            &p.ctx,
            &locals,
            &mut |f| for_each_stmt_expr(src, f),
        );
    }
    for p in &elab.pending_initial {
        let mut locals = HashSet::default();
        collect_stmt_declared_names(&p.source, &mut locals);
        add_construct_bound_names(&p.source, &mut locals);
        let src = &p.source;
        check_body(
            std::rc::Rc::as_ptr(src) as usize,
            &p.ctx,
            &locals,
            &mut |f| for_each_stmt_expr(src, f),
        );
    }
    for p in &elab.pending_cont_assign {
        let locals = HashSet::default();
        let l = p.source_lhs();
        let r = &p.rhs_source;
        check_body(std::rc::Rc::as_ptr(r) as usize, &p.ctx, &locals, &mut |f| {
            f(&l);
            f(r);
        });
    }
    if let Some((name, span, owner)) = first {
        let loc = span_location_of(elab, span, &owner)
            .map(|l| format!(" at {}", l))
            .unwrap_or_default();
        return Err(format!("Undeclared identifier '{}'{}", name, loc));
    }
    validate_subroutine_bodies(elab, definitions, &known)
}

/// Names a statement's constructs bind themselves, for the undeclared-name
/// checks: the §7.12 array-method iterator (`item`, or `x` in
/// `arr.find(x) with (x > 0)`) and the §18.11 `obj.randomize(v, w)` operands,
/// which name members of `obj`.
fn add_construct_bound_names(s: &Statement, locals: &mut HashSet<String>) {
    locals.insert("item".to_string());
    for_each_stmt_expr(s, &mut |e| {
        for_each_sub_expr(e, &mut |x| {
            let args = match &x.kind {
                ExprKind::WithClause { expr, .. } => match &expr.kind {
                    ExprKind::Call { args, .. } => args,
                    _ => return,
                },
                // §18.11: `obj.randomize(v, w)` names members of `obj`.
                ExprKind::Call { func, args } => match &func.kind {
                    ExprKind::MemberAccess { member, .. } if member.name == "randomize" => args,
                    ExprKind::Ident(h)
                        if h.path.len() > 1
                            && h.path.last().is_some_and(|s| s.name.name == "randomize") =>
                    {
                        args
                    }
                    _ => return,
                },
                _ => return,
            };
            for a in args {
                if let ExprKind::Ident(h) = &a.kind {
                    if h.path.len() == 1 {
                        locals.insert(h.path[0].name.name.clone());
                    }
                }
            }
        })
    });
}

/// One task/function body to check.
struct SubroutineBody<'a> {
    /// Definition it lives in, for the source location.
    owner: &'a str,
    /// Class whose members it may name bare: the enclosing class of a method,
    /// or the `C` of an out-of-class `C::m` body; empty otherwise.
    class: String,
    /// The subroutine's own name (a function's return variable).
    name: &'a str,
    ports: &'a [crate::ast::decl::FunctionPort],
    items: &'a [Statement],
}

impl<'a> SubroutineBody<'a> {
    fn task(owner: &'a str, class: &'a str, t: &'a TaskDeclaration) -> Self {
        let class = Self::class_scope(class, &t.name);
        SubroutineBody {
            owner,
            class,
            name: &t.name.name.name,
            ports: &t.ports,
            items: &t.items,
        }
    }

    fn function(owner: &'a str, class: &'a str, f: &'a FunctionDeclaration) -> Self {
        let class = Self::class_scope(class, &f.name);
        SubroutineBody {
            owner,
            class,
            name: &f.name.name.name,
            ports: &f.ports,
            items: &f.items,
        }
    }

    /// §8.24/§23.9 (#842): preserve the complete owner of a nested method.
    /// A bare last component could name an unrelated class, while a body
    /// written inside its enclosing class has a relative class scope.
    fn class_scope(enclosing: &str, name: &crate::ast::types::TypeName) -> String {
        let scope = name.scope_prefix();
        if scope.is_empty() {
            enclosing.to_string()
        } else if enclosing.is_empty() {
            scope
        } else {
            nested_scope_name(enclosing, &scope)
        }
    }
}

/// §13.3/§13.4 (and §8.6 class methods): the same "declared nowhere" bar for
/// task and function BODIES — module, interface and program subroutines of
/// every definition the design instantiates, package subroutines, and class
/// methods wherever the class is declared. No validator ever walked them, so
/// `task t; undeclared_x = 1; endtask` elaborated and ran silently, while the
/// reference simulator rejects it at compile time.
///
/// A method is skipped when its class derives (directly or not) from a class
/// the design does not declare — `extends mailbox #(T)` or a type-parameter
/// base — since the members it may name bare are then unknown.
///
/// §8/§23.9: a class member is visible bare only inside its own class
/// hierarchy (and nested classes). A method body is therefore checked
/// against `outside_classes` — every name declared anywhere except class
/// members — plus the members of its own class, its ancestors, the
/// interface classes it implements and its enclosing classes. With the
/// plain "declared anywhere" bar, UVM 1.2 code naming the removed global
/// `factory` compiled because an unrelated class has a `factory` member,
/// and `factory.set_inst_override_by_name(...)` then did nothing.
fn validate_subroutine_bodies(
    elab: &ElaboratedModule,
    definitions: &HashMap<String, Definition>,
    known: &HashSet<String>,
) -> Result<(), String> {
    use crate::ast::decl::{ClassItem, ClassMethodKind, PackageItem};

    /// Module-level items of every generate branch, flattened.
    fn flat_items<'a>(items: &'a [ModuleItem], out: &mut Vec<&'a ModuleItem>) {
        for it in items {
            match it {
                ModuleItem::GenerateRegion(gr) => flat_items(&gr.items, out),
                ModuleItem::GenerateFor(gf) => flat_items(&gf.items, out),
                ModuleItem::GenerateIf(gi) => {
                    for (_, b) in &gi.branches {
                        flat_items(b, out);
                    }
                }
                ModuleItem::GenerateCase(gc) => {
                    for arm in &gc.arms {
                        flat_items(&arm.items, out);
                    }
                }
                _ => out.push(it),
            }
        }
    }
    fn class_bodies<'a>(
        owner: &'a str,
        c: &'a ClassDeclaration,
        out: &mut Vec<SubroutineBody<'a>>,
    ) {
        for it in &c.items {
            match it {
                ClassItem::Method(m) => match &m.kind {
                    ClassMethodKind::Function(f) => {
                        out.push(SubroutineBody::function(owner, &c.name.name, f))
                    }
                    ClassMethodKind::Task(t) => {
                        out.push(SubroutineBody::task(owner, &c.name.name, t))
                    }
                    _ => {}
                },
                ClassItem::Class(inner) => class_bodies(owner, inner, out),
                _ => {}
            }
        }
    }
    fn all_classes<'a>(
        c: &'a ClassDeclaration,
        out: &mut HashMap<&'a str, &'a ClassDeclaration>,
        outer: &mut HashMap<&'a str, &'a str>,
        same_name: &mut HashMap<&'a str, Vec<&'a ClassDeclaration>>,
    ) {
        out.insert(c.name.name.as_str(), c);
        same_name.entry(c.name.name.as_str()).or_default().push(c);
        for it in &c.items {
            if let ClassItem::Class(inner) = it {
                outer.insert(inner.name.name.as_str(), c.name.name.as_str());
                all_classes(inner, out, outer, same_name);
            }
        }
    }

    // Definitions the elaborated design instantiates (binds were already
    // folded into their targets as plain instantiations).
    let mut used: HashSet<&str> = HashSet::default();
    let mut stack: Vec<&str> = vec![elab.name.as_str()];
    while let Some(n) = stack.pop() {
        let Some((key, def)) = definitions.get_key_value(n) else {
            continue;
        };
        if !used.insert(key.as_str()) {
            continue;
        }
        let mut items = Vec::new();
        flat_items(def.items(), &mut items);
        for it in items {
            if let ModuleItem::ModuleInstantiation(mi) = it {
                stack.push(&mi.module_name.name);
            }
        }
    }

    let mut names: Vec<&String> = definitions.keys().collect();
    names.sort();
    let mut classes: HashMap<&str, &ClassDeclaration> = HashMap::default();
    let mut outer: HashMap<&str, &str> = HashMap::default();
    let mut same_name: HashMap<&str, Vec<&ClassDeclaration>> = HashMap::default();
    let mut bodies: Vec<SubroutineBody> = Vec::new();
    for name in names {
        let def = &definitions[name];
        match def {
            Definition::Module(_) | Definition::Interface(_) | Definition::Program(_) => {
                let mut items = Vec::new();
                flat_items(def.items(), &mut items);
                let checked = used.contains(name.as_str());
                for it in items {
                    match it {
                        ModuleItem::ClassDeclaration(c) => {
                            all_classes(c, &mut classes, &mut outer, &mut same_name);
                            if checked {
                                class_bodies(name, c, &mut bodies);
                            }
                        }
                        ModuleItem::TaskDeclaration(t) if checked => {
                            bodies.push(SubroutineBody::task(name, "", t))
                        }
                        ModuleItem::FunctionDeclaration(f) if checked => {
                            bodies.push(SubroutineBody::function(name, "", f))
                        }
                        _ => {}
                    }
                }
            }
            Definition::Package(p) => {
                for it in &p.items {
                    match it {
                        PackageItem::Task(t) => bodies.push(SubroutineBody::task(name, "", t)),
                        PackageItem::Function(f) => {
                            bodies.push(SubroutineBody::function(name, "", f))
                        }
                        PackageItem::Class(c) => {
                            all_classes(c, &mut classes, &mut outer, &mut same_name);
                            class_bodies(name, c, &mut bodies);
                        }
                        _ => {}
                    }
                }
            }
            Definition::Class(c) => {
                all_classes(c, &mut classes, &mut outer, &mut same_name);
                class_bodies(name, c, &mut bodies);
            }
            _ => {}
        }
    }
    let bases_declared = |class: &str| -> bool {
        let mut cur = class;
        for _ in 0..64 {
            let Some(cd) = classes.get(cur) else {
                return false;
            };
            match &cd.extends {
                None => return true,
                Some(ext) => cur = ext.name.name.as_str(),
            }
        }
        false
    };
    // Members a method of `class` may name bare (see the doc comment).
    let class_scope = |class: &str| -> HashSet<String> {
        let mut out: HashSet<String> = HashSet::default();
        let mut todo: Vec<&str> = vec![class];
        let mut seen: HashSet<&str> = HashSet::default();
        while let Some(c) = todo.pop() {
            if !seen.insert(c) {
                continue;
            }
            // Same-named classes of different packages: take them all.
            for cd in same_name.get(c).into_iter().flatten() {
                decl_class_member_names(cd, &mut out);
                if let Some(ext) = &cd.extends {
                    todo.push(ext.name.name.as_str());
                }
                todo.extend(cd.implements.iter().map(|i| i.name.as_str()));
            }
            if let Some(o) = outer.get(c) {
                todo.push(o);
            }
        }
        out
    };
    let mut scopes: HashMap<&str, HashSet<String>> = HashMap::default();
    // Only class methods need the stricter namespace. Most generated designs
    // have no class methods, so keep their large global-name table singular.
    let mut outside_classes = None;
    for body in &bodies {
        // Qualified and bare aliases point to one elaborated class, whose
        // declared name indexes the AST's lexical scope maps. Resolve the
        // full chain before choosing the declarations visible to the body.
        let class = elab
            .classes
            .get(&body.class)
            .map_or(body.class.as_str(), |c| c.name.as_str());
        if !class.is_empty() && !bases_declared(class) {
            continue;
        }
        let upward = |n: &str| {
            elab.upward_scopes
                .borrow()
                .every_instance_finds(body.owner, n)
        };
        let found = if class.is_empty() {
            first_undeclared_in_subroutine(body, known, None, &upward)
        } else {
            let scope = scopes.entry(class).or_insert_with(|| class_scope(class));
            let outside = outside_classes.get_or_insert_with(|| {
                let mut names = collect_design_declared_names(definitions, false);
                extend_elaborated_decl_leaves(elab, &mut names);
                names
            });
            first_undeclared_in_subroutine(body, outside, Some(scope), &upward)
        };
        if let Some((name, span)) = found {
            return Err(span_error_of(
                elab,
                span,
                body.owner,
                &format!("Undeclared identifier '{}'", name),
            ));
        }
    }
    Ok(())
}

/// The first bare identifier (or called name) in a subroutine body that the
/// binding leaves undeclared, or, where the binder did not walk, that is
/// neither local to it — a formal, the function's own name, a body-local
/// declaration, a `with` iterator — nor declared anywhere in the design.
/// `upward` says whether a bare call the binding leaves upward is found.
fn first_undeclared_in_subroutine(
    body: &SubroutineBody,
    known: &HashSet<String>,
    class_scope: Option<&HashSet<String>>,
    upward: &dyn Fn(&str) -> bool,
) -> Option<(String, Span)> {
    let mut locals: HashSet<String> = HashSet::default();
    locals.insert(body.name.to_string());
    for p in body.ports {
        locals.insert(p.name.name.clone());
    }
    for s in body.items {
        collect_stmt_declared_names(s, &mut locals);
    }
    for s in body.items {
        add_construct_bound_names(s, &mut locals);
    }
    let mut first: Option<(String, Span)> = None;
    let mut roles = HeadRoles::new();
    for s in body.items {
        for_each_stmt_expr(s, &mut |e| {
            for_each_sub_expr(e, &mut |x| {
                if first.is_some() {
                    return;
                }
                roles.note(x);
                let ExprKind::Ident(h) = &x.kind else { return };
                let Some(head) = h.path.first() else { return };
                let raw = head.name.name.as_str();
                let name = crate::sv_parser::strip_unit_scope_name(raw).unwrap_or(raw);
                if name.starts_with('$') || name.contains('.') || is_builtin_bare_name(name) {
                    return;
                }
                match head_verdict(h, roles.role(x)) {
                    HeadVerdict::Declared => return,
                    HeadVerdict::UpwardCall if upward(name) => return,
                    HeadVerdict::UpwardCall | HeadVerdict::Undeclared => {
                        first = Some((name.to_string(), x.span));
                        return;
                    }
                    HeadVerdict::Unbound => {}
                }
                if h.root.is_some()
                    || h.path.len() != 1
                    || locals.contains(name)
                    || known.contains(name)
                    || class_scope.is_some_and(|c| c.contains(name))
                {
                    return;
                }
                first = Some((name.to_string(), x.span));
            })
        });
        if first.is_some() {
            break;
        }
    }
    first
}

/// Names legal as a bare identifier without any declaration: `this`/`super`,
/// the built-in `std` package and `process` class, the §18 built-in class
/// methods callable unqualified inside a method, and built-in type keywords
/// (`$bits(int)`).
fn is_builtin_bare_name(name: &str) -> bool {
    matches!(
        name,
        "new"
            | "super"
            | "this"
            | "null"
            | "std"
            | "process"
            | "randomize"
            | "srandom"
            | "get_randstate"
            | "set_randstate"
            | "rand_mode"
            | "constraint_mode"
            | "pre_randomize"
            | "post_randomize"
            | "integer"
            | "int"
            | "shortint"
            | "longint"
            | "byte"
            | "time"
            | "bit"
            | "logic"
            | "reg"
            | "real"
            | "shortreal"
            | "realtime"
            | "string"
            | "chandle"
            | "void"
    )
}
