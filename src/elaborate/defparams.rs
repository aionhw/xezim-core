use super::*;

/// §23.10.1: a `defparam` whose path starts at a top-level module
/// (`defparam tb.u.P = 3` inside `tb`, or `other.u.P` naming another top)
/// resolves from the root, not from the scope that declares it, where it
/// matched no child and was dropped. Collected from every definition the root
/// reaches, as the root scope's pending defparams: with a single top its own
/// name is dropped (the root's children are its instances); under the
/// multi-top wrapper each top is a child of the root. Only values constant
/// without the declaring scope's own parameters are taken.
pub(super) fn absolute_defparams(
    root: &str,
    definitions: &HashMap<String, Definition>,
    root_params: &HashMap<String, Value>,
) -> Vec<PendingDefparam> {
    fn instances<'i>(items: &'i [ModuleItem], out: &mut Vec<&'i ModuleInstantiation>) {
        for it in items {
            match it {
                ModuleItem::ModuleInstantiation(mi) => out.push(mi),
                ModuleItem::GenerateRegion(r) => instances(&r.items, out),
                ModuleItem::GenerateIf(g) => {
                    for (_, items) in &g.branches {
                        instances(items, out);
                    }
                }
                ModuleItem::GenerateFor(g) => instances(&g.items, out),
                ModuleItem::GenerateCase(g) => {
                    for arm in &g.arms {
                        instances(&arm.items, out);
                    }
                }
                _ => {}
            }
        }
    }
    let inst_names = |items: &[ModuleItem]| -> HashSet<String> {
        let mut mis = Vec::new();
        instances(items, &mut mis);
        mis.iter()
            .flat_map(|mi| mi.instances.iter().map(|hi| hi.name.name.clone()))
            .collect()
    };
    let Some(root_def) = definitions.get(root) else {
        return Vec::new();
    };
    let wrapper = root == crate::MULTI_TOP_WRAPPER;
    let tops: HashSet<String> = if wrapper {
        inst_names(root_def.items())
    } else {
        std::iter::once(root.to_string()).collect()
    };
    let no_params = HashMap::default();
    let mut out = Vec::new();
    let mut seen: HashSet<String> = HashSet::default();
    let mut stack = vec![root.to_string()];
    while let Some(name) = stack.pop() {
        if !seen.insert(name.clone()) {
            continue;
        }
        let Some(def) = definitions.get(&name) else {
            continue;
        };
        let mut mis = Vec::new();
        instances(def.items(), &mut mis);
        stack.extend(mis.iter().map(|mi| mi.module_name.name.clone()));
        let own = inst_names(def.items());
        let params = if name == root {
            root_params
        } else {
            &no_params
        };
        for it in def.items() {
            let ModuleItem::Defparam(assigns) = it else {
                continue;
            };
            for (lhs, rhs) in assigns {
                let Some(path) = defparam_path_segments(lhs) else {
                    continue;
                };
                if path.len() < 3
                    || !tops.contains(&path[0])
                    || own.contains(&path[0])
                    || !is_const_expr(rhs, params)
                {
                    continue;
                }
                let path = if wrapper { path } else { path[1..].to_vec() };
                out.push(PendingDefparam {
                    path,
                    value: eval_const_expr_val(rhs, params),
                    span: lhs.span,
                    owner: name.clone(),
                });
            }
        }
    }
    out
}

/// §23.10.1/§23.8: a `defparam` path that starts neither at a child of the
/// declaring scope nor at a top is resolved UPWARD, like any hierarchical
/// name: its first segment names a child of an enclosing instance (the
/// parent, the grandparent, …) or the definition name of an enclosing
/// instance (`defparam mid.l.P` inside `mid`'s sub-instance). Such paths
/// matched nothing top-down and were dropped. Each is resolved per
/// declaring instance (walking the instance tree from `root`) into a path
/// from the root, and returned as root-scope pending defparams in the same
/// form as `absolute_defparams`. Instances inside generate blocks and
/// instance arrays are not walked; only constant values are taken.
pub(super) fn upward_defparams(
    root: &str,
    definitions: &HashMap<String, Definition>,
) -> Vec<PendingDefparam> {
    /// Plain (non-generate, non-array) child instances: (name, definition).
    fn children(items: &[ModuleItem]) -> Vec<(String, String)> {
        let mut out = Vec::new();
        for it in items {
            match it {
                ModuleItem::ModuleInstantiation(mi) => {
                    for hi in &mi.instances {
                        if hi.dimensions.is_empty() {
                            out.push((hi.name.name.clone(), mi.module_name.name.clone()));
                        }
                    }
                }
                ModuleItem::GenerateRegion(r) => out.extend(children(&r.items)),
                _ => {}
            }
        }
        out
    }
    /// Every name a path can start with inside a scope: its instances in
    /// any generate branch, and its generate block labels.
    fn scope_names(items: &[ModuleItem], out: &mut HashSet<String>) {
        for it in items {
            match it {
                ModuleItem::ModuleInstantiation(mi) => {
                    out.extend(mi.instances.iter().map(|hi| hi.name.name.clone()));
                }
                ModuleItem::GenerateRegion(r) => scope_names(&r.items, out),
                ModuleItem::GenerateIf(g) => {
                    out.extend(g.branch_labels.iter().flatten().cloned());
                    for (_, b) in &g.branches {
                        scope_names(b, out);
                    }
                }
                ModuleItem::GenerateCase(g) => {
                    for arm in &g.arms {
                        out.extend(arm.label.iter().cloned());
                        scope_names(&arm.items, out);
                    }
                }
                ModuleItem::GenerateFor(g) => {
                    out.extend(g.name.iter().cloned());
                    scope_names(&g.items, out);
                }
                _ => {}
            }
        }
    }
    let names_of = |d: &Definition| {
        let mut n = HashSet::default();
        scope_names(d.items(), &mut n);
        n
    };
    let Some(root_def) = definitions.get(root) else {
        return Vec::new();
    };
    let tops: HashSet<String> = if root == crate::MULTI_TOP_WRAPPER {
        names_of(root_def)
    } else {
        std::iter::once(root.to_string()).collect()
    };
    let upward_head = |p: &[String], own: &HashSet<String>| {
        p.len() >= 2 && !own.contains(&p[0]) && !tops.contains(&p[0])
    };
    // Definitions declaring a candidate.
    let mut candidates: HashSet<&str> = HashSet::default();
    for (name, def) in definitions {
        let mut own: Option<HashSet<String>> = None;
        let has = def.items().iter().any(|it| {
            let ModuleItem::Defparam(assigns) = it else {
                return false;
            };
            let own = own.get_or_insert_with(|| names_of(def));
            assigns
                .iter()
                .any(|(lhs, _)| defparam_path_segments(lhs).is_some_and(|p| upward_head(&p, own)))
        });
        if has {
            candidates.insert(name.as_str());
        }
    }
    if candidates.is_empty() {
        return Vec::new();
    }
    // Definitions whose subtree reaches a candidate: the only ones walked.
    fn reaches(
        name: &str,
        definitions: &HashMap<String, Definition>,
        candidates: &HashSet<&str>,
        memo: &mut HashMap<String, bool>,
    ) -> bool {
        if let Some(&r) = memo.get(name) {
            return r;
        }
        memo.insert(name.to_string(), false);
        let r = candidates.contains(name)
            || definitions.get(name).is_some_and(|d| {
                children(d.items())
                    .iter()
                    .any(|(_, dn)| reaches(dn, definitions, candidates, memo))
            });
        memo.insert(name.to_string(), r);
        r
    }
    let mut memo: HashMap<String, bool> = HashMap::default();
    let no_params = HashMap::default();
    let mut out = Vec::new();
    // (instance path below the root, definitions from the root down).
    let mut stack: Vec<(Vec<String>, Vec<String>)> = vec![(Vec::new(), vec![root.to_string()])];
    while let Some((path, chain)) = stack.pop() {
        let Some(def) = definitions.get(chain.last().unwrap()) else {
            continue;
        };
        let depth = chain.len() - 1;
        if depth > 0 && candidates.contains(chain[depth].as_str()) {
            let own = names_of(def);
            for it in def.items() {
                let ModuleItem::Defparam(assigns) = it else {
                    continue;
                };
                for (lhs, rhs) in assigns {
                    let Some(p) = defparam_path_segments(lhs) else {
                        continue;
                    };
                    if !upward_head(&p, &own) || !is_const_expr(rhs, &no_params) {
                        continue;
                    }
                    // Nearest enclosing scope first: a name declared in that
                    // scope, else that scope's own definition name.
                    let mut target: Option<Vec<String>> = None;
                    for j in (0..depth).rev() {
                        if definitions
                            .get(&chain[j])
                            .is_some_and(|d| names_of(d).contains(&p[0]))
                        {
                            let mut t = path[..j].to_vec();
                            t.extend(p.iter().cloned());
                            target = Some(t);
                            break;
                        }
                        if chain[j] == p[0] {
                            let mut t = path[..j].to_vec();
                            t.extend(p[1..].iter().cloned());
                            target = Some(t);
                            break;
                        }
                    }
                    if let Some(t) = target.filter(|t| t.len() >= 2) {
                        out.push(PendingDefparam {
                            path: t,
                            value: eval_const_expr_val(rhs, &no_params),
                            span: lhs.span,
                            owner: chain[depth].clone(),
                        });
                    }
                }
            }
        }
        for (inst, dn) in children(def.items()) {
            if reaches(&dn, definitions, &candidates, &mut memo) {
                let mut np = path.clone();
                np.push(inst);
                let mut nc = chain.clone();
                nc.push(dn);
                stack.push((np, nc));
            }
        }
    }
    out
}

/// Extract the dotted instance/parameter path of a `defparam` LHS
/// (`u.sub.PARAM` → `["u","sub","PARAM"]`). Returns None for anything that
/// isn't a plain hierarchical identifier (bit-selects etc. are not valid
/// defparam targets). The last segment is the parameter name.
pub(super) fn defparam_path_segments(e: &Expression) -> Option<Vec<String>> {
    // `u.sub.PARAM` parses as a MemberAccess chain (`.` is member access),
    // and a bare `u` (or a whole path) as an Ident — handle both.
    fn walk(e: &Expression, out: &mut Vec<String>) -> bool {
        match &e.kind {
            ExprKind::Ident(h) => {
                for seg in &h.path {
                    if !seg.selects.is_empty() {
                        return false;
                    }
                    out.push(seg.name.name.clone());
                }
                true
            }
            ExprKind::MemberAccess { expr, member } => {
                walk(expr, out) && {
                    out.push(member.name.clone());
                    true
                }
            }
            // `u[2].V` — an array-of-instances element. Array expansion names
            // elements `u[<j>]` (ai_expand_instances), so fold the constant
            // index into the preceding segment to match that instance name.
            ExprKind::Index { expr, index } => {
                if !walk(expr, out) {
                    return false;
                }
                let idx = eval_const_expr(index, &HashMap::default());
                match out.last_mut() {
                    Some(last) => {
                        *last = format!("{}[{}]", last, idx);
                        true
                    }
                    None => false,
                }
            }
            _ => false,
        }
    }
    let mut segs = Vec::new();
    if walk(e, &mut segs) && segs.len() >= 2 {
        Some(segs)
    } else {
        None
    }
}

/// §6.18/§23.10: a submodule VARIABLE declared with one of the module's own
/// typedefs records the INSTANCE-scoped typedef name as its `type_name`, so
/// run-time reflection (`.name()`, `.num()`, `.first()`) keys the right
/// member list — the bare name is unbound after inlining and collides across
/// modules that reuse common typedef names like `state_e`.
pub(super) fn scope_local_type_name(
    tn: Option<String>,
    local_typedefs: &std::collections::HashSet<String>,
    inst_prefix: &str,
) -> Option<String> {
    tn.map(|t| {
        if local_typedefs.contains(&t) {
            cat2(&inst_prefix, &t)
        } else {
            t
        }
    })
}

/// Retype every local declaration in a subroutine body (`T v;` in any
/// nested block) for which `rename` returns a type.
pub(super) fn scope_local_decl_types(
    stmts: &mut [Statement],
    rename: &dyn Fn(&DataType) -> Option<DataType>,
) {
    for s in stmts {
        scope_local_decl_types_in(s, rename);
    }
}

fn scope_local_decl_types_in(s: &mut Statement, rename: &dyn Fn(&DataType) -> Option<DataType>) {
    match &mut s.kind {
        StatementKind::VarDecl { data_type, .. } | StatementKind::ParamDecl { data_type, .. } => {
            if let Some(dt) = rename(data_type) {
                *data_type = dt;
            }
        }
        StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
            scope_local_decl_types(stmts, rename)
        }
        StatementKind::If {
            then_stmt,
            else_stmt,
            ..
        } => {
            scope_local_decl_types_in(then_stmt, rename);
            if let Some(e) = else_stmt {
                scope_local_decl_types_in(e, rename);
            }
        }
        StatementKind::Case { items, .. } => {
            for it in items {
                scope_local_decl_types_in(&mut it.stmt, rename);
            }
        }
        StatementKind::For { body, .. }
        | StatementKind::Foreach { body, .. }
        | StatementKind::While { body, .. }
        | StatementKind::DoWhile { body, .. }
        | StatementKind::Repeat { body, .. }
        | StatementKind::Forever { body } => scope_local_decl_types_in(body, rename),
        StatementKind::TimingControl { stmt, .. } | StatementKind::Wait { stmt, .. } => {
            scope_local_decl_types_in(stmt, rename)
        }
        _ => {}
    }
}

/// §7.4.1: whether `dt` names (through plain aliases) a packed array of a
/// named type (`lane_t [0:1]`, or `typedef lane_t [0:1] arr_t;`) or a packed
/// structure or union. A port of such a type keeps its declaration, as a
/// variable of it does: an element of a named signed type is signed, and so
/// is one of a packed-array member of the structure.
pub(super) fn names_packed_array_or_struct(
    dt: &DataType,
    typedef_types: &HashMap<String, DataType>,
) -> bool {
    let mut cur = dt;
    for _ in 0..64 {
        match cur {
            DataType::TypeReference {
                name, dimensions, ..
            } => {
                if !dimensions.is_empty() {
                    return true;
                }
                match lookup_scoped_type(name, typedef_types) {
                    Some(next) => cur = next,
                    None => return false,
                }
            }
            DataType::Struct(su) => return su.packed,
            _ => return false,
        }
    }
    false
}

/// One typedef step of a BARE reference with no dimensions of its own:
/// `w_t` gives `b_t [0:3]` for `typedef b_t [0:3] w_t;`. A reference that
/// carries dims keeps them for the chained walk instead.
pub(super) fn bare_typedef_step(
    dt: &DataType,
    typedef_types: &HashMap<String, DataType>,
) -> Option<DataType> {
    match dt {
        DataType::TypeReference {
            name, dimensions, ..
        } if dimensions.is_empty() => lookup_scoped_type(name, typedef_types).cloned(),
        _ => None,
    }
}

/// §6.18/§23.10: rename every bare `TypeReference` in `dt` that names one of
/// `local_names` to its instance-scoped form `"<prefix><name>"`. A typedef
/// stored under a scoped key still carried BARE member-type references, so a
/// param-dependent struct's members resolved against whichever same-named
/// typedef some OTHER instance registered last.
pub(super) fn scope_local_typerefs(
    dt: &DataType,
    local_names: &std::collections::HashSet<String>,
    prefix: &str,
) -> DataType {
    match dt {
        DataType::TypeReference {
            name,
            dimensions,
            type_args,
            span,
        } if name.scopes.is_empty() && local_names.contains(&name.name.name) => {
            let mut nn = name.clone();
            nn.name.name = cat2(&prefix, &name.name.name);
            DataType::TypeReference {
                name: nn,
                dimensions: dimensions.clone(),
                type_args: type_args.clone(),
                span: *span,
            }
        }
        DataType::Struct(su) => {
            let mut s2 = su.clone();
            for m in &mut s2.members {
                m.data_type = scope_local_typerefs(&m.data_type, local_names, prefix);
            }
            DataType::Struct(s2)
        }
        DataType::Enum(e) => {
            let mut e2 = e.clone();
            if let Some(b) = &e.base_type {
                e2.base_type = Some(Box::new(scope_local_typerefs(b, local_names, prefix)));
            }
            DataType::Enum(e2)
        }
        _ => dt.clone(),
    }
}

/// §6.20.3, §23.10: a type parameter override is written in the
/// instantiating body, so a typedef name in it is that body's. A non-top
/// body's typedefs outlive its inlining only under their instance-scoped keys
/// (`m.id_t`), so name the override's local typedefs (`local`, those of the
/// body at `prefix`) by those keys before resolving it. Left bare, the struct
/// `s_t { id_t id; ... }` of instance `m`, bound to a child's `T`, kept a
/// bare `id_t` member that resolved to nothing once `m`'s bare typedefs were
/// restored (a 32-bit `int`), and a child typedef of the same name captured
/// it while the child was inlined.
pub(super) fn scope_override_typerefs(
    dt: &DataType,
    local: &std::collections::HashSet<String>,
    prefix: &str,
    typedef_types: &HashMap<String, DataType>,
) -> DataType {
    if prefix.is_empty() || local.is_empty() || !names_local_typedef(dt, local) {
        return dt.clone();
    }
    let scoped: std::collections::HashSet<String> = local
        .iter()
        .filter(|n| typedef_types.contains_key(&cat2(prefix, n)))
        .cloned()
        .collect();
    scope_local_typerefs(dt, &scoped, prefix)
}

/// Whether `scope_local_typerefs` would change `dt`: it names a typedef the
/// instance declares itself, directly or in a member or an enum base.
fn names_local_typedef(dt: &DataType, local_names: &std::collections::HashSet<String>) -> bool {
    match dt {
        DataType::TypeReference { name, .. } => {
            name.scopes.is_empty() && local_names.contains(&name.name.name)
        }
        DataType::Struct(su) => su
            .members
            .iter()
            .any(|m| names_local_typedef(&m.data_type, local_names)),
        DataType::Enum(e) => e
            .base_type
            .as_ref()
            .is_some_and(|b| names_local_typedef(b, local_names)),
        _ => false,
    }
}

/// §6.8 (#721): the declared type a signal of an instance records. A type
/// that names no typedef of the instance reads the same for every instance
/// of the definition, so those signals share the definition's one copy; a
/// type that does is scoped to the instance and belongs to the signal.
pub(super) fn instance_decl_type(
    pool: &mut crate::decl_types::DeclTypeInterner,
    dt: &DataType,
    local_names: &std::collections::HashSet<String>,
    prefix: &str,
    owner: &str,
) -> Rc<DataType> {
    if names_local_typedef(dt, local_names) {
        Rc::new(scope_local_typerefs(dt, local_names, prefix))
    } else {
        pool.intern(dt, owner)
    }
}

/// §23.10: prefix a port-connection path whose ROOT names a sibling instance
/// of the module currently being inlined — see `sibling_inst_names` at the top
/// of `inline_module_items`.
pub(super) fn qualify_sibling_conn(
    path: String,
    prefix: &str,
    siblings: &std::collections::HashSet<String>,
) -> String {
    if prefix.is_empty() {
        return path;
    }
    let root = path.split(|c| c == '.' || c == '[').next().unwrap_or("");
    if siblings.contains(root) {
        cat2(&prefix, &path)
    } else {
        path
    }
}
