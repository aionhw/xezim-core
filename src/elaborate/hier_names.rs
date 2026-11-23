use super::*;

/// §10.11: the child's own `alias` statements, applied to the instance's
/// port connections.
///
/// An alias statement names ONE physical net. When the names it names are
/// the child's PORTS, the ports are one net, so the actuals they connect to
/// are one net too: every port of the group takes the FIRST port's actual.
/// (`shorter u(c1, c2)` with `alias p = q;` inside `shorter` makes `c1` and
/// `c2` one net — §10.11's "same physical net".)
///
/// A group member that is not a port is the child's own net; the group is
/// recorded for the unification pass, which merges it with the rest of the
/// group.
fn net_port_actual_name(expr: &Expression) -> Option<String> {
    if let Some(flat) = whole_net_ident_name(expr) {
        return Some(flat);
    }
    if let ExprKind::Index { expr: base, index } = &expr.kind
        && let Some(bn) = whole_net_ident_name(base)
        && let Some(idx) = const_eval_i64_with_params(index, None)
    {
        return Some(format!("{bn}[{idx}]"));
    }
    None
}

pub(super) fn apply_child_alias_groups(
    items: &[ModuleItem],
    inst_prefix: &str,
    port_map: &mut HashMap<String, Expression>,
    alias_groups: &mut Vec<Vec<String>>,
) {
    for item in items {
        let ModuleItem::AliasDecl(terms) = item else {
            continue;
        };
        let Ok(names) = alias_term_names(terms) else {
            continue;
        };
        // The child's OWN nets the statement names: they carry the instance
        // prefix (`u.x`), so the group stays inside the instance's scope.
        let mut group: Vec<String> = Vec::with_capacity(names.len());
        // The first group member that is a PORT carries the group's actual.
        let mut actual: Option<Expression> = None;
        // The actuals the group's PORTS connect to: they are the SAME net in
        // the parent, so they join a parent-scope group.
        let mut actuals: Vec<String> = Vec::new();
        for n in &names {
            if let Some(a) = port_map.get(n).cloned() {
                if let Some(flat) = net_port_actual_name(&a)
                    && !actuals.contains(&flat)
                {
                    actuals.push(flat);
                }
                match &actual {
                    None => actual = Some(a),
                    Some(first) => {
                        // Every port of the group is the same net: the
                        // second one takes the first one's actual.
                        if !same_expr(first, &a) {
                            port_map.insert(n.clone(), first.clone());
                        }
                    }
                }
            } else {
                group.push(cat2(inst_prefix, n));
            }
        }
        // When an alias joins child-local net(s) with port(s), bridge them
        // to the port's parent actual so they resolve and unify together.
        if !group.is_empty()
            && let Some(first_actual) = actuals.first()
            && !group.contains(first_actual)
        {
            group.push(first_actual.clone());
        }
        if group.len() > 1 {
            alias_groups.push(group);
        }
        // The group's actuals are one net in the parent: they join a
        // parent-scope group, so the unification pass merges them.
        if actuals.len() > 1 {
            alias_groups.push(actuals);
        }
    }
}

/// §10.11: the names an `alias` statement names, in the order written.
/// Only a WHOLE hierarchical identifier names a net here — a select, a
/// concatenation or any other expression names a PART of a net (§10.11's
/// `constant_select` is a bit-level overlay, handled elsewhere), so it is
/// left out and the caller rejects the statement.
pub(super) fn alias_term_names(terms: &[Expression]) -> Result<Vec<String>, ()> {
    let mut names = Vec::with_capacity(terms.len());
    for t in terms {
        let ExprKind::Ident(h) = &t.kind else {
            return Err(());
        };
        if !h.path.iter().all(|s| s.selects.is_empty()) {
            return Err(());
        }
        names.push(
            h.path
                .iter()
                .map(|s| s.name.name.as_str())
                .collect::<Vec<_>>()
                .join("."),
        );
    }
    Ok(names)
}

pub(super) fn make_ident_expr(name: &str) -> Expression {
    Expression::new(
        ExprKind::Ident(HierarchicalIdentifier {
            root: None,
            path: vec![HierPathSegment {
                name: Identifier {
                    name: name.to_string(),
                    span: Span::dummy(),
                },
                selects: Vec::new(),
            }],
            span: Span::dummy(),
            cached_signal_id: crate::ast::cache::SignalCache::new(None),
            cached_resolved_name: crate::ast::cache::NameCache::new(),
            bound: crate::ast::binding::Bound::UNSET,
        }),
        Span::dummy(),
    )
}

/// The dotted name of `expr` when it is a WHOLE net/variable reference — a plain
/// hierarchical identifier with no selects anywhere (`src_bus`, `u_a.q`). Returns
/// `None` for a bit-select, part-select, array index, concat, literal or any other
/// expression: those name a *part of* (or a *function of*) a net, not the net, and
/// must stay a distinct object in a dump.
/// Do these two selects denote the SAME constant range? Used to collapse a
/// redundant part-select stacked over an identical part-select connection;
/// anything non-constant, or a differently-bounded range, is left alone.
/// Do these two expressions evaluate to the SAME constant? Non-constant
/// operands never compare equal, so only provably redundant selects collapse.
pub(super) fn same_const_expr(a: &Expression, b: &Expression) -> bool {
    match (
        const_eval_i64_with_params(a, None),
        const_eval_i64_with_params(b, None),
    ) {
        (Some(x), Some(y)) => x == y,
        _ => false,
    }
}

/// Do two expressions name the same thing? Used to compare a port's actual
/// with another one: two idents with the same path are the same net.
fn same_expr(a: &Expression, b: &Expression) -> bool {
    fn flat(e: &Expression) -> Option<String> {
        match &e.kind {
            ExprKind::Ident(h) if h.path.iter().all(|s| s.selects.is_empty()) => Some(
                h.path
                    .iter()
                    .map(|s| s.name.name.as_str())
                    .collect::<Vec<_>>()
                    .join("."),
            ),
            _ => None,
        }
    }
    match (flat(a), flat(b)) {
        (Some(x), Some(y)) => x == y,
        _ => false,
    }
}

pub(super) fn same_const_range(a: &Expression, b: &Expression) -> bool {    let bounds = |e: &Expression| -> Option<(i64, i64)> {
        if let ExprKind::Range(l, r) = &e.kind {
            Some((
                const_eval_i64_with_params(l, None)?,
                const_eval_i64_with_params(r, None)?,
            ))
        } else {
            None
        }
    };
    match (bounds(a), bounds(b)) {
        (Some(x), Some(y)) => x == y,
        _ => false,
    }
}

pub(super) fn whole_net_ident_name(expr: &Expression) -> Option<String> {
    match &expr.kind {
        ExprKind::Ident(hier) => {
            // Root-TOLERANT on purpose: a rooted whole-net ident (a substituted
            // actual whose name collided with a child declaration — see
            // `rewrite_expr_impl`) is still the same physical net under the
            // same absolute name, and `port_aliases` / interface paths must
            // keep collapsing it. Rooting only changes RESOLUTION, not
            // identity.
            if hier.path.is_empty() {
                return None;
            }
            if hier.path.iter().any(|s| !s.selects.is_empty()) {
                return None;
            }
            Some(
                hier.path
                    .iter()
                    .map(|s| s.name.name.as_str())
                    .collect::<Vec<_>>()
                    .join("."),
            )
        }
        _ => None,
    }
}

/// §27.4, §27.6: a hierarchical path that names a net INSIDE an indexed
/// scope (`g[1].w`) denotes that WHOLE net — the `[1]` selects a
/// generate-block INSTANCE (§27.6), not a bit of a vector and not an element
/// of an unpacked array. `w[3]` names a bit of `w` and `arr[2]` an element of
/// an unpacked array; those are different objects and get no alias.
///
/// The scope-indexed flat name is built from the path itself; whether it
/// names a real net is decided by the caller, which looks the name up in
/// the elaborated tables.
fn scope_indexed_flat_name(expr: &Expression, elab: &ElaboratedModule) -> Option<String> {
    scope_indexed_flat_name_params(expr, &elab.parameters)
}

/// `scope_indexed_flat_name` with the parameter table it needs to fold the
/// constant index of an indexed scope.
pub(super) fn scope_indexed_flat_name_params(
    expr: &Expression,
    params: &HashMap<String, Value>,
) -> Option<String> {
    match &expr.kind {
        // A bare scope name: the base of an indexed scope.
        ExprKind::Ident(h) => {
            let mut flat = String::new();
            for seg in &h.path {
                if !flat.is_empty() {
                    flat.push('.');
                }
                flat.push_str(&seg.name.name);
                for index in &seg.selects {
                    let idx = const_eval_i64_with_params(index, Some(params))?;
                    use std::fmt::Write;
                    write!(&mut flat, "[{idx}]").ok()?;
                }
            }
            (!flat.is_empty()).then_some(flat)
        }
        ExprKind::Index { expr: base, index } => {
            let prefix = scope_indexed_flat_name_params(base, params)?;
            let idx = const_eval_i64_with_params(index, Some(params))?;
            Some(format!("{prefix}[{idx}]"))
        }
        ExprKind::MemberAccess { expr: base, member } => {
            let prefix = scope_indexed_flat_name_params(base, params)?;
            Some(format!("{prefix}.{}", member.name))
        }
        _ => None,
    }
}

/// The flat, absolute name of a NET reached through an indexed scope
/// (`g[1].w`), or `None` when the path names no net.
///
/// `prefix` is the scope the path was written in: a path whose head is a
/// scope of that scope (`g[1].w` inside `mid`) names `mid.g[1].w`, while a
/// path that already reaches outside it keeps its own name. The candidate
/// names are looked up in the elaborated tables, so only a name that really
/// exists is accepted — an interface instance's member (`k.g[1].w`, whose
/// flat name depends on the binding) and an unpacked array element are not
/// there and are left alone.
pub(super) fn scope_indexed_net_name(
    expr: &Expression,
    prefix: &str,
    elab: &ElaboratedModule,
) -> Option<String> {
    if !path_has_index_step(expr) || !scope_index_selects_scopes(expr, elab) {
        return None;
    }
    let rel = scope_indexed_flat_name(expr, elab)?;
    let scoped = cat2(prefix, &rel);
    if is_net_name(elab, &scoped) {
        return Some(scoped);
    }
    if is_net_name(elab, &rel) {
        return Some(rel);
    }
    None
}

/// Is `name` a net — a wire-like declaration, or a net of a user-defined
/// nettype (§6.6.7), which permits several drivers just like a wire?
pub(super) fn is_net_name(elab: &ElaboratedModule, name: &str) -> bool {
    if elab.nets.contains(name) {
        return true;
    }
    elab.signals.get(name).is_some_and(|s| {
        s.type_name.as_deref().is_some_and(|t| {
            elab.nettype_resolvers.contains_key(t) && !elab.shadowed_nettypes.contains(t)
        })
    })
}

/// §6.6.7: the user-defined nettype a declaration of type `dt` declares a
/// net of, by the nettype's registry key. A type name the module hides with
/// its own typedef, class or type parameter names that declaration instead
/// (§6.18, §26.3, §26.5), so the object is a variable.
pub(super) fn declared_user_nettype(elab: &ElaboratedModule, dt: &DataType) -> Option<String> {
    let DataType::TypeReference { name, .. } = dt else {
        return None;
    };
    let bare = &name.name.name;
    let key = match name.scopes.as_slice() {
        [] if elab.shadowed_nettypes.contains(bare) => return None,
        [] => bare.clone(),
        [pkg] => format!("{}::{}", pkg.name.name, bare),
        _ => return None,
    };
    elab.nettype_resolvers.contains_key(&key).then_some(key)
}

/// The user-defined nettype (§6.6.7) `name` is declared with, if any: its
/// signal's type name, or the declared type of a nettype net over an
/// unpacked struct, which is stored as member leaves with no signal of its
/// own.
pub(super) fn user_nettype_of(elab: &ElaboratedModule, name: &str) -> Option<String> {
    let tn = match elab.signals.get(name) {
        Some(s) => s.type_name.clone(),
        None => elab.var_decl_types.get(name).and_then(get_type_name),
    }?;
    elab.nettype_resolvers.contains_key(&tn).then_some(tn)
}

/// The head name of a hierarchical path expression — `g[1].w` names the
/// scope `g`, `a.b.c` names `a`. `None` for anything that is not a path.
pub(super) fn path_head_name(expr: &Expression) -> Option<String> {
    match &expr.kind {
        ExprKind::Ident(h) => h.path.first().map(|s| s.name.name.clone()),
        ExprKind::Index { expr, .. } | ExprKind::MemberAccess { expr, .. } => path_head_name(expr),
        _ => None,
    }
}

/// `whole_net_ident_name`, extended to a net reached through an indexed
/// SCOPE (`g[1].w`). A port actual that names such a net connects the port
/// to that net, so the formal and the actual are ONE physical net and their
/// drivers resolve together (§23.3.3.7, Table 23-1).
pub(super) fn whole_net_ident_name_scoped(
    expr: &Expression,
    elab: &ElaboratedModule,
) -> Option<String> {
    if let Some(n) = whole_net_ident_name(expr) {
        return Some(n);
    }
    if !path_has_index_step(expr) || !scope_index_selects_scopes(expr, elab) {
        return None;
    }
    let flat = scope_indexed_flat_name(expr, elab)?;
    is_net_name(elab, &flat).then_some(flat)
}

/// Does the path contain an index step at all? A plain hierarchical name
/// (`a.b.c`) names no scope instance, so it is never rewritten into a
/// scope-indexed flat name — its own segments already are the path.
fn path_has_index_step(expr: &Expression) -> bool {
    match &expr.kind {
        ExprKind::Ident(h) => h.path.iter().any(|s| !s.selects.is_empty()),
        ExprKind::Index { .. } => true,
        ExprKind::MemberAccess { expr: base, .. } => path_has_index_step(base),
        _ => false,
    }
}

/// §27.6 vs §7.4.2: an index in a path selects a SCOPE INSTANCE when it
/// names a generate block (`g[1].w` is the net `w` inside the scope `g[1]`),
/// and an ARRAY ELEMENT when it names an unpacked array (`arr[2]` is the
/// second element of `arr`, a separate object with its own drivers). Only
/// the former can name a whole net.
fn scope_index_selects_scopes(expr: &Expression, elab: &ElaboratedModule) -> bool {
    match &expr.kind {
        ExprKind::Ident(h) => match h.path.first() {
            Some(first) => !is_unpacked_array_name(elab, &first.name.name),
            None => true,
        },
        ExprKind::Index { expr: base, .. } | ExprKind::MemberAccess { expr: base, .. } => {
            scope_index_selects_scopes(base, elab)
        }
        _ => true,
    }
}

/// Is `name` an unpacked array in the elaborated tables? Such a name
/// selects ELEMENTS (§7.4.2), not scope instances (§27.6).
pub(super) fn is_unpacked_array_name(elab: &ElaboratedModule, name: &str) -> bool {
    elab.arrays.contains_key(name)
        || elab.arrays_2d.contains_key(name)
        || elab.arrays_nd.contains_key(name)
}

/// The base interconnect name of an ELEMENT select (`iBus[1]`, `m.ic[2]`) —
/// used to shape a typeless `interconnect` ARRAY from a typed ELEMENT that
/// drives (or reads) a single member. `whole_net_ident_name` deliberately
/// returns None for an index/select because a select is a separate object;
/// here the SIZE/realness has to live on the base array net itself.
pub(super) fn interconnect_array_base_name(expr: &Expression) -> Option<String> {
    match &expr.kind {
        ExprKind::Index { expr: base, .. } | ExprKind::RangeSelect { expr: base, .. } => {
            whole_net_ident_name(base)
        }
        _ => None,
    }
}

/// §23.3.3.7, Table 23-1: a tri0 or tri1 port bound to a bit or part select
/// of a `wire` makes those bits of the merged net tri0/tri1, while the
/// vector's other bits stay a `wire`. The implicit pull (§6.6.5) of the
/// selected bits is a pull-strength driver of that select, which the
/// multi-driver fold resolves against the bits' other drivers. `None` for any
/// other formal or actual, and for an external net with a type of its own.
pub(super) fn tri_port_select_pull(
    actual: &Expression,
    formal: &str,
    elab: &mut ElaboratedModule,
) -> Option<ContinuousAssignment> {
    let one = match elab.resolved_net_kinds.get(formal)? {
        ResolvedNetKind::Tri0 => false,
        ResolvedNetKind::Tri1 => true,
        _ => return None,
    };
    if !matches!(
        actual.kind,
        ExprKind::Index { .. } | ExprKind::RangeSelect { .. }
    ) {
        return None;
    }
    let (net, lo, hi) = cont_assign_net_span(actual, elab, None)?;
    if elab.arrays.contains_key(&net)
        || elab.resolved_net_kinds.contains_key(&net)
        || elab.supply_nets.contains(&net)
        || elab.signals.get(&net).is_none_or(|s| s.is_real)
        || (lo..=hi).any(|b| elab.tri_select_pulls.contains(&(net.clone(), b)))
    {
        return None;
    }
    for b in lo..=hi {
        elab.tri_select_pulls.insert((net.clone(), b));
    }
    let span = actual.span;
    Some(ContinuousAssignment {
        delay_select: None,
        origin: None,
        lhs: actual.clone(),
        rhs: make_syscall(
            "$__pull",
            vec![
                make_fill_expr(one, span),
                strength_code_literal(5 * 8 + 5, span),
            ],
            span,
        ),
        delay: 0,
        rhs_parent_scoped: false,
        delay_fall: None,
        delay_off: None,
        gate_delay_fall: None,
        delay_exprs: None,
    })
}

/// A continuous assign whose LHS names a HIERARCHICAL target writes into a
/// foreign scope, but its RHS names are lexical to the WRITING scope. The
/// simulator infers a resolution hint from the write target, so a bare RHS
/// name colliding with a net INSIDE the target scope resolved target-first:
/// a TB `assign dut.deep.rst_in = grst_l` silently read the DUT's own dead
/// `grst_l` and forwarded x forever (while a sibling clock assign whose RHS
/// had no deep twin worked — the asymmetry that hid this). Root-mark the
/// RHS so its names resolve absolutely (top-level lexical names ARE the
/// absolute names); anything unresolvable falls through to the normal path.
///
/// `is_struct` tells whether a FIRST-IDENTIFIER name is a struct-typed data
/// variable (a member access on it is a record read, NOT a scope descent; the
/// netlist registers module instances as signals typed by their definition
/// name, which never appears here). A continuous assign whose LHS passes
/// through a member-access on a NON-struct base targets a foreign (instance /
/// generate) scope, whose RHS names are lexical to the WRITING scope — so
/// they must be rooted. This is the `assign l.n = n`/`assign bif.vec = ~vec`/
/// `assign ga[0].lpg.v = ~v` form that parsed as a bare-ident MemberAccess
/// and was invisible to the multi-segment check. A struct-member write
/// (`assign s.b = x`) leaves the first identifier a struct, so it stays
/// un-rooted (its RHS is the same scope).
pub(super) fn root_mark_hier_ca_rhs(
    lhs: &Expression,
    rhs: &mut Expression,
    is_struct: &dyn Fn(&str) -> bool,
    is_package: &dyn Fn(&str) -> bool,
) {
    /// `crossed_member` tracks whether the LHS reached the first identifier
    /// THROUGH a member access (`a.b`, `gen[0].sig`). A bare index (`arr[2]`)
    /// writes a data element, not a scope, and must never root its RHS.
    fn hier_lhs(e: &Expression, is_struct: &dyn Fn(&str) -> bool, crossed_member: bool) -> bool {
        match &e.kind {
            ExprKind::Ident(h) => {
                h.path.len() > 1
                    || h.path.first().is_some_and(|s| s.name.name.contains('.'))
                    // A member access on a bare identifier that is NOT a
                    // struct variable reaches into an instance / generate
                    // scope, so the RHS is the writer's scope.
                    || (crossed_member
                        && h.path.first().is_some_and(|s| !is_struct(&s.name.name)))
            }
            // `tb.uut.u_core.sig = x` parses the LHS as a MemberAccess chain,
            // not a multi-segment Ident.
            ExprKind::MemberAccess { expr, .. } => hier_lhs(expr, is_struct, true),
            ExprKind::Index { expr, .. } | ExprKind::RangeSelect { expr, .. } => {
                hier_lhs(expr, is_struct, crossed_member)
            }
            _ => false,
        }
    }
    if hier_lhs(lhs, is_struct, false) {
        mark_actual_rooted(rhs, is_package);
    }
}

pub fn rewrite_expr(
    expr: &Expression,
    prefix: &str,
    port_map: &HashMap<String, Expression>,
    local_names: &std::collections::HashSet<String>,
    interface_map: &HashMap<String, String>,
) -> Expression {
    rewrite_expr_impl(expr, prefix, port_map, local_names, interface_map)
}

/// §23.8 (upward name referencing) for a hierarchical name in an inlined body
/// whose first segment names none of the body's own declarations (not a
/// local, a port, an interface port or a package). The first segment is
/// looked for as a SCOPE NAME, starting at the instance the body belongs to
/// and walking up one enclosing scope at a time, until the top module:
///   a) a scope the current design element declares anywhere (a child
///      instance of any generate branch, a generate or block label, a
///      subroutine) makes it a downward reference, which the ordinary
///      scope-relative resolution already handles — left alone;
///   b) in each enclosing scope `p`: the DEFINITION name of `p`'s own
///      instance (`node1.req1` from a module bound into `u_node1`, an
///      instance of `node1`, is the nearest enclosing instance of that
///      module — it wins over a same-named instance further up), then a
///      child instance of `p` by its INSTANCE name, then a generate or block
///      label `p` declares. A module name that is not an ancestor's (a
///      sibling's) matches nothing, as in the reference simulator.
/// The hit is rewritten to the matched scope's absolute path and rooted, so
/// the simulator resolves it exactly there instead of guessing from a
/// scope hint: the earlier runtime-only search bound `node1.req1` to a
/// same-named signal of the top module (#890). A head that names nothing
/// (the top module's own name, `$root`, a `$unit` variable) is left as it
/// was.
pub(super) fn upward_scope_rewrite(
    hier: &HierarchicalIdentifier,
    prefix: &str,
) -> Option<ExprKind> {
    if hier.root.is_some() || hier.path.len() < 2 || !hier.path[0].selects.is_empty() {
        return None;
    }
    let head = hier.path[0].name.name.as_str();
    if head.contains(['.', ':', '$']) || stmt_local_declared(head) {
        return None;
    }
    let scopes = UPWARD_SCOPES_TLS.with(|c| c.borrow().clone())?;
    let scopes = scopes.borrow();
    if scopes.packages.contains(head) {
        return None;
    }
    let declares = |p: &str| -> bool {
        scopes
            .defs
            .get(p)
            .and_then(|d| scopes.declared.get(&**d))
            .is_some_and(|names| names.contains(head))
    };
    let child_named = |p: &str| scopes.child_named(p, head);
    let cur = prefix.trim_end_matches('.');
    // Step a: the current design element's own scopes are downward.
    if declares(cur) || child_named(cur).is_some() {
        return None;
    }
    let mut p = cur;
    // The matched scope and what replaces the head below it: nothing when
    // the head named `p`'s module, the child's name, or the label itself.
    let hit: Option<(&str, Option<&str>)> = loop {
        if !p.is_empty() && scopes.defs.get(p).is_some_and(|d| &**d == head) {
            break Some((p, None));
        }
        if p != cur {
            if let Some(leaf) = child_named(p) {
                break Some((p, Some(leaf)));
            }
            if declares(p) {
                break Some((p, Some(head)));
            }
        }
        if p.is_empty() {
            break None;
        }
        p = p.rsplit_once('.').map_or("", |(parent, _)| parent);
    };
    let (scope, below) = hit?;
    let mut new_hier = hier.clone();
    let template = HierPathSegment {
        name: new_hier.path[0].name.clone(),
        selects: Vec::new(),
    };
    let segment = |name: &str| {
        let mut s = template.clone();
        s.name.name = name.to_string();
        s
    };
    let mut path: Vec<HierPathSegment> = Vec::with_capacity(hier.path.len() + 4);
    if !scope.is_empty() {
        path.extend(scope.split('.').map(segment));
    }
    path.extend(below.map(segment));
    path.extend(new_hier.path.drain(1..));
    new_hier.path = path;
    new_hier.root = Some("$root".to_string());
    new_hier.cached_signal_id = crate::ast::cache::SignalCache::new(None);
    new_hier.cached_resolved_name = crate::ast::cache::NameCache::new();
    Some(ExprKind::Ident(new_hier))
}

/// §23.8.1: the key of the subroutine a bare name the binder left to the
/// hierarchy (`Bound::UPWARD`) calls from the instance at `prefix`, when it
/// differs from the name.
pub(super) fn upward_subroutine_key(hier: &HierarchicalIdentifier, prefix: &str) -> Option<String> {
    if !hier.bound.is_upward() || hier.path.len() != 1 || !hier.path[0].selects.is_empty() {
        return None;
    }
    let scopes = UPWARD_SCOPES_TLS.with(|c| c.borrow().clone())?;
    let scopes = scopes.borrow();
    let name = hier.path[0].name.name.as_str();
    let inst = prefix.trim_end_matches('.');
    let key = scopes.subroutine_key(inst, name)?;
    if bind::audit_enabled() {
        let def = scopes.parents.get(inst).map_or("", |up| &*up.def);
        eprintln!(
            "[bind-audit] upward {} {name} in {inst} -> {key}",
            audit_location(def, hier.span)
        );
    }
    (key != name).then_some(key)
}

/// §23.8 / §23.10.1: a port actual `dut.gclk_a` whose first segment names
/// no local, port, interface or child instance of the current scope but IS
/// the definition name of an enclosing instance (the harness is bound into
/// `dut`, instantiated as `t.u_dut`) refers to that instance. The runtime
/// resolves such a name in a statement by its upward search, but an
/// actual is bound at elaboration, so rewrite it to the instance's path and
/// root it; the simulator then resolves it absolutely. Instance names take
/// precedence over definition names (§23.8), and the top module itself is
/// left to the existing absolute-path handling.
pub(super) fn resolve_upward_module_name(
    e: &mut Expression,
    local_names: &std::collections::HashSet<String>,
    port_map: &HashMap<String, Expression>,
    interface_map: &HashMap<String, String>,
    elab: &ElaboratedModule,
) {
    let ExprKind::Ident(h) = &mut e.kind else {
        return;
    };
    if h.root.is_some() || h.path.len() < 2 || !h.path[0].selects.is_empty() {
        return;
    }
    let head = h.path[0].name.name.clone();
    if local_names.contains(&head)
        || port_map.contains_key(&head)
        || interface_map.contains_key(&head)
        || elab.packages.contains(&head)
    {
        return;
    }
    let chain: Vec<(String, String)> = INLINE_CHAIN_TLS.with(|c| c.borrow().clone());
    // The current scope's own child instances shadow definition names.
    let current = chain.last().map(|(p, _)| p.clone()).unwrap_or_default();
    let child = cat2(&current, &head);
    if elab.instances.iter().any(|i| i.path == child) {
        return;
    }
    let Some((inst_prefix, _)) = chain
        .iter()
        .rev()
        .find(|(p, d)| !p.is_empty() && *d == head)
    else {
        return;
    };
    let segs: Vec<&str> = inst_prefix.trim_end_matches('.').split('.').collect();
    let first = h.path.remove(0);
    for (i, seg) in segs.iter().enumerate() {
        let mut s = first.clone();
        s.name.name = (*seg).to_string();
        h.path.insert(i, s);
    }
    h.root = Some("$root".to_string());
}

/// Mark every identifier in an EXPRESSION port actual as parent-rooted
/// (`root = Some("$root")`). The actual's names were rewritten in the parent's
/// context; once the expression is pasted into the CHILD's body by port-map
/// substitution, its bare idents would otherwise re-resolve child-first under
/// the child's scope hint — `.d(d ^ 1)` with a child port also named `d` read
/// the child's own `u1.d` and applied the map to its own output (issue #48).
/// A rooted ident is skipped by `rewrite_expr_impl` (no re-prefixing, no
/// re-substitution) and resolved absolutely by the simulator. A package
/// member (`pkg::member`, §26.3) names no scope path and stays unrooted.
pub(super) fn mark_actual_rooted(e: &mut Expression, is_package: &dyn Fn(&str) -> bool) {
    match &mut e.kind {
        ExprKind::Ident(h) => {
            if h.root.is_none() && !(h.path.len() > 1 && is_package(&h.path[0].name.name)) {
                h.root = Some("$root".to_string());
            }
            for seg in &mut h.path {
                for sel in &mut seg.selects {
                    mark_actual_rooted(sel, is_package);
                }
            }
        }
        ExprKind::Binary { left, right, .. } => {
            mark_actual_rooted(left, is_package);
            mark_actual_rooted(right, is_package);
        }
        ExprKind::Unary { operand, .. } => mark_actual_rooted(operand, is_package),
        ExprKind::Conditional {
            condition,
            then_expr,
            else_expr,
        } => {
            mark_actual_rooted(condition, is_package);
            mark_actual_rooted(then_expr, is_package);
            mark_actual_rooted(else_expr, is_package);
        }
        ExprKind::Paren(inner) => mark_actual_rooted(inner, is_package),
        ExprKind::Concatenation(parts) => {
            for p in parts {
                mark_actual_rooted(p, is_package);
            }
        }
        ExprKind::Replication { count, exprs } => {
            mark_actual_rooted(count, is_package);
            for p in exprs {
                mark_actual_rooted(p, is_package);
            }
        }
        ExprKind::Call { func, args } => {
            // The callee name is not a net reference — leave it resolvable
            // through the normal function tables; its selects/args are values.
            if let ExprKind::Ident(h) = &mut func.kind {
                for seg in &mut h.path {
                    for sel in &mut seg.selects {
                        mark_actual_rooted(sel, is_package);
                    }
                }
            } else {
                mark_actual_rooted(func, is_package);
            }
            for a in args {
                mark_actual_rooted(a, is_package);
            }
        }
        ExprKind::SystemCall { args, .. } => {
            for a in args {
                mark_actual_rooted(a, is_package);
            }
        }
        ExprKind::Index { expr, index } => {
            mark_actual_rooted(expr, is_package);
            mark_actual_rooted(index, is_package);
        }
        ExprKind::RangeSelect {
            expr, left, right, ..
        } => {
            mark_actual_rooted(expr, is_package);
            mark_actual_rooted(left, is_package);
            mark_actual_rooted(right, is_package);
        }
        ExprKind::MemberAccess { expr, .. } => {
            if !matches!(&expr.kind, ExprKind::Ident(h)
                if h.path.len() == 1 && is_package(&h.path[0].name.name))
            {
                mark_actual_rooted(expr, is_package);
            }
        }
        _ => {}
    }
}
