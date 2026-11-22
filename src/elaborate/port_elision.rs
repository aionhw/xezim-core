use super::*;

/// Unobserved-port elision. Inlining substitutes an input port's actual for
/// every read inside the child (see `rewrite_port_map`), yet it still built
/// the port's own net and the connection assign `<inst>.<port> = actual`
/// that keeps it current. Nothing in the child reads that net any more, so
/// in a design with nothing that can reach it BY NAME it is dead weight: on
/// a bit-cell array it was one scattered single-bit write per cell for
/// every change of the shared actual, and half of the signal table.
///
/// The elaborator cannot see every name observer alone — a waveform dump,
/// a VPI or DPI library, an SDF file or a library caller inspecting signals
/// after the run are decided by whoever drives it — so this is OFF unless
/// the driver switches it on after ruling those out. What the sources
/// themselves can reach is decided here: see `port_elision_setup` and
/// `port_elision_blocked_by_items`.
static PORT_ELISION: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// Allow [`inline_instantiations`] to leave out the nets of substituted input
/// ports that nothing in the sources can reach by name. Only a driver that
/// has ruled out every run-time name observer may turn this on: waveform
/// dumps, VPI/DPI libraries, SDF/UPF annotation, coverage, x-warnings,
/// artifacts written for later runs, and API callers that look signals up
/// after the run.
pub fn set_port_elision(on: bool) {
    PORT_ELISION.store(on, std::sync::atomic::Ordering::Relaxed);
}

/// Whether [`set_port_elision`] is on.
pub fn port_elision_requested() -> bool {
    PORT_ELISION.load(std::sync::atomic::Ordering::Relaxed)
}

/// The hash recorded in `ElaboratedModule::elided_port_hashes` for a flat
/// signal name (64-bit FNV-1a; stable across builds).
pub fn elided_port_hash(name: &str) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in name.bytes() {
        h ^= b as u64;
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

thread_local! {
    /// Per-elaboration elision state, set by `port_elision_setup`: `None`
    /// when elision is off for this design, else the names a port must not
    /// carry to be left out: every name written after a `.`, and every name
    /// spelled in class, package or compilation-unit code (see
    /// `sv_parser::ReferenceCensus`).
    pub(super) static PORT_ELISION_DOTTED: std::cell::RefCell<Option<Rc<crate::sv_parser::CensusSet>>> =
        const { std::cell::RefCell::new(None) };
}

/// System tasks that reach nets by a string or a scope walk rather than by
/// an expression the inliner rewrites: waveform dumps (the scope form walks
/// every net under an instance), SDF annotation (names instance ports),
/// signal spies and string-keyed forces, and the interactive listing tasks.
fn systask_observes_by_name(name: &str) -> bool {
    const PREFIXES: [&str; 9] = [
        "$dump",
        "$fsdb",
        "$vcdplus",
        "$shm_",
        "$record",
        "$sdf",
        "$init_signal",
        "$signal_",
        "$hdl_",
    ];
    PREFIXES.iter().any(|p| name.starts_with(p))
        || matches!(
            name,
            "$showvars" | "$showscopes" | "$list" | "$scope" | "$toggle_start" | "$toggle_report"
        )
}

/// Decide, once per elaboration, whether port elision applies to this
/// design, and publish the dotted-name census the per-port test uses.
pub(super) fn port_elision_setup() {
    let state = if port_elision_requested() {
        let census = crate::sv_parser::reference_census();
        let blocked = census.dpi
            || census
                .system_names
                .iter()
                .any(|n| systask_observes_by_name(n));
        (!blocked).then(|| {
            let mut names = census.dotted;
            names.extend(census.unit_idents);
            Rc::new(names)
        })
    } else {
        None
    };
    PORT_ELISION_DOTTED.with(|d| *d.borrow_mut() = state);
}

/// Module items that can reach a port's own net without going through the
/// substituted actual: class bodies are not rewritten into the instance at
/// all, a clocking block falls back to the formal's net for an expression
/// actual, `let`/checker bodies expand late, specify blocks and SDF name the
/// ports themselves, a UDP instance's terminals and a checker instance's
/// actuals are resolved WITHOUT the port substitution (`plain_inst` says
/// false for those), and `alias`/nested modules/`bind` are rare enough to
/// keep out of the analysis. A module carrying any of them keeps every port.
pub(super) fn port_elision_blocked_by_items(
    items: &[ModuleItem],
    plain_inst: &dyn Fn(&str) -> bool,
) -> bool {
    items.iter().any(|it| match it {
        ModuleItem::ClassDeclaration(_)
        | ModuleItem::ClockingDeclaration(_)
        | ModuleItem::CheckerDeclaration(_)
        | ModuleItem::LetDeclaration(_)
        | ModuleItem::SpecifyBlock(_)
        | ModuleItem::AliasDecl(_)
        | ModuleItem::NestedModule(_)
        | ModuleItem::Bind(_)
        | ModuleItem::DPIImport(_)
        | ModuleItem::DPIExport(_)
        | ModuleItem::NettypeDeclaration(_) => true,
        ModuleItem::ModuleInstantiation(mi) => !plain_inst(&mi.module_name.name),
        ModuleItem::GenerateRegion(g) => port_elision_blocked_by_items(&g.items, plain_inst),
        ModuleItem::GenerateIf(g) => g
            .branches
            .iter()
            .any(|(_, items)| port_elision_blocked_by_items(items, plain_inst)),
        ModuleItem::GenerateFor(g) => port_elision_blocked_by_items(&g.items, plain_inst),
        ModuleItem::GenerateCase(g) => g
            .arms
            .iter()
            .any(|a| port_elision_blocked_by_items(&a.items, plain_inst)),
        _ => false,
    })
}

/// Drop every trace of an elided port's net from the name-keyed tables its
/// declaration and connection filled, and record it for the simulator's
/// lookup check.
pub(super) fn forget_elided_port(elab: &mut ElaboratedModule, name: &str, leaf: &str, track: bool) {
    elab.signals.remove(name);
    unregister_net_type(elab, name);
    elab.port_aliases.remove(name);
    elab.packed_full_dims.remove(name);
    elab.packed_signal_elem_widths.remove(name);
    elab.var_decl_types.remove(name);
    elab.two_state_signals.remove(name);
    elab.z_init_signals.remove(name);
    elab.decl_sites.remove(name);
    elab.net_strengths.remove(name);
    elab.elided_port_count += 1;
    if track {
        elab.elided_port_hashes.push(elided_port_hash(name));
    }
    if !elab.elided_port_leaves.contains(leaf) {
        elab.elided_port_leaves.insert(leaf.to_string());
    }
}

/// Port `pname` of `sub_mod` is declared as a plain scalar, vector or real
/// net/variable: no struct, enum, typedef or interface type, no unpacked or
/// multi-dimensional packed shape, no default, and a plain-wire net kind.
/// Only such a port's net carries nothing but the value the connection
/// copies into it, which is what makes leaving it out invisible.
pub(super) fn port_decl_is_plain(sub_mod: &Definition, items: &[ModuleItem], pname: &str) -> bool {
    fn plain_type(dt: Option<&DataType>) -> bool {
        match dt {
            None => true,
            Some(DataType::IntegerVector { dimensions, .. })
            | Some(DataType::Implicit { dimensions, .. }) => dimensions.len() <= 1,
            Some(DataType::IntegerAtom { .. }) | Some(DataType::Real { .. }) => true,
            _ => false,
        }
    }
    fn plain_net(nt: Option<NetType>) -> bool {
        matches!(
            nt,
            None | Some(NetType::Wire | NetType::Tri | NetType::Uwire)
        )
    }
    match sub_mod.ports() {
        PortList::Ansi(ps) => ps.iter().find(|p| p.name.name == pname).is_some_and(|p| {
            p.dimensions.is_empty()
                && p.default.is_none()
                && plain_net(p.net_type)
                && plain_type(p.data_type.as_ref())
        }),
        PortList::NonAnsi(_) => {
            let mut declared = false;
            for it in items {
                match it {
                    ModuleItem::PortDeclaration(pd) => {
                        for d in pd.declarators.iter().filter(|d| d.name.name == pname) {
                            if !d.dimensions.is_empty()
                                || d.init.is_some()
                                || !plain_net(pd.net_type)
                                || !plain_type(Some(&pd.data_type))
                            {
                                return false;
                            }
                            declared = true;
                        }
                    }
                    ModuleItem::NetDeclaration(nd) => {
                        if nd.declarators.iter().any(|d| {
                            d.name.name == pname
                                && (!d.dimensions.is_empty()
                                    || d.init.is_some()
                                    || nd.delay.is_some()
                                    || nd.strength.is_some()
                                    || !plain_net(Some(nd.net_type))
                                    || !plain_type(Some(&nd.data_type)))
                        }) {
                            return false;
                        }
                    }
                    ModuleItem::DataDeclaration(dd) => {
                        if dd.declarators.iter().any(|d| {
                            d.name.name == pname
                                && (!d.dimensions.is_empty()
                                    || d.init.is_some()
                                    || !plain_type(Some(&dd.data_type)))
                        }) {
                            return false;
                        }
                    }
                    _ => {}
                }
            }
            declared
        }
        PortList::Empty => false,
    }
}

/// A port actual that only NAMES storage: a net or variable, a constant bit
/// or part select of one, a literal, or a concatenation/replication of those.
/// Anything that computes (an operator, a call, a select with a run-time
/// index) is not simple.
pub(super) fn port_actual_is_simple(
    e: &Expression,
    params: &HashMap<String, Value>,
    global: &HashMap<String, Value>,
) -> bool {
    let konst = |x: &Expression| is_const_expr(x, params) || is_const_expr(x, global);
    match &e.kind {
        ExprKind::Number(_) | ExprKind::StringLiteral(_) => true,
        ExprKind::Ident(h) => h.path.iter().all(|seg| {
            seg.selects.iter().all(|sel| match &sel.kind {
                ExprKind::Range(l, r) => konst(l) && konst(r),
                _ => konst(sel),
            })
        }),
        ExprKind::Paren(inner) => port_actual_is_simple(inner, params, global),
        ExprKind::Index { expr, index } => {
            port_actual_is_simple(expr, params, global) && konst(index)
        }
        ExprKind::RangeSelect {
            expr, left, right, ..
        } => port_actual_is_simple(expr, params, global) && konst(left) && konst(right),
        ExprKind::MemberAccess { expr, .. } => port_actual_is_simple(expr, params, global),
        ExprKind::Concatenation(parts) => parts
            .iter()
            .all(|p| port_actual_is_simple(p, params, global)),
        ExprKind::Replication { count, exprs } => {
            konst(count)
                && exprs
                    .iter()
                    .all(|p| port_actual_is_simple(p, params, global))
        }
        _ => false,
    }
}

/// §11.8.1: whether a port actual that `port_actual_is_simple` accepts is a
/// signed expression. A part-select, a bit-select of a vector, a
/// concatenation and a replication are unsigned; a whole net or parameter
/// and a literal keep their own signedness, as does a package parameter
/// (`p::V`, §26.3), which is bound under its scoped name. `None` when it
/// cannot tell (an element of an unpacked array, a struct member).
pub(super) fn simple_actual_signedness(
    e: &Expression,
    elab: &ElaboratedModule,
    params: &HashMap<String, Value>,
) -> Option<bool> {
    let lookup = |name: &str| {
        elab.signals.get(name).map(|sig| sig.is_signed).or_else(|| {
            params
                .get(name)
                .or_else(|| elab.parameters.get(name))
                .map(|v| v.is_signed)
        })
    };
    match &e.kind {
        ExprKind::Paren(inner) => simple_actual_signedness(inner, elab, params),
        ExprKind::Number(NumberLiteral::Integer {
            size, signed, base, ..
        }) => Some(*signed || (size.is_none() && matches!(base, NumberBase::Decimal))),
        ExprKind::Number(NumberLiteral::UnbasedUnsized(_)) | ExprKind::StringLiteral(_) => {
            Some(false)
        }
        ExprKind::Ident(h) => {
            if let Some(name) = whole_net_ident_name(e) {
                return lookup(&name).or_else(|| match h.path.as_slice() {
                    [pkg, member] if elab.packages.contains(&pkg.name.name) => {
                        lookup(&format!("{}::{}", pkg.name.name, member.name.name))
                    }
                    _ => None,
                });
            }
            // A select in the name: a bit- or part-select of a packed vector
            // is unsigned; an element of an unpacked array is not known here.
            let base: Vec<&str> = h.path.iter().map(|s| s.name.name.as_str()).collect();
            let base = base.join(".");
            let last_selects = h.path.last().map_or(0, |s| s.selects.len());
            let earlier_selects = h.path.iter().rev().skip(1).any(|s| !s.selects.is_empty());
            let unpacked = elab.arrays.contains_key(&base)
                || elab.arrays_2d.contains_key(&base)
                || elab.arrays_nd.contains_key(&base);
            (!earlier_selects
                && last_selects > 0
                && !unpacked
                && elab.signals.contains_key(base.as_str()))
            .then_some(false)
        }
        ExprKind::Index { expr, .. } | ExprKind::RangeSelect { expr, .. } => {
            // A bit- or part-select of a packed vector is unsigned however many
            // packed dimensions it goes through (§11.8.1): `a[1][3:1]` on
            // `logic [3:0][5:0][7:0] a` is a select of a select of `a`.
            let mut inner = expr.as_ref();
            let mut nested = false;
            while let ExprKind::Index { expr, .. } | ExprKind::RangeSelect { expr, .. } =
                &inner.kind
            {
                inner = expr;
                nested = true;
            }
            // The width check after this one skips an actual it can't measure,
            // so a nested select is known here only when it can be measured:
            // otherwise `p[1][2]` (8 bits) could rename `input logic [3:0]`.
            if nested && port_conn_width(e, elab).is_none() {
                return None;
            }
            let base = whole_net_ident_name(inner)?;
            let unpacked = elab.arrays.contains_key(&base)
                || elab.arrays_2d.contains_key(&base)
                || elab.arrays_nd.contains_key(&base);
            (!unpacked && elab.signals.contains_key(base.as_str())).then_some(false)
        }
        ExprKind::MemberAccess { expr, member } => match &expr.kind {
            ExprKind::Ident(bh)
                if bh.path.len() == 1
                    && bh.path[0].selects.is_empty()
                    && elab.packages.contains(&bh.path[0].name.name) =>
            {
                lookup(&format!("{}::{}", bh.path[0].name.name, member.name))
            }
            _ => None,
        },
        ExprKind::Concatenation(_) | ExprKind::Replication { .. } => Some(false),
        _ => None,
    }
}

/// §7.2.1, §7.4, §11.8.1: the declared signedness of a port actual that
/// selects an element of an unpacked array (`sa[0]`, `m[1][0]`), a member of
/// a packed struct (`st.f`, `o.i.a`) or a member of an array element
/// (`ia[1].a`), when its width is also `width`. An element has its array's
/// element type and a member its own declared type, so either is signed only
/// when that type is. The width is read from the tables the connection uses
/// (`arrays*` for an element, `packed_struct_fields` for a member), which
/// `port_conn_width` does not read for a member. `None` for anything else, or
/// when the type or the width cannot be read: such an actual keeps the
/// formal's own net.
pub(super) fn declared_select_signedness(
    e: &Expression,
    elab: &ElaboratedModule,
    width: u32,
) -> Option<bool> {
    enum Step<'a> {
        Index,
        Member(&'a str),
    }
    fn flatten<'a>(
        e: &'a Expression,
        elab: &ElaboratedModule,
        steps: &mut Vec<Step<'a>>,
    ) -> Option<String> {
        match &e.kind {
            ExprKind::Paren(inner) => flatten(inner, elab, steps),
            ExprKind::MemberAccess { expr, member } => {
                let root = flatten(expr, elab, steps)?;
                steps.push(Step::Member(member.name.as_str()));
                Some(root)
            }
            ExprKind::Index { expr, .. } => {
                let root = flatten(expr, elab, steps)?;
                steps.push(Step::Index);
                Some(root)
            }
            ExprKind::Ident(h) => {
                // The root is the longest leading run of segments that names a
                // declared variable; only its last segment may carry selects,
                // and the segments after it are members.
                let names: Vec<&str> = h.path.iter().map(|s| s.name.name.as_str()).collect();
                let k = (1..=h.path.len()).rev().find(|&k| {
                    h.path[..k - 1].iter().all(|s| s.selects.is_empty())
                        && elab.var_decl_types.contains_key(&names[..k].join("."))
                })?;
                for (j, seg) in h.path.iter().enumerate().skip(k - 1) {
                    if j >= k {
                        steps.push(Step::Member(seg.name.name.as_str()));
                    }
                    for sel in &seg.selects {
                        if matches!(sel.kind, ExprKind::Range(..)) {
                            return None;
                        }
                        steps.push(Step::Index);
                    }
                }
                Some(names[..k].join("."))
            }
            _ => None,
        }
    }
    let mut steps = Vec::new();
    let root = flatten(e, elab, &mut steps)?;
    let (unpacked, elem_w) = if let Some(&(_, _, w)) = elab.arrays.get(&root) {
        (1, w)
    } else if let Some(&(_, _, w)) = elab.arrays_2d.get(&root) {
        (2, w)
    } else if let Some((dims, w)) = elab.arrays_nd.get(&root) {
        (dims.len(), *w)
    } else {
        (0, 0)
    };
    // Exactly one index per unpacked dimension, then only members.
    let indices = steps
        .iter()
        .take_while(|s| matches!(s, Step::Index))
        .count();
    let members: Vec<&str> = steps[indices..]
        .iter()
        .map(|s| match s {
            Step::Member(m) => Some(*m),
            Step::Index => None,
        })
        .collect::<Option<_>>()?;
    if indices != unpacked || (unpacked == 0 && members.is_empty()) {
        return None;
    }
    let actual_w = if members.is_empty() {
        elem_w
    } else {
        let path = members.join(".");
        elab.packed_struct_fields
            .get(&root)?
            .iter()
            .find(|(m, _, _)| *m == path)?
            .2
    };
    if actual_w != width || width == 0 {
        return None;
    }
    let mut dt = elab.var_decl_types.get(&root)?;
    for m in &members {
        let DataType::Struct(su) = resolve_typedef_chain(dt, &elab.typedef_types) else {
            return None;
        };
        if !su.packed {
            return None;
        }
        dt = &su
            .members
            .iter()
            .find(|mm| mm.declarators.iter().any(|d| d.name.name == *m))?
            .data_type;
    }
    match resolve_typedef_chain(dt, &elab.typedef_types) {
        DataType::IntegerAtom { .. }
        | DataType::IntegerVector { .. }
        | DataType::Enum(_)
        | DataType::Struct(_) => Some(is_type_signed_resolved(dt, &elab.typedef_types)),
        _ => None,
    }
}

/// §11.8.1: "Concatenation results are unsigned, regardless of the operands."
/// A port actual that is a concatenation or replication therefore carries no
/// sign into a signed formal — §23.3.3.8 keeps the sign of a bounded formal
/// from the actual. Used to decide whether a simple INPUT actual may be
/// substituted as a rename without silently dropping the formal's sign.
pub(super) fn port_actual_is_unsigned_concat(e: &Expression) -> bool {
    match &e.kind {
        ExprKind::Concatenation(_)
        | ExprKind::Replication { .. }
        | ExprKind::RangeSelect { .. }
        | ExprKind::Index { .. } => true,
        ExprKind::Paren(inner) => port_actual_is_unsigned_concat(inner),
        _ => false,
    }
}

/// The value of a port actual naming a parameter of the connecting scope or
/// a package constant (`pk::P`, a two-segment path), if it names one.
pub(super) fn port_actual_param<'a>(
    h: &crate::ast::expr::HierarchicalIdentifier,
    params: &'a HashMap<String, Value>,
    elab: &'a ElaboratedModule,
) -> Option<&'a Value> {
    if h.path.iter().any(|s| !s.selects.is_empty()) {
        return None;
    }
    let segs: Vec<&str> = h.path.iter().map(|s| s.name.name.as_str()).collect();
    let dotted = segs.join(".");
    params
        .get(&dotted)
        .or_else(|| elab.parameters.get(&dotted))
        .or_else(|| (segs.len() == 2).then(|| elab.parameters.get(&segs.join("::")))?)
}

/// §6.11.2, §6.6.5: can a simple port actual (`port_actual_is_simple`) read
/// as X or Z? A 2-state signal or a parameter without X/Z bits cannot. A
/// literal is answered by its digits. Anything not known to be 2-state can.
pub(super) fn port_actual_may_carry_xz(
    e: &Expression,
    elab: &ElaboratedModule,
    params: &HashMap<String, Value>,
) -> bool {
    match &e.kind {
        ExprKind::Paren(inner) => port_actual_may_carry_xz(inner, elab, params),
        ExprKind::Number(NumberLiteral::Integer { value, .. }) => {
            value.contains(['x', 'X', 'z', 'Z', '?'])
        }
        ExprKind::Number(NumberLiteral::UnbasedUnsized(c)) => !matches!(c, '0' | '1'),
        ExprKind::Number(_) | ExprKind::StringLiteral(_) => false,
        ExprKind::Ident(h) => {
            if h.path.is_empty() {
                return true;
            }
            let name = h
                .path
                .iter()
                .map(|s| s.name.name.as_str())
                .collect::<Vec<_>>()
                .join(".");
            if elab.signals.contains_key(&name) {
                return !elab.two_state_signals.contains(&name);
            }
            port_actual_param(h, params, elab).is_none_or(Value::has_xz)
        }
        ExprKind::Index { expr, .. }
        | ExprKind::RangeSelect { expr, .. }
        | ExprKind::MemberAccess { expr, .. } => port_actual_may_carry_xz(expr, elab, params),
        ExprKind::Concatenation(parts) | ExprKind::Replication { exprs: parts, .. } => parts
            .iter()
            .any(|p| port_actual_may_carry_xz(p, elab, params)),
        _ => true,
    }
}
