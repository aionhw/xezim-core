//! Net delays, aliases, driver resolution and bidirectional switches.

use super::*;

/// §6.7.1 / §10.3.3 / §28.16: apply each recorded NET delay (`wire #2 w;`)
/// to the net, whatever drives it.
///
/// A net delay delays every driver of the net — an `assign` written apart
/// from the declaration, a port connection that brings a sub-module output
/// in, a gate, a UDP. Only the declaration-assignment form used to see it
/// (and that delay is the assignment's own, §10.3.3), so `wire #2 w;
/// assign w = a;` tracked `a` undelayed, at the top and inside instances.
///
/// The delay acts on the net's RESOLVED value, after the drivers' own
/// delays: `wire #2 w; assign #3 w = a;` is two inertial stages, so a
/// 4-unit pulse on `a` survives both (a single `#5` would swallow it), and a
/// pulse shorter than 2 on the resolved value of several drivers is
/// swallowed even when no single driver's pulse is.
///
/// When a scalar net's only driver is an undelayed `assign` onto the whole
/// net, the net delay simply becomes that driver's delay. Otherwise
/// (several drivers, a driver with its own delay, a select or concatenation
/// target, a UDP, a vector net) the drivers are moved onto a hidden
/// driver-side net `<net>$netdrv` of the same kind, and the net follows it
/// through delayed continuous assignments — one, or one per bit of a
/// vector. Runs before `resolve_multi_driver_nets`, which resolves the
/// hidden net's drivers.
pub fn apply_net_delays(elab: &mut ElaboratedModule) {
    if elab.net_delays.is_empty() {
        return;
    }
    let mut delays = std::mem::take(&mut elab.net_delays);
    // A later variable redeclaration (`output o; reg o;`) unmade the net.
    delays.retain(|n, _| elab.nets.contains(n) && elab.signals.contains_key(n));
    if delays.is_empty() {
        return;
    }
    // §23.3.3.7 port collapsing: an OUTPUT port bound to a whole delayed net
    // (through any depth of such ports) is that same net. Its drivers drive
    // the delayed net, and the port reads the net's delayed value, as the
    // reference shows it from inside the instance.
    // An output connection is the synthesized `actual = port` assign of a
    // port whose actual is a whole net (`port_aliases`).
    let out_conns: Vec<(String, String)> = if elab.port_aliases.is_empty() {
        Vec::new()
    } else {
        elab.continuous_assigns
            .iter()
            .filter(|ca| ca.origin.is_none())
            .filter_map(|ca| {
                let port = ident_flat_name(&ca.rhs)?;
                let actual = ident_flat_name(&ca.lhs)?;
                (elab.port_aliases.get(&port) == Some(&actual) && elab.nets.contains(&port))
                    .then_some((port, actual))
            })
            .collect()
    };
    let mut merged: HashMap<String, String> = HashMap::default();
    loop {
        let mut grew = false;
        for (port, actual) in &out_conns {
            if merged.contains_key(port) || delays.contains_key(port) {
                continue;
            }
            if let Some(root) = delays
                .contains_key(actual)
                .then(|| actual.clone())
                .or_else(|| merged.get(actual).cloned())
            {
                merged.insert(port.clone(), root);
                grew = true;
            }
        }
        if !grew {
            break;
        }
    }
    let is_net = |n: &str| delays.contains_key(n) || merged.contains_key(n);
    let targets_of = |e: &Expression| -> Vec<(String, bool)> {
        let mut v = Vec::new();
        lvalue_nets(e, &is_net, &mut v);
        v
    };
    // Sub-module drivers may still be pending; bring in the ones that write
    // a delayed net (one target rewrite each — the fold below does the same).
    if !elab.pending_cont_assign.is_empty() {
        let pending = std::mem::take(&mut elab.pending_cont_assign);
        for p in pending {
            let lhs = p.materialize_lhs();
            if targets_of(&lhs).iter().any(|(n, _)| is_net(n)) {
                let ca = p.materialize(&elab.parameters);
                elab.continuous_assigns.push(ca);
            } else {
                elab.pending_cont_assign.push(p);
            }
        }
    }
    if !merged.is_empty() {
        // Drop each merged port's connection (`actual = port`), move the
        // port's own drivers onto the delayed net, and let the port follow it.
        let is_connection = |ca: &ContinuousAssignment| {
            ca.origin.is_none()
                && ident_flat_name(&ca.rhs).is_some_and(|p| {
                    merged.contains_key(&p)
                        && ident_flat_name(&ca.lhs).as_ref() == elab.port_aliases.get(&p)
                })
        };
        let mut cas = std::mem::take(&mut elab.continuous_assigns);
        cas.retain(|ca| !is_connection(ca));
        for ca in cas.iter_mut() {
            for (n, _) in targets_of(&ca.lhs) {
                if let Some(root) = merged.get(&n) {
                    retarget_lvalue_net(&mut ca.lhs, &n, root);
                }
            }
        }
        for u in elab.udp_instances.iter_mut() {
            for (n, _) in targets_of(&u.output) {
                if let Some(root) = merged.get(&n) {
                    retarget_lvalue_net(&mut u.output, &n, root);
                }
            }
        }
        let mut members: Vec<(&String, &String)> = merged.iter().collect();
        members.sort();
        for (port, root) in members {
            cas.push(ContinuousAssignment {
                gate_delay_fall: None,
                delay_exprs: None,
                delay_select: None,
                origin: None,
                lhs: make_ident_expr(port),
                rhs: make_ident_expr(root),
                delay: 0,
                rhs_parent_scoped: false,
                delay_fall: None,
                delay_off: None,
            });
        }
        elab.continuous_assigns = cas;
    }
    let is_net = |n: &str| delays.contains_key(n);
    let targets_of = |e: &Expression| -> Vec<(String, bool)> {
        let mut v = Vec::new();
        lvalue_nets(e, &is_net, &mut v);
        v
    };
    // Per delayed net: its driving assigns, and whether some driver needs
    // the net to be a stage of its own.
    let mut drivers: HashMap<String, Vec<usize>> = HashMap::default();
    let mut staged: HashSet<String> = HashSet::default();
    let mut gate_staged: HashSet<String> = HashSet::default();
    for (i, ca) in elab.continuous_assigns.iter().enumerate() {
        let ts = targets_of(&ca.lhs);
        let own_delay = ca.delay != 0 || ca.delay_fall.is_some() || ca.delay_off.is_some();
        let gate_delay = !own_delay && cont_assign_has_own_delay(ca);
        for (n, whole) in ts.iter().filter(|(n, _)| is_net(n)) {
            let ds = drivers.entry(n.clone()).or_default();
            ds.push(i);
            // §10.3.3, §28.16: a zero-rise primitive with a fall delay
            // needs its own stage before the net's declaration delay.
            // §28.12: keep implicit supply, pull and charge drivers on
            // their existing path; extra stages can lose their strengths.
            // Keep existing names that would collide with the new stage.
            let gate_delay = gate_delay
                && gate_tristate_parts(ca).is_none()
                && !elab.supply_nets.contains(n)
                && !matches!(
                    elab.resolved_net_kinds.get(n),
                    Some(ResolvedNetKind::Tri0)
                        | Some(ResolvedNetKind::Tri1)
                        | Some(ResolvedNetKind::ChargeStorage)
                )
                && !elab.signals.contains_key(&format!("{n}$netdrv"))
                && !elab.parameters.contains_key(&format!("{n}$netdrv"))
                && !elab.arrays.contains_key(&format!("{n}$netdrv"));
            if own_delay || ts.len() > 1 || !whole || ds.len() > 1 {
                staged.insert(n.clone());
                gate_staged.remove(n);
            } else if gate_delay {
                staged.insert(n.clone());
                gate_staged.insert(n.clone());
            }
        }
    }
    for u in &elab.udp_instances {
        for (n, _) in targets_of(&u.output) {
            if is_net(&n) {
                drivers.entry(n.clone()).or_default();
                gate_staged.remove(&n);
                staged.insert(n);
            }
        }
    }
    let mut names: Vec<String> = drivers.keys().cloned().collect();
    names.sort();
    for net in names {
        let (rise, fall, off, delay_exprs) = delays.remove(&net).unwrap();
        let (width, is_real) = elab
            .signals
            .get(&net)
            .map_or((1, false), |s| (s.width, s.is_real));
        // §28.16: a vector net's delay acts on each BIT — a bit that changes
        // keeps its own schedule when another changes a tick later, and each
        // bit's transition picks rise, fall or turn-off for itself. The
        // simulator's delayed update is per signal, so a vector net takes the
        // driver-net route and follows it bit by bit.
        let per_bit = width > 1 && !is_real;
        if gate_staged.contains(&net) && !per_bit {
            // §28.4/§28.5: retain z→x even on the delayed evaluator path.
            // A conditional ending in z could be a MOS or a buf input;
            // those indistinguishable lowered forms keep the old path.
            let ca = &mut elab.continuous_assigns[drivers[&net][0]];
            ca.rhs = Expression::new(
                ExprKind::Binary {
                    op: BinaryOp::BitXor,
                    left: Box::new(ca.rhs.clone()),
                    right: Box::new(make_fill_expr(false, ca.rhs.span)),
                },
                ca.rhs.span,
            );
        }
        if !staged.contains(&net) && !per_bit && delay_exprs.is_none() {
            // A constant delay is already rounded to ticks and can be applied
            // directly to the lone driver. A variable net delay must evaluate
            // in the declaring net's time precision, even if a different
            // module supplied the driver, so it keeps a separate stage.
            let ca = &mut elab.continuous_assigns[drivers[&net][0]];
            // §28.16: this is a net delay, even on a [0:0] vector.
            ca.delay_select = Some((0, width, false));
            ca.delay = rise;
            ca.delay_fall = fall;
            ca.delay_off = off;
            continue;
        }
        // The driver side: a copy of the net, same kind and shape.
        let drv = format!("{net}$netdrv");
        let mut sig = elab.signals[&net].clone();
        sig.name = drv.clone().into();
        sig.direction = None;
        elab.signals.insert(drv.clone(), sig);
        elab.nets.insert(drv.clone());
        if let Some(k) = elab.resolved_net_kinds.get(&net).cloned() {
            elab.resolved_net_kinds.insert(drv.clone(), k);
        }
        if let Some(v) = elab.ascending_packed.get(&net).copied() {
            elab.ascending_packed.insert(drv.clone(), v);
        }
        if let Some(v) = elab.packed_full_dims.get(&net).cloned() {
            elab.packed_full_dims.insert(drv.clone(), v);
        }
        if let Some(v) = elab.packed_signal_elem_widths.get(&net).copied() {
            elab.packed_signal_elem_widths.insert(drv.clone(), v);
        }
        if let Some(v) = elab.packed_struct_fields.get(&net).cloned() {
            elab.packed_struct_fields.insert(drv.clone(), v);
        }
        if let Some(v) = elab.var_decl_types.get(&net).cloned() {
            elab.var_decl_types.insert(drv.clone(), v);
        }
        // A gate's §28.4 z→x rule and fall delay belong to its output.
        if elab.gate_driven_nets.remove(&net) {
            elab.gate_driven_nets.insert(drv.clone());
        }
        if let Some(f) = elab.gate_fall_delays.remove(&net) {
            elab.gate_fall_delays.insert(drv.clone(), f);
        }
        for &i in drivers.get(&net).map(|v| v.as_slice()).unwrap_or(&[]) {
            retarget_lvalue_net(&mut elab.continuous_assigns[i].lhs, &net, &drv);
        }
        for u in elab.udp_instances.iter_mut() {
            retarget_lvalue_net(&mut u.output, &net, &drv);
        }
        if !per_bit {
            elab.continuous_assigns.push(ContinuousAssignment {
                gate_delay_fall: None,
                delay_exprs: delay_exprs.clone(),
                delay_select: None,
                origin: None,
                lhs: make_ident_expr(&net),
                rhs: make_ident_expr(&drv),
                delay: rise,
                rhs_parent_scoped: false,
                delay_fall: fall,
                delay_off: off,
            });
            continue;
        }
        // One delayed scalar stage per bit (`<net>$netbit<i>` follows physical
        // bit i of the driver net), then the net is their concatenation.
        let mut bits: Vec<Expression> = Vec::with_capacity(width as usize);
        for i in 0..width {
            let b = format!("{net}$netbit{i}");
            elab.signals.insert(
                b.clone(),
                Signal {
                    name: b.clone().into(),
                    width: 1,
                    is_signed: false,
                    is_real: false,
                    is_const: false,
                    direction: None,
                    value: Value::all_z(1),
                    type_name: None,
                },
            );
            elab.nets.insert(b.clone());
            let bit_of_drv = Expression::new(
                ExprKind::Binary {
                    op: BinaryOp::ShiftRight,
                    left: Box::new(make_ident_expr(&drv)),
                    right: Box::new(make_udp_int_expr(i as i64)),
                },
                Span::dummy(),
            );
            elab.continuous_assigns.push(ContinuousAssignment {
                gate_delay_fall: None,
                delay_exprs: delay_exprs.clone(),
                delay_select: None,
                origin: None,
                lhs: make_ident_expr(&b),
                rhs: bit_of_drv,
                delay: rise,
                rhs_parent_scoped: false,
                delay_fall: fall,
                delay_off: off,
            });
            bits.push(make_ident_expr(&b));
        }
        bits.reverse();
        elab.continuous_assigns.push(ContinuousAssignment {
            gate_delay_fall: None,
            delay_exprs: None,
            delay_select: None,
            origin: None,
            lhs: make_ident_expr(&net),
            rhs: Expression::new(ExprKind::Concatenation(bits), Span::dummy()),
            delay: 0,
            rhs_parent_scoped: false,
            delay_fall: None,
            delay_off: None,
        });
    }
}

/// A driver a tristate PRIMITIVE produced (`bufif*`/`notif*`, the MOS
/// switches): elaboration lowers each to `ctl ? data : 'z` and marks it as
/// synthesized (no `origin`). Returns `(ctl, data)`. A user-written `assign
/// w = en ? d : 'z` has an origin and keeps the ordinary `?:` semantics.
/// §10.3.3, §28.16: does this driver delay its own transitions? A primitive
/// with a zero rise delay and a fall delay (`buf #(0, 5)`) does.
pub(super) fn cont_assign_has_own_delay(ca: &ContinuousAssignment) -> bool {
    ca.delay != 0
        || ca.delay_fall.is_some()
        || ca.delay_off.is_some()
        || ca.gate_delay_fall.is_some_and(|f| f != 0)
}

fn gate_tristate_parts(ca: &ContinuousAssignment) -> Option<(&Expression, &Expression)> {
    if ca.origin.is_some() {
        return None;
    }
    match &ca.rhs.kind {
        ExprKind::Conditional {
            condition,
            then_expr,
            else_expr,
        } if matches!(
            else_expr.kind,
            ExprKind::Number(NumberLiteral::UnbasedUnsized('z'))
        ) =>
        {
            Some((condition, then_expr))
        }
        _ => None,
    }
}

/// A `k`-bit all-z literal.
fn make_z_fill(k: u32, span: Span) -> Expression {
    Expression::new(
        ExprKind::Number(NumberLiteral::Integer {
            size: Some(k),
            signed: false,
            base: NumberBase::Binary,
            value: "z".repeat(k as usize),
            cached_val: crate::ast::cache::LiteralCache::new(None),
        }),
        span,
    )
}

/// The constant bit span `(net, lo, hi)` a continuous assign drives: the whole
/// net for a bare name, or the physical bits of a constant bit/part select
/// (`w[3]`, `w[7:2]`, `w[2 +: 4]`). `None` for anything else (a variable
/// index, a multi-dimensional packed net, a concatenation lvalue).
pub(super) fn cont_assign_net_span(
    lhs: &Expression,
    elab: &ElaboratedModule,
    signal_width: Option<u32>,
) -> Option<(String, u32, u32)> {
    let net_width = |n: &str| -> Option<u32> {
        if !elab.nets.contains(n) {
            return None;
        }
        elab.signals.get(n).map(|s| s.width).or(signal_width).filter(|&w| w > 0)
    };
    if let Some(n) = ident_flat_name(lhs) {
        let w = net_width(&n)?;
        return Some((n, 0, w - 1));
    }
    // §7.4.2: the first select of an unpacked array of nets names an
    // ELEMENT, a net of its own, not a bit of one vector.
    let unpacked = |n: &str| {
        elab.arrays.contains_key(n)
            || elab.arrays_2d.contains_key(n)
            || elab.arrays_nd.contains_key(n)
    };
    let (base, l, r) = match &lhs.kind {
        ExprKind::Index { expr, index } => {
            let i = const_eval_i64_with_params(index, Some(&elab.parameters))?;
            (expr, i, i)
        }
        ExprKind::RangeSelect {
            expr,
            kind,
            left,
            right,
        } => {
            let a = const_eval_i64_with_params(left, Some(&elab.parameters))?;
            let b = const_eval_i64_with_params(right, Some(&elab.parameters))?;
            match kind {
                RangeKind::Constant => (expr, a, b),
                RangeKind::IndexedUp if b > 0 => (expr, a + b - 1, a),
                RangeKind::IndexedDown if b > 0 => (expr, a, a - b + 1),
                _ => return None,
            }
        }
        _ => return None,
    };
    let n = ident_flat_name(base).filter(|n| !unpacked(n))?;
    let w = net_width(&n)? as i64;
    // Label → physical bit (§7.4.1). A single non-normalized dimension is
    // recorded in `packed_full_dims`/`ascending_packed`; absence means [w-1:0].
    let phys = |p: i64| -> Option<i64> {
        if let Some(&(_, hi)) = elab.ascending_packed.get(&n) {
            return Some(hi - p);
        }
        match elab.packed_full_dims.get(&n).map(|d| d.as_slice()) {
            None => Some(p),
            Some([(dl, dr)]) if dl >= dr => Some(p - dr),
            Some([(_, dr)]) => Some(dr - p),
            Some(_) => None,
        }
    };
    let (a, b) = (phys(l)?, phys(r)?);
    let (lo, hi) = (a.min(b), a.max(b));
    if lo < 0 || hi >= w {
        return None;
    }
    Some((n, lo as u32, hi as u32))
}

/// §7.2.1, §7.4.1: the bit span a MEMBER of a packed-struct net occupies.
/// A continuous assignment to such a member drives that part of the net,
/// so it takes part in the net's resolution like a bit-select driver
/// (§6.6.1) instead of overwriting the whole net. The member's bits are
/// recorded in `packed_struct_fields` as (name, lsb offset, width).
///
/// The target names the member as the LAST segment of its path (`s.x`,
/// `u.s.x`); the segments before it name the net.
fn packed_member_net_span(
    lhs: &Expression,
    elab: &ElaboratedModule,
) -> Option<(String, u32, u32)> {
    let (base, member) = match &lhs.kind {
        ExprKind::Ident(h) => {
            if h.path.len() < 2 {
                return None;
            }
            let last = h.path.len() - 1;
            if !h.path[last].selects.is_empty()
                || !h.path[..last].iter().all(|s| s.selects.is_empty())
            {
                return None;
            }
            let member = h.path[last].name.name.clone();
            let base = h.path[..last]
                .iter()
                .map(|s| s.name.name.as_str())
                .collect::<Vec<_>>()
                .join(".");
            (base, member)
        }
        ExprKind::MemberAccess { expr, member } => (ident_flat_name(expr)?, member.name.clone()),
        _ => return None,
    };
    // The base must be a WHOLE net: a further select addresses a part of
    // the member, which the member's own width does not describe.
    if !elab.nets.contains(base.as_str()) {
        return None;
    }
    let fields = elab.packed_struct_fields.get(base.as_str())?;
    let (_, off, width) = fields.iter().find(|(n, _, _)| *n == member)?;
    let w = elab.signals.get(base.as_str()).map(|s| s.width)?;
    let lo = *off;
    let hi = off.checked_add(width.checked_sub(1)?)?;
    if hi >= w {
        return None;
    }
    Some((base, lo, hi))
}

/// The bits of the net a continuous assignment drives: a whole net, a bit
/// select, or a member of a packed-struct net. §10.11: the name is the
/// canonical net of the alias group it belongs to, so the group is one net
/// here too.
fn cont_assign_driver_span(
    lhs: &Expression,
    elab: &ElaboratedModule,
) -> Option<(String, u32, u32)> {
    cont_assign_net_span(lhs, elab, None)
        .or_else(|| packed_member_net_span(lhs, elab))
        .map(|(n, lo, hi)| (alias_canonical(&elab.alias_canon, n), lo, hi))
}

/// §6.9 / §6.9.1 / §10.3.3: delay selection follows target shape, not width.
/// Also used for assignments materialized lazily after driver resolution;
/// the simulator supplies the width after releasing the elaborated signals.
pub fn continuous_assign_delay_select(
    lhs: &Expression,
    elab: &ElaboratedModule,
    signal_width: Option<u32>,
) -> Option<(u32, u32, bool)> {
    let Some((n, lo, hi)) = cont_assign_net_span(lhs, elab, signal_width) else {
        // §10.3.2: a whole variable may be the target too; §10.3.3 then
        // chooses its delay by the same rules, from its declared shape.
        let n = ident_flat_name(lhs).filter(|n| !elab.arrays.contains_key(n))?;
        let dt = elab.var_decl_types.get(&n)?;
        let w = elab
            .signals
            .get(&n)
            .map(|s| s.width)
            .or(signal_width)
            .filter(|&w| w > 0)?;
        return Some((
            0,
            w,
            w > 1 || declared_vector_shape(Some(dt), &elab.typedef_types),
        ));
    };
    let vector = match &lhs.kind {
        ExprKind::Index { .. } => false,
        ExprKind::RangeSelect { .. } => true,
        _ => hi > lo || elab.vector_nets.contains(&n),
    };
    Some((lo, hi - lo + 1, vector))
}

/// IEEE 1800-2017 §6.6.1/§11.5.1: a bit or part select driver of a net is a
/// driver of those bits only, and every bit resolves ALL of its drivers.
/// Select drivers that overlap another driver of the same net (`assign w =
/// {4{a}}; assign w[3] = b;`) used to be applied one after the other, so the
/// last assign won the shared bits, and an edge on such a bit was counted from
/// the wrong value. Widen each select driver of such a net to a whole-net
/// driver that leaves the other bits at z (`{'z, 1'(b), 'z}`), so the
/// whole-net fold below resolves the shared bits and passes the rest through.
/// Nets whose select drivers are disjoint keep their per-select assigns.
fn widen_overlapping_select_drivers(elab: &mut ElaboratedModule) {
    // Compute each materialized driver's net span, and the same for LAZY
    // sub-module drivers without materializing them: a future instance whose
    // body sits in `pending_cont_assign` (bit/part selects on `n` inside a
    // child module) is invisible to a scan of `elab.continuous_assigns`, so
    // an overlapping-select net driven only from a sub-module was never
    // widened and its overlapping selects stayed per-bit (#1062).
    let materialized_spans: Vec<Option<(String, u32, u32)>> = elab
        .continuous_assigns
        .iter()
        .map(|ca| cont_assign_driver_span(&ca.lhs, elab))
        .collect();
    let mut pending_spans: Vec<Option<(String, u32, u32)>> =
        Vec::with_capacity(elab.pending_cont_assign.len());
    for p in &elab.pending_cont_assign {
        let lhs = p.materialize_lhs();
        pending_spans.push(cont_assign_driver_span(&lhs, elab));
    }
    let mut by_net: HashMap<&str, Vec<(u32, u32, bool)>> = HashMap::default();
    for (s, ca) in materialized_spans.iter().zip(&elab.continuous_assigns) {
        if let Some((n, lo, hi)) = s {
            // A member of a packed-struct net drives that part of the net,
            // so it is a select driver like a bit-select (§7.2.1).
            let is_select = match &ca.lhs.kind {
                ExprKind::Ident(_) | ExprKind::MemberAccess { .. } => {
                    packed_member_net_span(&ca.lhs, elab).is_some()
                }
                _ => true,
            };
            by_net
                .entry(n.as_str())
                .or_default()
                .push((*lo, *hi, is_select));
        }
    }
    // Pending assigns count toward a net's driver roster (a select is
    // always a select) even though we do not widen them here yet.
    for s in &pending_spans {
        if let Some((n, lo, hi)) = s {
            by_net.entry(n.as_str()).or_default().push((*lo, *hi, true));
        }
    }
    // §6.6.5: every bit of a tri0 or tri1 net resolves against the net's
    // implicit pull, which the whole-net fold supplies; a select driver left
    // per-select kept its z bits, and the bits no select drives, at z.
    let pulled = |n: &str| {
        matches!(
            elab.resolved_net_kinds.get(n),
            Some(ResolvedNetKind::Tri0 | ResolvedNetKind::Tri1)
        )
    };
    let widen: HashSet<String> = by_net
        .into_iter()
        .filter(|(n, v)| {
            v.iter().any(|s| s.2)
                && (pulled(n)
                    || v.iter()
                        .enumerate()
                        .any(|(i, a)| v[i + 1..].iter().any(|b| a.0 <= b.1 && b.0 <= a.1)))
        })
        .map(|(n, _)| n.to_string())
        .collect();
    if widen.is_empty() {
        return;
    }
    // A pending driver on a widen net must join the materialized roster so
    // the widening below (and the whole-net fold that follows) sees every
    // driver of the net, not only the first select.
    if !elab.pending_cont_assign.is_empty() {
        let mut pending = std::mem::take(&mut elab.pending_cont_assign);
        for (p, s) in pending.drain(..).zip(pending_spans) {
            if s.is_some_and(|(n, _, _)| widen.contains(&n)) {
                elab.continuous_assigns
                    .push(p.materialize(&elab.parameters));
            } else {
                elab.pending_cont_assign.push(p);
            }
        }
    }
    let spans: Vec<Option<(String, u32, u32)>> = elab
        .continuous_assigns
        .iter()
        .map(|ca| cont_assign_driver_span(&ca.lhs, elab))
        .collect();
    // A driver that already names the whole net needs no widening; a member
    // of a packed-struct net does (§7.2.1).
    let whole_net_drives: Vec<bool> = elab
        .continuous_assigns
        .iter()
        .map(|ca| {
            ident_flat_name(&ca.lhs).is_some() && packed_member_net_span(&ca.lhs, elab).is_none()
        })
        .collect();
    let z_fill = make_z_fill;
    let delay_selects: Vec<_> = elab
        .continuous_assigns
        .iter()
        .zip(&spans)
        .map(|(ca, s)| {
            s.as_ref()
                .filter(|(n, _, _)| widen.contains(n))
                .and_then(|_| continuous_assign_delay_select(&ca.lhs, elab, None))
        })
        .collect();
    for (((ca, s), delay_select), whole_net_drive) in elab
        .continuous_assigns
        .iter_mut()
        .zip(spans)
        .zip(delay_selects)
        .zip(whole_net_drives)
    {
        let Some((n, lo, hi)) = s else { continue };
        if !widen.contains(&n) || whole_net_drive {
            continue;
        }
        let w = elab.signals.get(&n).map(|s| s.width).unwrap_or(0);
        let span = ca.rhs.span;
        // A tristate primitive keeps its `ctl ? data : 'z` shape (the
        // resolution below treats an unknown control specially); only the
        // data is widened.
        let gate_ctl = gate_tristate_parts(ca).map(|(c, _)| c.clone());
        let rhs = std::mem::replace(&mut ca.rhs, Expression::new(ExprKind::Empty, span));
        // §28.12: a drive-strength marker (`$__weak(v, pair)`, a pullup's
        // `$__pull`) stays outermost so the fold still sees the driver's
        // strength; only its value is widened.
        let (marker, rhs) = match rhs.kind {
            ExprKind::SystemCall { name, mut args }
                if matches!(
                    name.as_str(),
                    "$__supply" | "$__drive" | "$__pull" | "$__weak"
                ) && !args.is_empty() =>
            {
                let inner = args.remove(0);
                (Some((name, args)), inner)
            }
            kind => (None, Expression::new(kind, span)),
        };
        let rhs = match (gate_ctl.is_some(), rhs.kind) {
            (true, ExprKind::Conditional { then_expr, .. }) => *then_expr,
            (_, kind) => Expression::new(kind, span),
        };
        let sized = make_syscall(
            "$__xz_size_cast",
            vec![
                const_value_literal(&Value::from_u64(u64::from(hi - lo + 1), 32), span)
                    .expect("width literal"),
                rhs,
            ],
            span,
        );
        let mut parts = Vec::with_capacity(3);
        if hi + 1 < w {
            parts.push(z_fill(w - 1 - hi, span));
        }
        parts.push(sized);
        if lo > 0 {
            parts.push(z_fill(lo, span));
        }
        let widened = if parts.len() == 1 {
            parts.pop().unwrap()
        } else {
            Expression::new(ExprKind::Concatenation(parts), span)
        };
        ca.rhs = match gate_ctl {
            Some(ctl) => make_tristate(ctl, widened, span),
            None => widened,
        };
        if let Some((name, rest)) = marker {
            let mut args = vec![std::mem::replace(
                &mut ca.rhs,
                Expression::new(ExprKind::Empty, span),
            )];
            args.extend(rest);
            ca.rhs = make_syscall(&name, args, span);
        }
        ca.lhs = make_ident_expr(&n);
        ca.delay_select = delay_select;
    }
}

/// §29.3, §28.12: a UDP instance's output terminal is a driver of its net
/// like a gate's. The instance writes the net it names directly, so beside a
/// continuous assignment or another UDP on the same net the last writer won
/// and nothing was resolved (`udp u(w, a); assign w = b;` read `b`, or `a`,
/// where the two disagreed). Such an instance drives a stage of its own,
/// `<net>$udp<k>`, with its instance delay, and an undelayed assignment of
/// the stage joins the net's other drivers in the fold. A UDP that is the
/// only driver of its net keeps writing it.
fn stage_shared_udp_outputs(elab: &mut ElaboratedModule) {
    if elab.udp_instances.is_empty() {
        return;
    }
    let mut drivers: HashMap<String, usize> = HashMap::default();
    for u in &elab.udp_instances {
        if let Some(n) = ident_flat_name(&u.output).filter(|n| elab.nets.contains(n)) {
            *drivers.entry(n).or_insert(0) += 1;
        }
    }
    if drivers.is_empty() {
        return;
    }
    for ca in &elab.continuous_assigns {
        if let Some(n) = ident_flat_name(&ca.lhs)
            && let Some(c) = drivers.get_mut(&n)
        {
            *c += 1;
        }
    }
    let mut staged: HashMap<String, usize> = HashMap::default();
    for i in 0..elab.udp_instances.len() {
        let Some(net) = ident_flat_name(&elab.udp_instances[i].output)
            .filter(|n| drivers.get(n).is_some_and(|&c| c > 1))
        else {
            continue;
        };
        let k = staged.entry(net.clone()).or_insert(0);
        let stage = format!("{net}$udp{k}");
        *k += 1;
        let Some(mut sig) = elab.signals.get(&net).cloned() else {
            continue;
        };
        sig.name = stage.clone().into();
        sig.direction = None;
        elab.signals.insert(stage.clone(), sig);
        let span = elab.udp_instances[i].output.span;
        elab.udp_instances[i].output = Expression::new(make_ident_expr(&stage).kind, span);
        elab.continuous_assigns.push(ContinuousAssignment {
            gate_delay_fall: None,
            delay_exprs: None,
            delay_select: None,
            origin: None,
            lhs: make_ident_expr(&net),
            rhs: make_ident_expr(&stage),
            delay: 0,
            rhs_parent_scoped: false,
            delay_fall: None,
            delay_off: None,
        });
    }
}

/// §10.11: the names an `alias` statement names are ONE physical net.
///
/// The groups are CUMULATIVE ("The same nets can appear in multiple alias
/// statements. The effects are cumulative"), so two groups naming a common
/// net are one group. Each group gets a canonical name — the first member
/// that names a net the elaborated tables know — and every other member
/// stands for it:
///
/// * the driver count and the resolution fold (§6.6.1) key the group's
///   drivers by the canonical name, so the drivers of ALL the members
///   resolve together, and
/// * the simulator points every member at the canonical's storage slot, so
///   every read of any of them sees the same value (§10.11's "same
///   physical net").
///
/// A member that names no net the tables know — a name that was already
/// collapsed away, or a name outside the design — cannot stand for the
/// group and is left alone.
/// §14.16: a clocking block's OUTPUT clockvar creates a DRIVER on the net
/// it is bound to. The driver takes part in the net's resolution like any
/// other driver (§6.6.1): a wire with another driver reads x where the two
/// disagree, a `wor` net ORs them.
///
/// The simulator drives the clockvar's net directly, so beside another
/// driver of that net the clocking drive simply OVERWROTE it. Such a
/// clockvar therefore drives a stage of its own, `<net>$clk<k>`, and an
/// undelayed assignment of the stage joins the net's other drivers in the
/// fold. A clockvar that is the net's ONLY driver keeps driving the net
/// itself.
fn stage_shared_clocking_outputs(elab: &mut ElaboratedModule) {
    if elab.clocking_blocks.is_empty() {
        return;
    }
    // The nets a clocking output drives. Only an OUTPUT (or INOUT) clockvar
    // creates a driver (§14.16); an input is sampled.
    let mut outputs: Vec<(String, String)> = Vec::new();
    for cd in elab.clocking_blocks.values() {
        for s in &cd.signals {
            if matches!(
                s.direction,
                crate::ast::types::PortDirection::Input
            ) {
                continue;
            }
            // §14.3: `output alias = expr;` binds the clockvar to another
            // signal; that signal is what the output drives. A plain
            // `output name;` drives the net of that name itself.
            let Some(net) = (match &s.bound_to {
                Some(e) => ident_flat_name(e),
                None => Some(s.name.name.clone()),
            }) else {
                continue;
            };
            if !elab.nets.contains(net.as_str()) {
                continue;
            }
            outputs.push((cd.name.name.clone(), net));
        }
    }
    if outputs.is_empty() {
        return;
    }
    // §10.11: the net may be an alias member; a driver of any member
    // drives the group's canonical net, so the driver count keys by the
    // canonical name.
    let canon_of = |net: &str| alias_canonical(&elab.alias_canon, net.to_string());
    let mut drivers: HashMap<String, usize> = HashMap::default();
    for (_, net) in &outputs {
        *drivers.entry(canon_of(net)).or_insert(0) += 1;
    }
    for ca in &elab.continuous_assigns {
        let Some(n) = ident_flat_name(&ca.lhs) else {
            continue;
        };
        let n = canon_of(&n);
        if let Some(c) = drivers.get_mut(&n) {
            *c += 1;
        }
    }
    let mut staged: HashMap<String, usize> = HashMap::default();
    for (cb, net) in &outputs {
        if !drivers.get(&canon_of(net)).is_some_and(|&c| c > 1) {
            continue;
        }
        let k = staged.entry(net.clone()).or_insert(0);
        let stage = format!("{net}$clk{k}");
        *k += 1;
        let Some(mut sig) = elab.signals.get(net).cloned() else {
            continue;
        };
        sig.name = stage.clone().into();
        sig.direction = None;
        elab.signals.insert(stage.clone(), sig);
        // §10.11: the net may be an alias member; the stage follows the
        // group's canonical net.
        let canon = alias_canonical(&elab.alias_canon, net.clone());
        elab.clocking_output_stages
            .insert((cb.clone(), net.clone()), stage.clone());
        let span = elab.clocking_blocks[cb].span;
        elab.continuous_assigns.push(ContinuousAssignment {
            gate_delay_fall: None,
            delay_exprs: None,
            delay_select: None,
            origin: None,
            lhs: make_ident_expr(&canon),
            rhs: make_ident_expr(&stage),
            delay: 0,
            rhs_parent_scoped: false,
            delay_fall: None,
            delay_off: None,
        });
        let _ = span;
    }
}

/// §10.11: the canonical net of the alias group a name belongs to, or the
/// name itself when it belongs to no group.
fn alias_canonical(alias_canon: &HashMap<String, String>, name: String) -> String {
    alias_canon.get(name.as_str()).cloned().unwrap_or(name)
}

pub fn unify_alias_nets(elab: &mut ElaboratedModule) {
    if elab.alias_groups.is_empty() {
        return;
    }
    let components = collect_alias_components(elab);
    // The canonical name of each component: the first member that names a net
    // the elaborated tables know. A member whose net does not exist (a port
    // already collapsed onto its actual, say) cannot stand for the group.
    elab.alias_pairs.clear();
    for (canon_opt, members) in &components {
        let Some(canon) = canon_opt.as_ref() else {
            continue;
        };
        // §6.6.5, §6.6.6: the members are ONE net, so they share its net
        // type — a tri0/tri1 or supply member makes the whole group that
        // kind. Without this the group's canonical net reads as an ordinary
        // wire and the implicit pull of the tri member is lost.
        if let Some(kind) = members
            .iter()
            .find_map(|m| elab.resolved_net_kinds.get(m).cloned())
        {
            for m in members {
                elab.resolved_net_kinds.insert(m.clone(), kind.clone());
            }
        }
        if members.iter().any(|m| elab.supply_nets.contains(m)) {
            for m in members {
                elab.supply_nets.insert(m.clone());
            }
        }
        if let Some(delay) = members.iter().find_map(|m| elab.net_delays.get(m).cloned()) {
            for m in members {
                elab.net_delays.insert(m.clone(), delay.clone());
            }
        }
        for m in members {
            if m != canon {
                elab.alias_canon.insert(m.clone(), canon.clone());
                // §10.11: the simulator repoints every member of a group at
                // the canonical's storage slot, so the names share ONE signal.
                elab.alias_pairs.push((canon.clone(), m.clone()));
            }
        }
    }
}

/// §7.4.2: a constant subscript on a fixed array of nets names a whole
/// net cell. A subscript on a packed vector is a part of the same net.
pub(super) fn fixed_net_cell(elab: &ElaboratedModule, expr: &Expression) -> Option<(String, String)> {
    let ExprKind::Index { expr: base, index } = &expr.kind else {
        return None;
    };
    let base = ident_flat_name(base)?;
    if !elab.nets.contains(base.as_str()) || elab.dynamic_arrays.contains(&base) {
        return None;
    }
    let &(lo, hi, _) = elab.arrays.get(&base)?;
    let index = const_eval_i64_with_params(index, Some(&elab.parameters))?;
    if !(lo..=hi).contains(&index) {
        return None;
    }
    let cell = format!("{base}[{index}]");
    // A separately declared scalar with brackets in its escaped name is
    // distinct from this unpacked element, as in net_base_of.
    (!elab.signals.contains_key(&cell)).then_some((cell, base))
}

fn register_fixed_net_cell(elab: &mut ElaboratedModule, expr: &mut Expression) {
    if let Some((cell, base)) = fixed_net_cell(elab, expr) {
        elab.nets.insert(cell.clone());
        if let Some(kind) = elab.resolved_net_kinds.get(base.as_str()).cloned() {
            elab.resolved_net_kinds.insert(cell.clone(), kind);
        }
        *expr = make_ident_expr(&cell);
    }
}

fn normalize_net_cell_drivers(elab: &mut ElaboratedModule) -> HashMap<String, u32> {
    if elab.arrays.is_empty()
        || !elab
            .arrays
            .keys()
            .any(|name| elab.nets.contains(name.as_str()))
    {
        return HashMap::default();
    }
    // Only cells that need net resolution get scalar driver names. Ordinary
    // stores retain the element type and the port keeps its connection copy.
    let mut seen = HashSet::default();
    let mut resolve = HashMap::default();
    let merged: HashSet<&str> = elab.net_port_merges.values().map(String::as_str).collect();
    let mut count = |lhs: &Expression| {
        if let Some((cell, base)) = fixed_net_cell(elab, lhs) {
            if !seen.insert(cell.clone())
                || elab.resolved_net_kinds.contains_key(base.as_str())
                || merged.contains(cell.as_str())
            {
                resolve.insert(cell, elab.arrays[&base].2);
            }
        }
    };
    for ca in &elab.continuous_assigns {
        count(&ca.lhs);
    }
    for p in &elab.pending_cont_assign {
        count(&p.materialize_lhs());
    }
    if resolve.is_empty() {
        return HashMap::default();
    }
    for p in std::mem::take(&mut elab.pending_cont_assign) {
        if fixed_net_cell(elab, &p.materialize_lhs()).is_some_and(|(cell, _)| resolve.contains_key(&cell)) {
            elab.continuous_assigns.push(p.materialize(&elab.parameters));
        } else {
            elab.pending_cont_assign.push(p);
        }
    }
    let mut assignments = std::mem::take(&mut elab.continuous_assigns);
    for ca in &mut assignments {
        if fixed_net_cell(elab, &ca.lhs).is_some_and(|(cell, _)| resolve.contains_key(&cell)) {
            register_fixed_net_cell(elab, &mut ca.lhs);
        }
    }
    elab.continuous_assigns = assignments;
    resolve
}

pub fn resolve_multi_driver_nets(elab: &mut ElaboratedModule) {
    let resolved_cells = normalize_net_cell_drivers(elab);
    widen_overlapping_select_drivers(elab);
    // §10.11: the names an `alias` statement names are ONE physical net, so
    // a driver of any member of a group is a driver of the group's
    // canonical net. The map is taken out of the module so the fold below
    // can use it while the module's own tables are moved.
    let alias_canon: HashMap<String, String> = elab.alias_canon.clone();
    let port_aliases: HashMap<String, String> = elab.port_aliases.clone();
    let top_name: String = elab.name.clone();
    // §23.3.3.3: an INOUT port and the net it is connected to are ONE
    // physical net, so the connection copies the net onto itself and drives
    // nothing. An input or output connection is a directional copy and DOES
    // drive its net.
    let merged_formals: HashSet<String> = elab.net_port_merges.keys().cloned().collect();
    // The name of the top scope may also be an instance name in the design
    // (a child named like the top), and such a reference names that child.
    let top_shadowed = elab
        .instances
        .iter()
        .any(|i| i.path.split('.').next() == Some(top_name.as_str()));
    // §10.11: the canonical name of the physical net a driver name belongs
    // to. A name of an alias member names the group's canonical net; a name
    // that reaches the group through a port (`u.p`, `u.h.p`) names it too.
    let alias_lookup_name = |n: &str| -> Option<String> {
        if alias_canon.is_empty() {
            return None;
        }
        if let Some(c) = alias_canon.get(n) {
            return Some(c.clone());
        }
        if port_aliases.is_empty() {
            return None;
        }
        // §23.3.3: a port name reaches the net it is connected to; the
        // chain of collapsed levels is followed to its end.
        let mut cur = n;
        for _ in 0..64 {
            let Some(actual) = port_aliases.get(cur) else {
                break;
            };
            if let Some(c) = alias_canon.get(actual) {
                return Some(c.clone());
            }
            if actual == cur {
                break;
            }
            cur = actual.as_str();
        }
        None
    };
    // The same for a driver's left-hand side: a reference into the top
    // scope may be written with the scope's name (`top.b`) or from the root
    // (`$root.top.b`), and both name the top scope's `b` (§23.6).
    let alias_lookup_lhs = |e: &Expression| -> Option<String> {
        if alias_canon.is_empty() {
            return None;
        }
        let ExprKind::Ident(h) = &e.kind else {
            return None;
        };
        if !h.path.iter().all(|s| s.selects.is_empty()) {
            return None;
        }
        let flat = h
            .path
            .iter()
            .map(|s| s.name.name.as_str())
            .collect::<Vec<_>>()
            .join(".");
        // A root reference is written `$root.top.b`; elaboration may carry
        // the root as a path segment of its own.
        let (flat, rooted) = match flat.strip_prefix("$root.") {
            Some(rest) => (rest, true),
            None => (flat.as_str(), h.root.is_some()),
        };
        if let Some(c) = alias_lookup_name(flat) {
            return Some(c);
        }
        // A root reference (`$root.top.b`) names the top scope whatever the
        // scope it is written in. A plain `top.b` names the top scope too
        // unless an instance of the design carries that name (§23.6).
        if !rooted && top_shadowed {
            return None;
        }
        let rest = flat.strip_prefix(top_name.as_str())?.strip_prefix('.')?;
        alias_canon.get(rest).cloned()
    };
    // §26.2: a package net driven by its qualified name (`assign
    // nets::w = ...`, a port connected to `nets::w`) is the hoisted bare net
    // `w`. Spelled `nets.w` its drivers were never counted together, so a
    // `wand` kept the last write (#610). Not when a local declaration
    // displaces the bare name (`local_decl_displaces`): that is another net.
    if !elab.packages.is_empty() {
        for ca in elab.continuous_assigns.iter_mut() {
            if let ExprKind::Ident(h) = &ca.lhs.kind
                && h.root.is_none()
                && h.path.len() == 2
                && h.path.iter().all(|s| s.selects.is_empty())
                && elab.packages.contains(&h.path[0].name.name)
                && elab
                    .nets
                    .contains(&format!("{}::{}", h.path[0].name.name, h.path[1].name.name))
            {
                let bare = h.path[1].name.name.clone();
                if elab.nets.contains(&bare)
                    && !elab.wildcard_shadowed.contains(&bare)
                    && !elab.foreign_package_names.contains(&bare)
                {
                    ca.lhs = make_ident_expr(&bare);
                }
            }
        }
    }
    // §28.12: a driver with a strength inside an instance joins the roster
    // now, so its net records the strength for `%v` like a top-level one.
    if elab
        .pending_cont_assign
        .iter()
        .any(|p| p.strength.is_some())
    {
        let pending = std::mem::take(&mut elab.pending_cont_assign);
        for p in pending {
            if p.strength.is_some() {
                let ca = p.materialize(&elab.parameters);
                elab.continuous_assigns.push(ca);
            } else {
                elab.pending_cont_assign.push(p);
            }
        }
    }
    stage_shared_udp_outputs(elab);
    // §14.16: a clocking output is a driver of its net, so it takes part in
    // the net's resolution. It drives a stage of its own when the net has
    // another driver.
    stage_shared_clocking_outputs(elab);
    // §28.12 / §21.2.1.5: a net with ONE driver that carries a strength or
    // is a tristate primitive keeps that driver for `%v`; a net several
    // drivers resolve replaces it below.
    let mut single: Vec<(String, StrengthDriver)> = Vec::new();
    for ca in &elab.continuous_assigns {
        // §23.3.3.3: the connection of an INOUT port is a copy of the net
        // onto itself; it contributes no strength of its own.
        if ca.rhs_parent_scoped
            && let Some(f) = ident_flat_name(&ca.lhs)
            && merged_formals.contains(&f)
        {
            continue;
        }
        // §10.11: the group's members are one net, so the strength a driver
        // records belongs to the group's canonical net.
        let n = match alias_lookup_lhs(&ca.lhs) {
            Some(c) => c,
            None => {
                let Some(n) = ident_flat_name(&ca.lhs) else {
                    continue;
                };
                alias_lookup_name(&n).unwrap_or(n)
            }
        };
        if !elab.nets.contains(&n) {
            continue;
        }
        if let Some((ctl, data)) = gate_tristate_parts(ca) {
            single.push((
                n,
                StrengthDriver {
                    value: data.clone(),
                    ctl: Some(ctl.clone()),
                    s0: 6,
                    s1: 6,
                },
            ));
        } else if let ExprKind::SystemCall { name, args } = &ca.rhs.kind
            && matches!(
                name.as_str(),
                "$__supply" | "$__drive" | "$__pull" | "$__weak"
            )
            && let (Some(v), Some(code)) = (
                args.first(),
                args.get(1)
                    .and_then(|c| const_eval_i64_with_params(c, None)),
            )
        {
            let code = code as u8;
            single.push((
                n,
                StrengthDriver {
                    value: v.clone(),
                    ctl: None,
                    s0: code / 8,
                    s1: code % 8,
                },
            ));
        }
    }
    for (n, d) in single {
        elab.strength_drivers.insert(n, vec![d]);
    }
    // A user-written HIERARCHICAL continuous assign onto an instance PORT
    // (`assign dut.u_mid.u_leaf.clk_i = tb_clk;` — a multi-segment path)
    // drives the port's whole alias chain: the simulator fans it out across
    // every collapsed level of the connection. Counting it here as a second
    // driver beside the port's own connect assign folded the two into one
    // `$__wres` on a single level, consuming both the connect alias and the
    // drive, so readers bound at another level of the chain were never
    // driven. That broke every such drive onto a port declared as a net
    // (`input wire clk_i`, and §23.2.2.3 implicit-net ports like
    // `input logic clk_i`); leave it to the fan-out.
    let is_hier_port_drive = |ca: &ContinuousAssignment| -> bool {
        matches!(&ca.lhs.kind,
            ExprKind::Ident(h) if h.path.len() > 1 && h.path.iter().all(|s| s.selects.is_empty()))
            && ident_flat_name(&ca.lhs)
                .is_some_and(|n| elab.signals.get(&n).is_some_and(|s| s.direction.is_some()))
    };
    // The net a continuous assignment drives, and whether it drives it at
    // all. A driver of an alias member drives the group's canonical net
    // (§10.11); a port connection is an implied continuous assignment — a
    // COPY of the actual into the formal (§23.3.3.2) — and drives nothing;
    // a hierarchical drive onto a port of an alias group DOES drive the
    // physical net.
    let driver_net = |ca: &ContinuousAssignment, hier: bool| -> Option<String> {
        let flat = ident_flat_name(&ca.lhs);
        // §23.3.3.3: the connection of an INOUT port is a copy of the net
        // onto itself; it drives nothing.
        if ca.rhs_parent_scoped
            && flat.as_deref().is_some_and(|f| merged_formals.contains(f))
        {
            return None;
        }
        match alias_lookup_lhs(&ca.lhs) {
            Some(c) => Some(c),
            None => {
                if hier {
                    None
                } else {
                    flat
                }
            }
        }
    };
    // Keyed by the flat name, borrowed from a single-segment lhs (every
    // inlined connect), so counting costs no copy per assign.
    let mut counts: HashMap<std::borrow::Cow<'_, str>, usize> = HashMap::default();
    for ca in &elab.continuous_assigns {
        if ca.rhs_parent_scoped
            && let Some(f) = ident_flat_name(&ca.lhs)
            && merged_formals.contains(&f)
        {
            // §23.3.3.3: the connection of an INOUT port is a copy of the
            // net onto itself; it drives nothing.
            continue;
        }
        // §10.11: a driver of an alias member drives the group's canonical
        // net, so it is counted there.
        if let Some(c) = alias_lookup_lhs(&ca.lhs) {
            *counts
                .entry(std::borrow::Cow::Owned(c))
                .or_insert(0) += 1;
            continue;
        }
        if is_hier_port_drive(ca) {
            continue;
        }
        let n = match &ca.lhs.kind {
            ExprKind::Ident(h) if h.path.len() == 1 && h.path[0].selects.is_empty() => {
                Some(std::borrow::Cow::Borrowed(h.path[0].name.name.as_str()))
            }
            _ => ident_flat_name(&ca.lhs).map(std::borrow::Cow::Owned),
        };
        if let Some(n) = n {
            *counts.entry(n).or_insert(0) += 1;
        }
    }
    // Sub-module bodies may still sit in the LAZY pending list; two
    // instances driving one parent net (`m u1(.b(b)); m u2(.b(b));`) are
    // invisible to the count above — the net silently lost ALL drivers
    // (read z). Resolve each pending assign's LHS name (cheap: one ident
    // rewrite), and MATERIALIZE only the entries that hit a multi-driven
    // net so they join the fold; everything else stays lazy.
    let pending_lhs: Vec<Option<String>> = elab
        .pending_cont_assign
        .iter()
        .map(|p| {
            let lhs = p.materialize_lhs();
            // §10.11: a driver of an alias member drives the group's
            // canonical net.
            match alias_lookup_lhs(&lhs) {
                Some(c) => Some(c),
                None => ident_flat_name(&lhs).map(|n| alias_lookup_name(&n).unwrap_or(n)),
            }
        })
        .collect();
    for n in pending_lhs.iter().flatten() {
        *counts
            .entry(std::borrow::Cow::Owned(n.clone()))
            .or_insert(0) += 1;
    }
    // A tri0/tri1 net needs the fold even with a SINGLE driver, because the
    // implicit pull is a second (weak) driver: `strong` alone would leave the
    // bits that driver holds at z reading z instead of pulling. Nets with NO
    // driver never reach the fold at all and are handled by their declared
    // initial value instead (see the net-declaration sites).
    let mut multi: HashSet<String> = counts
        .iter()
        .filter(|(n, c)| **c > 1 && elab.nets.contains(n.as_ref()))
        .map(|(n, _)| n.to_string())
        .collect();
    for (n, c) in &counts {
        if *c >= 1
            && elab.nets.contains(n.as_ref())
            && matches!(
                elab.resolved_net_kinds.get(n.as_ref()),
                Some(ResolvedNetKind::Tri0)
                    | Some(ResolvedNetKind::Tri1)
                    | Some(ResolvedNetKind::ChargeStorage)
            )
        {
            // A WHOLE-NET port connection (`.p(w)`) is one physical net, and
            // after substitution the sub-module's drivers land on the ACTUAL
            // (`w`), leaving the leftover formal `u_diff.p` as a pure reader
            // driven only by its connection assign. If it is itself tri0/tri1
            // it joined `multi` here and folded a SECOND time — for a
            // same-named actual (`u_same.p` vs `p`) that second fold read the
            // actual it was also writing, a cycle that settled to x and made
            // `@(p)` inside hang (#1060). The actual carries the merged kind
            // (see the `port_aliases` insertion), so the leftover must NOT
            // pull-fold independently. A VARIABLE actual (`.p(r)`) is not
            // part of the net: the port keeps its own pull, and reads 1
            // while the variable holds z. An OUTPUT formal is the real SOURCE
            // (its driver is not substituted), so it keeps folding. A
            // leftover with >1 driver still folds via the `count > 1` rule
            // above.
            if *c == 1
                && elab
                    .port_aliases
                    .get(n.as_ref())
                    .is_some_and(|actual| elab.nets.contains(actual))
                && matches!(
                    elab.signals.get(n.as_ref()).map(|s| s.direction),
                    Some(Some(PortDirection::Inout | PortDirection::Input))
                )
            {
                continue;
            }
            multi.insert(n.to_string());
        }
    }
    // §6.6.4: a trireg's charge starts unknown once something drives it,
    // but a trireg no driver reaches at all is high-impedance (as the
    // reference simulator reads it).
    let undriven_trireg: Vec<String> = elab
        .resolved_net_kinds
        .iter()
        .filter(|(n, k)| {
            matches!(k, ResolvedNetKind::ChargeStorage) && !counts.contains_key(n.as_str())
        })
        .map(|(n, _)| n.clone())
        .collect();
    drop(counts);
    let set_undriven_z = |elab: &mut ElaboratedModule| {
        for n in &undriven_trireg {
            if let Some(sig) = elab.signals.get_mut(n)
                && !sig.is_real
            {
                sig.value = Value::all_z(sig.width.max(1));
            }
        }
    };
    if multi.is_empty() {
        set_undriven_z(elab);
        return;
    }
    // §28.12: the single-driver entries recorded above are per NET, so with
    // several tristate primitives the last one stood for the whole net. The
    // fold below records the drivers of a resolved net afresh where their
    // strengths matter; without this a net whose tristate drivers all moved
    // to delayed stages kept that one entry, and read as that one primitive,
    // undelayed, with every other driver ignored.
    for n in &multi {
        elab.strength_drivers.remove(n);
    }
    if pending_lhs
        .iter()
        .any(|n| n.as_ref().is_some_and(|n| multi.contains(n)))
    {
        let pending = std::mem::take(&mut elab.pending_cont_assign);
        for (p, name) in pending.into_iter().zip(pending_lhs) {
            if name.is_some_and(|n| multi.contains(&n)) {
                let ca = p.materialize(&elab.parameters);
                elab.continuous_assigns.push(ca);
            } else {
                elab.pending_cont_assign.push(p);
            }
        }
    }
    let all = std::mem::take(&mut elab.continuous_assigns);
    let hier_port_drive: Vec<bool> = all.iter().map(is_hier_port_drive).collect();
    // §10.3.3: each continuous assignment's delay is its OWN — it delays that
    // driver's value before the net resolves it with the others. Folding the
    // drivers into one assign that carried the FIRST driver's delay ran every
    // driver through it: `wor #2 w = a; assign w = b;` delayed `b` by 2 too.
    // Where several drivers meet and any carries a delay, each delayed driver
    // keeps its delay on a driver net of its own (`<net>$drv<k>`), and the
    // fold reads those undelayed.
    let mut fold_drivers: HashMap<String, (usize, bool)> = HashMap::default();
    for (ca, &hier) in all.iter().zip(&hier_port_drive) {
        if let Some(n) = driver_net(ca, hier).filter(|n| multi.contains(n)) {
            let e = fold_drivers.entry(n).or_insert((0, false));
            e.0 += 1;
            e.1 |= cont_assign_has_own_delay(ca);
        }
    }
    let split_delays: HashSet<String> = fold_drivers
        .into_iter()
        .filter(|(_, (count, delayed))| *count > 1 && *delayed)
        .map(|(n, _)| n)
        .collect();
    // §28.16: a primitive's fall delay is recorded under the net it drives.
    // Where the net's drivers get a stage each, that entry moves to the
    // primitive's own stage — a tristate, MOS or zero-rise primitive
    // included — so the net itself is no longer delayed by one of them.
    let split_gate_delays: HashSet<String> = split_delays
        .iter()
        .filter(|n| elab.gate_fall_delays.contains_key(*n))
        .cloned()
        .collect();
    for name in &split_gate_delays {
        elab.gate_fall_delays.remove(name);
    }
    let mut split_count: HashMap<String, usize> = HashMap::default();
    // Per multi-driven net: keep the lhs/delay, and accumulate STRONG drivers
    // and WEAK (pull) drivers into separate `$__wres` chains. A pull driver's
    // rhs is `$__pull(v)`; unwrap it into the weak chain. Final rhs resolves
    // strong first and only falls back to the pull where strong is z.
    struct Acc {
        lhs: Expression,
        delay: u64,
        delay_fall: Option<u64>,
        delay_off: Option<u64>,
        /// §28.12 drive-strength levels, strongest first: supply, strong
        /// (the default), pull (`weak` below, which also holds a tri0/tri1
        /// net's implicit pull and a trireg's charge), weak.
        supply: Option<Expression>,
        strong: Option<Expression>,
        weak: Option<Expression>,
        weakest: Option<Expression>,
        /// Tristate-primitive drivers `(ctl, data)`, resolved together with
        /// the strong chain by one `$__wres_tri`.
        tri: Vec<(Expression, Expression)>,
    }
    let mut folded: HashMap<String, Acc> = HashMap::default();
    let mut order: Vec<String> = Vec::new();
    // The strength level a driver's marker gives it: 0 supply, 1 strong
    // (unmarked), 2 pull, 3 weak.
    let marker_level = |e: &Expression| match &e.kind {
        ExprKind::SystemCall { name, .. } if name == "$__supply" => Some(0u8),
        ExprKind::SystemCall { name, .. } if name == "$__drive" => Some(1),
        ExprKind::SystemCall { name, .. } if name == "$__pull" => Some(2),
        ExprKind::SystemCall { name, .. } if name == "$__weak" => Some(3),
        _ => None,
    };
    // §28.12 strength pair of a marked driver (see `strength_code`); an
    // unmarked one is strong.
    let marker_code = |e: &Expression| -> Option<u8> {
        match &e.kind {
            ExprKind::SystemCall { args, .. } if marker_level(e).is_some() => args
                .get(1)
                .and_then(|c| const_eval_i64_with_params(c, None))
                .map(|c| c as u8),
            _ => None,
        }
    };
    // Per folded net: its drivers with their strengths, and whether any
    // of them makes the strengths worth keeping for `%v`.
    let mut strength: HashMap<String, (Vec<StrengthDriver>, bool)> = HashMap::default();
    for (ca, hier) in all.into_iter().zip(hier_port_drive) {
        let name = driver_net(&ca, hier).filter(|n| multi.contains(n));
        let Some(name) = name else {
            elab.continuous_assigns.push(ca);
            continue;
        };
        let mut ca = ca;
        if split_delays.contains(&name) && cont_assign_has_own_delay(&ca) {
            let k = split_count.entry(name.clone()).or_insert(0);
            let drv = format!("{name}$drv{k}");
            *k += 1;
            if let Some(sig) = elab.signals.get(&name) {
                let mut sig = sig.clone();
                sig.name = drv.clone().into();
                sig.direction = None;
                elab.signals.insert(drv.clone(), sig);
            }
            let rhs = make_ident_expr(&drv);
            let mut delayed = ca.clone();
            if delayed.origin.is_some() && delayed.delay_select.is_none() {
                delayed.delay_select = continuous_assign_delay_select(&ca.lhs, elab, None);
            }
            delayed.lhs = make_ident_expr(&drv);
            if split_gate_delays.contains(&name)
                && let Some(fall) = ca.gate_delay_fall
            {
                delayed.delay_fall = Some(fall);
                elab.gate_driven_nets.insert(drv.clone());
                if fall != ca.delay {
                    elab.gate_fall_delays.insert(drv.clone(), fall);
                }
            }
            // A strength marker stays on the folded driver (its level and
            // §28.12 pair); the delayed driver net carries the bare value.
            let marked = match &ca.rhs.kind {
                ExprKind::SystemCall { name: m, args } if marker_level(&ca.rhs).is_some() => {
                    delayed.rhs = args
                        .first()
                        .cloned()
                        .unwrap_or_else(|| make_z_expr(ca.rhs.span));
                    let mut margs = vec![Expression::new(rhs.kind.clone(), ca.rhs.span)];
                    margs.extend(args.iter().skip(1).cloned());
                    Some(make_syscall(m, margs, ca.rhs.span))
                }
                _ => None,
            };
            elab.continuous_assigns.push(delayed);
            ca.rhs = marked.unwrap_or_else(|| Expression::new(rhs.kind, ca.rhs.span));
            ca.delay = 0;
            ca.delay_exprs = None;
            ca.delay_fall = None;
            ca.delay_off = None;
        }
        let span = ca.rhs.span;
        let slot = folded.entry(name.clone()).or_insert_with(|| {
            order.push(name.clone());
            let split = split_delays.contains(&name);
            Acc {
                lhs: if resolved_cells.contains_key(&name) {
                    make_net_lhs_expr(&name)
                } else {
                    make_ident_expr(&name)
                },
                delay: if split { 0 } else { ca.delay },
                delay_fall: if split { None } else { ca.delay_fall },
                delay_off: if split { None } else { ca.delay_off },
                supply: None,
                strong: None,
                weak: None,
                weakest: None,
                tri: Vec::new(),
            }
        });
        // §28.4/§28.7: a tristate primitive with an unknown control drives
        // `L`/`H` (its value or z), so it is resolved against the net's
        // other drivers last, by `$__wres_tri` — on a plain wire only.
        if !matches!(
            elab.resolved_net_kinds.get(&name),
            Some(ResolvedNetKind::Wand)
                | Some(ResolvedNetKind::Wor)
                | Some(ResolvedNetKind::RealSum)
        ) {
            if let Some((ctl, data)) = gate_tristate_parts(&ca) {
                slot.tri.push((ctl.clone(), data.clone()));
                let e = strength.entry(name.clone()).or_default();
                e.0.push(StrengthDriver {
                    value: data.clone(),
                    ctl: Some(ctl.clone()),
                    s0: 6,
                    s1: 6,
                });
                e.1 = true;
                continue;
            }
        }
        // Unwrap a strength marker into the raw value for its level's chain.
        let marked = marker_level(&ca.rhs);
        let level = marked.unwrap_or(1);
        let code = marker_code(&ca.rhs).unwrap_or(6 * 8 + 6);
        let rhs = if marked.is_some() {
            if let ExprKind::SystemCall { args, .. } = ca.rhs.kind {
                args.into_iter().next().unwrap_or_else(|| make_z_expr(span))
            } else {
                make_z_expr(span)
            }
        } else {
            ca.rhs
        };
        let e = strength.entry(name.clone()).or_default();
        e.0.push(StrengthDriver {
            value: rhs.clone(),
            ctl: None,
            s0: code / 8,
            s1: code % 8,
        });
        e.1 |= marked.is_some();
        let weak = level != 1;
        let slot = folded.get_mut(&name).expect("slot created above");
        // §6.6.2: a wand/triand net ANDs its drivers and a wor/trior net ORs
        // them, instead of the wire rule (z yields, equal passes, conflict ->
        // x). Plain wires and the weak pull chain keep `$__wres`.
        let fold_op = match elab.resolved_net_kinds.get(&name) {
            Some(ResolvedNetKind::Wand) if !weak => "$__wand",
            Some(ResolvedNetKind::Wor) if !weak => "$__wor",
            _ => "$__wres",
        };
        let chain = match level {
            0 => &mut slot.supply,
            1 => &mut slot.strong,
            2 => &mut slot.weak,
            _ => &mut slot.weakest,
        };
        let sums = matches!(
            elab.resolved_net_kinds.get(&name),
            Some(ResolvedNetKind::RealSum)
        );
        *chain = Some(match chain.take() {
            // A `wreal` net adds its drivers. Plain `+` rather than a
            // marker syscall, so this rides the ordinary real arithmetic
            // path and folds like any other sum.
            Some(acc) if sums => Expression::new(
                ExprKind::Binary {
                    op: crate::ast::expr::BinaryOp::Add,
                    left: Box::new(acc),
                    right: Box::new(rhs),
                },
                span,
            ),
            Some(acc) => make_syscall(fold_op, vec![acc, rhs], span),
            None => rhs,
        });
    }
    // §6.6.3 tri0/tri1: bits that no driver is driving pull to 0/1. Model that
    // as an implicit WEAK driver, which is exactly what `$__wres_pull` already
    // resolves against the strong chain — so a real driver still wins and only
    // undriven (z) bits take the pull.
    for (name, acc) in folded.iter_mut() {
        let pull_bit = match elab.resolved_net_kinds.get(name) {
            Some(ResolvedNetKind::Tri0) => Some(false),
            Some(ResolvedNetKind::Tri1) => Some(true),
            _ => None,
        };
        if let Some(one) = pull_bit {
            if acc.weak.is_none() {
                let span = acc.lhs.span;
                acc.weak = Some(make_fill_expr(one, span));
            }
            let w = resolved_cells.get(name).copied().or_else(|| elab.signals.get(name).map(|s| s.width)).unwrap_or(1).max(1);
            let fill = if one { Value::ones(w) } else { Value::zero(w) };
            let e = strength.entry(name.clone()).or_default();
            e.0.push(StrengthDriver {
                value: const_value_literal(&fill, acc.lhs.span)
                    .unwrap_or_else(|| make_fill_expr(one, acc.lhs.span)),
                ctl: None,
                s0: 5,
                s1: 5,
            });
            e.1 = true;
        }
        // §6.6.4 trireg: undriven bits HOLD the previous value — the implicit
        // weak driver is the net's own current value. The self-reference is a
        // fixpoint (held bits re-read unchanged), so settling converges.
        if matches!(
            elab.resolved_net_kinds.get(name),
            Some(ResolvedNetKind::ChargeStorage)
        ) && acc.weak.is_none()
        {
            acc.weak = Some(make_ident_expr(name));
            // §28.12: the held charge is of medium strength.
            let e = strength.entry(name.clone()).or_default();
            e.0.push(StrengthDriver {
                value: make_ident_expr(name),
                ctl: None,
                s0: 2,
                s1: 2,
            });
            e.1 = true;
        }
    }
    for (name, (drivers, keep)) in strength {
        // Wired AND/OR and summed nets do not resolve by strength alone.
        let wired = matches!(
            elab.resolved_net_kinds.get(&name),
            Some(ResolvedNetKind::Wand)
                | Some(ResolvedNetKind::Wor)
                | Some(ResolvedNetKind::RealSum)
        );
        if keep && !wired {
            elab.strength_drivers.insert(name, drivers);
        }
    }
    for name in order {
        if let Some(mut acc) = folded.remove(&name) {
            let span = acc.lhs.span;
            if !acc.tri.is_empty() {
                let w = resolved_cells.get(&name).copied().or_else(|| elab.signals.get(&name).map(|s| s.width)).unwrap_or(1).max(1);
                let mut args = vec![acc.strong.take().unwrap_or_else(|| make_z_fill(w, span))];
                for (ctl, data) in std::mem::take(&mut acc.tri) {
                    args.push(ctl);
                    args.push(data);
                }
                acc.strong = Some(make_syscall("$__wres_tri", args, span));
            }
            // §28.12: a stronger level wins on every bit it drives; a weaker
            // one fills only the bits the stronger levels leave at z.
            let over = |hi: Option<Expression>, lo: Option<Expression>| match (hi, lo) {
                (Some(h), Some(l)) => Some(make_syscall("$__wres_pull", vec![h, l], span)),
                (h, l) => h.or(l),
            };
            let rhs = over(acc.supply, over(acc.strong, over(acc.weak, acc.weakest)))
                .unwrap_or_else(|| make_z_expr(span));
            // §28.12: a net whose drivers carry strengths resolves them by
            // strength — `$__sres(width, pair, ctl, value, ...)`, the
            // resolution `%v` reports. The level chains above only order
            // whole strength classes, so a tristate's `H` beside a pull or an
            // asymmetric pair (`strong0, weak1`) came out wrong.
            let rhs = match elab.strength_drivers.get(&name) {
                Some(drivers) => {
                    let w = resolved_cells.get(&name).copied().or_else(|| elab.signals.get(&name).map(|s| s.width)).unwrap_or(1).max(1);
                    let mut args = vec![
                        const_value_literal(&Value::from_u64(u64::from(w), 32), span)
                            .expect("width literal"),
                    ];
                    for d in drivers {
                        args.push(strength_code_literal(d.s0 * 8 + d.s1, span));
                        args.push(d.ctl.clone().unwrap_or_else(|| make_fill_expr(true, span)));
                        args.push(d.value.clone());
                    }
                    make_syscall("$__sres", args, span)
                }
                None => rhs,
            };
            elab.continuous_assigns.push(ContinuousAssignment {
                gate_delay_fall: None,
                delay_exprs: None,
                delay_select: None,
                origin: None,
                lhs: acc.lhs,
                rhs,
                delay: acc.delay,
                // A multi-driver fold merges driver expressions from several
                // scopes (§23.3.3.7 strand resolution); the merged `$__wres`/
                // `$__wor` reads are already bound in their own scopes. Mark it
                // parent-scoped so the simulator does NOT re-infer a parent
                // scope hint from the folded LHS (`l.n`) and requalify a bare
                // driver read that collides with a child declaration into the
                // folded net itself (self-read -> x).
                rhs_parent_scoped: true,
                delay_fall: acc.delay_fall,
                delay_off: acc.delay_off,
            });
        }
    }
    set_undriven_z(elab);
}

pub fn resolve_bidirectional_switches(elab: &mut ElaboratedModule) {
    let switches = std::mem::take(&mut elab.tran_switches);
    if switches.is_empty() {
        return;
    }
    // A terminal's drivers may live in a sub-module and still be pending. The
    // pass needs every driver of every terminal in hand, so materialize them.
    // Only designs that actually contain a switch pay for this.
    let pending = std::mem::take(&mut elab.pending_cont_assign);
    for p in pending {
        let ca = p.materialize(&elab.parameters);
        elab.continuous_assigns.push(ca);
    }
    // A cross-module terminal names the top module explicitly; signals and
    // driver lvalues are keyed without that root.
    let root = format!("{}.", elab.name);
    let norm = |n: String| -> String {
        n.strip_prefix(root.as_str())
            .map(|r| r.to_string())
            .unwrap_or(n)
    };
    for sw in switches {
        let (Some(na), Some(nb)) = (
            ident_flat_name(&sw.a).map(&norm),
            ident_flat_name(&sw.b).map(&norm),
        ) else {
            continue;
        };
        let (term_a, term_b) = (make_ident_expr(&na), make_ident_expr(&nb));
        let span = sw.a.span;

        // Each terminal's OWN drivers, folded with the wired-net resolution.
        let mut take_drivers = |name: &str| -> Option<Expression> {
            let mut rhs: Vec<Expression> = Vec::new();
            elab.continuous_assigns.retain(|ca| {
                if ident_flat_name(&ca.lhs).map(&norm).as_deref() == Some(name) {
                    rhs.push(ca.rhs.clone());
                    false
                } else {
                    true
                }
            });
            let mut it = rhs.into_iter();
            let first = it.next()?;
            Some(it.fold(first, |acc, r| make_syscall("$__wres", vec![acc, r], span)))
        };
        let own_a = take_drivers(&na);
        let own_b = take_drivers(&nb);
        // A terminal with no driver of its own contributes high impedance.
        let z = || make_z_expr(span);
        let own_a = own_a.unwrap_or_else(z);
        let own_b = own_b.unwrap_or_else(z);

        let ctl = sw.ctl.clone().unwrap_or_else(|| {
            Expression::new(
                ExprKind::Number(crate::ast::expr::NumberLiteral::UnbasedUnsized('1')),
                span,
            )
        });
        let active = Expression::new(
            ExprKind::Number(crate::ast::expr::NumberLiteral::UnbasedUnsized(
                if sw.active_high { '1' } else { '0' },
            )),
            span,
        );

        elab.continuous_assigns.push(ContinuousAssignment {
            gate_delay_fall: None,
            delay_exprs: None,
            delay_select: None,
            origin: None,
            lhs: term_a,
            rhs: make_syscall(
                "$__tranif",
                vec![own_a.clone(), own_b.clone(), ctl.clone(), active.clone()],
                span,
            ),
            delay: 0,
            rhs_parent_scoped: true,
            delay_fall: None,
            delay_off: None,
        });
        elab.continuous_assigns.push(ContinuousAssignment {
            gate_delay_fall: None,
            delay_exprs: None,
            delay_select: None,
            origin: None,
            lhs: term_b,
            rhs: make_syscall("$__tranif", vec![own_b, own_a, ctl, active], span),
            delay: 0,
            rhs_parent_scoped: true,
            delay_fall: None,
            delay_off: None,
        });
    }
}
