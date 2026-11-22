use super::*;

/// Build a high-impedance (`'z`) literal expression for tristate gate models.
/// `'0` / `'1` — an unbased-unsized fill, which replicates to the consuming
/// width. Used as the implicit weak driver of a tri0/tri1 net (§6.6.3).
pub(super) fn make_fill_expr(one: bool, span: Span) -> Expression {
    Expression::new(
        ExprKind::Number(crate::ast::expr::NumberLiteral::UnbasedUnsized(if one {
            '1'
        } else {
            '0'
        })),
        span,
    )
}

pub(super) fn make_z_expr(span: Span) -> Expression {
    Expression::new(
        ExprKind::Number(crate::ast::expr::NumberLiteral::UnbasedUnsized('z')),
        span,
    )
}

/// `cond ? then : 'z` — the canonical enabled-output / tristate shape used by
/// `bufif`/`notif` and the MOS/switch primitives.
pub(super) fn make_tristate(cond: Expression, then_e: Expression, span: Span) -> Expression {
    Expression::new(
        ExprKind::Conditional {
            condition: Box::new(cond),
            then_expr: Box::new(then_e),
            else_expr: Box::new(make_z_expr(span)),
        },
        span,
    )
}

pub(super) fn gate_inst_to_assign_pairs(gi: &GateInstantiation) -> Vec<(Expression, Expression)> {
    let mut pairs = Vec::new();
    for inst in &gi.instances {
        // §28 pull gates: `pullup (net)` / `pulldown (net)` — single terminal
        // tied to a constant. Handled before the 2-terminal guard.
        match gi.gate_type {
            GateType::Pullup | GateType::Pulldown => {
                if let Some(net) = inst.terminals.first() {
                    let v = if matches!(gi.gate_type, GateType::Pullup) {
                        '1'
                    } else {
                        '0'
                    };
                    let lit = Expression::new(
                        ExprKind::Number(crate::ast::expr::NumberLiteral::UnbasedUnsized(v)),
                        net.span,
                    );
                    // §28.4: pullup/pulldown are WEAK (pull strength). Tag the
                    // driver so multi-driver resolution lets a strong driver win
                    // and only falls back to the pull where the net is otherwise
                    // z. A lone pull driver evaluates to its value ($__pull is
                    // identity in the simulator).
                    let code = strength_code_literal(5 * 8 + 5, net.span);
                    let weak = make_syscall("$__pull", vec![lit, code], net.span);
                    pairs.push((net.clone(), weak));
                }
                continue;
            }
            _ => {}
        }
        if inst.terminals.len() < 2 {
            continue;
        }
        let out = inst.terminals[0].clone();
        let in1 = inst.terminals[1].clone();
        let sp = out.span;
        match gi.gate_type {
            // §28 tristate buffers/inverters: `bufif1(out,in,ctl)` etc.
            GateType::Bufif1 | GateType::Bufif0 | GateType::Notif1 | GateType::Notif0
                if inst.terminals.len() >= 3 =>
            {
                let ctl = inst.terminals[2].clone();
                // §28.4 Table 28-5: a bufif with a `z` data input drives `x`
                // (the gate is a buffer, not a switch). `d ^ '0` maps z to x
                // and passes 0, 1 and x unchanged; notif's `~d` already does.
                let data = if matches!(gi.gate_type, GateType::Notif0 | GateType::Notif1) {
                    Expression::new(
                        ExprKind::Unary {
                            op: UnaryOp::BitNot,
                            operand: Box::new(in1),
                        },
                        sp,
                    )
                } else {
                    Expression::new(
                        ExprKind::Binary {
                            op: BinaryOp::BitXor,
                            left: Box::new(in1),
                            right: Box::new(make_fill_expr(false, sp)),
                        },
                        sp,
                    )
                };
                let active_high = matches!(gi.gate_type, GateType::Bufif1 | GateType::Notif1);
                let cond = if active_high {
                    ctl
                } else {
                    Expression::new(
                        ExprKind::Unary {
                            op: UnaryOp::LogNot,
                            operand: Box::new(ctl),
                        },
                        sp,
                    )
                };
                pairs.push((out, make_tristate(cond, data, sp)));
            }
            // §28 MOS switches: `nmos(out,data,ctl)` conducts on ctl, `pmos` on !ctl.
            GateType::Nmos | GateType::Rnmos | GateType::Pmos | GateType::Rpmos
                if inst.terminals.len() >= 3 =>
            {
                let ctl = inst.terminals[2].clone();
                let active_high = matches!(gi.gate_type, GateType::Nmos | GateType::Rnmos);
                let cond = if active_high {
                    ctl
                } else {
                    Expression::new(
                        ExprKind::Unary {
                            op: UnaryOp::LogNot,
                            operand: Box::new(ctl),
                        },
                        sp,
                    )
                };
                pairs.push((out, make_tristate(cond, in1, sp)));
            }
            // §28 CMOS: `cmos(out,data,nctl,pctl)` — conducts when nctl|!pctl.
            GateType::Cmos | GateType::Rcmos if inst.terminals.len() >= 4 => {
                let nctl = inst.terminals[2].clone();
                let pctl = inst.terminals[3].clone();
                let pnot = Expression::new(
                    ExprKind::Unary {
                        op: UnaryOp::LogNot,
                        operand: Box::new(pctl),
                    },
                    sp,
                );
                let cond = Expression::new(
                    ExprKind::Binary {
                        op: BinaryOp::LogOr,
                        left: Box::new(nctl),
                        right: Box::new(pnot),
                    },
                    sp,
                );
                pairs.push((out, make_tristate(cond, in1, sp)));
            }
            // §28.8 bidirectional switches are not one-directional assigns.
            // They are recorded and resolved against each terminal's own
            // drivers by `resolve_bidirectional_switches`.
            GateType::Tran | GateType::Rtran => {}
            GateType::Tranif1 | GateType::Rtranif1 | GateType::Tranif0 | GateType::Rtranif0 => {}
            GateType::And => {
                let mut rhs = in1;
                for i in 2..inst.terminals.len() {
                    rhs = Expression::new(
                        ExprKind::Binary {
                            op: BinaryOp::BitAnd,
                            left: Box::new(rhs),
                            right: Box::new(inst.terminals[i].clone()),
                        },
                        out.span,
                    );
                }
                pairs.push((out, rhs));
            }
            GateType::Or => {
                let mut rhs = in1;
                for i in 2..inst.terminals.len() {
                    rhs = Expression::new(
                        ExprKind::Binary {
                            op: BinaryOp::BitOr,
                            left: Box::new(rhs),
                            right: Box::new(inst.terminals[i].clone()),
                        },
                        out.span,
                    );
                }
                pairs.push((out, rhs));
            }
            GateType::Xor => {
                let mut rhs = in1;
                for i in 2..inst.terminals.len() {
                    rhs = Expression::new(
                        ExprKind::Binary {
                            op: BinaryOp::BitXor,
                            left: Box::new(rhs),
                            right: Box::new(inst.terminals[i].clone()),
                        },
                        out.span,
                    );
                }
                pairs.push((out, rhs));
            }
            GateType::Nand => {
                let mut rhs = in1;
                for i in 2..inst.terminals.len() {
                    rhs = Expression::new(
                        ExprKind::Binary {
                            op: BinaryOp::BitAnd,
                            left: Box::new(rhs),
                            right: Box::new(inst.terminals[i].clone()),
                        },
                        out.span,
                    );
                }
                rhs = Expression::new(
                    ExprKind::Unary {
                        op: UnaryOp::BitNot,
                        operand: Box::new(rhs),
                    },
                    out.span,
                );
                pairs.push((out, rhs));
            }
            GateType::Nor => {
                let mut rhs = in1;
                for i in 2..inst.terminals.len() {
                    rhs = Expression::new(
                        ExprKind::Binary {
                            op: BinaryOp::BitOr,
                            left: Box::new(rhs),
                            right: Box::new(inst.terminals[i].clone()),
                        },
                        out.span,
                    );
                }
                rhs = Expression::new(
                    ExprKind::Unary {
                        op: UnaryOp::BitNot,
                        operand: Box::new(rhs),
                    },
                    out.span,
                );
                pairs.push((out, rhs));
            }
            GateType::Xnor => {
                let mut rhs = in1;
                for i in 2..inst.terminals.len() {
                    rhs = Expression::new(
                        ExprKind::Binary {
                            op: BinaryOp::BitXor,
                            left: Box::new(rhs),
                            right: Box::new(inst.terminals[i].clone()),
                        },
                        out.span,
                    );
                }
                rhs = Expression::new(
                    ExprKind::Unary {
                        op: UnaryOp::BitNot,
                        operand: Box::new(rhs),
                    },
                    out.span,
                );
                pairs.push((out, rhs));
            }
            // §28.4: `buf` and `not` have one or more outputs and one input,
            // the last terminal (`buf (o1, o2, i);`).
            GateType::Not => {
                let (input, outs) = inst.terminals.split_last().unwrap_or((&in1, &[]));
                for o in outs {
                    let rhs = Expression::new(
                        ExprKind::Unary {
                            op: UnaryOp::BitNot,
                            operand: Box::new(input.clone()),
                        },
                        o.span,
                    );
                    pairs.push((o.clone(), rhs));
                }
            }
            GateType::Buf => {
                let (input, outs) = inst.terminals.split_last().unwrap_or((&in1, &[]));
                for o in outs {
                    pairs.push((o.clone(), input.clone()));
                }
            }
            _ => {}
        }
    }
    pairs
}

/// LRM §17.2 checker port substitution helper. Substitutes formal
/// names with actual expressions in a ModuleItem. Reuses
/// `rewrite_stmt` / `rewrite_expr` with an empty prefix and no
/// interface map. Only handles the item shapes a checker body can
/// realistically contain (initial/always/assertion/etc.).
pub(super) fn rewrite_module_item_subst(
    item: &ModuleItem,
    subst: &HashMap<String, Expression>,
) -> ModuleItem {
    let empty: std::collections::HashSet<String> = std::collections::HashSet::new();
    let empty_iface: HashMap<String, String> = HashMap::default();
    match item {
        ModuleItem::InitialConstruct(ic) => {
            let mut new_ic = ic.clone();
            new_ic.stmt = rewrite_stmt(&ic.stmt, "", subst, &empty, &empty_iface);
            ModuleItem::InitialConstruct(new_ic)
        }
        ModuleItem::AlwaysConstruct(ac) => {
            let mut new_ac = ac.clone();
            new_ac.stmt = rewrite_stmt(&ac.stmt, "", subst, &empty, &empty_iface);
            ModuleItem::AlwaysConstruct(new_ac)
        }
        ModuleItem::AssertionItem(a) => {
            let mut new_a = a.clone();
            new_a.expr = rewrite_expr(&a.expr, "", subst, &empty, &empty_iface);
            if let Some(act) = &a.action {
                new_a.action = Some(Box::new(rewrite_stmt(act, "", subst, &empty, &empty_iface)));
            }
            if let Some(ea) = &a.else_action {
                new_a.else_action =
                    Some(Box::new(rewrite_stmt(ea, "", subst, &empty, &empty_iface)));
            }
            ModuleItem::AssertionItem(new_a)
        }
        // Other item kinds are passed through unchanged — extending
        // this map is straightforward when a real testbench needs it.
        other => other.clone(),
    }
}

/// Flat dotted name of an identifier expression. A hierarchical reference may
/// parse as an `Ident` with several path segments OR as a `MemberAccess` chain
/// (`top.inst.net`), so fold both shapes.
pub(super) fn ident_flat_name(e: &Expression) -> Option<String> {
    match &e.kind {
        ExprKind::Ident(h) if h.path.iter().all(|s| s.selects.is_empty()) => Some(
            h.path
                .iter()
                .map(|s| s.name.name.as_str())
                .collect::<Vec<_>>()
                .join("."),
        ),
        ExprKind::MemberAccess { expr, member } => {
            Some(format!("{}.{}", ident_flat_name(expr)?, member.name))
        }
        _ => None,
    }
}

/// True when a continuous-assign drive strength is entirely WEAK (pull/weak/
/// highz on both the 1 and 0 sides) — such a driver behaves like a pullup/
/// pulldown and loses to any strong driver. A mixed strength (e.g. strong1,
/// pull0) is not treated as weak (approximated as strong).
/// The resolution marker for a continuous assign's drive strength (§28.12):
/// `$__supply` when both sides are supply, `$__weak` when both are weak,
/// `$__pull` for any other all-weak (pull/weak/highz) pair, and `None` for a
/// strong driver. A mixed strong/weak pair (`strong0, weak1`) is approximated
/// as strong, as before.
///
/// Every marker carries the exact pair as a second argument (see
/// `strength_code`) for `%v`; a pair with a strong or supply side that is not
/// all-supply gets `$__drive`, which resolves like an unmarked (strong)
/// driver.
pub(super) fn strength_marker(s: &str) -> Option<(&'static str, u8)> {
    let toks: Vec<&str> = s
        .split(',')
        .map(|t| t.trim().trim_end_matches(['0', '1']))
        .filter(|t| !t.is_empty())
        .collect();
    let code = strength_code(s);
    if toks.is_empty() {
        None
    } else if toks.iter().all(|t| *t == "supply") {
        Some(("$__supply", code))
    } else if toks.iter().all(|t| *t == "weak") {
        Some(("$__weak", code))
    } else if strength_is_weak(s) {
        Some(("$__pull", code))
    } else {
        Some(("$__drive", code))
    }
}

/// §28.12 strength level of one strength keyword: 7 supply, 6 strong,
/// 5 pull, 4 large, 3 weak, 2 medium, 1 small, 0 highz.
fn strength_level(tok: &str) -> u8 {
    match tok.trim().trim_end_matches(['0', '1']) {
        "supply" => 7,
        "strong" => 6,
        "pull" => 5,
        "large" => 4,
        "weak" => 3,
        "medium" => 2,
        "small" => 1,
        "highz" => 0,
        _ => 6,
    }
}

/// A drive-strength pair `(s0, s1)` packed as `s0 * 8 + s1`; a side the
/// spec leaves out is strong.
fn strength_code(s: &str) -> u8 {
    let (mut s0, mut s1) = (6u8, 6u8);
    for tok in s.split(',').map(str::trim) {
        if tok.ends_with('0') {
            s0 = strength_level(tok);
        } else if tok.ends_with('1') {
            s1 = strength_level(tok);
        }
    }
    s0 * 8 + s1
}

pub(super) fn strength_code_literal(code: u8, span: Span) -> Expression {
    const_value_literal(&Value::from_u64(u64::from(code), 8), span).expect("strength literal")
}

fn strength_is_weak(s: &str) -> bool {
    let toks: Vec<&str> = s
        .split(',')
        .map(|t| t.trim())
        .filter(|t| !t.is_empty())
        .collect();
    !toks.is_empty()
        && toks.iter().all(|t| {
            let base = t.trim_end_matches(['0', '1']);
            matches!(base, "pull" | "weak" | "highz")
        })
}

pub(super) fn make_syscall(name: &str, args: Vec<Expression>, span: Span) -> Expression {
    Expression::new(
        ExprKind::SystemCall {
            name: name.to_string(),
            args,
        },
        span,
    )
}

pub(super) fn gate_inst_to_assigns(gi: &GateInstantiation, elab: &mut ElaboratedModule) {
    // §28.8 bidirectional switches: record, don't lower to an assign.
    if record_tran_switches(gi, elab, |e| e.clone()) {
        return;
    }
    // Gate delay (`buf #(4)`) — pre-scaled to ticks by the module-delay
    // rewrite; carried onto the lowered cont-assign, whose delayed-update
    // path models the §28.9 single-delay INERTIAL behavior (a pulse
    // narrower than the delay is filtered).
    let (delay, fall, off, delay_exprs) = cont_assign_delays(
        [gi.delay.as_ref(), gi.delay_fall.as_ref(), gi.delay_off.as_ref()], &elab.parameters);
    let pairs = gate_inst_to_assign_pairs(gi);
    for (lhs, rhs) in pairs {
        // Mark the driven net as gate-driven so the runtime keeps §28.4 truth-
        // table semantics for it and only for it.
        if let Some(n) = ident_flat_name(&lhs) {
            elab.gate_driven_nets.insert(n);
        }
        if let Some(f) = fall {
            if f != delay {
                if let Some(n) = ident_flat_name(&lhs) {
                    elab.gate_fall_delays.insert(n, f);
                }
            }
        }
        elab.continuous_assigns.push(ContinuousAssignment {
            gate_delay_fall: fall,
            delay_exprs: delay_exprs.clone(),
            delay_select: None,
            origin: None,
            lhs: lhs.clone(),
            rhs,
            delay,
            rhs_parent_scoped: false,
            delay_fall: None,
            delay_off: off,
        });
    }
}

/// IEEE 1800-2017 §29: lower each UDP instance in `inst` into a flattened
/// `UdpInstance` on `elab`. Terminals are positional; supports instance arrays
/// (`u[hi:lo](...)`, bit-selecting each terminal) and a scalar `#(delay)`.
pub(super) fn lower_udp_instances(
    elab: &mut ElaboratedModule,
    udp: &crate::ast::decl::UdpDecl,
    inst: &ModuleInstantiation,
    prefix: &str,
    local_names: &std::collections::HashSet<String>,
    interface_map: &HashMap<String, String>,
) {
    use crate::ast::decl::PortConnection;
    let n_ports = udp.ports.len();
    // Instance delay: `#(d)` or `#(rise, fall)` before the instance — scalar
    // time values in the enclosing module's time units (§28.16, §29.3).
    // A parameter it names (`#(D)`) belongs to the enclosing INSTANCE: bring
    // the expression into that scope first, like the terminals below, or an
    // inlined instance's `D` missed the flattened `u.D` and the delay was 0.
    let delay_at = |k: usize| -> Option<u64> {
        match inst.params.as_ref()?.get(k)? {
            crate::ast::decl::ParamConnection::Ordered(Some(
                crate::ast::decl::ParamValue::Expr(e),
            )) => {
                // §3.14.2: `rewrite_udp_instance_delays` left the value in
                // ticks: a literal folded to a real count, any other
                // expression multiplied by the ticks of one time unit.
                let (inner, scale) = match &e.kind {
                    ExprKind::Binary {
                        op: BinaryOp::Mul,
                        left,
                        right,
                    } => match &right.kind {
                        ExprKind::Number(crate::ast::expr::NumberLiteral::Real(s)) => {
                            (left.as_ref(), *s)
                        }
                        _ => (e, 1.0),
                    },
                    _ => (e, 1.0),
                };
                let inner =
                    rewrite_expr(inner, prefix, &HashMap::default(), local_names, interface_map);
                let ticks = |units: f64| -> u64 {
                    let t = (units * scale).round();
                    if t.is_finite() && t > 0.0 { t as u64 } else { 0 }
                };
                let v = eval_const_expr_val(&inner, &elab.parameters);
                if v.is_real {
                    Some(ticks(v.to_f64()))
                } else if v.has_xz() {
                    // An unknown delay value is no delay, as the reference
                    // simulator takes it.
                    Some(0)
                } else {
                    // A non-constant value stays "not given". The integer
                    // evaluator has no select of a parameter (`#(V[3:0] + 0)`
                    // is 0 to it); the value evaluator has.
                    let by_value = || {
                        if v.is_signed {
                            v.to_i64().unwrap_or(0).max(0) as u64
                        } else {
                            v.to_u64().unwrap_or(0)
                        }
                    };
                    match const_eval_i64_with_params(&inner, Some(&elab.parameters)) {
                        Some(0) => Some(ticks(by_value() as f64)),
                        Some(d) => Some(ticks(d.max(0) as f64)),
                        None => Some(by_value()).filter(|u| *u > 0).map(|u| ticks(u as f64)),
                    }
                }
            }
            _ => None,
        }
    };
    let delay: u64 = delay_at(0).unwrap_or(0);
    // The fall delay: a 1->0 output change waited the rise delay instead.
    let delay_fall: Option<u64> = delay_at(1);

    for hi in &inst.instances {
        // Positional terminals only (§29.7).
        let mut terms: Vec<Expression> = Vec::with_capacity(n_ports);
        let mut bad = false;
        for conn in &hi.connections {
            match conn {
                PortConnection::Ordered(Some(e)) => terms.push(rewrite_expr(
                    e,
                    prefix,
                    &HashMap::default(),
                    local_names,
                    interface_map,
                )),
                _ => {
                    bad = true;
                    break;
                }
            }
        }
        let inst_path = cat2(&prefix, &hi.name.name);
        // §6.10: an undeclared identifier used in a PRIMITIVE TERMINAL gets an
        // implicit 1-bit net, exactly like one in a continuous assign. The
        // cont-assign pass never sees a net that only wires two UDPs together
        // (e.g. a vendor cell's `udp_mux2 I1 (n1, ...)` feeding
        // `udp_dff I0 (n0, n1, ...)`) — without this, both instances were
        // DROPPED as unresolved and the cell went dead.
        if hi.dimensions.is_empty() && !sv_parser::default_nettype_none_seen() {
            // (instance arrays excluded: their terminals are vectors that get
            // bit-selected per element — a 1-bit implicit net would be wrong)
            for t in &terms {
                if let ExprKind::Ident(h) = &t.kind {
                    if h.path.iter().all(|seg| seg.selects.is_empty()) {
                        let name = h
                            .path
                            .iter()
                            .map(|seg| seg.name.name.as_str())
                            .collect::<Vec<_>>()
                            .join(".");
                        if !name.is_empty()
                            && !elab.signals.contains_key(&name)
                            && !elab.parameters.contains_key(&name)
                        {
                            if crate::implicit_net_warn() {
                                crate::elab_diag(format!(
                                    "[xezim][warning] implicit 1-bit net created for undeclared identifier '{}' \
                                     (IEEE 1800-2017 §6.10, primitive terminal of '{}'). Add an explicit declaration to silence.",
                                    name, inst_path
                                ));
                            }
                            signals_insert_traced(
                                &mut elab.signals,
                                line!(),
                                name.clone(),
                                Signal {
                                    is_const: false,
                                    name: name.clone().into(),
                                    width: 1,
                                    is_signed: false,
                                    direction: None,
                                    value: Value::new(1),
                                    is_real: false,
                                    type_name: None,
                                },
                            );
                            elab.implicit_nets.insert(name.clone());
                            elab.nets.insert(name);
                        }
                    }
                }
            }
        }
        if bad || terms.len() != n_ports {
            eprintln!(
                "\n========================================================================\n\
                 Warning: UDP INSTANCE PORT MISMATCH — '{}' instance '{}'\n\
                 primitive '{}' expects {} positional terminals (1 output + {} inputs)\n\
                 but the instantiation supplied {}{}.\n\
                 Consequence: this instance is SKIPPED; its output net is left UNDRIVEN.\n\
                 ========================================================================\n",
                udp.name.name,
                inst_path,
                udp.name.name,
                n_ports,
                n_ports.saturating_sub(1),
                hi.connections.len(),
                if bad {
                    " (non-positional/unconnected terminal)"
                } else {
                    ""
                },
            );
            continue;
        }

        // Instance array `u[hi:lo]` — expand to one UdpInstance per element,
        // bit-selecting the matching wire bit of every terminal.
        let arr_range = hi.dimensions.iter().rev().find_map(|d| match d {
            crate::ast::types::UnpackedDimension::Range { left, right, .. } => {
                let l = const_eval_i64_with_params(left, Some(&elab.parameters))?;
                let r = const_eval_i64_with_params(right, Some(&elab.parameters))?;
                Some((l, r))
            }
            _ => None,
        });

        match arr_range {
            None => {
                elab.udp_instances.push(UdpInstance {
                    udp_name: udp.name.name.clone(),
                    inst_path,
                    output: terms[0].clone(),
                    inputs: terms[1..].to_vec(),
                    is_sequential: udp.is_sequential,
                    init: udp.init,
                    rows: udp.rows.clone(),
                    delay,
                    delay_fall,
                    span: udp.span,
                });
            }
            Some((l, r)) => {
                let (lo, hi_b) = if l <= r { (l, r) } else { (r, l) };
                for idx in lo..=hi_b {
                    let sel = |e: &Expression| {
                        Expression::new(
                            ExprKind::Index {
                                expr: Box::new(e.clone()),
                                index: Box::new(make_udp_int_expr(idx)),
                            },
                            Span::dummy(),
                        )
                    };
                    elab.udp_instances.push(UdpInstance {
                        udp_name: udp.name.name.clone(),
                        inst_path: format!("{}[{}]", inst_path, idx),
                        output: sel(&terms[0]),
                        inputs: terms[1..].iter().map(sel).collect(),
                        is_sequential: udp.is_sequential,
                        init: udp.init,
                        rows: udp.rows.clone(),
                        delay,
                        delay_fall,
                        span: udp.span,
                    });
                }
            }
        }
    }
}

/// A plain decimal integer-literal expression (for synthesized bit-selects).
pub(super) fn make_udp_int_expr(v: i64) -> Expression {
    use crate::ast::expr::{NumberBase, NumberLiteral, UnaryOp};
    // A leading minus belongs to a unary expression, never to a numeric
    // token (§5.7.1). Preserve it when synthesizing negative unpacked indices.
    let number = Expression::new(
        ExprKind::Number(NumberLiteral::Integer {
            size: (v < 0).then_some(64),
            signed: true,
            base: NumberBase::Decimal,
            value: v.unsigned_abs().to_string(),
            cached_val: crate::ast::cache::LiteralCache::new(None),
        }),
        Span::dummy(),
    );
    if v < 0 {
        Expression::new(
            ExprKind::Unary {
                op: UnaryOp::Minus,
                operand: Box::new(number),
            },
            Span::dummy(),
        )
    } else {
        number
    }
}

/// `name[idx]` as an expression.
pub(super) fn make_index_expr(name: &str, idx: i64) -> Expression {
    index_expr(make_ident_expr(name), idx)
}

pub(super) fn index_expr(base: Expression, idx: i64) -> Expression {
    Expression::new(
        ExprKind::Index {
            expr: Box::new(base),
            index: Box::new(make_udp_int_expr(idx)),
        },
        Span::dummy(),
    )
}
