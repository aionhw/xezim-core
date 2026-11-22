use super::*;

pub(super) fn simple_lhs_name(expr: &Expression) -> Option<String> {
    match &expr.kind {
        ExprKind::Ident(hier) if hier.path.len() == 1 && hier.path[0].selects.is_empty() => {
            Some(hier.path[0].name.name.clone())
        }
        ExprKind::Paren(inner) => simple_lhs_name(inner),
        _ => None,
    }
}

pub(super) fn collect_written_idents(stmt: &Statement, out: &mut HashSet<String>) {
    match &stmt.kind {
        StatementKind::BlockingAssign { lvalue, .. }
        | StatementKind::NonblockingAssign { lvalue, .. } => {
            if let Some(n) = simple_lhs_name(lvalue) {
                out.insert(n);
            }
        }
        StatementKind::If {
            then_stmt,
            else_stmt,
            ..
        } => {
            collect_written_idents(then_stmt, out);
            if let Some(eb) = else_stmt {
                collect_written_idents(eb, out);
            }
        }
        StatementKind::Case { items, .. } => {
            for item in items {
                collect_written_idents(&item.stmt, out);
            }
        }
        StatementKind::For { body, init, .. } => {
            for fi in init {
                if let ForInit::Assign { lvalue, .. } = fi {
                    if let Some(n) = simple_lhs_name(lvalue) {
                        out.insert(n);
                    }
                }
            }
            collect_written_idents(body, out);
        }
        StatementKind::Foreach { body, .. } => collect_written_idents(body, out),
        StatementKind::While { body, .. } | StatementKind::DoWhile { body, .. } => {
            collect_written_idents(body, out)
        }
        StatementKind::Repeat { body, .. } => collect_written_idents(body, out),
        StatementKind::Forever { body } => collect_written_idents(body, out),
        StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
            for s in stmts {
                collect_written_idents(s, out);
            }
        }
        StatementKind::TimingControl { stmt, .. } => collect_written_idents(stmt, out),
        StatementKind::Wait { stmt, .. } => collect_written_idents(stmt, out),
        _ => {}
    }
}

/// The kind of process (or continuous assign) that writes a variable, for the
/// §6.5 / §9.2.2 single-writer rules.
#[derive(Clone, Copy, PartialEq, Eq)]
enum WriterKind {
    /// `assign v = ...` onto a variable.
    Continuous,
    /// `always_comb` / `always_latch` (§9.2.2.2, §9.2.2.3).
    Comb,
    /// `always_ff` (§9.2.2.4).
    Ff,
    /// `always`, `initial`, `final`.
    Other,
    /// §6.5, §23.3.3: the actual of an instance's OUTPUT port, which the
    /// port connection drives like a continuous assignment.
    Port,
}

/// What an lvalue writes: the variable and the declared-label span of a
/// constant bit or part select (`None` = the whole variable). Selects the
/// check cannot place (a variable or genvar index, an element of an array or
/// of a multi-dimensional packed vector, a struct member) yield nothing, so
/// they are never reported.
fn lvalue_write_spans(
    lv: &Expression,
    elab: &ElaboratedModule,
    out: &mut Vec<(String, Option<(i64, i64)>)>,
) {
    let plain_vector = |n: &str| {
        !elab.arrays.contains_key(n)
            && !elab.packed_signal_elem_widths.contains_key(n)
            && elab.packed_full_dims.get(n).is_none_or(|d| d.len() <= 1)
    };
    match &lv.kind {
        ExprKind::Paren(inner) => lvalue_write_spans(inner, elab, out),
        ExprKind::Concatenation(items) => {
            for item in items {
                lvalue_write_spans(item, elab, out);
            }
        }
        ExprKind::Ident(_) => {
            if let Some(n) = simple_lhs_name(lv) {
                out.push((n, None));
            }
        }
        ExprKind::Index { expr, index } => {
            if let Some(n) = simple_lhs_name(expr).filter(|n| plain_vector(n)) {
                if let Some(i) = const_eval_i64_with_params(index, Some(&elab.parameters)) {
                    out.push((n, Some((i, i))));
                }
            }
        }
        ExprKind::RangeSelect {
            expr,
            kind,
            left,
            right,
        } => {
            if let Some(n) = simple_lhs_name(expr).filter(|n| plain_vector(n)) {
                let a = const_eval_i64_with_params(left, Some(&elab.parameters));
                let b = const_eval_i64_with_params(right, Some(&elab.parameters));
                if let (Some(a), Some(b)) = (a, b) {
                    let span = match kind {
                        RangeKind::Constant => Some((a.min(b), a.max(b))),
                        RangeKind::IndexedUp if b > 0 => Some((a, a + b - 1)),
                        RangeKind::IndexedDown if b > 0 => Some((a - b + 1, a)),
                        _ => None,
                    };
                    if let Some(span) = span {
                        out.push((n, Some(span)));
                    }
                }
            }
        }
        _ => {}
    }
}

/// Every lvalue a process body assigns (blocking, nonblocking, or an
/// assignment expression). Calls are not followed.
fn collect_stmt_write_spans(
    stmt: &Statement,
    elab: &ElaboratedModule,
    out: &mut Vec<(String, Option<(i64, i64)>)>,
) {
    use crate::ast::stmt::StatementKind as K;
    match &stmt.kind {
        K::BlockingAssign { lvalue, .. } | K::NonblockingAssign { lvalue, .. } => {
            lvalue_write_spans(lvalue, elab, out)
        }
        K::Expr(e) => {
            if let ExprKind::AssignExpr { lvalue, .. } = &e.kind {
                lvalue_write_spans(lvalue, elab, out);
            }
        }
        K::If {
            then_stmt,
            else_stmt,
            ..
        } => {
            collect_stmt_write_spans(then_stmt, elab, out);
            if let Some(eb) = else_stmt {
                collect_stmt_write_spans(eb, elab, out);
            }
        }
        K::Case { items, .. } => {
            for item in items {
                collect_stmt_write_spans(&item.stmt, elab, out);
            }
        }
        K::For { body, init, .. } => {
            for fi in init {
                if let ForInit::Assign { lvalue, .. } = fi {
                    lvalue_write_spans(lvalue, elab, out);
                }
            }
            collect_stmt_write_spans(body, elab, out);
        }
        K::Foreach { body, .. }
        | K::While { body, .. }
        | K::DoWhile { body, .. }
        | K::Repeat { body, .. }
        | K::Forever { body } => collect_stmt_write_spans(body, elab, out),
        K::SeqBlock { stmts, .. } | K::ParBlock { stmts, .. } => {
            for s in stmts {
                collect_stmt_write_spans(s, elab, out);
            }
        }
        K::TimingControl { stmt, .. } | K::Wait { stmt, .. } => {
            collect_stmt_write_spans(stmt, elab, out)
        }
        _ => {}
    }
}

/// IEEE 1800-2017 §6.5: a variable may be written by one continuous
/// assignment, or by procedural statements, but not by both and not by two
/// continuous assignments; §9.2.2.2/§9.2.2.3: a variable an `always_comb` or
/// `always_latch` writes shall not be written by any other process;
/// §9.2.2.4: likewise for `always_ff`. Each rule applies per written bit
/// (the longest static prefix), so writers of disjoint constant selects
/// (`v[0]` and `v[1]`) do not conflict.
///
/// Each conflict is an error unless `--relax-driver-conflicts` downgrades it
/// to a warning (every shape here is one the LRM forbids but tools commonly
/// let users accept). Matches the reference simulator's verdicts: two `always_ff` blocks
/// writing one variable are accepted (it does not enforce §9.2.2.4 between
/// them), a write made inside a called function is not attributed to the
/// caller, and a variable driven through an output port conflicts with a
/// continuous assignment or another output port, but not with procedural
/// writes (the reference only warns about those).
pub(super) fn validate_driver_conflicts(
    elab: &ElaboratedModule,
    module: Definition,
    all_defs: Option<&HashMap<String, Definition>>,
) -> Result<(), String> {
    let is_var = |n: &str| elab.signals.contains_key(n) && !elab.nets.contains(n);
    // (writer index, kind, span) per variable.
    let mut writers: HashMap<String, Vec<(usize, WriterKind, Option<(i64, i64)>)>> =
        HashMap::default();
    let mut next = 0usize;
    for ca in &elab.continuous_assigns {
        let mut spans = Vec::new();
        lvalue_write_spans(&ca.lhs, elab, &mut spans);
        for (n, sp) in spans {
            if is_var(&n) {
                writers
                    .entry(n)
                    .or_default()
                    .push((next, WriterKind::Continuous, sp));
            }
        }
        next += 1;
    }
    // §6.5 / §23.3.3: each output-port connection of an instance in this
    // module is a continuous driver of its actual.
    if let Some(defs) = all_defs {
        for item in module.items() {
            let ModuleItem::ModuleInstantiation(mi) = item else {
                continue;
            };
            let Some(sub) = defs.get(&mi.module_name.name) else {
                continue;
            };
            if !matches!(sub, Definition::Module(_) | Definition::Program(_)) {
                continue;
            }
            for hi in &mi.instances {
                for actual in output_port_actuals(sub, &hi.connections) {
                    let mut spans = Vec::new();
                    lvalue_write_spans(&actual, elab, &mut spans);
                    if let ExprKind::Concatenation(parts) = &actual.kind {
                        for part in parts {
                            lvalue_write_spans(part, elab, &mut spans);
                        }
                    }
                    for (n, sp) in spans {
                        if is_var(&n) {
                            writers
                                .entry(n)
                                .or_default()
                                .push((next, WriterKind::Port, sp));
                        }
                    }
                    next += 1;
                }
            }
        }
    }
    let mut add_process = |stmt: &Statement, kind: WriterKind, next: &mut usize| {
        let mut spans = Vec::new();
        collect_stmt_write_spans(stmt, elab, &mut spans);
        if !spans.is_empty() {
            let mut local = HashSet::default();
            collect_stmt_declared_names(stmt, &mut local);
            let mut seen: HashSet<(String, Option<(i64, i64)>)> = HashSet::default();
            for (n, sp) in spans {
                if is_var(&n) && !local.contains(&n) && seen.insert((n.clone(), sp)) {
                    writers.entry(n).or_default().push((*next, kind, sp));
                }
            }
        }
        *next += 1;
    };
    for ab in &elab.always_blocks {
        let kind = match ab.kind {
            AlwaysKind::AlwaysComb | AlwaysKind::AlwaysLatch => WriterKind::Comb,
            AlwaysKind::AlwaysFf => WriterKind::Ff,
            AlwaysKind::Always => WriterKind::Other,
        };
        add_process(&ab.stmt, kind, &mut next);
    }
    for ib in elab.initial_blocks.iter().chain(&elab.final_blocks) {
        add_process(&ib.stmt, WriterKind::Other, &mut next);
    }
    let overlap = |a: Option<(i64, i64)>, b: Option<(i64, i64)>| match (a, b) {
        (Some((al, ah)), Some((bl, bh))) => al <= bh && bl <= ah,
        _ => true,
    };
    let show = |n: &str, sp: Option<(i64, i64)>| match sp {
        None => n.to_string(),
        Some((l, h)) if l == h => format!("{n}[{l}]"),
        Some((l, h)) => format!("{n}[{h}:{l}]"),
    };
    // Report in a stable order (the variable that sorts first).
    let mut names: Vec<&String> = writers.keys().collect();
    names.sort();
    for n in names {
        let ws = &writers[n];
        for (i, &(pa, ka, sa)) in ws.iter().enumerate() {
            for &(pb, kb, sb) in &ws[i + 1..] {
                if pa == pb || !overlap(sa, sb) {
                    continue;
                }
                let sp = if sa.is_some() { sa } else { sb };
                use WriterKind as W;
                let msg = match (ka, kb) {
                    // A port beside a procedural write is accepted.
                    (W::Port, W::Comb | W::Ff | W::Other)
                    | (W::Comb | W::Ff | W::Other, W::Port) => {
                        continue;
                    }
                    (W::Continuous | W::Port, W::Continuous | W::Port) => {
                        if sp.is_none() {
                            format!("Variable '{n}' has multiple continuous drivers")
                        } else {
                            format!(
                                "Variable '{}' has multiple continuous drivers (IEEE 1800-2017 §6.5)",
                                show(n, sp)
                            )
                        }
                    }
                    (W::Continuous, _) | (_, W::Continuous) => {
                        if sp.is_none() {
                            format!("Variable '{n}' has both continuous and procedural drivers")
                        } else {
                            format!(
                                "Variable '{}' has both continuous and procedural drivers (IEEE 1800-2017 §6.5)",
                                show(n, sp)
                            )
                        }
                    }
                    (W::Comb, _) | (_, W::Comb) => format!(
                        "Variable '{}' is written by an always_comb or always_latch block and by another process (IEEE 1800-2017 §9.2.2.2)",
                        show(n, sp)
                    ),
                    (W::Ff, W::Other) | (W::Other, W::Ff) => format!(
                        "Variable '{}' is written by an always_ff block and by another process (IEEE 1800-2017 §9.2.2.4)",
                        show(n, sp)
                    ),
                    _ => continue,
                };
                if relax_driver_conflicts() {
                    // One warning per conflicting variable and module, however
                    // many times the module is elaborated.
                    static SEEN: std::sync::Mutex<Option<HashSet<String>>> =
                        std::sync::Mutex::new(None);
                    let line = format!(
                        "[xezim][warning] {msg} in module '{}'; accepted because \
                         --relax-driver-conflicts is in effect",
                        elab.name
                    );
                    let mut seen = SEEN.lock().unwrap_or_else(|e| e.into_inner());
                    if seen
                        .get_or_insert_with(HashSet::default)
                        .insert(line.clone())
                    {
                        crate::log_eprintln(&line);
                    }
                    break;
                }
                return Err(format!(
                    "{msg}\n  or accept it with a warning: --relax-driver-conflicts \
                     (env XEZIM_RELAX_DRIVER_CONFLICTS=1)"
                ));
            }
        }
    }
    Ok(())
}

/// The actual expressions an instance connects to the OUTPUT ports of `sub`:
/// named (`.o(v)`), implicit (`.o`), positional and `.*` connections.
fn output_port_actuals(sub: &Definition, conns: &[PortConnection]) -> Vec<Expression> {
    let is_output = |name: &str| -> bool {
        match sub.ports() {
            PortList::Ansi(ports) => ports
                .iter()
                .find(|p| p.name.name == name)
                .is_some_and(|p| matches!(p.direction, Some(PortDirection::Output))),
            _ => sub.items().iter().any(|it| {
                matches!(it, ModuleItem::PortDeclaration(pd)
                    if matches!(pd.direction, PortDirection::Output)
                        && pd.declarators.iter().any(|d| d.name.name == name))
            }),
        }
    };
    let port_names: Vec<String> = match sub.ports() {
        PortList::Ansi(ports) => ports.iter().map(|p| p.name.name.clone()).collect(),
        PortList::NonAnsi(names) => names.iter().map(|n| n.name.clone()).collect(),
        PortList::Empty => Vec::new(),
    };
    let mut out = Vec::new();
    let mut named: HashSet<&str> = HashSet::default();
    for (i, c) in conns.iter().enumerate() {
        match c {
            PortConnection::Ordered(Some(e)) => {
                if port_names.get(i).is_some_and(|n| is_output(n)) {
                    out.push(e.clone());
                }
            }
            PortConnection::Named {
                name,
                expr,
                implicit,
            } => {
                named.insert(name.name.as_str());
                if !is_output(&name.name) {
                    continue;
                }
                match expr {
                    Some(e) => out.push(e.clone()),
                    None if *implicit => out.push(make_ident_expr(&name.name)),
                    None => {}
                }
            }
            _ => {}
        }
    }
    if conns.iter().any(|c| matches!(c, PortConnection::Wildcard)) {
        for n in &port_names {
            if !named.contains(n.as_str()) && is_output(n) {
                out.push(make_ident_expr(n));
            }
        }
    }
    out
}

/// Escape hatch for `validate_driver_conflicts`: report a conflicting
/// variable driver (§6.5, §9.2.2.2, §9.2.2.4) as a warning instead of an
/// error, so an existing design that, say, initializes an `always_ff`
/// variable from an `initial` block still runs. Set by
/// `--relax-driver-conflicts` or `XEZIM_RELAX_DRIVER_CONFLICTS=1`.
static RELAX_DRIVER_CONFLICTS: std::sync::atomic::AtomicBool =
    std::sync::atomic::AtomicBool::new(false);

pub fn set_relax_driver_conflicts(on: bool) {
    RELAX_DRIVER_CONFLICTS.store(on, std::sync::atomic::Ordering::Relaxed);
}

pub fn relax_driver_conflicts() -> bool {
    if RELAX_DRIVER_CONFLICTS.load(std::sync::atomic::Ordering::Relaxed) {
        return true;
    }
    static ENV: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENV.get_or_init(|| {
        std::env::var("XEZIM_RELAX_DRIVER_CONFLICTS")
            .ok()
            .as_deref()
            == Some("1")
    })
}
