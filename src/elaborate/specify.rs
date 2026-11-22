use super::*;

/// §31: argument positions holding time limits. They count the module's
/// time unit like any delay and are pre-scaled to ticks with it.
pub fn timing_check_limit_args(name: &str) -> &'static [usize] {
    match name {
        "$setup" | "$hold" | "$recovery" | "$removal" | "$skew" | "$timeskew" => &[2],
        "$setuphold" | "$recrem" | "$fullskew" | "$nochange" => &[2, 3],
        "$period" => &[1],
        "$width" => &[1, 2],
        _ => &[],
    }
}

/// §31.4.4/§31.4.5: `event_based_flag` / `remain_active_flag` positions.
pub fn timing_check_flag_args(name: &str) -> &'static [usize] {
    match name {
        "$timeskew" => &[4, 5],
        "$fullskew" => &[5, 6],
        _ => &[],
    }
}

/// Index into `ModulePath::delays` of the transition between two levels
/// (0, 1, 2 = x, 3 = z); `None` when the level does not change.
pub fn path_transition_index(from: u8, to: u8) -> Option<usize> {
    Some(match (from, to) {
        (0, 1) => 0,
        (1, 0) => 1,
        (0, 3) => 2,
        (3, 1) => 3,
        (1, 3) => 4,
        (3, 0) => 5,
        (0, 2) => 6,
        (2, 1) => 7,
        (1, 2) => 8,
        (2, 0) => 9,
        (2, 3) => 10,
        (3, 2) => 11,
        _ => return None,
    })
}

/// §30.5.1 Table 30-3: the twelve transition delays of a 1, 2, 3, 6 or 12
/// value delay list. Short of twelve, the x transitions follow §30.5.2 —
/// to x the smallest, from x the largest of the delays they could stand for.
pub fn path_transition_delays(d: &[u64]) -> [u64; 12] {
    let g = |i: usize| d.get(i).copied().unwrap_or(0);
    let (t01, t10, t0z, tz1, t1z, tz0) = match d.len() {
        0 => (0, 0, 0, 0, 0, 0),
        1 => (g(0), g(0), g(0), g(0), g(0), g(0)),
        2 => (g(0), g(1), g(0), g(0), g(1), g(1)),
        3..=5 => (g(0), g(1), g(2), g(0), g(2), g(1)),
        _ => (g(0), g(1), g(2), g(3), g(4), g(5)),
    };
    if d.len() >= 12 {
        return [
            t01,
            t10,
            t0z,
            tz1,
            t1z,
            tz0,
            g(6),
            g(7),
            g(8),
            g(9),
            g(10),
            g(11),
        ];
    }
    [
        t01,
        t10,
        t0z,
        tz1,
        t1z,
        tz0,
        t01.min(t0z),
        t01.max(tz1),
        t10.min(t1z),
        t10.max(tz0),
        t0z.max(t1z),
        tz1.min(tz0),
    ]
}

/// Flatten one specify block's §30.4 module paths into `elab.module_paths`
/// (and the per-net `specify_delays` summary: the largest delay, which marks
/// the net as path-delayed). `params` evaluates the delays in the instance's
/// own parameter scope; `rewrite` maps a module-local expression into the
/// flat namespace. The delays were scaled to ticks by the module-delay
/// rewrite. `delay_vals[i][j]` is the pre-evaluated `paths[i].delays[j]`.
pub(super) fn elaborate_module_paths(
    elab: &mut ElaboratedModule,
    paths: &[crate::ast::decl::SpecifyPath],
    delay_vals: &[Vec<u64>],
    rewrite: &dyn Fn(&Expression) -> Expression,
) {
    let flat = |id: &Identifier| -> Option<String> {
        match rewrite(&make_ident_expr(&id.name)).kind {
            ExprKind::Ident(h) => Some(
                h.path
                    .iter()
                    .map(|s| s.name.name.as_str())
                    .collect::<Vec<_>>()
                    .join("."),
            ),
            _ => None,
        }
    };
    for (p, vals) in paths.iter().zip(delay_vals.iter()) {
        let delays = path_transition_delays(vals);
        let srcs: Vec<String> = p.srcs.iter().filter_map(|s| flat(s)).collect();
        let cond = p.cond.as_ref().map(rewrite);
        let most = delays.iter().copied().max().unwrap_or(0);
        for dst in &p.dsts {
            let Some(name) = flat(dst) else {
                continue;
            };
            let d = elab.specify_delays.entry(name.clone()).or_insert(0);
            *d = (*d).max(most);
            elab.module_paths.entry(name).or_default().push(ModulePath {
                delays,
                srcs: srcs.clone(),
                cond: cond.clone(),
                ifnone: p.ifnone,
            });
        }
    }
}

/// Flatten one specify block's timing checks into `elab.timing_checks`.
/// `consts[i][j]` holds the pre-evaluated limit/flag value (or `None`) for
/// `checks[i].args[j]`; `rewrite` maps a module-local expression into the flat
/// namespace.
pub(super) fn elaborate_timing_checks(
    elab: &mut ElaboratedModule,
    checks: &[crate::ast::decl::TimingCheck],
    scope: &str,
    def_name: &str,
    consts: &[Vec<Option<i64>>],
    rewrite: &dyn Fn(&Expression) -> Expression,
) {
    for (tc, tc_consts) in checks.iter().zip(consts.iter()) {
        let args = tc
            .args
            .iter()
            .map(|a| {
                a.as_ref().map(|a| crate::ast::decl::TimingCheckArg {
                    edges: a.edges,
                    expr: rewrite(&a.expr),
                    cond: a.cond.as_ref().map(rewrite),
                    text: a.text.clone(),
                })
            })
            .collect();
        elab.timing_checks.push(TimingCheckInstance {
            name: tc.name.clone(),
            scope: scope.to_string(),
            def_name: def_name.to_string(),
            args,
            consts: tc_consts.clone(),
            span: tc.span,
        });
    }
}
