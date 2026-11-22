use super::*;

/// §27.4: a generate-for genvar's start value. The initializer is a constant
/// expression — a parameter, a negative number, `$low(a)` — folded against
/// the enclosing parameters (outer genvars included); the parser could only
/// fold a plain literal, so every other start silently began at 0.
pub fn generate_for_start(gf: &GenerateFor, params: &HashMap<String, Value>) -> i64 {
    gf.init
        .as_ref()
        .and_then(|e| const_eval_i64_with_params(e, Some(params)))
        .unwrap_or(gf.init_val)
}

/// §27.5: a generate-if/-case condition may be a user constant-function call
/// (`if (has_neighbor(r, dir))`). `is_const_expr` rejects a Call and
/// `eval_const_expr` reads one as 0, so fold the calls to literals first —
/// the same substitution parameter initializers use. None leaves the
/// expression as written (and its prior error).
fn fold_const_fn_in_generate(expr: &Expression, elab: &ElaboratedModule) -> Option<Expression> {
    if !expr_has_call(expr) {
        return None;
    }
    substitute_const_fn_calls(expr,Some(&elab.parameters), elab, 0).filter(|f| !expr_has_call(f))
}

/// Evaluate a generate-if: pick the first branch whose condition is true (or the else branch).
pub(super) fn elaborate_generate_if(
    gi: &GenerateIf,
    elab: &mut ElaboratedModule,
    all_defs: Option<&HashMap<String, Definition>>,
) -> Result<(), String> {
    // §27.5, §27.6: a branch is a scope, its declarations renamed to their
    // hierarchical name (`g.x`, or `genblk1.x` unlabelled), the convention
    // for-generate uses. §27.5: a directly nested branch is not a scope; its
    // construct carries this construct's implicit name.
    let take_branch = |bi: usize, items: &Vec<ModuleItem>, elab: &mut ElaboratedModule| {
        if gi.branch_direct.get(bi) == Some(&true) {
            return elaborate_items(items, elab, all_defs);
        }
        let label = gi.branch_labels.get(bi).and_then(|l| l.as_ref());
        let scope = gen_scope_name(label, &gi.implicit_name);
        let mut renamed = rename_decls_in_iter(items, &scope);
        stamp_gen_scope(&mut renamed, &scope);
        elaborate_block_items(&renamed, elab, all_defs)
    };
    for (bi, (cond, items)) in gi.branches.iter().enumerate() {
        match cond {
            Some(c) => {
                let folded = fold_const_fn_in_generate(c, elab);
                let c = folded.as_ref().unwrap_or(c);
                if !is_const_expr(c, &elab.parameters) {
                    return Err("Generate if condition must be a constant expression".to_string());
                }
                let val = eval_const_expr(c, &elab.parameters);
                if val != 0 {
                    return take_branch(bi, items, elab);
                }
            }
            None => {
                // Unconditional else branch
                return take_branch(bi, items, elab);
            }
        }
    }
    Ok(())
}

pub(super) fn elaborate_generate_case(
    gc: &GenerateCase,
    elab: &mut ElaboratedModule,
    all_defs: Option<&HashMap<String, Definition>>,
) -> Result<(), String> {
    let sel_folded = fold_const_fn_in_generate(&gc.selector, elab);
    let selector = sel_folded.as_ref().unwrap_or(&gc.selector);
    if !is_const_expr(selector, &elab.parameters) {
        return Err("Generate case selector must be a constant expression".to_string());
    }
    let sel = eval_const_expr(selector, &elab.parameters);
    // First pass: try to match a non-default arm.
    for arm in &gc.arms {
        if arm.values.is_empty() {
            continue;
        } // skip default in this pass
        for v in &arm.values {
            let v_folded = fold_const_fn_in_generate(v, elab);
            let v = v_folded.as_ref().unwrap_or(v);
            if !is_const_expr(v, &elab.parameters) {
                return Err("Generate case value must be a constant expression".to_string());
            }
            if eval_const_expr(v, &elab.parameters) == sel {
                return elaborate_generate_case_arm(gc, arm, elab, all_defs);
            }
        }
    }
    // No non-default match — fall through to default arm if present.
    for arm in &gc.arms {
        if arm.values.is_empty() {
            return elaborate_generate_case_arm(gc, arm, elab, all_defs);
        }
    }
    Ok(())
}

/// Case arms scope their declarations like if branches do (see
/// elaborate_generate_if).
fn elaborate_generate_case_arm(
    gc: &GenerateCase,
    arm: &GenerateCaseArm,
    elab: &mut ElaboratedModule,
    all_defs: Option<&HashMap<String, Definition>>,
) -> Result<(), String> {
    // §27.5: a directly nested arm is not a scope.
    if arm.direct {
        return elaborate_items(&arm.items, elab, all_defs);
    }
    let scope = gen_scope_name(arm.label.as_ref(), &gc.implicit_name);
    let mut renamed = rename_decls_in_iter(&arm.items, &scope);
    stamp_gen_scope(&mut renamed, &scope);
    elaborate_block_items(&renamed, elab, all_defs)
}

/// §21.2.1.7: the processes of a generate block of the ROOT module run in
/// the block's scope (`tb.g`, `tb.fl[0]`) — the inlining path does the same
/// for instances through `prefix_gen_scope`. Applied outermost first, so a
/// nested block appends its own name (`g.h`).
fn stamp_gen_scope(items: &mut [ModuleItem], scope: &str) {
    let stamp = |gs: &mut String| {
        *gs = if gs.is_empty() {
            scope.to_string()
        } else {
            format!("{}.{}", gs, scope)
        };
    };
    for item in items.iter_mut() {
        match item {
            ModuleItem::AlwaysConstruct(ac) => stamp(&mut ac.gen_scope),
            ModuleItem::InitialConstruct(ic) => stamp(&mut ic.gen_scope),
            ModuleItem::AssertionItem(_) => assertion_item_in_gen_scope(item, scope),
            ModuleItem::GenerateRegion(gr) => stamp_gen_scope(&mut gr.items, scope),
            ModuleItem::GenerateIf(gi) => {
                for (_, branch) in &mut gi.branches {
                    stamp_gen_scope(branch, scope);
                }
            }
            ModuleItem::GenerateCase(gc) => {
                for arm in &mut gc.arms {
                    stamp_gen_scope(&mut arm.items, scope);
                }
            }
            ModuleItem::GenerateFor(gf) => stamp_gen_scope(&mut gf.items, scope),
            _ => {}
        }
    }
}

pub(super) fn elaborate_generate_for(
    gf: &GenerateFor,
    elab: &mut ElaboratedModule,
    all_defs: Option<&HashMap<String, Definition>>,
) -> Result<(), String> {
    let var = &gf.var;
    let mut i = generate_for_start(gf, &elab.parameters);
    let trace = elab_trace_enabled();
    let mut iter_count = 0u32;
    let mut hit_cap = true;
    for _ in 0..10000 {
        // §27.4: a genvar is a signed integer — a down-counting loop
        // (`for (i = 3; i >= 0; i--)`) must see -1 as negative, not
        // 0xFFFFFFFF, or the condition never goes false (ivtest br_gh568).
        let mut gv = Value::from_u64(i as u64 as u32 as u64, 32);
        gv.is_signed = true;
        elab.set_param(line!(), var.clone(), gv);
        let cond_val = eval_const_expr(&gf.cond, &elab.parameters);
        if cond_val == 0 {
            hit_cap = false;
            break;
        }
        // Rename per-iteration declarations so each iteration owns a fresh
        // copy. Without this, two iterations both declare e.g. `valid_q` and
        // the elaborator's flat signal table flags a duplicate.
        let subst = substitute_genvar_in_items(&gf.items, var, i);
        // §27.6: unnamed blocks use the construct's implicit name, exactly as
        // named blocks use their label. Data and process scopes agree.
        let scope = format!(
            "{}[{}]",
            gen_scope_name(gf.name.as_ref(), &gf.implicit_name),
            i
        );
        let mut renamed = rename_decls_in_iter(&subst, &scope);
        stamp_gen_scope(&mut renamed, &scope);
        elaborate_block_items(&renamed, elab, all_defs)?;
        if trace && (iter_count % 8) == 0 {
            let rss = std::fs::read_to_string("/proc/self/statm")
                .ok()
                .and_then(|s| {
                    s.split_whitespace()
                        .nth(1)
                        .and_then(|n| n.parse::<u64>().ok())
                })
                .map(|p| p * 4096 / (1024 * 1024))
                .unwrap_or(0);
            eprintln!(
                "[xezim][gf] var={} iter={} rss={}MB assigns={} signals={}",
                var,
                iter_count,
                rss,
                elab.continuous_assigns.len(),
                elab.signals.len()
            );
        }
        iter_count += 1;
        // Evaluate increment: handle i++, i=i+1, etc.
        match &gf.incr.kind {
            ExprKind::Unary {
                op: UnaryOp::PostIncr,
                ..
            }
            | ExprKind::Unary {
                op: UnaryOp::PreIncr,
                ..
            } => {
                i += 1;
            }
            ExprKind::Unary {
                op: UnaryOp::PostDecr,
                ..
            }
            | ExprKind::Unary {
                op: UnaryOp::PreDecr,
                ..
            } => {
                i -= 1;
            }
            _ => {
                // Try to evaluate as expression (e.g. i = i + 1 expanded by parser)
                let new_val = eval_const_expr(&gf.incr, &elab.parameters) as i64;
                if new_val == i {
                    i += 1;
                } else {
                    i = new_val;
                }
            }
        }
    }
    elab.remove_param(var);
    if hit_cap {
        return Err(format!(
            "generate-for loop for genvar '{}' exceeded 10000 iterations \
             without its condition becoming false (IEEE 1800-2017 \u{a7}27.4)",
            var
        ));
    }
    // §27.4: bounds must be elaboration-time constants. An unresolvable
    // name in the condition made it evaluate 0 and the whole loop silently
    // elaborated ZERO iterations — hardware vanished without a diagnostic.
    if iter_count == 0 {
        let mut names: Vec<String> = Vec::new();
        collect_ident_names(&gf.cond, &mut names);
        let unresolved: Vec<String> = names
            .into_iter()
            .filter(|n| {
                n != var && !elab.parameters.contains_key(n) && param_fallback_get(n).is_none()
            })
            .collect();
        if !unresolved.is_empty() {
            return Err(format!(
                "generate-for condition references non-constant name(s) {:?}; \
                 generate bounds must be elaboration-time constants \
                 (IEEE 1800-2017 \u{a7}27.4)",
                unresolved
            ));
        }
    }
    Ok(())
}
