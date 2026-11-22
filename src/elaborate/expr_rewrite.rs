use super::*;

pub(super) fn rewrite_expr_impl(
    expr: &Expression,
    prefix: &str,
    port_map: &HashMap<String, Expression>,
    local_names: &std::collections::HashSet<String>,
    interface_map: &HashMap<String, String>,
) -> Expression {
    let new_kind = match &expr.kind {
        ExprKind::Ident(hier) => {
            if hier.root.is_some() {
                return expr.clone();
            }
            if hier.path.is_empty() {
                return expr.clone();
            }
            // §3.12.1: `$unit::x` carries the qualifier as the reserved name
            // `$unit::x`, which only EXISTS in a scope that shadows `x` with a
            // declaration of its own. Where nothing shadows it the $unit
            // variable was injected under its plain name, so drop the
            // qualifier and let the normal port-map / local-name handling
            // below bind (and prefix) it like any other reference.
            // A generate block that declares `x` hides the plain name there:
            // the qualified name is rooted, so no later rewrite strips it and
            // the run time reads the unit's `x`.
            if let Some(bare) = crate::sv_parser::strip_unit_scope_name(&hier.path[0].name.name) {
                // §3.12.1: the unit's one storage, held by the hierarchy root.
                if let Some(e) = unit_storage::qualified(hier, bare, prefix, expr.span, &|s| {
                    rewrite_expr_impl(s, prefix, port_map, local_names, interface_map)
                }) {
                    return e;
                }
                if gen_rename_declares(bare) {
                    let mut rooted = hier.clone();
                    rooted.root = Some("$root".to_string());
                    return Expression::new(ExprKind::Ident(rooted), expr.span);
                }
                if !local_names.contains(hier.path[0].name.name.as_str()) {
                    let mut new_hier = hier.clone();
                    new_hier.path[0].name.name = bare.to_string();
                    new_hier.cached_signal_id = crate::ast::cache::SignalCache::new(None);
                    new_hier.cached_resolved_name = crate::ast::cache::NameCache::new();
                    let bare_expr = Expression::new(ExprKind::Ident(new_hier), expr.span);
                    return rewrite_expr_impl(
                        &bare_expr,
                        prefix,
                        port_map,
                        local_names,
                        interface_map,
                    );
                }
            }
            let name = &hier.path[0].name.name;
            if let Some(if_prefix) = interface_map.get(name).filter(|_| hier.bound != Bound::NO_TARGET) {
                if let Some(view) = interface_arrays::view(interface_map, name) {
                    let mut selected = hier.clone();
                    for segment in &mut selected.path {
                        for index in &mut segment.selects {
                            *index = rewrite_expr_impl(
                                index,
                                prefix,
                                port_map,
                                local_names,
                                interface_map,
                            );
                        }
                    }
                    return view.rewrite_hier(&selected, expr.span);
                }
                // §25.5.4: a modport EXPRESSION member (`.b(word[7:0])`)
                // stands for an expression over the interface instance's
                // signals — substitute it (registered by
                // `register_modport_expressions`), applying any selects the
                // reference carried on the member.
                if hier.path.len() == 2 && hier.path[0].selects.is_empty() {
                    let key = format!("{}.{}", if_prefix, hier.path[1].name.name);
                    let hit = MODPORT_EXPR_TLS.with(|m| m.borrow().get(&key).cloned());
                    if let Some(mut e) = hit {
                        for sel in &hier.path[1].selects {
                            e = Expression::new(
                                ExprKind::Index {
                                    expr: Box::new(e),
                                    index: Box::new(rewrite_expr_impl(
                                        sel,
                                        prefix,
                                        port_map,
                                        local_names,
                                        interface_map,
                                    )),
                                },
                                expr.span,
                            );
                        }
                        MODPORT_SUBST_FLAG.with(|f| f.set(true));
                        return e;
                    }
                }
                let mut new_hier = hier.clone();
                new_hier.path[0].name.name = if_prefix.clone();
                return Expression::new(ExprKind::Ident(new_hier), expr.span);
            }
            // §6.20.2: `Cfg.VLEN` names a MEMBER of a packed-struct
            // parameter, mapped under its dotted spelling. Substitute the
            // member's constant whole; substituting the head alone left the
            // struct's literal with a dangling `.VLEN`.
            if hier.path.len() >= 2 && hier.path.iter().all(|s| s.selects.is_empty()) {
                let dotted = hier
                    .path
                    .iter()
                    .map(|s| s.name.name.as_str())
                    .collect::<Vec<_>>()
                    .join(".");
                if let Some(mapped) = port_map.get(dotted.as_str()) {
                    return mapped.clone();
                }
            }
            // §23.9, §27.6: a name bound to a declaration of the generate
            // block being renamed takes the declaration's key. A whole name
            // is a new one, without a source span.
            if let Some(key) = gen_renamed(hier.bound, name, |_| true) {
                let mut h = hier.clone();
                // A path through a nested block's label keeps the head's
                // place, where a diagnostic about the path points.
                let span = match gen_renamed_label(hier.bound) {
                    true => hier.path[0].name.span,
                    false => Span::dummy(),
                };
                h.path[0].name = Identifier { name: key, span };
                h.cached_signal_id = crate::ast::cache::SignalCache::new(None);
                h.cached_resolved_name = crate::ast::cache::NameCache::new();
                if h.path.len() > 1 || !h.path[0].selects.is_empty() {
                    return Expression::new(ExprKind::Ident(h), expr.span);
                }
                h.span = Span::dummy();
                return Expression::new(ExprKind::Ident(h), Span::dummy());
            }
            if let Some(mapped) = port_map.get(name).filter(|_| !genvar_hidden(hier.bound)) {
                // §25.5.4: `p.b` through a modport-typed port whose actual is
                // an interface instance — a modport EXPRESSION member
                // substitutes its registered expression (see
                // `register_modport_expressions`).
                if hier.path.len() == 2 && hier.path[0].selects.is_empty() {
                    if let Some(inst) = whole_net_ident_name(mapped) {
                        let key = format!("{}.{}", inst, hier.path[1].name.name);
                        let hit = MODPORT_EXPR_TLS.with(|m| m.borrow().get(&key).cloned());
                        if let Some(mut e) = hit {
                            for sel in &hier.path[1].selects {
                                e = Expression::new(
                                    ExprKind::Index {
                                        expr: Box::new(e),
                                        index: Box::new(rewrite_expr_impl(
                                            sel,
                                            prefix,
                                            port_map,
                                            local_names,
                                            interface_map,
                                        )),
                                    },
                                    expr.span,
                                );
                            }
                            MODPORT_SUBST_FLAG.with(|f| f.set(true));
                            return e;
                        }
                    }
                }
                // Preserve any trailing path segments and first-segment selects:
                // `a.b.c` parsed as one ident with path=[a,b,c] where `a` is the
                // port-mapped name must become `<mapped>.b.c`, not just
                // `<mapped>`. Dropping the tail silently mis-resolved black-parrot
                // coherence-NoC multi-segment port references (the 6th write /
                // header-length field).
                let has_tail = hier.path.len() > 1 || !hier.path[0].selects.is_empty();
                // §23.3.3 (issue #128): the substituted actual's bare name may
                // ALSO be declared by this child (`.v_node(out_val)` into a
                // module whose own output port is `out_val`). Pasted un-rooted
                // into the child's body, the name re-resolves child-first
                // under the child's scope hint, so the block reads its own
                // output and the parent feedback path is silently severed.
                // Root exactly the colliding whole-net substitutions — the
                // rewritten actual is already the absolute parent name — and
                // leave every other actual on the plain machinery
                // (`whole_net_ident_name` is root-tolerant, so port_aliases
                // and interface path collapsing still see these).
                // Gate on the mapped LEAF differing from the key's leaf: a
                // generate-scope RENAME map (`vec` → `gen_arbiter.vec`, and
                // from a nested scope `g.u` → `g.inner.u`) flows through this
                // same function, its values are not yet instance-prefixed,
                // and rooting them freezes the un-prefixed name (every genfor
                // CA write vanished). A rename keeps the leaf; a genuine
                // port-actual collision (`v_node` → `out_val`) changes it.
                // A dotted key is a nested rename only when the mapped name
                // also keeps its first segment; an escaped port name such as
                // `\foo.bar ` bound to the parent's `bar` keeps only the leaf.
                let collides = whole_net_ident_name(mapped).is_some_and(|an| {
                    let leaf = an.rsplit('.').next().unwrap_or(an.as_str());
                    let key_leaf = match name.split_once('.') {
                        Some((head, _)) if an.split('.').next() == Some(head) => {
                            name.rsplit('.').next().unwrap_or(name.as_str())
                        }
                        _ => name.as_str(),
                    };
                    leaf != key_leaf
                        && (local_names.contains(leaf) || port_map.contains_key(leaf))
                        && !an.split_once('.').is_some_and(|(head, _)| design_package(head))
                });
                if !has_tail {
                    let mut m = mapped.clone();
                    if collides {
                        mark_actual_rooted(&mut m, &|_| false);
                    }
                    return m;
                }
                // Graft only when the mapped target's last segment carries NO
                // selects of its own: stacking the port reference's select
                // after a part-select connection (`.p(arr[15:0])` used as
                // `p[11]`) makes `arr[15:0][11]` read as bit-11-of-a-16-bit-
                // slice instead of ELEMENT 11 (§11.5.1 keeps element labels).
                // Selected connections fall through to the Index-node path
                // below, which the evaluator normalizes correctly.
                if let ExprKind::Ident(mut mhier) = mapped.kind.clone() {
                    // Colliding actual under a member/select tail: root the
                    // grafted head too — the appended segments name FIELDS of
                    // the actual's net, so the whole path stays absolute.
                    if collides && mhier.root.is_none() {
                        mhier.root = Some("$root".to_string());
                    }
                    // Graft seg0's selects onto the mapped target's last
                    // segment, then append the trailing segments verbatim
                    // (each keeps its own selects).
                    if !hier.path[0].selects.is_empty() {
                        if let Some(last) = mhier.path.last_mut() {
                            // §11.5.1: a constant part-select keeps the
                            // original labels, so indexing THROUGH a ranged
                            // connection selects the same element of the
                            // underlying signal: `p[11]` over `.p(arr[15:0])`
                            // is `arr[11]`. Stacking the selects instead
                            // (`arr[15:0][11]`) read bit 11 of a 16-bit
                            // slice — a one-hot arbiter granted element 0
                            // forever. Drop the redundant range before
                            // grafting an index select.
                            if last.selects.len() == 1
                                && matches!(last.selects[0].kind, ExprKind::Range(..))
                                && !hier.path[0]
                                    .selects
                                    .iter()
                                    .any(|s| matches!(s.kind, ExprKind::Range(..)))
                            {
                                last.selects.clear();
                            } else if last.selects.len() == 1
                                && hier.path[0].selects.len() == 1
                                && same_const_range(&last.selects[0], &hier.path[0].selects[0])
                            {
                                // §11.5.1: an IDENTICAL constant part-select
                                // over a part-select connection selects the
                                // very same bits, so it is a no-op. Stacking
                                // it built `net[7:0][7:0]`, which resolves to
                                // nothing — with a part-select actual at TWO
                                // nested levels a `.*`-bound interface output
                                // stopped aliasing the port net and every
                                // reader below read z instead of the driven
                                // value. One level was fine (a single select);
                                // it took two to stack. Drop the redundant
                                // repeat and keep a single select.
                                last.selects.clear();
                            }
                            last.selects.extend(hier.path[0].selects.iter().cloned());
                        }
                    }
                    for seg in &hier.path[1..] {
                        mhier.path.push(seg.clone());
                    }
                    // The grafted path is this reference, not the mapped
                    // target: give it the reference's span. With the
                    // target's, every `p.<member>` of a renamed local shared
                    // one span, and a cache keyed by it answered `p.b.size()`
                    // with `p.a`'s queue (§6.21).
                    mhier.span = hier.span;
                    return Expression::new(ExprKind::Ident(mhier), expr.span);
                }
                // Non-ident mapped target (e.g. an Index/part-select/concat
                // connection): rebuild the reference over the mapped
                // expression. Every segment's SELECTS must be preserved as
                // Index nodes — dropping them turned `p[11]` through a
                // `.p(arr[15:0])` connection into plain `arr[15:0]`, which
                // reads ELEMENT 0 instead of element 11 (a one-hot arbiter
                // granted bank 0 forever).
                let mut acc = mapped.clone();
                for sel in &hier.path[0].selects {
                    acc = Expression::new(
                        ExprKind::Index {
                            expr: Box::new(acc),
                            index: Box::new(rewrite_expr_impl(
                                sel,
                                prefix,
                                port_map,
                                local_names,
                                interface_map,
                            )),
                        },
                        expr.span,
                    );
                }
                for seg in &hier.path[1..] {
                    acc = Expression::new(
                        ExprKind::MemberAccess {
                            expr: Box::new(acc),
                            member: seg.name.clone(),
                        },
                        expr.span,
                    );
                    for sel in &seg.selects {
                        acc = Expression::new(
                            ExprKind::Index {
                                expr: Box::new(acc),
                                index: Box::new(rewrite_expr_impl(
                                    sel,
                                    prefix,
                                    port_map,
                                    local_names,
                                    interface_map,
                                )),
                            },
                            expr.span,
                        );
                    }
                }
                return acc;
            }
            if local_names.contains(name) {
                let mut new_hier = hier.clone();
                new_hier.path[0].name.name = cat2(&prefix, &name);
                ExprKind::Ident(new_hier)
            } else if let Some(e) = unit_storage::bare(hier, prefix, expr.span, &|s| {
                rewrite_expr_impl(s, prefix, port_map, local_names, interface_map)
            }) {
                // §3.12.1: a compilation-unit variable or net is declared
                // once, in the hierarchy root.
                return e;
            } else if let Some(key) = upward_subroutine_key(hier, prefix) {
                let mut new_hier = hier.clone();
                new_hier.path[0].name.name = key;
                new_hier.cached_signal_id = crate::ast::cache::SignalCache::new(None);
                new_hier.cached_resolved_name = crate::ast::cache::NameCache::new();
                ExprKind::Ident(new_hier)
            } else if let Some(upward) = upward_scope_rewrite(hier, prefix) {
                // §23.8: a name headed by an enclosing scope (the bind
                // target's module name, a sibling instance, ...) resolves
                // there, not to whatever the runtime's scope hint suggests.
                upward
            } else {
                expr.kind.clone()
            }
        }
        ExprKind::Unary { op, operand } => ExprKind::Unary {
            op: *op,
            operand: Box::new(rewrite_expr_impl(
                operand,
                prefix,
                port_map,
                local_names,
                interface_map,
            )),
        },
        ExprKind::Binary { op, left, right } => ExprKind::Binary {
            op: *op,
            left: Box::new(rewrite_expr_impl(
                left,
                prefix,
                port_map,
                local_names,
                interface_map,
            )),
            right: Box::new(rewrite_expr_impl(
                right,
                prefix,
                port_map,
                local_names,
                interface_map,
            )),
        },
        ExprKind::Conditional {
            condition,
            then_expr,
            else_expr,
        } => ExprKind::Conditional {
            condition: Box::new(rewrite_expr_impl(
                condition,
                prefix,
                port_map,
                local_names,
                interface_map,
            )),
            then_expr: Box::new(rewrite_expr_impl(
                then_expr,
                prefix,
                port_map,
                local_names,
                interface_map,
            )),
            else_expr: Box::new(rewrite_expr_impl(
                else_expr,
                prefix,
                port_map,
                local_names,
                interface_map,
            )),
        },
        ExprKind::Concatenation(parts) => ExprKind::Concatenation(
            parts
                .iter()
                .map(|p| rewrite_expr_impl(p, prefix, port_map, local_names, interface_map))
                .collect(),
        ),
        // §11.4.13: the tested operand and the set members are references
        // like any other — `bus.addr inside {[LO:HI]}` over an interface
        // port kept the port name and read x, so the test was always false.
        ExprKind::Inside { expr: e, ranges } => ExprKind::Inside {
            expr: Box::new(rewrite_expr_impl(
                e,
                prefix,
                port_map,
                local_names,
                interface_map,
            )),
            ranges: ranges
                .iter()
                .map(|r| rewrite_expr_impl(r, prefix, port_map, local_names, interface_map))
                .collect(),
        },
        ExprKind::Range(lo, hi) => ExprKind::Range(
            Box::new(rewrite_expr_impl(
                lo,
                prefix,
                port_map,
                local_names,
                interface_map,
            )),
            Box::new(rewrite_expr_impl(
                hi,
                prefix,
                port_map,
                local_names,
                interface_map,
            )),
        ),
        ExprKind::Replication { count, exprs } => ExprKind::Replication {
            count: Box::new(rewrite_expr_impl(
                count,
                prefix,
                port_map,
                local_names,
                interface_map,
            )),
            exprs: exprs
                .iter()
                .map(|e| rewrite_expr_impl(e, prefix, port_map, local_names, interface_map))
                .collect(),
        },
        ExprKind::Index { expr: base, index } => {
            if let Some(view) = interface_arrays::bare_view(interface_map, base) {
                let index = rewrite_expr_impl(index, prefix, port_map, local_names, interface_map);
                return view.element(index, expr.span);
            }
            MODPORT_SUBST_FLAG.with(|f| f.set(false));
            let nb = rewrite_expr_impl(base, prefix, port_map, local_names, interface_map);
            let from_modport = MODPORT_SUBST_FLAG.with(|f| f.replace(false));
            let ni = rewrite_expr_impl(index, prefix, port_map, local_names, interface_map);
            // §11.5.1: a bit-select of a CONSTANT part-select (`word[7:0][k]`,
            // which is what a modport-expression member `.b(word[7:0])`
            // rewrites `p.b[k]` into) addresses bit `min(l,r) + k` of the
            // base — fold it so the select stays a plain, assignable
            // bit-select instead of an index over a part-select value.
            if from_modport
                && let ExprKind::RangeSelect {
                    expr: inner,
                    kind: RangeKind::Constant,
                    left,
                    right,
                } = &nb.kind
            {
                let lit = |e: &Expression| match &e.kind {
                    ExprKind::Number(NumberLiteral::Integer { value, .. }) => {
                        value.parse::<i64>().ok()
                    }
                    _ => None,
                };
                if let (Some(l), Some(r)) = (lit(left), lit(right)) {
                    let lo = l.min(r);
                    let idx = match lit(&ni) {
                        Some(k) => make_i64_literal(lo + k, ni.span),
                        None => Expression::new(
                            ExprKind::Binary {
                                op: BinaryOp::Add,
                                left: Box::new(make_i64_literal(lo, ni.span)),
                                right: Box::new(ni.clone()),
                            },
                            ni.span,
                        ),
                    };
                    return Expression::new(
                        ExprKind::Index {
                            expr: inner.clone(),
                            index: Box::new(idx),
                        },
                        expr.span,
                    );
                }
            }
            ExprKind::Index {
                expr: Box::new(nb),
                index: Box::new(ni),
            }
        }
        ExprKind::RangeSelect {
            expr: base,
            kind,
            left,
            right,
        } => {
            if *kind == RangeKind::Constant
                && let Some(view) = interface_arrays::bare_view(interface_map, base)
            {
                let left = rewrite_expr_impl(left, prefix, port_map, local_names, interface_map);
                let right = rewrite_expr_impl(right, prefix, port_map, local_names, interface_map);
                return view.range(left, right, expr.span);
            }
            let nb = rewrite_expr_impl(base, prefix, port_map, local_names, interface_map);
            let nl = rewrite_expr_impl(left, prefix, port_map, local_names, interface_map);
            let nr = rewrite_expr_impl(right, prefix, port_map, local_names, interface_map);
            // §11.5.1: substituting a part-select actual THROUGH another
            // part-select connection stacks the two selects. When the inner
            // one denotes the SAME constant range the repeat is a no-op, and
            // stacking it built `net[7:0][7:0]`, which resolves to nothing:
            // with a part-select actual at TWO nested levels a `.*`-bound
            // interface output stopped aliasing the port net and every reader
            // below read z instead of the driven value. ONE level was fine —
            // it takes two to stack. Differently-bounded ranges are left
            // alone; they genuinely re-select.
            if let ExprKind::RangeSelect {
                kind: ik,
                left: il,
                right: ir,
                ..
            } = &nb.kind
            {
                if ik == kind && same_const_expr(il, &nl) && same_const_expr(ir, &nr) {
                    return nb;
                }
            }
            ExprKind::RangeSelect {
                expr: Box::new(nb),
                kind: *kind,
                left: Box::new(nl),
                right: Box::new(nr),
            }
        }
        ExprKind::Specialization {
            base,
            type_args_text,
        } => ExprKind::Specialization {
            base: Box::new(module_class_scope::specialized_receiver(
                base,
                prefix,
                port_map,
                local_names,
                interface_map,
            )),
            type_args_text: module_class_scope::spec_args_text(type_args_text, prefix, local_names),
        },
        ExprKind::MemberAccess { expr: base, member } => {
            // §6.20.2: `Cfg.VLEN` as member access on a packed-struct
            // parameter — the member is mapped under its dotted spelling
            // (see the Ident arm); take it whole.
            if let ExprKind::Ident(h) = &base.kind
                && h.root.is_none()
                && h.path.iter().all(|s| s.selects.is_empty())
            {
                let mut dotted = h
                    .path
                    .iter()
                    .map(|s| s.name.name.as_str())
                    .collect::<Vec<_>>()
                    .join(".");
                dotted.push('.');
                dotted.push_str(&member.name);
                if let Some(mapped) = port_map.get(dotted.as_str()) {
                    return mapped.clone();
                }
            }
            let rewritten_base =
                rewrite_expr_impl(base, prefix, port_map, local_names, interface_map);
            // `flatten_pkg_member_refs`: only a package-headed `P::m` folds.
            let keep = gen_in_class()
                || PKG_FLATTEN_ONLY.with(|s| {
                    s.borrow().as_ref().is_some_and(|pkgs| {
                        !matches!(&rewritten_base.kind, ExprKind::Ident(h)
                            if h.root.is_none()
                                && h.path.len() == 1
                                && h.path[0].selects.is_empty()
                                && pkgs.contains(&h.path[0].name.name))
                    })
                });
            if keep {
                return Expression::new(
                    ExprKind::MemberAccess {
                        expr: Box::new(rewritten_base),
                        member: member.clone(),
                    },
                    expr.span,
                );
            }
            if let ExprKind::Ident(mut hier) = rewritten_base.kind {
                // §25.5.4: `p.b` where `p` rewrote to an interface instance
                // and `b` is a modport EXPRESSION member — substitute the
                // registered expression (see `register_modport_expressions`).
                if hier.path.len() == 1 && hier.path[0].selects.is_empty() {
                    let key = format!("{}.{}", hier.path[0].name.name, member.name);
                    let hit = MODPORT_EXPR_TLS.with(|m| m.borrow().get(&key).cloned());
                    if let Some(e) = hit {
                        MODPORT_SUBST_FLAG.with(|f| f.set(true));
                        return e;
                    }
                }
                hier.path.push(HierPathSegment {
                    name: member.clone(),
                    selects: Vec::new(),
                });
                // §23.8: `node1.req1` parses as a member access on the bare
                // `node1`; folded into one path, its head may name an
                // enclosing scope (see `upward_scope_rewrite`). A head the
                // body declares was prefixed above and is skipped there.
                match upward_scope_rewrite(&hier, prefix) {
                    Some(upward) => upward,
                    None => ExprKind::Ident(hier),
                }
            } else {
                ExprKind::MemberAccess {
                    expr: Box::new(rewritten_base),
                    member: member.clone(),
                }
            }
        }
        ExprKind::Paren(inner) => ExprKind::Paren(Box::new(rewrite_expr_impl(
            inner,
            prefix,
            port_map,
            local_names,
            interface_map,
        ))),
        ExprKind::Call { func, args } => ExprKind::Call {
            func: Box::new(rewrite_expr_impl(
                func,
                prefix,
                port_map,
                local_names,
                interface_map,
            )),
            args: args
                .iter()
                .map(|a| rewrite_expr_impl(a, prefix, port_map, local_names, interface_map))
                .collect(),
        },
        ExprKind::SystemCall { name, args } => {
            // `$bits(T)` / `$left(T)` / … on a bound type parameter fold here,
            // before the ident could be prefixed into a nonexistent signal.
            if let Some(v) = query_of_bound_type_param(name, args) {
                return make_i64_literal(v, expr.span);
            }
            ExprKind::SystemCall {
                name: name.clone(),
                args: args
                    .iter()
                    .map(|a| rewrite_expr_impl(a, prefix, port_map, local_names, interface_map))
                    .collect(),
            }
        }
        // LRM §16.5 SVA property body — substitute formal-arg
        // references in both the clock signal and the body. Without
        // this, a checker like
        //   `assert property (@(posedge clk) in_a |=> in_b);`
        // would keep references to formal `in_a`/`in_b` after the
        // port-substitution pass, causing the sva site to read
        // non-existent signals.
        ExprKind::SvaClocked { events, body } => {
            let events = events
                .iter()
                .map(|event| {
                    let mut expr = rewrite_expr_impl(
                        &event.expr,
                        prefix,
                        port_map,
                        local_names,
                        interface_map,
                    );
                    let mut edge = event.edge;
                    // §17.2: a checker event formal carries its actual edge as
                    // a marker call; retain that edge on every event-list term.
                    if edge.is_none() {
                        if let ExprKind::SystemCall { name, args } = &expr.kind {
                            if args.len() == 1 {
                                let actual = match name.as_str() {
                                    "$__posedge" => Some(Edge::Posedge),
                                    "$__negedge" => Some(Edge::Negedge),
                                    "$__edge" => Some(Edge::Edge),
                                    _ => None,
                                };
                                if actual.is_some() {
                                    edge = actual;
                                    expr = args[0].clone();
                                }
                            }
                        }
                    }
                    EventExpr {
                        expr,
                        edge,
                        iff: event.iff.as_ref().map(|g| {
                            rewrite_expr_impl(g, prefix, port_map, local_names, interface_map)
                        }),
                        span: event.span,
                    }
                })
                .collect();
            ExprKind::SvaClocked {
                events,
                body: Box::new(rewrite_expr_impl(
                    body,
                    prefix,
                    port_map,
                    local_names,
                    interface_map,
                )),
            }
        }
        // §10.9.2: an assignment pattern is an EXPRESSION, and its items name
        // parameters and signals of the module it was written in. Falling
        // through to `other.clone()` left every one of them unprefixed, so once
        // the instance was inlined they resolved to nothing in the parent scope
        // and read 0:
        //
        //     module ch #(parameter real P = 3.5) (output S o);
        //       assign o = '{P, 1.0};        // o.a read 0, not 3.5
        //
        // A plain `assign direct = P;` in the same module was always correct,
        // which is what made this look like a struct bug rather than a
        // port-rewriting one. Member NAMES in `Named` items are field
        // identifiers, not references, so only the value side is rewritten; a
        // `Keyed` item's key IS an expression (associative-array index) and is.
        ExprKind::AssignmentPattern(items) => ExprKind::AssignmentPattern(
            items
                .iter()
                .map(|it| {
                    use crate::ast::expr::AssignmentPatternItem as Api;
                    let rw = |e: &Expression| {
                        rewrite_expr_impl(e, prefix, port_map, local_names, interface_map)
                    };
                    match it {
                        Api::Ordered(e) => {
                            let mut rewritten = rw(e);
                            // §10.9.2: substituting a genvar/port or folding a
                            // type query must not admit a nonliteral count to
                            // literal-only structure expansion. Parentheses
                            // retain its value for the existing handling.
                            if let ExprKind::Replication { count, .. } = &e.kind
                                && !matches!(
                                    count.kind,
                                    ExprKind::Number(NumberLiteral::Integer { .. })
                                )
                                && let ExprKind::Replication {
                                    count: new_count, ..
                                } = &mut rewritten.kind
                                && matches!(
                                    new_count.kind,
                                    ExprKind::Number(NumberLiteral::Integer { .. })
                                )
                            {
                                **new_count =
                                    Expression::new(ExprKind::Paren(new_count.clone()), count.span);
                            }
                            Api::Ordered(rewritten)
                        }
                        Api::Named(n, e) => {
                            let mut n = n.clone();
                            let typedef = |k| k == crate::ast::binding::DeclKind::Typedef;
                            if let Some(key) = gen_renamed(n.bound, n.type_key_name(), typedef) {
                                n.type_key = Some(key.into_boxed_str());
                            }
                            if !prefix.is_empty() {
                                let lookup = n.type_key_name();
                                if !lookup.contains("::")
                                    && (local_names.contains(lookup)
                                        || TYPE_BIND_TYPES_TLS.with(|c| {
                                            c.borrow()
                                                .as_ref()
                                                .is_some_and(|m| m.contains_key(lookup))
                                        }))
                                {
                                    n.type_key = Some(format!("{prefix}{lookup}").into_boxed_str());
                                }
                            }
                            Api::Named(n, rw(e))
                        }
                        Api::Typed(t, e) => Api::Typed(
                            rewrite_typed_pattern_type(
                                t,
                                prefix,
                                port_map,
                                local_names,
                                interface_map,
                            ),
                            rw(e),
                        ),
                        Api::Default(e) => Api::Default(rw(e)),
                        Api::Keyed(k, e) => Api::Keyed(rw(k), rw(e)),
                    }
                })
                .collect(),
        ),
        // `$bits(logic [W-1:0])`: the type's bounds name this instance's
        // parameters like any other expression. Left bare, they resolved
        // against the root module's (or none, under the multi-top wrapper).
        ExprKind::TypeLiteral(dt) => {
            ExprKind::TypeLiteral(Box::new(module_class_scope::data_type(
                &rewrite_data_type_scoped(dt, prefix, port_map, local_names, interface_map),
                prefix,
                port_map,
            )))
        }
        ExprKind::TypedPattern { ty, pattern } => ExprKind::TypedPattern {
            ty: Box::new(rewrite_typed_pattern_type(
                ty,
                prefix,
                port_map,
                local_names,
                interface_map,
            )),
            pattern: Box::new(rewrite_expr_impl(
                pattern,
                prefix,
                port_map,
                local_names,
                interface_map,
            )),
        },
        // A named class-parameter value `#(.W(N))`: `N` is scoped like any
        // positional value.
        ExprKind::NamedArg { name, expr: inner } => ExprKind::NamedArg {
            name: name.clone(),
            expr: inner.as_ref().map(|x| {
                Box::new(rewrite_expr_impl(
                    x,
                    prefix,
                    port_map,
                    local_names,
                    interface_map,
                ))
            }),
        },
        // §7.12 / §18.7 / §18.12: an array method's `with (expr)` clause and
        // a `randomize(...) with { ... }` call name the instance's own objects
        // like any other operand, so they take the instance prefix (see
        // `rescope_expr`). Cloning them verbatim left their operands as bare
        // leaf names: in a child instance `std::randomize(arr) with {...}`
        // solved the top module's same-named `arr`, or no array at all, and
        // the constraints and `arr.sum() with (...)` read the wrong storage.
        ExprKind::WithClause { .. } => {
            return rescope_expr(expr, prefix, port_map, local_names, interface_map);
        }
        ExprKind::RandomizeWith { call, constraints } => ExprKind::RandomizeWith {
            call: Box::new(rescope_expr(
                call,
                prefix,
                port_map,
                local_names,
                interface_map,
            )),
            constraints: constraints
                .iter()
                .map(|c| rewrite_constraint_item(c, prefix, port_map, local_names, interface_map))
                .collect(),
        },
        // §11.3.6: an assignment used as an expression (`i = i + 1` as a
        // `for` step, `(a += 1)`) names its target and operand like the
        // assignment statement does. Cloned verbatim, a renamed block local
        // (§6.21) used as a loop variable kept its old name in the step,
        // which wrote another variable, and the loop never ended.
        ExprKind::AssignExpr { lvalue, rvalue } => ExprKind::AssignExpr {
            lvalue: Box::new(rewrite_expr(
                lvalue,
                prefix,
                port_map,
                local_names,
                interface_map,
            )),
            rvalue: Box::new(rewrite_expr(
                rvalue,
                prefix,
                port_map,
                local_names,
                interface_map,
            )),
        },
        // §12.6: `expr matches pattern` names the instance's objects too.
        ExprKind::Matches { expr: e, pattern } => ExprKind::Matches {
            expr: Box::new(rewrite_expr_impl(
                e,
                prefix,
                port_map,
                local_names,
                interface_map,
            )),
            pattern: Box::new(rewrite_pattern(
                pattern,
                prefix,
                port_map,
                local_names,
                interface_map,
            )),
        },
        // §11.4.14: a streaming concatenation's operands (and slice size)
        // name variables like any operand. Cloned verbatim, a renamed block
        // local (§6.21) inside `{<<{a}}` kept its old name.
        ExprKind::StreamOp {
            left_to_right,
            slice_size,
            exprs,
        } => ExprKind::StreamOp {
            left_to_right: *left_to_right,
            slice_size: slice_size.as_ref().map(|e| {
                Box::new(rewrite_expr(
                    e,
                    prefix,
                    port_map,
                    local_names,
                    interface_map,
                ))
            }),
            exprs: exprs
                .iter()
                .map(|e| rewrite_expr(e, prefix, port_map, local_names, interface_map))
                .collect(),
        },
        other => other.clone(),
    };
    Expression::new(new_kind, expr.span)
}

/// Instance rewrite of an operand of a `with` clause or an inline-constraint
/// block that keeps the expression's SHAPE: only identifiers are renamed (by
/// `rewrite_expr_impl`), and every other node is rebuilt around its rewritten
/// children. The generic rewrite flattens `a.m` into the dotted identifier
/// `a.m`; the randomize call (`std::randomize`, `obj.randomize`), the
/// constraint solver (`arr.size()`, `arr.sum()`) and the `with` evaluation
/// recognize these constructs by their member-access form.
fn rescope_expr(
    e: &Expression,
    prefix: &str,
    port_map: &HashMap<String, Expression>,
    local_names: &std::collections::HashSet<String>,
    interface_map: &HashMap<String, String>,
) -> Expression {
    let rx = |x: &Expression| rescope_expr(x, prefix, port_map, local_names, interface_map);
    let bx = |x: &Expression| Box::new(rx(x));
    let kind = match &e.kind {
        ExprKind::Ident(h) => {
            let mut h = h.clone();
            // The selects held on the path name instance objects too; a
            // port-mapped head is substituted whole below instead, which
            // rewrites its selects itself.
            let mapped = h.root.is_none()
                && h.path
                    .first()
                    .is_some_and(|s| port_map.contains_key(&s.name.name));
            if !mapped {
                for seg in &mut h.path {
                    for sel in &mut seg.selects {
                        *sel = rx(sel);
                    }
                }
            }
            // §18.7.1 `local::name` binds in the scope of the randomize()
            // call: the instance's own object when the instance declares it.
            if h.root.as_deref() == Some(LOCAL_SCOPE_ROOT) {
                if let Some(seg) = h.path.first_mut() {
                    if local_names.contains(seg.name.name.as_str()) {
                        seg.name.name = cat2(prefix, &seg.name.name);
                    }
                }
                return Expression::new(ExprKind::Ident(h), e.span);
            }
            let renamed = Expression::new(ExprKind::Ident(h), e.span);
            return rewrite_expr_impl(&renamed, prefix, port_map, local_names, interface_map);
        }
        ExprKind::MemberAccess { expr: base, member } => ExprKind::MemberAccess {
            expr: bx(base),
            member: member.clone(),
        },
        ExprKind::WithClause { expr: base, filter } => {
            // The iterator (`item`, or the method's single identifier
            // argument) is a declaration bound by the clause: it is left as
            // written and shadows a same-named instance object in the filter.
            let iter_arg = match &base.kind {
                ExprKind::Call { args, .. } => match args.as_slice() {
                    [a] => match &a.kind {
                        ExprKind::Ident(h)
                            if h.root.is_none()
                                && h.path.len() == 1
                                && h.path[0].selects.is_empty() =>
                        {
                            Some(h.path[0].name.name.clone())
                        }
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            };
            let base_out = match (&base.kind, &iter_arg) {
                (ExprKind::Call { func, args }, Some(_)) => Expression::new(
                    ExprKind::Call {
                        func: bx(func),
                        args: args.clone(),
                    },
                    base.span,
                ),
                _ => rx(base),
            };
            let iter = iter_arg.unwrap_or_else(|| "item".to_string());
            let filter_out = with_shadowed(&[iter.as_str()], port_map, local_names, |pm, ln| {
                rescope_expr(filter, prefix, pm, ln, interface_map)
            });
            ExprKind::WithClause {
                expr: Box::new(base_out),
                filter: Box::new(filter_out),
            }
        }
        ExprKind::Call { func, args } => ExprKind::Call {
            func: bx(func),
            args: args.iter().map(rx).collect(),
        },
        ExprKind::Unary { op, operand } => ExprKind::Unary {
            op: *op,
            operand: bx(operand),
        },
        ExprKind::Binary { op, left, right } => ExprKind::Binary {
            op: *op,
            left: bx(left),
            right: bx(right),
        },
        ExprKind::Conditional {
            condition,
            then_expr,
            else_expr,
        } => ExprKind::Conditional {
            condition: bx(condition),
            then_expr: bx(then_expr),
            else_expr: bx(else_expr),
        },
        ExprKind::Concatenation(parts) => ExprKind::Concatenation(parts.iter().map(rx).collect()),
        ExprKind::Replication { count, exprs } => ExprKind::Replication {
            count: bx(count),
            exprs: exprs.iter().map(rx).collect(),
        },
        ExprKind::Inside { expr: x, ranges } => ExprKind::Inside {
            expr: bx(x),
            ranges: ranges.iter().map(rx).collect(),
        },
        ExprKind::Range(lo, hi) => ExprKind::Range(bx(lo), bx(hi)),
        // §23.3.3.5: select in the formal's index space before rebuilding
        // a method receiver. Rewriting the base alone creates a whole-array
        // slice, then applies the formal label to the actual slice.
        ExprKind::Index { expr: x, index } => {
            if let Some(view) = interface_arrays::bare_view(interface_map, x) {
                return view.element(rx(index), e.span);
            }
            ExprKind::Index { expr: bx(x), index: bx(index) }
        }
        ExprKind::RangeSelect { expr: x, kind, left, right } => {
            if *kind == RangeKind::Constant
                && let Some(view) = interface_arrays::bare_view(interface_map, x)
            {
                return view.range(rx(left), rx(right), e.span);
            }
            ExprKind::RangeSelect { expr: bx(x), kind: *kind, left: bx(left), right: bx(right) }
        }
        ExprKind::Paren(x) => ExprKind::Paren(bx(x)),
        ExprKind::SystemCall { name, args } if query_of_bound_type_param(name, args).is_none() => {
            ExprKind::SystemCall {
                name: name.clone(),
                args: args.iter().map(rx).collect(),
            }
        }
        _ => return rewrite_expr_impl(e, prefix, port_map, local_names, interface_map),
    };
    Expression::new(kind, e.span)
}

/// Run `f` with `bound` names removed from the instance's local names and
/// port map: names a construct binds itself (a `with` iterator, a constraint
/// `foreach` loop variable) shadow the instance's same-named objects. The
/// sets are only cloned when a bound name actually collides.
pub(super) fn with_shadowed<R>(
    bound: &[&str],
    port_map: &HashMap<String, Expression>,
    local_names: &std::collections::HashSet<String>,
    f: impl FnOnce(&HashMap<String, Expression>, &std::collections::HashSet<String>) -> R,
) -> R {
    // §13.3: the formals are not scopes either (`upward_scope_rewrite`).
    let _stmt_locals = push_stmt_locals(bound.iter().map(|b| (*b).to_string()).collect());
    let ln = without_declared(local_names, bound.iter().copied());
    let pm = if bound.iter().any(|b| port_map.contains_key(*b)) {
        let mut m = port_map.clone();
        for b in bound {
            m.remove(*b);
        }
        Some(m)
    } else {
        None
    };
    f(
        pm.as_ref().unwrap_or(port_map),
        ln.as_ref().unwrap_or(local_names),
    )
}

/// Rewrite one inline-constraint item (§18.5) of a `randomize() with` for the
/// instance: every operand takes the instance prefix, and a `foreach` loop
/// variable shadows a same-named instance object inside its body.
pub(super) fn rewrite_constraint_item(
    c: &ConstraintItem,
    prefix: &str,
    port_map: &HashMap<String, Expression>,
    local_names: &std::collections::HashSet<String>,
    interface_map: &HashMap<String, String>,
) -> ConstraintItem {
    let rx = |e: &Expression| rescope_expr(e, prefix, port_map, local_names, interface_map);
    let ri = |i: &ConstraintItem| {
        Box::new(rewrite_constraint_item(
            i,
            prefix,
            port_map,
            local_names,
            interface_map,
        ))
    };
    match c {
        ConstraintItem::Expr(e) => ConstraintItem::Expr(rx(e)),
        ConstraintItem::Inside {
            expr,
            range,
            is_dist,
            dist_weights,
            span,
        } => ConstraintItem::Inside {
            expr: rx(expr),
            range: range
                .iter()
                .map(|r| match r {
                    ConstraintRange::Value(v) => ConstraintRange::Value(rx(v)),
                    ConstraintRange::Range { lo, hi } => ConstraintRange::Range {
                        lo: rx(lo),
                        hi: rx(hi),
                    },
                })
                .collect(),
            is_dist: *is_dist,
            dist_weights: dist_weights
                .iter()
                .map(|w| {
                    w.as_ref().map(|w| match w {
                        DistWeight::Each(e) => DistWeight::Each(rx(e)),
                        DistWeight::Total(e) => DistWeight::Total(rx(e)),
                    })
                })
                .collect(),
            span: *span,
        },
        ConstraintItem::Implication {
            condition,
            constraint,
            span,
        } => ConstraintItem::Implication {
            condition: rx(condition),
            constraint: ri(constraint),
            span: *span,
        },
        ConstraintItem::IfElse {
            condition,
            then_item,
            else_item,
            span,
        } => ConstraintItem::IfElse {
            condition: rx(condition),
            then_item: ri(then_item),
            else_item: else_item.as_ref().map(|e| ri(e)),
            span: *span,
        },
        ConstraintItem::Foreach {
            array,
            vars,
            item,
            span,
        } => {
            let bound: Vec<&str> = vars.iter().flatten().map(|v| v.name.as_str()).collect();
            let body = with_shadowed(&bound, port_map, local_names, |pm, ln| {
                rewrite_constraint_item(item, prefix, pm, ln, interface_map)
            });
            ConstraintItem::Foreach {
                array: rx(array),
                vars: vars.clone(),
                item: Box::new(body),
                span: *span,
            }
        }
        ConstraintItem::Solve {
            before,
            after,
            before_paths,
            after_paths,
            span,
        } => {
            // §18.5.10: the operands name random variables — for a
            // `std::randomize` call, the instance's own objects.
            let rid = |id: &Identifier| {
                let mut id = id.clone();
                if local_names.contains(id.name.as_str()) && !port_map.contains_key(&id.name) {
                    id.name = cat2(prefix, &id.name);
                }
                id
            };
            ConstraintItem::Solve {
                before: before.iter().map(rid).collect(),
                after: after.iter().map(rid).collect(),
                before_paths: before_paths.iter().map(rx).collect(),
                after_paths: after_paths.iter().map(rx).collect(),
                span: *span,
            }
        }
        ConstraintItem::Soft(inner) => ConstraintItem::Soft(ri(inner)),
        ConstraintItem::Block(items) => ConstraintItem::Block(
            items
                .iter()
                .map(|i| rewrite_constraint_item(i, prefix, port_map, local_names, interface_map))
                .collect(),
        ),
        ConstraintItem::Unique { exprs, span } => ConstraintItem::Unique {
            exprs: exprs.iter().map(rx).collect(),
            span: *span,
        },
    }
}

/// Rewrite the constant-expression leaves of a §12.6 pattern for an instance.
/// Tag names and `.v` binding names are not signals and are left alone.
pub(super) fn rewrite_pattern(
    p: &crate::ast::stmt::Pattern,
    prefix: &str,
    port_map: &HashMap<String, Expression>,
    local_names: &std::collections::HashSet<String>,
    interface_map: &HashMap<String, String>,
) -> crate::ast::stmt::Pattern {
    use crate::ast::stmt::Pattern as P;
    match p {
        P::Wildcard => P::Wildcard,
        P::Binding(id) => P::Binding(id.clone()),
        P::Tagged { tag, inner } => P::Tagged {
            tag: tag.clone(),
            inner: inner.as_ref().map(|i| {
                Box::new(rewrite_pattern(
                    i,
                    prefix,
                    port_map,
                    local_names,
                    interface_map,
                ))
            }),
        },
        P::Expr(e) => P::Expr(rewrite_expr(
            e,
            prefix,
            port_map,
            local_names,
            interface_map,
        )),
        P::Struct(ms) => P::Struct(
            ms.iter()
                .map(|(n, sp)| {
                    (
                        n.clone(),
                        rewrite_pattern(sp, prefix, port_map, local_names, interface_map),
                    )
                })
                .collect(),
        ),
    }
}
