use super::*;

/// Scan pending_cont_assign for implicit-net candidates after sub-module
/// inlining. For each pending cont-assign with LHS = bare identifier X
/// (no prior `wire X` declaration), construct the prefixed name
/// `<ctx.prefix>X` and add it as a 1-bit wire to elab.signals.
///
/// Why this matters: `assign undeclared_wire = expr;` implicitly creates
/// a 1-bit wire per IEEE 1800-2017 §6.10. The initial pass in
/// `create_implicit_nets` only sees the top-level `continuous_assigns`
/// vec, missing sub-module bodies still in pending. Without this
/// follow-up pass, the cont-assign can't resolve its LHS signal_id and
/// gets dropped silently — symptom: c910 wid_for_axi4's `create_en`
/// stayed X forever, freezing the wid-tracking FIFO.
pub(super) fn create_implicit_nets_for_pending(elab: &mut ElaboratedModule) {
    let mut names_to_add: Vec<String> = Vec::new();
    for pending in &elab.pending_cont_assign {
        let prefix = &pending.ctx.prefix;
        let mut bare = Vec::new();
        collect_implicit_net_candidates(&pending.source_lhs(), &mut bare);
        collect_implicit_net_candidates(&pending.rhs_source, &mut bare);
        for name in bare {
            // If the bare name is a port (in port_map), it gets rewritten
            // to the parent's signal — don't create an implicit net here.
            if pending.ctx.port_map.contains_key(&name) {
                continue;
            }
            // If it's a parameter, no implicit net needed.
            if elab.parameters.contains_key(&name) {
                continue;
            }
            // A pending wrapped through NESTED inlining carries ALREADY-
            // PREFIXED identifiers in its source expressions; re-prefixing
            // fabricated doubled names (`u0.l0.u0.l0.w0`) and phantom 1-bit
            // nets for signals that exist. If the candidate as-is is a known
            // signal or net, it needs nothing.
            // ...but only when the candidate ALREADY LOOKS ABSOLUTE. A bare
            // sub-module-local identifier still needs its own `<prefix>name`
            // net even when something elsewhere shares the bare spelling, and
            // something usually does: instance names and generate-block labels
            // are both registered as placeholder SIGNALS. A cell's
            // `buf B (gen, A);` beside a `begin : gen` generate block lost its
            // implicit net and the cell read x. Nested-inlining candidates are
            // dotted, so the dot test keeps their protection intact.
            if name.contains('.') && (elab.signals.contains_key(&name) || elab.nets.contains(&name))
            {
                continue;
            }
            // The bare name is a sub-module-local identifier; after rewrite
            // it becomes `<prefix>name`.
            let prefixed = cat2(&prefix, &name);
            // An unpacked ARRAY has no signal under its own name — its
            // ELEMENTS are the signals — so `assign dst = src;` between two
            // arrays inside a sub-module looked like two undeclared
            // identifiers here and got 1-BIT implicit nets. The assignment
            // then drove a phantom scalar and the real elements stayed x for
            // the whole run. An array is declared; never synthesize a net for
            // it.
            let is_declared_array = |n: &String| {
                elab.arrays.contains_key(n)
                    || elab.arrays_2d.contains_key(n)
                    || elab.arrays_nd.contains_key(n)
                    || elab.associative_arrays.contains_key(n)
            };
            if is_declared_array(&prefixed) || is_declared_array(&name) {
                continue;
            }
            // §7.2 / §6.6.7(d): an UNPACKED STRUCT has no signal under its own
            // name either — `register_unpacked_aggregate` registers the member
            // LEAVES (`base.i`, `base.v`, ...) and nothing at `base`. That is
            // how a user-defined nettype whose data type is an unpacked struct
            // is stored, so a nettype net declared inside a SUB-MODULE looked
            // undeclared here and got a 1-bit implicit net laid over its own
            // base name. The scalar then absorbed the continuous assign: the
            // member leaves were never written and every read of the net came
            // back 0.0, silently, in a design that elaborated without error.
            // The same declaration in the TOP module was correct, because that
            // path never reaches this pass.
            //
            // `var_decl_types` is written for instance-scope declarations by
            // the sub-module inlining path, which runs before this one, so the
            // declared type is on file by now. Check the resolved type rather
            // than the mere presence of a key: scalar child declarations are
            // recorded there too, and those DO want an implicit net when the
            // name is otherwise unknown.
            let is_unpacked_aggregate = |n: &String| {
                elab.var_decl_types.get(n).is_some_and(|dt| {
                    matches!(
                        resolve_typedef_chain(dt, &elab.typedef_types),
                        DataType::Struct(su)
                            if !su.packed
                                && !(matches!(su.kind, StructUnionKind::Union) && !su.tagged)
                    )
                })
            };
            if is_unpacked_aggregate(&prefixed) || is_unpacked_aggregate(&name) {
                continue;
            }
            if !elab.signals.contains_key(&prefixed)
                && !elab.parameters.contains_key(&prefixed)
                && !elab.nets.contains(&prefixed)
            {
                names_to_add.push(prefixed);
            }
        }
    }
    names_to_add.sort();
    names_to_add.dedup();
    for name in names_to_add {
        if crate::implicit_net_warn() {
            crate::elab_diag(format!(
                "[xezim][warning] implicit 1-bit net created for undeclared identifier '{}' \
                 (IEEE 1800-2017 §6.10, pending sub-module cont-assign). Add an explicit declaration to silence.",
                name
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

/// True when every identifier in `e` already has a value in `params`.
pub(super) fn expr_idents_all_known(e: &Expression, params: &HashMap<String, Value>) -> bool {
    let mut ok = true;
    fn walk(e: &Expression, params: &HashMap<String, Value>, ok: &mut bool) {
        if !*ok {
            return;
        }
        match &e.kind {
            ExprKind::Ident(h) => {
                if let Some(seg) = h.path.last() {
                    if !params.contains_key(&seg.name.name) {
                        *ok = false;
                    }
                } else {
                    *ok = false;
                }
            }
            ExprKind::Paren(i) => walk(i, params, ok),
            ExprKind::Unary { operand, .. } => walk(operand, params, ok),
            ExprKind::Binary { left, right, .. } => {
                walk(left, params, ok);
                walk(right, params, ok);
            }
            ExprKind::Conditional {
                condition,
                then_expr,
                else_expr,
            } => {
                walk(condition, params, ok);
                walk(then_expr, params, ok);
                walk(else_expr, params, ok);
            }
            ExprKind::SystemCall { args, .. } => {
                for a in args {
                    walk(a, params, ok);
                }
            }
            _ => {}
        }
    }
    walk(e, params, &mut ok);
    ok
}

/// True when every identifier in `e` is a plain, unqualified name — no
/// package/class scope (`pkg::X`) and no hierarchical or member path. Such an
/// expression can be evaluated from the module's own parameter table alone.
pub(super) fn expr_refs_are_all_local(e: &Expression) -> bool {
    let mut ok = true;
    fn walk(e: &Expression, ok: &mut bool) {
        if !*ok {
            return;
        }
        match &e.kind {
            ExprKind::Ident(h) => {
                if h.path.len() != 1 || !h.path[0].selects.is_empty() {
                    *ok = false;
                }
            }
            ExprKind::MemberAccess { .. } => *ok = false,
            ExprKind::Paren(i) => walk(i, ok),
            ExprKind::Unary { operand, .. } => walk(operand, ok),
            ExprKind::Binary { left, right, .. } => {
                walk(left, ok);
                walk(right, ok);
            }
            ExprKind::Conditional {
                condition,
                then_expr,
                else_expr,
            } => {
                walk(condition, ok);
                walk(then_expr, ok);
                walk(else_expr, ok);
            }
            ExprKind::SystemCall { args, .. } => {
                for a in args {
                    walk(a, ok);
                }
            }
            // §6.20.2: an unbased-unsized init (`'1`) is self-determined and
            // gets dedicated handling in the walk (1-bit, fill semantics).
            // Pre-seeding it would store a sized value and defeat that.
            ExprKind::Number(NumberLiteral::UnbasedUnsized(_)) => *ok = false,
            // A real-valued parameter has its own width/real handling in the
            // walk; pre-seeding would store an integer and lose it.
            ExprKind::Number(NumberLiteral::Real(_)) => *ok = false,
            ExprKind::Number(_) => {}
            // Anything else (calls, concatenations, casts, …) is not worth
            // pre-seeding; the walk handles it in declaration order as before.
            _ => *ok = false,
        }
    }
    walk(e, &mut ok);
    ok
}

/// Create implicit 1-bit wire signals for identifiers referenced in continuous assigns
/// but not declared anywhere (IEEE 1800-2017 §6.10).
/// §6.10 candidates that appear as INSTANCE PORT ACTUALS. Walks generate
/// constructs too, since an instantiation inside `generate`/`if`/`for` binds
/// nets the same way. Only the connection EXPRESSION is scanned — the formal
/// port name (`.foo` in `.foo(bar)`) names a port of the child, not a net here.
/// §6.6.8: for each instance port actual that is a bare undeclared identifier,
/// record the NETTYPE of the formal it connects to, when the formal has one.
///
/// The plain candidate collector above yields names only, which is all §6.10
/// needs to make a scalar implicit net. Coercion needs the formal's type, so
/// this walks the same instantiations and resolves each connection against the
/// instantiated module's port list.
pub(super) fn collect_nettype_port_actuals(
    items: &[ModuleItem],
    defs: Option<&HashMap<String, Definition>>,
    nettypes: &HashSet<String>,
    out: &mut HashMap<String, String>,
) {
    let Some(defs) = defs else { return };
    // The nettype of module `m`'s port, by name and by position.
    let port_nettype = |mname: &str, pname: Option<&str>, idx: usize| -> Option<String> {
        let Some(Definition::Module(md)) = defs.get(mname) else {
            return None;
        };
        let PortList::Ansi(ports) = &md.ports else {
            return None;
        };
        let port = match pname {
            Some(n) => ports.iter().find(|p| p.name.name == n)?,
            None => ports.get(idx)?,
        };
        let dt = port.data_type.as_ref()?;
        let DataType::TypeReference { name, .. } = dt else {
            return None;
        };
        let tn = &name.name.name;
        if nettypes.contains(tn) {
            Some(tn.clone())
        } else {
            None
        }
    };
    for item in items {
        match item {
            ModuleItem::ModuleInstantiation(inst) => {
                for hi in &inst.instances {
                    for (idx, c) in hi.connections.iter().enumerate() {
                        let (expr, pname) = match c {
                            PortConnection::Ordered(Some(e)) => (e, None),
                            PortConnection::Named {
                                name,
                                expr: Some(e),
                                implicit: false,
                            } => (e, Some(name.name.as_str())),
                            _ => continue,
                        };
                        let mut bare = Vec::new();
                        collect_implicit_net_candidates(expr, &mut bare);
                        // Only a WHOLE-net actual coerces; a concatenation or
                        // select of undeclared names is not a nettype value.
                        if bare.len() != 1 {
                            continue;
                        }
                        if let Some(nt) = port_nettype(&inst.module_name.name, pname, idx) {
                            out.entry(bare.pop().unwrap()).or_insert(nt);
                        }
                    }
                }
            }
            ModuleItem::GenerateRegion(g) => {
                collect_nettype_port_actuals(&g.items, Some(defs), nettypes, out)
            }
            _ => {}
        }
    }
}

pub(super) fn collect_port_connection_net_candidates(items: &[ModuleItem], out: &mut Vec<String>) {
    for item in items {
        match item {
            ModuleItem::ModuleInstantiation(inst) => {
                for hi in &inst.instances {
                    for c in &hi.connections {
                        match c {
                            PortConnection::Ordered(Some(e)) => {
                                collect_implicit_net_candidates(e, out)
                            }
                            // `.name(expr)`; the parenthesis-free `.name` form
                            // (§23.3.2.2) requires an EXISTING net, so it is
                            // not a source of implicit declarations.
                            PortConnection::Named {
                                expr: Some(e),
                                implicit: false,
                                ..
                            } => collect_implicit_net_candidates(e, out),
                            _ => {}
                        }
                    }
                }
            }
            ModuleItem::GenerateRegion(g) => collect_port_connection_net_candidates(&g.items, out),
            _ => {}
        }
    }
}

/// §6.10, §27: a port actual of an instance in a generate block that is an
/// implicit net of the block (renamed `g[0].n`) is a scalar net of that key.
/// Module-level port actuals are `create_implicit_nets`'.
pub(super) fn declare_block_port_implicit_nets(
    e: &Expression,
    elab: &mut ElaboratedModule,
) -> Result<(), String> {
    match &e.kind {
        ExprKind::Ident(h)
            if h.root.is_none() && h.path.len() == 1 && h.bound.is_block_implicit_net() =>
        {
            let name = &h.path[0].name.name;
            if elab.signals.contains_key(name) || elab.nets.contains(name) {
                return Ok(());
            }
            if sv_parser::default_nettype_none_seen() {
                return Err(format!(
                    "Implicit net '{}' under `default_nettype none (IEEE 1800-2017 §6.10)",
                    name
                ));
            }
            if crate::implicit_net_warn() {
                crate::elab_diag(format!(
                    "[xezim][warning] implicit 1-bit net created for undeclared identifier '{}' \
                     (IEEE 1800-2017 §6.10). Add an explicit declaration to silence.",
                    name
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
            elab.nets.insert(name.clone());
            Ok(())
        }
        ExprKind::Concatenation(parts) => {
            for p in parts {
                declare_block_port_implicit_nets(p, elab)?;
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

pub(super) fn create_implicit_nets(
    elab: &mut ElaboratedModule,
    port_conn_names: &[String],
    nettype_actuals: &HashMap<String, String>,
) -> Result<(), String> {
    let mut implicit_names = Vec::new();
    let mut lhs_names = Vec::new();
    for ca in &elab.continuous_assigns {
        collect_assign_net_names(&ca.lhs, &mut lhs_names);
        collect_assign_net_names(&ca.rhs, &mut implicit_names);
    }
    implicit_names.extend(lhs_names.iter().cloned());
    let lhs_names: HashSet<String> = lhs_names.into_iter().collect();
    // §6.10 also covers an identifier that appears ONLY as an instance port
    // actual — `.out(net)` on one instance and `.in(net)` on another, with
    // `net` never declared. Those were skipped, so the name existed nowhere:
    // reading it raised "Undeclared identifier" and it was absent from a
    // $dumpvars trace even though the connection itself worked (the ports were
    // wired to each other directly).
    implicit_names.sort();
    implicit_names.dedup();
    let none_active = sv_parser::default_nettype_none_seen();
    for name in implicit_names {
        if !elab.signals.contains_key(&name) && !elab.parameters.contains_key(&name) {
            // An UNPACKED collection (array/queue/assoc/dynamic) is a genuine
            // declaration living in its own map, not in `signals` — §6.10
            // does not apply, so it must not error under `default_nettype
            // none` (GitHub xezim#106: `input wire t_word din` with
            // `typedef t_byte t_word [0:3]` was rejected as an implicit net
            // whenever `din` appeared in a continuous assign). The port-actual
            // pass below has the same namespace checks.
            //
            // A collection that is only READ (`assign w = m[2];`) gets no
            // placeholder signal at all: the read resolves through the
            // elements, and the 1-bit signal this pass used to register was a
            // phantom NET named after the array, which VPI listed under
            // vpiNet. One named in an assign TARGET still gets it (neither
            // error nor warning): the simulator treats `m[i][j] = …` whose
            // root has no signal as a no-op.
            let declared_collection = elab.arrays.contains_key(&name)
                || elab.arrays_2d.contains_key(&name)
                || elab.arrays_nd.contains_key(&name)
                || elab.associative_arrays.contains_key(&name)
                || elab.dynamic_arrays.contains(&name)
                || elab.queue_vars.contains(&name);
            if declared_collection && !lhs_names.contains(&name) {
                continue;
            }
            if none_active && !declared_collection {
                return Err(format!(
                    "Implicit net '{}' under `default_nettype none (IEEE 1800-2017 §6.10)",
                    name
                ));
            }
            if !declared_collection && crate::implicit_net_warn() {
                crate::elab_diag(format!(
                    "[xezim][warning] implicit 1-bit net created for undeclared identifier '{}' \
                     (IEEE 1800-2017 §6.10). Add an explicit declaration to silence.",
                    name
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

    // Port-actual candidates are handled in a SEPARATE pass with a stricter
    // "already declared" test. A port actual is routinely a whole UNPACKED
    // ARRAY (`.a(data)` for `bit [1:0] data [0:2]`), and arrays live in their
    // own maps — without those extra namespace checks such a name looks
    // undeclared and gets a bogus 1-bit net that shadows the real array. The
    // continuous-assign pass above still gives an array named in an assign
    // TARGET its placeholder signal: the simulator relies on it for
    // `m[i][j] = …`.
    let mut port_names: Vec<String> = port_conn_names.to_vec();
    port_names.sort();
    port_names.dedup();
    for name in port_names {
        if elab.signals.contains_key(&name)
            || elab.parameters.contains_key(&name)
            || elab.arrays.contains_key(&name)
            || elab.arrays_2d.contains_key(&name)
            || elab.arrays_nd.contains_key(&name)
            || elab.interfaces.contains(&name)
            || elab.nets.contains(&name)
        {
            continue;
        }
        if none_active {
            return Err(format!(
                "Implicit net '{}' under `default_nettype none (IEEE 1800-2017 §6.10)",
                name
            ));
        }
        // §6.6.8: an implicit net connected to a port of a USER-DEFINED
        // NETTYPE takes that nettype, rather than the §6.10 scalar default —
        // the "nets are automatically coerced" rule that lets an analog node be
        // named at the point of connection. Without it a 64-bit nettype port
        // truncated onto a 1-bit wire and the node resolved to 0 with only a
        // width warning.
        //
        // Deliberately narrow: an implicit net for an ordinary port stays
        // scalar, which is what §6.10 specifies and what the reference tooling
        // does. Only a nettype formal coerces.
        if let Some(nt) = nettype_actuals.get(&name) {
            let dt = elab.typedef_types.get(nt).cloned();
            let width = elab.typedefs.get(nt).copied().unwrap_or_else(|| {
                dt.as_ref()
                    .map(|d| resolve_type_width(d, Some(&elab.parameters), Some(&elab.typedefs)))
                    .unwrap_or(1)
            });
            let is_real = dt
                .as_ref()
                .is_some_and(|d| is_type_real_resolved(d, &elab.typedef_types));
            signals_insert_traced(
                &mut elab.signals,
                line!(),
                name.clone(),
                Signal {
                    is_const: false,
                    name: name.clone().into(),
                    width: width.max(1),
                    is_signed: false,
                    direction: None,
                    value: if is_real {
                        Value::from_f64(0.0)
                    } else {
                        Value::new(width.max(1))
                    },
                    is_real,
                    type_name: Some(nt.clone()),
                },
            );
            // Registering the struct member leaves is what makes a struct-typed
            // nettype readable; a scalar one needs nothing further.
            if let Some(d) = dt {
                if matches!(
                    resolve_typedef_chain(&d, &elab.typedef_types),
                    DataType::Struct(su) if !su.packed
                ) {
                    register_unpacked_aggregate(elab, &name, &d);
                }
            }
            elab.implicit_nets.insert(name.clone());
            elab.nets.insert(name);
            continue;
        }
        if crate::implicit_net_warn() {
            crate::elab_diag(format!(
                "[xezim][warning] implicit 1-bit net created for undeclared identifier '{}' \
                 used as a port actual (scalar per IEEE 1800-2017 §6.10, matching the \
                 reference tooling; a wider port truncates/extends per §23.3.3). An \
                 undeclared port actual is usually a missing declaration — check for a \
                 failed `include — so add an explicit declaration to silence.",
                name
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
    Ok(())
}

/// Names that §6.10 may implicitly declare as 1-bit nets. Unlike
/// `collect_ident_names` this does NOT descend into a `MemberAccess` base: a
/// dotted reference (`testbench.chip_inst.dqs`) is a HIERARCHICAL path, and its
/// first segment names an instance, not an undeclared net. Descending created a
/// bogus `<prefix>.testbench` net that then drove the real one to X.
///
/// §6.10 makes a net only of a name "not declared previously in the scope
/// ... or in any scope whose declarations can be directly referenced from
/// the scope", so a name the binder found through an import or `$unit`
/// (`Bound::NO_TARGET`: a wildcard-imported package enum label in
/// `.i(op == SYS_CSR)`) is no candidate. As one it joined the inlined
/// module's local names, so every use of it in the module took the instance
/// path (`m.l.SYS_CSR`), which names nothing, and read x.
pub(super) fn collect_implicit_net_candidates(expr: &Expression, out: &mut Vec<String>) {
    match &expr.kind {
        ExprKind::Ident(hier) if hier.path.len() == 1 && hier.path[0].selects.is_empty() => {
            // §3.12.1: a name the compilation unit declares is declared; the
            // hierarchy root holds its storage.
            let name = hier.path[0].name.name.as_str();
            let unit = match crate::sv_parser::strip_unit_scope_name(name) {
                Some(plain) => unit_storage::declares(plain),
                None => hier.bound.as_decl().is_none() && unit_storage::declares(name),
            };
            if unit || hier.bound == Bound::NO_TARGET {
                return;
            }
            out.push(hier.path[0].name.name.clone());
        }
        ExprKind::MemberAccess { .. } => {}
        ExprKind::Unary { operand, .. } => collect_implicit_net_candidates(operand, out),
        ExprKind::Binary { left, right, .. } => {
            collect_implicit_net_candidates(left, out);
            collect_implicit_net_candidates(right, out);
        }
        ExprKind::Paren(i) => collect_implicit_net_candidates(i, out),
        ExprKind::Concatenation(parts) => {
            for p in parts {
                collect_implicit_net_candidates(p, out);
            }
        }
        ExprKind::Conditional {
            condition,
            then_expr,
            else_expr,
        } => {
            collect_implicit_net_candidates(condition, out);
            collect_implicit_net_candidates(then_expr, out);
            collect_implicit_net_candidates(else_expr, out);
        }
        _ => {}
    }
}

/// §23.8: inside module or interface `own`, a name whose head is `own`
/// itself (`parent_if.kids[0].clk` in `parent_if`) is resolved upward to the
/// nearest scope with that definition name: this instance. A continuous
/// assign binds its target and its operands' sensitivity at elaboration,
/// where that head named no signal — the target drove nothing and an
/// operand never woke the assign — so drop it from every name in `e`.
/// Procedural code resolves it at run time.
fn strip_own_definition_head(e: &mut Expression, own: &str) {
    for_each_sub_expr_mut(e, &mut |e| {
        let names_own = |e: &Expression| {
            matches!(&e.kind, ExprKind::Ident(h) if h.root.is_none()
                && h.path.len() == 1
                && h.path[0].selects.is_empty()
                && h.path[0].name.name == own)
        };
        let member = match &e.kind {
            ExprKind::MemberAccess { expr, member } if names_own(expr) => Some(member.clone()),
            _ => None,
        };
        if let Some(member) = member {
            let mut bare = make_ident_expr(&member.name);
            if let ExprKind::Ident(h) = &mut bare.kind {
                h.path[0].name.span = member.span;
                h.span = e.span;
            }
            bare.span = e.span;
            *e = bare;
        } else if let ExprKind::Ident(h) = &mut e.kind
            && h.root.is_none()
            && h.path.len() >= 2
            && h.path[0].selects.is_empty()
            && h.path[0].name.name == own
        {
            h.path.remove(0);
        }
    });
}

/// [`strip_own_definition_head`] over both sides of every continuous assign
/// in `items`, through generate blocks.
pub(super) fn strip_own_definition_assign_targets(items: &mut [ModuleItem], own: &str) {
    for it in items {
        match it {
            ModuleItem::ContinuousAssign(ca) => {
                for (lhs, rhs) in &mut ca.assignments {
                    strip_own_definition_head(lhs, own);
                    strip_own_definition_head(rhs, own);
                }
            }
            ModuleItem::GenerateRegion(r) => strip_own_definition_assign_targets(&mut r.items, own),
            ModuleItem::GenerateIf(g) => {
                for (_, b) in &mut g.branches {
                    strip_own_definition_assign_targets(b, own);
                }
            }
            ModuleItem::GenerateCase(g) => {
                for arm in &mut g.arms {
                    strip_own_definition_assign_targets(&mut arm.items, own);
                }
            }
            ModuleItem::GenerateFor(g) => strip_own_definition_assign_targets(&mut g.items, own),
            _ => {}
        }
    }
}

/// Collect all plain identifier names from an expression tree.
pub(super) fn collect_ident_names(expr: &Expression, out: &mut Vec<String>) {
    collect_ident_names_in(expr, out, true);
}

/// §6.10 implicit-net candidates of a continuous assignment: like
/// `collect_ident_names`, but the root of a dotted reference (`blk.x`,
/// `u.sig`, `s.field`, `g[0].u.sig`) names a scope or a declared struct or
/// array, never an implicit net.
fn collect_assign_net_names(expr: &Expression, out: &mut Vec<String>) {
    collect_ident_names_in(expr, out, false);
}

fn collect_ident_names_in(expr: &Expression, out: &mut Vec<String>, member_roots: bool) {
    let rec = |e: &Expression, out: &mut Vec<String>| collect_ident_names_in(e, out, member_roots);
    match &expr.kind {
        ExprKind::Ident(hier) if hier.path.len() == 1 && hier.path[0].selects.is_empty() => {
            out.push(hier.path[0].name.name.clone());
        }
        ExprKind::Unary { operand, .. } => rec(operand, out),
        ExprKind::Binary { left, right, .. } => {
            rec(left, out);
            rec(right, out);
        }
        ExprKind::Conditional {
            condition,
            then_expr,
            else_expr,
        } => {
            rec(condition, out);
            rec(then_expr, out);
            rec(else_expr, out);
        }
        ExprKind::Concatenation(parts) => {
            for p in parts {
                rec(p, out);
            }
        }
        ExprKind::Replication { count, exprs } => {
            rec(count, out);
            for e in exprs {
                rec(e, out);
            }
        }
        ExprKind::Index { expr, index } => {
            rec(expr, out);
            rec(index, out);
        }
        ExprKind::RangeSelect {
            expr, left, right, ..
        } => {
            rec(expr, out);
            rec(left, out);
            rec(right, out);
        }
        ExprKind::Paren(inner) => rec(inner, out),
        // Only the CALL ARGUMENTS can name nets — the callee (`func`) is a
        // function/task name, never an implicit net. Collecting it created a
        // phantom 1-bit net for const functions like a user `clog2(N)`, which
        // then re-dirtied on every combinational settle pass so settle never
        // converged (black-parrot HardFloat / BSG width helpers).
        ExprKind::Call { func: _, args } => {
            for a in args {
                rec(a, out);
            }
        }
        ExprKind::MemberAccess { expr, .. } => {
            if member_roots {
                rec(expr, out);
                return;
            }
            // §6.10: the root of `blk.x`, and of `g[0].u.x` (a member reached
            // through a select), names a scope or an array of instances,
            // interfaces or structs, never a scalar net; only the select
            // expressions can name nets. Collected, the generate block `g`
            // of `assign g[0].u.a = s;` became a 1-bit implicit net.
            let mut base = expr.as_ref();
            let mut selects: Vec<&Expression> = Vec::new();
            loop {
                match &base.kind {
                    ExprKind::Index { expr, index } => {
                        selects.push(index);
                        base = expr;
                    }
                    ExprKind::RangeSelect {
                        expr, left, right, ..
                    } => {
                        selects.push(left);
                        selects.push(right);
                        base = expr;
                    }
                    _ => break,
                }
            }
            let bare_root = matches!(&base.kind,
                ExprKind::Ident(h) if h.path.len() == 1 && h.path[0].selects.is_empty());
            if bare_root {
                for s in selects {
                    rec(s, out);
                }
            } else {
                rec(expr, out);
            }
        }
        _ => {}
    }
}
