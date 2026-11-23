use super::*;

/// IEEE 1800-2017 §28.8. A bidirectional switch is not a one-directional
/// assign: both terminals settle to the resolution of BOTH sides' drivers when
/// the switch conducts, and keep their own driver when it does not.
///
/// Rewrite each terminal's own continuous drivers into a single bridged assign:
///
/// ```text
/// assign a = $__tranif(own_a, own_b, ctl, active);
/// assign b = $__tranif(own_b, own_a, ctl, active);
/// ```
///
/// `$__tranif` resolves the two sides when the switch conducts (`z` yields to a
/// driven value; conflicting values give `x`), passes the terminal's own value
/// through when it does not, and gives `x` per differing bit when the control
/// is unknown. An unconditional `tran` always conducts.
///
/// Only terminals that are plain (possibly dotted) names are handled; a switch
/// whose terminal is an expression is left unconnected, as before.
/// IEEE 1800-2017 §6.6.1: a NET with more than one continuous driver takes the
/// wired-net resolution of all of them, not whichever assign happened to run
/// last. Fold the drivers of each such net into a single `$__wres` chain.
///
/// Only whole-net drivers (`assign w = ...`) participate; a driver of a slice
/// (`assign w[3:0] = ...`) is left alone, and variables are untouched — they
/// legitimately have one driver.
/// Elaboration-time evaluation of a call to a SIMPLE user function over
/// constant arguments (IEEE 1800-2017 §13.4.3 constant functions): the usual
/// `LOG2`/ceil-log style helpers that size ports and parameters. Interprets
/// blocking assigns, if/else, for/while (bounded), and return over a locals
/// map; anything else (waits, tasks, hierarchical refs) bails to None. A
/// parameter initializer that calls one of these used to be DEFERRED with
/// value 0 — every dependent parameter and port width then wrapped
/// (`LOG_X - 6` → 4294967290) and whole buses collapsed to 1 bit.
/// §13.3 / §10.7: an integral formal provides the assignment context for
/// its actual expression, before the function body sees its converted value.
/// A pattern actual (`pick('{b: 7, a: 5})`) of a packed-struct formal,
/// packed by the formal's type (the instance's own types first). `None` for
/// any other actual or formal.
pub(super) fn const_fn_struct_pattern_actual<P: ParamLookup>(
    port: Option<&crate::ast::decl::FunctionPort>,
    expr: &Expression,
    params: Option<&P>,
    elab: &ElaboratedModule,
) -> Option<Value> {
    if !matches!(expr.kind, ExprKind::AssignmentPattern(_)) {
        return None;
    }
    let port = port.filter(|p| p.dimensions.is_empty())?;
    let inlined = inline_instance_typedefs(&port.data_type);
    let empty = HashMap::default();
    let snapshot = params.map(ParamLookup::to_hashmap);
    let base = snapshot.as_deref().unwrap_or(&empty);
    pack_struct_const_value(
        inlined.as_ref().unwrap_or(&port.data_type),
        expr,
        base,
        &elab.typedefs,
        &elab.typedef_types,
    )
}

pub(super) fn const_function_actual<P: ParamLookup>(
    port: Option<&crate::ast::decl::FunctionPort>,
    expr: &Expression,
    params: Option<&P>,
    elab: &ElaboratedModule,
) -> Value {
    let value = match params {
        Some(p) => eval_const_expr_val_inner(expr, p, &mut const_context::Types::default()),
        None => {
            let empty = HashMap::default();
            eval_const_expr_val(expr, &empty)
        }
    };
    if let Some(port) = port.filter(|p| p.dimensions.is_empty()) {
        let empty = HashMap::default();
        let snapshot = params.map(ParamLookup::to_hashmap);
        let base = snapshot.as_deref().unwrap_or(&empty);
        if let Some(target) = param_integral_target(
            &port.data_type,
            &HashMap::default(),
            base,
            &elab.typedefs,
            &elab.typedef_types,
        ) {
            return match params {
                Some(p) => convert_param_value(&value, Some(expr), p, target),
                None => convert_param_value(&value, Some(expr), &empty, target),
            };
        }
    }
    value
}

/// §6.18, §7.2.1: `dt` with each unqualified reference to a type the
/// instance declares in its body (`local`) replaced by that type's
/// declaration, through typedefs of typedefs and struct members. Those
/// types reach the design-wide `typedef_types` only once the instance's
/// constants are settled, and that table keeps the last same-named
/// declaration of any module, so a layout built from it while the first
/// instance folds its constants found no struct (#680). A reference with
/// packed dimensions is inlined for a struct (the dimensions go to it) and a
/// packed vector (outer dimensions first). `None` when nothing is replaced.
pub(super) fn inline_body_typedefs(
    dt: &DataType,
    local: &HashMap<String, DataType>,
) -> Option<DataType> {
    fn go(dt: &DataType, local: &HashMap<String, DataType>, depth: u32) -> Option<DataType> {
        if depth > 16 {
            return None;
        }
        match dt {
            DataType::TypeReference {
                name,
                dimensions,
                type_args,
                ..
            } if name.scopes.is_empty() && type_args.is_empty() => {
                let decl = local.get(&name.name.name)?;
                let decl = go(decl, local, depth + 1).unwrap_or_else(|| decl.clone());
                if dimensions.is_empty() {
                    return Some(decl);
                }
                match decl {
                    DataType::Struct(mut su) if su.packed => {
                        let mut dims = dimensions.clone();
                        dims.extend(su.dimensions);
                        su.dimensions = dims;
                        Some(DataType::Struct(su))
                    }
                    DataType::IntegerVector {
                        kind,
                        signing,
                        dimensions: inner,
                        span,
                    } => {
                        let mut dims = dimensions.clone();
                        dims.extend(inner);
                        Some(DataType::IntegerVector {
                            kind,
                            signing,
                            dimensions: dims,
                            span,
                        })
                    }
                    _ => None,
                }
            }
            DataType::Struct(su) => {
                let mut changed = false;
                let members = su
                    .members
                    .iter()
                    .map(|m| match go(&m.data_type, local, depth + 1) {
                        Some(t) => {
                            changed = true;
                            crate::ast::types::StructMember {
                                data_type: t,
                                ..m.clone()
                            }
                        }
                        None => m.clone(),
                    })
                    .collect();
                changed.then(|| {
                    DataType::Struct(crate::ast::types::StructUnionType {
                        members,
                        ..su.clone()
                    })
                })
            }
            _ => None,
        }
    }
    if local.is_empty() {
        return None;
    }
    go(dt, local, 0)
}

/// `inline_body_typedefs` against the running instance's own types
/// (`CONST_FN_LOCAL_TYPES`), installed while its constants are folded.
pub(super) fn inline_instance_typedefs(dt: &DataType) -> Option<DataType> {
    CONST_FN_LOCAL_TYPES.with(|c| inline_body_typedefs(dt, c.borrow().as_ref()?))
}

/// Packed-struct layouts bound into `STRUCT_FIELDS_TLS` for one constant
/// function call (see `eval_const_user_function`). Dropping it restores each
/// name's previous layout, so a caller's — or an outer recursion level's —
/// same-named struct keeps its own.
#[derive(Default)]
struct ConstFnStructLayouts {
    saved: Vec<(String, Option<Vec<(String, u32, u32)>>)>,
}

impl ConstFnStructLayouts {
    pub(super) fn bind(
        &mut self,
        name: &str,
        dt: &DataType,
        params: &dyn ParamLookup,
        elab: &ElaboratedModule,
    ) {
        let inlined = inline_instance_typedefs(dt);
        let dt = inlined.as_ref().unwrap_or(dt);
        let Some(fields) = flatten_struct_fields(dt, params, &elab.typedefs, &elab.typedef_types)
        else {
            return;
        };
        let prev = STRUCT_FIELDS_TLS.with(|c| c.borrow_mut().insert(name.to_string(), fields));
        self.saved.push((name.to_string(), prev));
    }
}

impl Drop for ConstFnStructLayouts {
    fn drop(&mut self) {
        STRUCT_FIELDS_TLS.with(|c| {
            let mut c = c.borrow_mut();
            for (name, prev) in self.saved.drain(..).rev() {
                match prev {
                    Some(fields) => c.insert(name, fields),
                    None => c.remove(&name),
                };
            }
        });
    }
}

/// Packed-array element geometry bound for one constant-function call.
/// `fmt_unit_types_t` is `unit_type_t [0:4]` (2-bit elements, index 0 at the
/// top) and `fmt_logic_t` is `logic [0:4]`. Without this, elaboration indexes
/// the formal as a bit vector from the LSB: `types[i] == MERGED` never hits,
/// and `cfg[0]` of a mask `5'b10000` reads 0. The merged opgroup is then not
/// generated and its ready stays undriven.
#[derive(Default)]
struct ConstFnPackedElems {
    saved_w: Vec<(String, Option<u32>)>,
    saved_msb: Vec<(String, bool)>,
    saved_low: Vec<(String, Option<i64>)>,
}

impl ConstFnPackedElems {
    pub(super) fn bind(
        &mut self,
        name: &str,
        dt: &DataType,
        params: &dyn ParamLookup,
        elab: &ElaboratedModule,
    ) {
        let inlined = inline_instance_typedefs(dt);
        let dt = inlined.as_ref().unwrap_or(dt);
        let qualified = qualify_const_fn_typedef(dt, elab);
        let dt = qualified.as_ref().unwrap_or(dt);
        let Some((ew, msb0, low)) = packed_outer_elem(dt, params, &elab.typedef_types) else {
            return;
        };
        self.saved_low
            .push((name.to_string(), tls_register_elem_low(name, low)));
        let prev_w = PACKED_ELEM_W_TLS.with(|c| {
            let mut map = c.borrow_mut();
            let prev = map.get(name).copied();
            map.insert(name.to_string(), ew);
            prev
        });
        self.saved_w.push((name.to_string(), prev_w));
        let had_msb = PACKED_ELEM_MSB0_TLS.with(|c| c.borrow().contains(name));
        PACKED_ELEM_MSB0_TLS.with(|c| {
            if msb0 {
                c.borrow_mut().insert(name.to_string());
            } else {
                c.borrow_mut().remove(name);
            }
        });
        self.saved_msb.push((name.to_string(), had_msb));
    }
}

impl Drop for ConstFnPackedElems {
    fn drop(&mut self) {
        PACKED_ELEM_W_TLS.with(|c| {
            let mut map = c.borrow_mut();
            for (name, prev) in self.saved_w.drain(..).rev() {
                match prev {
                    Some(w) => {
                        map.insert(name, w);
                    }
                    None => {
                        map.remove(&name);
                    }
                }
            }
        });
        PACKED_ELEM_MSB0_TLS.with(|c| {
            let mut map = c.borrow_mut();
            for (name, had) in self.saved_msb.drain(..).rev() {
                if had {
                    map.insert(name);
                } else {
                    map.remove(&name);
                }
            }
        });
        for (name, prev) in self.saved_low.drain(..).rev() {
            tls_register_elem_low(&name, prev.unwrap_or(0));
        }
    }
}

/// A function formal's typedef, as declared in the package that owns the
/// function. The generate-if evaluator's shell does not import the name, so
/// `fmt_unit_types_t` is only present as `fpnew_pkg::fmt_unit_types_t`.
fn qualify_const_fn_typedef(dt: &DataType, elab: &ElaboratedModule) -> Option<DataType> {
    let DataType::TypeReference { name, .. } = dt else {
        return None;
    };
    if elab.typedef_types.contains_key(&name.name.name) {
        return None;
    }
    let pkg = CONST_FN_PACKAGE.with(|c| c.borrow().clone())?;
    const_fn_package_typedef(&pkg, &name.name.name, elab).cloned()
}

/// `(low_bit, element_width)` of `name[idx]` when the name was bound as a
/// packed array. `None` keeps the plain bit-select.
fn const_fn_packed_slot(name: &str, width: u32, idx: u64) -> Option<(u32, u32)> {
    let (ew, msb0) = PACKED_ELEM_W_TLS.with(|widths| {
        let widths = widths.borrow();
        let ew = *widths.get(name)?;
        let msb0 = PACKED_ELEM_MSB0_TLS.with(|msb| msb.borrow().contains(name));
        Some((ew, msb0))
    })?;
    let low = PACKED_ELEM_LOW_TLS.with(|c| c.borrow().get(name).copied().unwrap_or(0));
    let lo = packed_elem_slot_lo(width, ew, msb0, low, idx as i64)?;
    Some((lo, ew))
}

/// `s.a.b` as an assignment target — `MemberAccess` chains, or the dotted
/// `Ident` path the parser also produces — split into the root variable and
/// the dotted field path the struct layout table keys on. `None` for anything
/// with a select along the way.
fn const_fn_member_target(target: &Expression) -> Option<(String, String)> {
    match &target.kind {
        ExprKind::Ident(h)
            if h.path.len() >= 2 && h.path.iter().all(|s| s.selects.is_empty()) =>
        {
            let field = h.path[1..]
                .iter()
                .map(|s| s.name.name.as_str())
                .collect::<Vec<_>>()
                .join(".");
            Some((h.path[0].name.name.clone(), field))
        }
        ExprKind::MemberAccess { expr, member } => match &expr.kind {
            ExprKind::Ident(h) if h.path.len() == 1 && h.path[0].selects.is_empty() => {
                Some((h.path[0].name.name.clone(), member.name.clone()))
            }
            _ => {
                let (root, field) = const_fn_member_target(expr)?;
                Some((root, format!("{}.{}", field, member.name)))
            }
        },
        _ => None,
    }
}

pub(super) fn eval_const_user_function<P: ParamLookup>(
    fd: &FunctionDeclaration,
    arg_vals: &[Value],
    caller_params: Option<&P>,
    elab: &ElaboratedModule,
    depth: u32,
) -> Option<Value> {
    if depth > 64 {
        return None;
    }
    let fname = fd.name.name.name.clone();
    let mut locals = const_function_scope::initial_locals(fd, caller_params, elab);
    // Geometry helpers (struct layouts, packed-element widths, declared
    // storage, return width) resolve type dimensions against module params
    // AND the caller/instance params — the first instance's constants resolve
    // `[W-1:0]` with `W` present only in `caller_params`, and `elab.parameters`
    // is empty during that propagation (#680). The fused scope is the call's
    // starting locals laid over the module table, read in place: copying the
    // table for each call cost calls x parameters of the whole design (#721).
    let geom_locals = locals.clone();
    let geom = ParamEnv::Overlay {
        base: &elab.parameters,
        top: &geom_locals,
    };
    for (i, port) in fd.ports.iter().enumerate() {
        let mut v = arg_vals.get(i).cloned().unwrap_or_else(|| Value::zero(32));
        // §13.3: the actual CONVERTS to the formal's declared type — a REAL
        // formal bound to the integer literal `5` otherwise did integer
        // arithmetic throughout (`x /= 2` gave 2, not 2.5).
        if port.dimensions.is_empty() {
            let storage = declared_storage(&port.data_type, geom, elab)?;
            v = store_value(v, &storage);
        }
        locals.insert(port.name.name.clone(), v);
    }
    // §7.2 / §13.4.3: a packed-struct formal, local or return variable is read
    // and written BY MEMBER inside the function (`cfg.XLEN = u.XLEN`). Member
    // selects resolve through the bare-name layout table, so bind each one's
    // layout for the call's duration; the guard restores the caller's on every
    // exit. Without this the whole call bailed and a struct localparam built
    // by a configuration function (CVA6's `build_config`) elaborated as 0.
    let mut layouts = ConstFnStructLayouts::default();
    let mut packed_elems = ConstFnPackedElems::default();
    for port in &fd.ports {
        layouts.bind(&port.name.name, &port.data_type, &geom, elab);
        packed_elems.bind(&port.name.name, &port.data_type, &geom, elab);
    }
    layouts.bind(&fname, &fd.return_type, &geom, elab);
    fn bind_decls(
        stmts: &[Statement],
        layouts: &mut ConstFnStructLayouts,
        packed_elems: &mut ConstFnPackedElems,
        geom: ParamEnv,
        elab: &ElaboratedModule,
    ) {
        use crate::ast::stmt::StatementKind as SK;
        for st in stmts {
            match &st.kind {
                SK::VarDecl {
                    data_type,
                    declarators,
                    ..
                }
                | SK::ParamDecl {
                    data_type,
                    declarators,
                    ..
                } => {
                    for d in declarators {
                        layouts.bind(&d.name.name, data_type, &geom, elab);
                        packed_elems.bind(&d.name.name, data_type, &geom, elab);
                    }
                }
                SK::SeqBlock { stmts, .. } => {
                    bind_decls(stmts, layouts, packed_elems, geom, elab)
                }
                _ => {}
            }
        }
    }
    bind_decls(&fd.items, &mut layouts, &mut packed_elems, geom, elab);
    // The implicit return variable (typed per the declared return type).
    let return_type = resolve_typedef_chain(&fd.return_type, &elab.typedef_types);
    let return_width = resolve_type_width_env(return_type, Some(&geom), Some(&elab.typedefs));
    let ret_init = if is_type_real(return_type) {
        Value::from_f64(0.0)
    } else {
        if return_width == 0 {
            return None;
        }
        // §13.4.1: assignments and compound operators inside the function
        // already operate on the declared return variable, not an unsigned int.
        let mut value = Value::zero(return_width);
        value.is_signed = is_type_signed(return_type);
        value
    };
    locals.insert(fname.clone(), ret_init);

    enum Flow {
        Normal,
        Returned,
    }

    // §6.12.2 / §13.4.1: locals, formals and the return variable keep
    // their declared representation across every assignment. A real target
    // converts the completed RHS; it does not turn integer division real.
    fn declared_storage(dt: &DataType, geom: ParamEnv, elab: &ElaboratedModule) -> Option<Value> {
        let dt = resolve_typedef_chain(dt, &elab.typedef_types);
        if is_type_real(dt) {
            return Some(Value::from_f64(0.0));
        }
        let width = resolve_type_width_env(dt, Some(&geom), Some(&elab.typedefs));
        if width == 0 {
            return None;
        }
        let mut value = Value::zero(width);
        value.is_signed = is_type_signed(dt);
        Some(value)
    }

    fn store_value(rhs: Value, storage: &Value) -> Value {
        if storage.is_real {
            return Value::from_f64(rhs.to_f64());
        }
        let mut value = if rhs.is_real {
            real_to_integral(rhs.to_f64(), storage.width)
        } else if rhs.width == storage.width && storage.width != 0 && !rhs.is_fill {
            rhs
        } else {
            rhs.resize_for_assign(storage.width)
        };
        value.is_signed = storage.is_signed;
        value
    }

    fn eval_for_storage(
        rhs: &Expression,
        storage: &Value,
        locals: &HashMap<String, Value>,
        elab: &ElaboratedModule,
        depth: u32,
    ) -> Option<Value> {
        let value = eval_fn_expr_ctx(
            rhs,
            locals,
            elab,
            depth,
            (!storage.is_real).then_some((storage.width, None)),
        )?;
        Some(store_value(value, storage))
    }

    fn eval_assignment(
        rhs: &Expression,
        target: &Expression,
        locals: &HashMap<String, Value>,
        elab: &ElaboratedModule,
        depth: u32,
    ) -> Option<Value> {
        if let ExprKind::Ident(h) = &target.kind {
            if h.root.is_none() && h.path.len() == 1 && h.path[0].selects.is_empty() {
                if let Some(storage) = locals.get(&h.path[0].name.name) {
                    return eval_for_storage(rhs, storage, locals, elab, depth);
                }
            }
        }
        let storage = eval_fn_expr(target, locals, elab, depth)?;
        eval_for_storage(rhs, &storage, locals, elab, depth)
    }

    fn assign_local(
        target: &Expression,
        rhs: Value,
        locals: &mut HashMap<String, Value>,
        elab: &ElaboratedModule,
        depth: u32,
    ) -> Option<()> {
        match &target.kind {
            ExprKind::Ident(h) if h.path.len() == 1 && h.path[0].selects.is_empty() => {
                let name = h.path[0].name.name.clone();
                if let Some(old) = locals.get(&name) {
                    let value = store_value(rhs, old);
                    locals.insert(name, value);
                } else {
                    locals.insert(name, rhs);
                }
                Some(())
            }
            // §7.2.1: a whole-member write `s.f = v` / `s.a.b = v` lands on the
            // member's bit range of the packed struct local.
            ExprKind::MemberAccess { .. } | ExprKind::Ident(_) => {
                let (name, field) = const_fn_member_target(target)?;
                let (off, w) = STRUCT_FIELDS_TLS.with(|c| {
                    c.borrow().get(&name).and_then(|layout| {
                        layout
                            .iter()
                            .find(|(f, _, _)| *f == field)
                            .map(|&(_, o, w)| (o, w))
                    })
                })?;
                let value = locals.get_mut(&name)?;
                if w == 0 || off + w > value.width {
                    return None;
                }
                let rhs = rhs.resize(w);
                for bit in 0..w {
                    value.set_bit((off + bit) as usize, rhs.get_bit(bit as usize));
                }
                Some(())
            }
            ExprKind::Index { expr, index } => {
                let name = match &expr.kind {
                    ExprKind::Ident(h) if h.path.len() == 1 && h.path[0].selects.is_empty() => {
                        h.path[0].name.name.clone()
                    }
                    _ => return None,
                };
                let idx = eval_fn_expr(index, locals, elab, depth)?.to_i64()?;
                if idx < 0 {
                    return None;
                }
                let width = locals.get(&name)?.width;
                if let Some((lo, ew)) = const_fn_packed_slot(&name, width, idx as u64) {
                    let rhs = rhs.resize(ew);
                    let value = locals.get_mut(&name)?;
                    for bit in 0..ew {
                        value.set_bit((lo + bit) as usize, rhs.get_bit(bit as usize));
                    }
                    return Some(());
                }
                let value = locals.get_mut(&name)?;
                if idx as u32 >= value.width {
                    return None;
                }
                value.set_bit(idx as usize, rhs.get_bit(0));
                Some(())
            }
            ExprKind::RangeSelect {
                expr,
                left,
                right,
                kind,
            } => {
                let name = match &expr.kind {
                    ExprKind::Ident(h) if h.path.len() == 1 && h.path[0].selects.is_empty() => {
                        h.path[0].name.name.clone()
                    }
                    _ => return None,
                };
                let left = eval_fn_expr(left, locals, elab, depth)?.to_i64()?;
                let right = eval_fn_expr(right, locals, elab, depth)?.to_i64()?;
                let (hi, lo) = match kind {
                    crate::ast::expr::RangeKind::Constant => (left.max(right), left.min(right)),
                    crate::ast::expr::RangeKind::IndexedUp => (left + right - 1, left),
                    crate::ast::expr::RangeKind::IndexedDown => (left, left - right + 1),
                };
                let value = locals.get_mut(&name)?;
                if lo < 0 || hi < lo || hi as u32 >= value.width {
                    return None;
                }
                for bit in lo..=hi {
                    value.set_bit(bit as usize, rhs.get_bit((bit - lo) as usize));
                }
                Some(())
            }
            _ => None,
        }
    }

    fn exec_stmt(
        stmt: &Statement,
        locals: &mut HashMap<String, Value>,
        fname: &str,
        geom: ParamEnv,
        elab: &ElaboratedModule,
        depth: u32,
        fuel: &mut u32,
    ) -> Option<Flow> {
        if *fuel == 0 {
            return None;
        }
        *fuel -= 1;
        use crate::ast::stmt::StatementKind as SK;
        match &stmt.kind {
            SK::Null => Some(Flow::Normal),
            SK::SeqBlock { stmts, .. } => {
                for st in stmts {
                    match exec_stmt(st, locals, fname, geom, elab, depth, fuel)? {
                        Flow::Returned => return Some(Flow::Returned),
                        Flow::Normal => {}
                    }
                }
                Some(Flow::Normal)
            }
            SK::VarDecl {
                data_type,
                declarators,
                ..
            } => {
                let storage = declared_storage(data_type, geom, elab)?;
                for d in declarators {
                    let v = match &d.init {
                        Some(e) => eval_for_storage(e, &storage, locals, elab, depth)?,
                        None => storage.clone(),
                    };
                    locals.insert(d.name.name.clone(), v);
                }
                Some(Flow::Normal)
            }
            SK::ParamDecl {
                data_type,
                declarators,
                ..
            } => {
                // §6.20.2: an UNTYPED block-scope `localparam`/`parameter`
                // takes the type and self-determined width of each
                // declarator's initializer (so `A = 1.5, B = 2` keeps A real
                // and B 32-bit int, and `Q = 4'd0 - 4'd1` stays 4-bit 15).
                if let crate::ast::types::DataType::Implicit {
                    signing,
                    dimensions,
                    ..
                } = data_type
                    && dimensions.is_empty()
                {
                    for d in declarators {
                        let mut v = match &d.init {
                            Some(e) => eval_fn_expr(e, locals, elab, depth)?,
                            None => Value::zero(32),
                        };
                        if !v.is_real {
                            match signing {
                                Some(crate::ast::types::Signing::Signed) => v.is_signed = true,
                                Some(crate::ast::types::Signing::Unsigned) => v.is_signed = false,
                                None => {}
                            }
                        }
                        locals.insert(d.name.name.clone(), v);
                    }
                } else {
                    let storage = declared_storage(data_type, geom, elab)?;
                    for d in declarators {
                        let v = match &d.init {
                            Some(e) => eval_for_storage(e, &storage, locals, elab, depth)?,
                            None => storage.clone(),
                        };
                        locals.insert(d.name.name.clone(), v);
                    }
                }
                Some(Flow::Normal)
            }
            SK::BlockingAssign { lvalue, rvalue } => {
                let v = eval_assignment(rvalue, lvalue, locals, elab, depth)?;
                assign_local(lvalue, v, locals, elab, depth)?;
                Some(Flow::Normal)
            }
            SK::If {
                condition,
                then_stmt,
                else_stmt,
                ..
            } => {
                let c = eval_fn_expr(condition, locals, elab, depth)?;
                if c.is_true() {
                    exec_stmt(then_stmt, locals, fname, geom, elab, depth, fuel)
                } else if let Some(e) = else_stmt {
                    exec_stmt(e, locals, fname, geom, elab, depth, fuel)
                } else {
                    Some(Flow::Normal)
                }
            }
            SK::For {
                init,
                condition,
                step,
                body,
            } => {
                for fi in init {
                    match fi {
                        crate::ast::stmt::ForInit::VarDecl {
                            data_type,
                            name,
                            init: e,
                        } => {
                            let storage = declared_storage(data_type, geom, elab)?;
                            let v = eval_for_storage(e, &storage, locals, elab, depth)?;
                            locals.insert(name.name.clone(), v);
                        }
                        crate::ast::stmt::ForInit::Assign { lvalue, rvalue } => {
                            let v = eval_assignment(rvalue, lvalue, locals, elab, depth)?;
                            assign_local(lvalue, v, locals, elab, depth)?;
                        }
                    }
                }
                loop {
                    if let Some(c) = condition {
                        if !eval_fn_expr(c, locals, elab, depth)?.is_true() {
                            break;
                        }
                    } else {
                        return None; // unbounded
                    }
                    match exec_stmt(body, locals, fname, geom, elab, depth, fuel)? {
                        Flow::Returned => return Some(Flow::Returned),
                        Flow::Normal => {}
                    }
                    // step entries are EXPRESSIONS: `i++`, `i = i + 1`.
                    for st in step {
                        step_expr(st, locals, elab, depth)?;
                    }
                    if *fuel == 0 {
                        return None;
                    }
                }
                Some(Flow::Normal)
            }
            SK::While { condition, body } => {
                loop {
                    if !eval_fn_expr(condition, locals, elab, depth)?.is_true() {
                        break;
                    }
                    match exec_stmt(body, locals, fname, geom, elab, depth, fuel)? {
                        Flow::Returned => return Some(Flow::Returned),
                        Flow::Normal => {}
                    }
                    if *fuel == 0 {
                        return None;
                    }
                }
                Some(Flow::Normal)
            }
            SK::Case {
                expr, items, kind, ..
            } => {
                use crate::ast::stmt::CaseKind;
                if items.iter().any(|item| item.pattern.is_some()) {
                    return None; // pattern-matching case: bail
                }
                // §12.5: the case expression and every case item expression
                // are evaluated at the width of the widest of them, signed
                // only when all are signed, and compared with `===`.
                let mut types = const_context::Types::default();
                let mut common = const_context::infer(expr, &ParamEnv::Overlay { base: &elab.parameters, top: &*locals }, &mut types);
                let mut has_ranges = false;
                for pat in items.iter().flat_map(|item| &item.patterns) {
                    if *kind == CaseKind::CaseInside && matches!(pat.kind, ExprKind::Range(..)) {
                        has_ranges = true;
                        continue;
                    }
                    let ty = const_context::infer(pat, &ParamEnv::Overlay { base: &elab.parameters, top: &*locals }, &mut types);
                    common.width = common.width.max(ty.width);
                    common.signed &= ty.signed;
                    common.integral &= ty.integral;
                }
                let context = common
                    .integral
                    .then_some((common.width, Some(common.signed)));
                let fit = |v: Value| {
                    if !common.integral || v.width == common.width {
                        v
                    } else {
                        v.resize_for_assign(common.width)
                    }
                };
                let sel = if has_ranges {
                    fn unparenthesized(mut expr: &Expression) -> &ExprKind {
                        while let ExprKind::Paren(inner) = &expr.kind {
                            expr = inner;
                        }
                        &expr.kind
                    }
                    // Like the runtime matcher, only size operation selectors
                    // and selectors compared with an unbased unsized item.
                    let sized = matches!(
                        unparenthesized(expr),
                        ExprKind::Binary { .. }
                            | ExprKind::Unary { .. }
                            | ExprKind::Conditional { .. }
                    ) || items.iter().flat_map(|item| &item.patterns).any(|pat| {
                        matches!(
                            unparenthesized(pat),
                            ExprKind::Number(NumberLiteral::UnbasedUnsized(_))
                        )
                    });
                    let context = (sized && common.integral).then_some((common.width, None));
                    eval_fn_expr_ctx(expr, locals, elab, depth, context)?
                } else {
                    fit(eval_fn_expr_ctx(expr, locals, elab, depth, context)?)
                };
                if sel.is_real && *kind != CaseKind::CaseInside {
                    return None;
                }
                let mut chosen: Option<&Statement> = None;
                for item in items {
                    if item.is_default {
                        continue;
                    }
                    let mut hit = false;
                    for pat in &item.patterns {
                        let hit_now = if let ExprKind::Range(lo, hi) = &pat.kind
                            && has_ranges
                        {
                            // §11.4.13, §12.5.4: compare both inclusive bounds.
                            let lo_ok = matches!(lo.kind, ExprKind::Dollar)
                                || sel
                                    .greater_equal(&eval_fn_expr(lo, locals, elab, depth)?)
                                    .is_true();
                            let hi_ok = matches!(hi.kind, ExprKind::Dollar)
                                || sel
                                    .less_equal(&eval_fn_expr(hi, locals, elab, depth)?)
                                    .is_true();
                            lo_ok && hi_ok
                        } else {
                            let v = if has_ranges {
                                eval_fn_expr(pat, locals, elab, depth)?
                            } else {
                                fit(eval_fn_expr_ctx(pat, locals, elab, depth, context)?)
                            };
                            if v.is_real && *kind != CaseKind::CaseInside {
                                return None;
                            }
                            match kind {
                                CaseKind::Casex => sel.casex_eq(&v),
                                CaseKind::Casez => sel.casez_eq(&v),
                                CaseKind::CaseInside if sel.is_real || v.is_real => {
                                    sel.is_equal(&v)
                                }
                                // §12.5.4: an integral value item matches as `==?`.
                                CaseKind::CaseInside => sel.wildcard_eq(&v),
                                CaseKind::Case => sel.case_eq(&v),
                            }
                            .is_true()
                        };
                        if hit_now {
                            hit = true;
                            break;
                        }
                    }
                    if hit {
                        chosen = Some(&item.stmt);
                        break;
                    }
                }
                if chosen.is_none() {
                    chosen = items.iter().find(|i| i.is_default).map(|i| &i.stmt);
                }
                match chosen {
                    Some(st) => exec_stmt(st, locals, fname, geom, elab, depth, fuel),
                    None => Some(Flow::Normal),
                }
            }
            SK::Return(e) => {
                if let Some(e) = e {
                    let storage = locals.get(fname)?;
                    let v = eval_for_storage(e, storage, locals, elab, depth)?;
                    locals.insert(fname.to_string(), v);
                }
                Some(Flow::Returned)
            }
            // Expression statements with side-effect ops (i++ in step position
            // arrives here as Expr) — support inc/dec on locals.
            SK::Expr(e) => {
                if let ExprKind::Unary { op, operand } = &e.kind {
                    use crate::ast::expr::UnaryOp;
                    if matches!(
                        op,
                        UnaryOp::PostIncr | UnaryOp::PreIncr | UnaryOp::PostDecr | UnaryOp::PreDecr
                    ) {
                        if let ExprKind::Ident(h) = &operand.kind {
                            if h.path.len() == 1 && h.path[0].selects.is_empty() {
                                let n = h.path[0].name.name.clone();
                                let cur_v = locals.get(&n)?.clone();
                                // Real-aware: `++x` on a real formal stepped
                                // through to_i64 (None on a real) and reset to
                                // 0.
                                if cur_v.is_real {
                                    let f = cur_v.to_f64();
                                    let nf = if matches!(op, UnaryOp::PostIncr | UnaryOp::PreIncr) {
                                        f + 1.0
                                    } else {
                                        f - 1.0
                                    };
                                    locals.insert(n, Value::from_f64(nf));
                                    return Some(Flow::Normal);
                                }
                                let cur = cur_v.to_i64().unwrap_or(0);
                                let nv = if matches!(op, UnaryOp::PostIncr | UnaryOp::PreIncr) {
                                    cur + 1
                                } else {
                                    cur - 1
                                };
                                locals.insert(n, Value::from_u64(nv as u64, 32));
                                return Some(Flow::Normal);
                            }
                        }
                    }
                }
                // Any OTHER expression statement is presumed side-effecting
                // (part-select inc/dec, assignment-expression on a select…):
                // bail so the parameter defers instead of silently dropping
                // the effect.
                None
            }
            _ => None,
        }
    }

    fn step_expr(
        e: &Expression,
        locals: &mut HashMap<String, Value>,
        elab: &ElaboratedModule,
        depth: u32,
    ) -> Option<()> {
        use crate::ast::expr::UnaryOp;
        match &e.kind {
            ExprKind::Unary { op, operand }
                if matches!(
                    op,
                    UnaryOp::PostIncr | UnaryOp::PreIncr | UnaryOp::PostDecr | UnaryOp::PreDecr
                ) =>
            {
                if let ExprKind::Ident(h) = &operand.kind {
                    if h.path.len() == 1 && h.path[0].selects.is_empty() {
                        let n = h.path[0].name.name.clone();
                        let cur_v = locals.get(&n)?.clone();
                        if cur_v.is_real {
                            let f = cur_v.to_f64();
                            let nf = if matches!(op, UnaryOp::PostIncr | UnaryOp::PreIncr) {
                                f + 1.0
                            } else {
                                f - 1.0
                            };
                            locals.insert(n, Value::from_f64(nf));
                            return Some(());
                        }
                        let cur = cur_v.to_i64().unwrap_or(0);
                        let nv = if matches!(op, UnaryOp::PostIncr | UnaryOp::PreIncr) {
                            cur + 1
                        } else {
                            cur - 1
                        };
                        locals.insert(n, Value::from_u64(nv as u64, 32));
                        return Some(());
                    }
                }
                None
            }
            ExprKind::Binary {
                op: crate::ast::expr::BinaryOp::Assign,
                left,
                right,
            }
            | ExprKind::AssignExpr {
                lvalue: left,
                rvalue: right,
            } => {
                let v = eval_assignment(right, left, locals, elab, depth)?;
                assign_local(left, v, locals, elab, depth)
            }
            _ => None,
        }
    }

    fn eval_fn_expr(
        e: &Expression,
        locals: &HashMap<String, Value>,
        elab: &ElaboratedModule,
        depth: u32,
    ) -> Option<Value> {
        eval_fn_expr_ctx(e, locals, elab, depth, None)
    }

    fn eval_fn_expr_ctx(
        e: &Expression,
        locals: &HashMap<String, Value>,
        elab: &ElaboratedModule,
        depth: u32,
        context: Option<(u32, Option<bool>)>,
    ) -> Option<Value> {
        // Most loop expressions contain neither casts nor calls. Borrow
        // their AST instead of cloning it in both rewriting passes.
        let mut has_cast = false;
        let mut has_call = false;
        for_each_sub_expr(e, &mut |part| match &part.kind {
            ExprKind::Call { .. } => has_call = true,
            ExprKind::SystemCall { name, .. }
                if name == "$__xz_named_cast" || name == "$__xz_type_cast" =>
            {
                has_cast = true
            }
            _ => {}
        });
        let resolved = has_cast.then(|| resolve_const_fn_cast_targets(e, Some(&elab.parameters), elab));
        let e = resolved.as_ref().unwrap_or(e);
        if !const_fn_expr_supported(e) {
            return None;
        }
        // §11.8.2 / §13.4: both arms determine the result type, but only
        // the selected arm runs. In particular an untaken recursive call
        // must not be substituted just to discover its declared width.
        if let ExprKind::Conditional {
            condition,
            then_expr,
            else_expr,
        } = &e.kind
        {
            let c = eval_fn_expr(condition, locals, elab, depth)?;
            let ty = const_context::infer(e, &ParamEnv::Overlay { base: &elab.parameters, top: &*locals }, &mut const_context::Types::default());
            let arm_context = ty.integral.then_some((
                context.map_or(ty.width, |(w, _)| w.max(ty.width)),
                Some(context.and_then(|(_, s)| s).unwrap_or(ty.signed)),
            ));
            // §11.4.11: only a condition with no known 1 bit is ambiguous.
            if c.is_nonzero().is_none() && (ty.integral || ty.real) {
                let left = eval_fn_expr_ctx(then_expr, locals, elab, depth, arm_context)?;
                let right = eval_fn_expr_ctx(else_expr, locals, elab, depth, arm_context)?;
                return Some(left.merge_unknown(&right));
            }
            let taken = if c.is_true() { then_expr } else { else_expr };
            let value = eval_fn_expr_ctx(taken, locals, elab, depth, arm_context)?;
            return Some(if ty.real && !value.is_real {
                Value::from_f64(value.to_f64())
            } else {
                value
            });
        }
        let subbed = if has_call {
            Some(substitute_const_fn_calls(e, Some(&ParamEnv::Overlay { base: &elab.parameters, top: &*locals }), elab, depth + 1)?)
        } else {
            None
        };
        let e = subbed.as_ref().unwrap_or(e);
        if expr_has_call(e) {
            return None;
        }
        let mut types = const_context::Types::default();
        if let Some((width, signed)) = context {
            let ty = const_context::infer(e, &ParamEnv::Overlay { base: &elab.parameters, top: &*locals }, &mut types);
            if ty.integral {
                return const_ctx_fold(
                    e,
                    &ParamEnv::Overlay { base: &elab.parameters, top: &*locals },
                    width.max(ty.width),
                    signed.unwrap_or(ty.signed),
                    &mut types,
                );
            }
        }
        Some(eval_const_expr_val_inner(e, &ParamEnv::Overlay { base: &elab.parameters, top: &*locals }, &mut types))
    }

    let mut fuel: u32 = 100_000;
    for st in &fd.items {
        match exec_stmt(st, &mut locals, &fname, geom, elab, depth, &mut fuel)? {
            Flow::Returned => break,
            Flow::Normal => {}
        }
    }
    let v = locals.remove(&fname)?;
    // A REAL return keeps its representation — resize() reinterprets the
    // IEEE-754 bits (f_id(5) came back 0.0).
    if is_type_real(return_type) {
        return Some(if v.is_real {
            v
        } else {
            Value::from_f64(v.to_f64())
        });
    }
    // §13.4.1: the result takes the DECLARED return type — a
    // `function [3:0]` returning 20 yields 4, not 20. Unresolvable return
    // widths bail (deferral) rather than guessing.
    let rw = return_width;
    if rw == 0 {
        return None;
    }
    let mut v = v.resize(rw);
    v.is_signed = is_type_signed(return_type);
    Some(v)
}

/// STRICT support check: only expression shapes we KNOW
/// eval_const_expr_val computes faithfully. Anything else (size casts,
/// part-selects, side-effect operators, unknown system calls) bails the
/// whole const-fn evaluation so the parameter falls back to sim-time
/// deferral rather than silently computing a wrong value.
pub(super) fn const_fn_expr_supported(e: &Expression) -> bool {
    use crate::ast::expr::{BinaryOp, UnaryOp};
    match &e.kind {
        ExprKind::Number(_) => true,
        // 1 segment: local/param. 2 segments: a SCOPED package param
        // (`q::DEPTH`) — eval_const_expr_val resolves it via the `q::DEPTH`
        // alias, so `LOG2(q::DEPTH)` args are safe to admit.
        ExprKind::Ident(h) => {
            h.path.len() <= 2
                && h.path
                    .iter()
                    .all(|seg| seg.selects.iter().all(const_fn_expr_supported))
        }
        ExprKind::Index { expr, index } => {
            const_fn_expr_supported(expr) && const_fn_expr_supported(index)
        }
        ExprKind::RangeSelect {
            expr, left, right, ..
        } => {
            const_fn_expr_supported(expr)
                && const_fn_expr_supported(left)
                && const_fn_expr_supported(right)
        }
        // `q::DEPTH` also parses as MemberAccess{Ident(q), DEPTH};
        // eval_const_expr_val resolves it through the scoped alias (and falls
        // back to struct-param field slicing, also supported).
        // `ENC[fmt].exp_bits` is a field of one packed element. The index
        // arm slices the element and the member arm slices the field; without
        // admitting it, `fp_width` bailed and a generated instance kept the
        // localparam at 0 (`slice_result[-1:0]`).
        ExprKind::MemberAccess {
            expr: base,
            member: _,
        } => match &base.kind {
            ExprKind::Ident(h)
                if h.path.len() == 1 && h.path[0].selects.is_empty() =>
            {
                true
            }
            ExprKind::Index { .. } => const_fn_expr_supported(base),
            _ => false,
        },
        ExprKind::Paren(i) => const_fn_expr_supported(i),
        ExprKind::Unary { op, operand } => {
            !matches!(
                op,
                UnaryOp::PreIncr | UnaryOp::PostIncr | UnaryOp::PreDecr | UnaryOp::PostDecr
            ) && const_fn_expr_supported(operand)
        }
        ExprKind::Binary { op, left, right } => {
            !matches!(op, BinaryOp::Assign)
                && const_fn_expr_supported(left)
                && const_fn_expr_supported(right)
        }
        ExprKind::Conditional {
            condition,
            then_expr,
            else_expr,
        } => {
            const_fn_expr_supported(condition)
                && const_fn_expr_supported(then_expr)
                && const_fn_expr_supported(else_expr)
        }
        ExprKind::Concatenation(items) => items.iter().all(const_fn_expr_supported),
        ExprKind::Replication { count, exprs } => {
            const_fn_expr_supported(count) && exprs.iter().all(const_fn_expr_supported)
        }
        ExprKind::Call { args, .. } => args.iter().all(const_fn_expr_supported),
        // §6.24.1: `signed'(e)` / `unsigned'(e)` reach here lowered onto
        // `$signed` / `$unsigned`. They only REINTERPRET signedness — no width
        // is resolved and no type table is consulted — so `eval_const_expr_val`
        // computes them faithfully with nothing more than `params`, which is
        // the bar this list is guarding.
        //
        //
        // §6.24.1 casts. A size cast (`32'(e)`) takes its width from an
        // expression this list already vets. A type cast (`int'(e)`,
        // `logic [N-1:0]'(e)`, an enum) is admitted only when the target
        // type alone fixes its width and signing: `eval_const_expr_val` then
        // sizes it without the `TYPEDEFS_TLS` width table, where a missing
        // entry silently yields width 1. A cast to a typedef reaches here
        // already replaced by its declared type
        // (`resolve_const_fn_cast_targets`); one that could not be resolved
        // (`$__xz_named_cast`, a type reference) still bails.
        ExprKind::SystemCall { name, args } if name == "$__xz_size_cast" => {
            args.len() == 2 && args.iter().all(const_fn_expr_supported)
        }
        ExprKind::SystemCall { name, args } if name == "$__xz_type_cast" => {
            args.len() == 2
                && matches!(&args[0].kind, ExprKind::TypeLiteral(dt) if const_fn_cast_type_static(dt))
                && const_fn_expr_supported(&args[1])
        }
        ExprKind::SystemCall { name, args } => {
            (matches!(name.as_str(), "$clog2" | "$bits" | "$signed" | "$unsigned")
                || (name == crate::ast::expr::TOLERANCE_BOUND_FN && args.len() == 3)
                || (matches!(
                    name.as_str(),
                    "$rtoi"
                        | "$itor"
                        | "$realtobits"
                        | "$bitstoreal"
                        | "$shortrealtobits"
                        | "$bitstoshortreal"
                ) && args.len() == 1)
                || const_real_math_arity(name) == Some(args.len()))
                && args.iter().all(const_fn_expr_supported)
        }
        _ => false,
    }
}

/// §6.24.1: a cast target type whose width and signing follow from the type
/// itself: an integer atom, or an integer vector or enum whose dimension
/// bounds `const_fn_expr_supported` admits. Anything naming another type
/// (a type reference, a struct member type) would need the width table.
fn const_fn_cast_type_static(dt: &DataType) -> bool {
    let dims_ok = |dims: &[PackedDimension]| {
        dims.iter().all(|d| {
            matches!(d, PackedDimension::Range { left, right, .. }
                if const_fn_expr_supported(left) && const_fn_expr_supported(right))
        })
    };
    match dt {
        DataType::IntegerAtom { .. } => true,
        DataType::IntegerVector { dimensions, .. } => dims_ok(dimensions),
        DataType::Enum(e) => {
            dims_ok(&e.dimensions) && e.base_type.as_deref().is_none_or(const_fn_cast_type_static)
        }
        _ => false,
    }
}

thread_local! {
    /// Set while an instantiated module is elaborated. Its own typedefs are
    /// kept in a per-instance table, not in `elab.typedef_types`, so there a
    /// bare typedef name could resolve to a same-named typedef of another
    /// scope; `const_fn_cast_typedef` resolves it through
    /// `CONST_FN_LOCAL_TYPES` instead.
    pub(super) static CONST_FN_IN_INSTANCE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// The instance's own typedefs and type parameters while its body
    /// localparams are folded, so a bare cast target inside an instantiated
    /// module resolves in that instance and nowhere else.
    pub(super) static CONST_FN_LOCAL_TYPES: std::cell::RefCell<Option<HashMap<String, DataType>>> =
        const { std::cell::RefCell::new(None) };
    /// The functions the instance being elaborated declares itself. A
    /// constant function it calls but does not declare (a `$unit` one)
    /// resolves the typedefs it casts to in its own scope, not through
    /// `CONST_FN_LOCAL_TYPES`.
    pub(super) static CONST_FN_LOCAL_FUNCS: std::cell::RefCell<Option<HashSet<String>>> =
        const { std::cell::RefCell::new(None) };
    /// Set while a `$unit` constant function called from inside an instance
    /// is folded: its bare cast targets resolve in `CONST_FN_UNIT_TYPES`.
    pub(super) static CONST_FN_IN_UNIT: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// (name, span start, span end) of each `$unit` function. They are
    /// injected into every module's items, where they look like the
    /// module's own; see `set_unit_function_sites`.
    pub(super) static UNIT_FUNCTION_SITES: std::cell::RefCell<HashSet<(String, usize, usize)>> =
        std::cell::RefCell::new(HashSet::default());
    /// The `$unit` typedefs' declared types, taken once they are all
    /// registered. The shared typedef table is overwritten by an instance's
    /// same-named body typedefs, so it cannot answer for `$unit` there.
    pub(super) static CONST_FN_UNIT_TYPES: std::cell::RefCell<Option<HashMap<String, DataType>>> =
        const { std::cell::RefCell::new(None) };
    /// The package that declares the constant function being folded, if
    /// any. Its body sees that package's typedefs (and what it imports), not
    /// those of the scope that called it.
    pub(super) static CONST_FN_PACKAGE: std::cell::RefCell<Option<String>> =
        const { std::cell::RefCell::new(None) };
}

/// The package that declares `fd`, found through its qualified registration
/// (`pkg::f`), so a module function that happens to share a package
/// function's name is not attributed to the package.
fn const_fn_owner_package(
    fname: &str,
    scoped_key: Option<&str>,
    fd: &FunctionDeclaration,
    elab: &ElaboratedModule,
) -> Option<String> {
    let pkg = match scoped_key.and_then(|k| k.split_once("::")) {
        Some((pkg, _)) => pkg.to_string(),
        None => elab.pkg_subr_owner.get(fname)?.clone(),
    };
    let registered = elab.functions.get(&format!("{pkg}::{fname}"))?;
    (registered.span == fd.span).then_some(pkg)
}

/// A typedef `leaf` as seen from package `pkg`: its own declaration, else the
/// one package that declares that name (an imported typedef), else the bare
/// entry, which no package declares and so is the `$unit` one. `None` when
/// several packages declare it, rather than guess which one is imported.
fn const_fn_package_typedef<'a>(
    pkg: &str,
    leaf: &str,
    elab: &'a ElaboratedModule,
) -> Option<&'a DataType> {
    if let Some(dt) = elab.typedef_types.get(&format!("{pkg}::{leaf}")) {
        return Some(dt);
    }
    const_fn_imported_typedef(leaf, elab)
}

/// A typedef `leaf` that the current scope does not declare: the one package
/// that declares it (an imported typedef), else the bare `$unit` entry.
/// `None` when several packages declare it.
fn const_fn_imported_typedef<'a>(leaf: &str, elab: &'a ElaboratedModule) -> Option<&'a DataType> {
    let suffix = format!("::{leaf}");
    let mut found = elab
        .typedef_types
        .iter()
        .filter(|(k, _)| k.ends_with(&suffix) && k.matches("::").count() == 1);
    match found.next() {
        None => elab.typedef_types.get(leaf),
        Some((_, dt)) => found.next().is_none().then_some(dt),
    }
}

/// A bare type name inside an instantiated module: the instance's own typedef
/// or type parameter (`CONST_FN_LOCAL_TYPES`), else a package typedef it
/// imports or a `$unit` one. `None` outside the instance's body localparams,
/// where its own typedefs are not known: the cast then defers rather than pick
/// a same-named type of another scope.
fn const_fn_local_typedef(name: &str, elab: &ElaboratedModule) -> Option<DataType> {
    CONST_FN_LOCAL_TYPES.with(|c| {
        let local = c.borrow();
        let local = local.as_ref()?;
        local
            .get(name)
            .or_else(|| const_fn_imported_typedef(name, elab))
            .cloned()
    })
}

/// Record the `$unit` functions of the design being elaborated (name and
/// declaration span), so an injected copy in a module is not taken for a
/// function the module declares itself.
pub(crate) fn set_unit_function_sites(sites: HashSet<(String, usize, usize)>) {
    UNIT_FUNCTION_SITES.with(|c| *c.borrow_mut() = sites);
}

/// A bare type name inside a `$unit` constant function folded for an
/// instance: the `$unit` typedef of that name, else the one package that
/// declares it (an imported typedef).
fn const_fn_unit_typedef(name: &str, elab: &ElaboratedModule) -> Option<DataType> {
    CONST_FN_UNIT_TYPES
        .with(|c| c.borrow().as_ref()?.get(name).cloned())
        .or_else(|| const_fn_imported_typedef(name, elab).cloned())
}

/// The declared type of the typedef a cast target names (`dir_e`, `p::dir_e`,
/// or a type literal referring to one), followed through typedefs of
/// typedefs. `None` when the target is not a typedef of `elab`, e.g. a
/// parameter used as a size (`AW'(v)`). A bare name resolves in the package
/// that declares the function being folded (`CONST_FN_PACKAGE`); outside a
/// package function it is refused inside an instantiated module (see
/// `CONST_FN_IN_INSTANCE`).
fn const_fn_cast_typedef(target: &Expression, elab: &ElaboratedModule) -> Option<DataType> {
    let (leaf, scoped) = match &target.kind {
        ExprKind::Ident(h) if h.path.iter().all(|s| s.selects.is_empty()) => match h.path.len() {
            1 => (h.path[0].name.name.clone(), None),
            2 => (
                h.path[1].name.name.clone(),
                Some(format!("{}::{}", h.path[0].name.name, h.path[1].name.name)),
            ),
            _ => return None,
        },
        ExprKind::MemberAccess { expr: base, member } => match &base.kind {
            ExprKind::Ident(bh) if bh.path.len() == 1 && bh.path[0].selects.is_empty() => (
                member.name.clone(),
                Some(format!("{}::{}", bh.path[0].name.name, member.name)),
            ),
            _ => return None,
        },
        ExprKind::TypeLiteral(dt) => match dt.as_ref() {
            DataType::TypeReference {
                name, dimensions, ..
            } if dimensions.is_empty() => (
                name.name.name.clone(),
                (!name.scopes.is_empty()).then(|| name.qualified()),
            ),
            _ => return None,
        },
        _ => return None,
    };
    let pkg = CONST_FN_PACKAGE.with(|c| c.borrow().clone());
    let mut dt = match (&scoped, &pkg) {
        (Some(k), _) => elab.typedef_types.get(k)?.clone(),
        (None, Some(pkg)) => const_fn_package_typedef(pkg, &leaf, elab)?.clone(),
        (None, None) if CONST_FN_IN_UNIT.with(|c| c.get()) => const_fn_unit_typedef(&leaf, elab)?,
        (None, None) if CONST_FN_IN_INSTANCE.with(|c| c.get()) => {
            const_fn_local_typedef(&leaf, elab)?
        }
        (None, None) => elab.typedef_types.get(&leaf)?.clone(),
    };
    for _ in 0..16 {
        match &dt {
            DataType::TypeReference {
                name, dimensions, ..
            } if dimensions.is_empty() => {
                dt = match &pkg {
                    Some(pkg) if name.scopes.is_empty() => {
                        const_fn_package_typedef(pkg, &name.name.name, elab)?.clone()
                    }
                    None if name.scopes.is_empty() && CONST_FN_IN_UNIT.with(|c| c.get()) => {
                        const_fn_unit_typedef(&name.name.name, elab)?
                    }
                    None if name.scopes.is_empty() && CONST_FN_IN_INSTANCE.with(|c| c.get()) => {
                        const_fn_local_typedef(&name.name.name, elab)?
                    }
                    _ => lookup_scoped_type(name, &elab.typedef_types)?.clone(),
                };
            }
            DataType::TypeReference { .. } => return None,
            _ => return Some(dt),
        }
    }
    None
}

/// §6.24.1: inside a constant function, replace each cast to a typedef
/// (`dir_e'(d)` lowers to `$__xz_named_cast`, `T'(e)` with a type operand to
/// `$__xz_type_cast` of a type reference) with a `$__xz_type_cast` of the
/// typedef's declared type, so `const_fn_expr_supported` can judge the cast
/// from the type itself. A named positive integral value in the call's
/// parameter/local scope is a size cast instead (§6.24.1, §13.4.3).
/// Other expressions are rebuilt unchanged.
/// §26.3: is `t` a BARE const-fn param (`PW`) that the active package
/// (`CONST_FN_PACKAGE`) declares, so a size cast `PW'(e)` inside a package
/// function body should lower to `$__xz_size_cast`? `is_const_expr` only
/// consults the caller's param map, which does not re-import the package's
/// own bare name; this resolves through the qualified fallback the way
/// `eval_const_expr_val_inner` does.
fn const_fn_bare_param_is_const<P: ParamLookup>(t: &Expression, params: Option<&P>) -> bool {
    let ExprKind::Ident(h) = &t.kind else {
        return false;
    };
    if h.path.len() != 1 {
        return false;
    }
    let name = h.path[0].name.name.as_str();
    if params.is_some_and(|p| p.contains_key(name)) {
        return true;
    }
    CONST_FN_PACKAGE.with(|c| {
        let Some(pkg) = c.borrow().clone() else {
            return false;
        };
        param_fallback_get(&format!("{pkg}::{name}")).is_some()
            || param_fallback_get(&format!("{pkg}.{name}")).is_some()
    })
}

fn resolve_const_fn_cast_targets<P: ParamLookup>(
    e: &Expression,
    params: Option<&P>,
    elab: &ElaboratedModule,
) -> Expression {
    let rec = |x: &Expression| resolve_const_fn_cast_targets(x, params, elab);
    let rebuild = |k: ExprKind| Expression::new(k, e.span);
    match &e.kind {
        ExprKind::SystemCall { name, args }
            if args.len() == 2 && (name == "$__xz_named_cast" || name == "$__xz_type_cast") =>
        {
            match const_fn_cast_typedef(&args[0], elab) {
                Some(dt) => rebuild(ExprKind::SystemCall {
                    name: "$__xz_type_cast".to_string(),
                    args: vec![
                        Expression::new(ExprKind::TypeLiteral(Box::new(dt)), args[0].span),
                        rec(&args[1]),
                    ],
                }),
                // `W'(x)` is parsed as a named cast too. The instance's
                // value parameters are already in `params`; leaving this as
                // a named cast made the support check reject the whole call.
                // Only admit a known positive integral size, so an unresolved
                // type/name still takes the prior deferral path.
                None if name == "$__xz_named_cast"
                    && (is_const_expr(&args[0], params.expect("cast params"))
                        // §26.3 / §13.4.3: inside a package function body a
                        // bare size cast names the package's OWN parameter
                        // (`PW'(x)` where `widths::PW`). `is_const_expr` above
                        // only sees the caller's map, which does not re-import
                        // the bare name; resolve it through the active package
                        // like `eval_const_expr_val_inner` does, so the
                        // size-cast lowering still happens.
                        || const_fn_bare_param_is_const(&args[0], params)) &&
                {
                    let size = eval_const_expr_val_inner(
                        &args[0],
                        params.expect("cast params"),
                        &mut const_context::Types::default(),
                    );
                    !size.is_real && size.to_i64().is_some_and(|n| n > 0)
                } =>
                {
                    rebuild(ExprKind::SystemCall {
                        name: "$__xz_size_cast".to_string(),
                        args: vec![args[0].clone(), rec(&args[1])],
                    })
                }
                None => rebuild(ExprKind::SystemCall {
                    name: name.clone(),
                    args: vec![args[0].clone(), rec(&args[1])],
                }),
            }
        }
        ExprKind::SystemCall { name, args } => rebuild(ExprKind::SystemCall {
            name: name.clone(),
            args: args.iter().map(rec).collect(),
        }),
        ExprKind::Call { func, args } => rebuild(ExprKind::Call {
            func: func.clone(),
            args: args.iter().map(rec).collect(),
        }),
        ExprKind::Binary { op, left, right } => rebuild(ExprKind::Binary {
            op: *op,
            left: Box::new(rec(left)),
            right: Box::new(rec(right)),
        }),
        ExprKind::Unary { op, operand } => rebuild(ExprKind::Unary {
            op: *op,
            operand: Box::new(rec(operand)),
        }),
        ExprKind::Paren(inner) => rebuild(ExprKind::Paren(Box::new(rec(inner)))),
        ExprKind::Conditional {
            condition,
            then_expr,
            else_expr,
        } => rebuild(ExprKind::Conditional {
            condition: Box::new(rec(condition)),
            then_expr: Box::new(rec(then_expr)),
            else_expr: Box::new(rec(else_expr)),
        }),
        ExprKind::Concatenation(items) => {
            rebuild(ExprKind::Concatenation(items.iter().map(rec).collect()))
        }
        ExprKind::Replication { count, exprs } => rebuild(ExprKind::Replication {
            count: Box::new(rec(count)),
            exprs: exprs.iter().map(rec).collect(),
        }),
        _ => e.clone(),
    }
}

/// The name a constant-function call `func(...)` resolves by, and the
/// package-qualified key it prefers (`pkg::f`, see `substitute_const_fn_calls`).
pub(super) fn const_fn_call_name(func: &Expression) -> Option<(String, Option<String>)> {
    match &func.kind {
        ExprKind::Ident(h) => {
            let leaf = h.path.last().map(|s| s.name.name.clone())?;
            let sk = (h.path.len() >= 2)
                .then(|| format!("{}::{}", h.path[h.path.len() - 2].name.name, leaf));
            Some((leaf, sk))
        }
        ExprKind::MemberAccess { expr: base, member } => {
            let sk = match &base.kind {
                ExprKind::Ident(bh) if bh.path.len() == 1 => {
                    Some(format!("{}::{}", bh.path[0].name.name, member.name))
                }
                _ => None,
            };
            Some((member.name.clone(), sk))
        }
        _ => None,
    }
}

/// §13.4.3, §8.10, §13.8: a call of a static function of a class, possibly a
/// specialization (`C#(PW)::id()`, `C::f(3)`), in a constant expression. The
/// function is a parameterized function of §13.8: its body is evaluated as a
/// constant function with the constants of the class (its parameters bound
/// from the `#(...)` arguments, read in the calling scope) in view. None
/// when `func` names no static function of a class, or it cannot be folded.
fn const_class_static_call<P: ParamLookup>(
    func: &Expression,
    args: &[Expression],
    params: Option<&P>,
    elab: &ElaboratedModule,
    depth: u32,
) -> Option<Value> {
    let (base, method): (&Expression, &str) = match &func.kind {
        ExprKind::MemberAccess { expr, member } => (expr, member.name.as_str()),
        _ => return None,
    };
    let (scope, spec_args) = match &base.kind {
        ExprKind::Specialization {
            base: inner,
            type_args_text,
        } => (&**inner, parse_spec_args(type_args_text)),
        _ => (base, Vec::new()),
    };
    let cls_name = match &scope.kind {
        ExprKind::Ident(h) if h.path.iter().all(|s| s.selects.is_empty()) => {
            h.path.last()?.name.name.as_str()
        }
        ExprKind::MemberAccess { member, .. } => member.name.as_str(),
        _ => return None,
    };
    let cls = elab.classes.get(cls_name)?;
    let m = cls.methods.get(method)?;
    let crate::ast::decl::ClassMethodKind::Function(fd) = &m.kind else {
        return None;
    };
    if !m
        .qualifiers
        .iter()
        .any(|q| matches!(q, crate::ast::decl::ClassQualifier::Static))
    {
        return None;
    }
    let mut env = params.map(|p| p.to_hashmap().into_owned()).unwrap_or_default();
    let mut consts = Vec::new();
    if class_spec_consts(cls_name, &spec_args, &env, 0, &mut consts).is_some() {
        env.extend(consts);
    } else if !spec_args.is_empty() {
        return None;
    }
    let mut argv = Vec::with_capacity(args.len());
    for a in args {
        let a = resolve_const_fn_cast_targets(a, params, elab);
        if !const_fn_expr_supported(&a) {
            return None;
        }
        let sa = substitute_const_fn_calls(&a, params, elab, depth)?;
        if expr_has_call(&sa) {
            return None;
        }
        argv.push(const_function_actual(
            fd.ports.get(argv.len()),
            &sa,
            params,
            elab,
        ));
    }
    eval_const_user_function(fd, &argv, Some(&env), elab, depth + 1)
}

/// Rewrite `expr`, replacing each call to a KNOWN simple user function with the
/// literal it evaluates to (arguments const-evaluated against `params`).
/// Returns None when a call can't be resolved — callers then fall back to
/// the old deferral behavior.
pub(super) fn substitute_const_fn_calls<P: ParamLookup>(
    expr: &Expression,
    params: Option<&P>,
    elab: &ElaboratedModule,
    depth: u32,
) -> Option<Expression> {
    if depth > 64 {
        return None;
    }
    let rebuild = |k: ExprKind| Expression::new(k, expr.span);
    let sub = |e: &Expression| substitute_const_fn_calls(e, params, elab, depth);
    Some(match &expr.kind {
        ExprKind::Call { func, args } => {
            // §26.3: a scoped call `pkg::f(...)` reaches this pass as
            // MemberAccess{Ident(pkg), f} in inlined-submodule items (the
            // top-module path sees a flat 2-segment Ident) — both forms
            // resolve, preferring the package-qualified registration.
            if let Some(v) = const_class_static_call(func, args, params, elab, depth) {
                return const_value_literal(&v, expr.span);
            }
            let (fname, scoped_key) = match &func.kind {
                ExprKind::Ident(_) | ExprKind::MemberAccess { .. } => const_fn_call_name(func)?,
                other => {
                    param_trace(
                        "const-fn:unsupported-func-shape",
                        "call",
                        &format!("{:?}", std::mem::discriminant(other)),
                    );
                    return None;
                }
            };
            let (resolved_key, fd_ref) = match scoped_key
                .as_deref()
                .and_then(|k| elab.functions.get_key_value(k))
                .or_else(|| elab.functions.get_key_value(&fname))
            {
                Some((k, fd)) => (k.as_str(), fd),
                None => {
                    param_trace("const-fn:MISS", &fname, "no function registration");
                    return None;
                }
            };
            let mut owned_fd;
            let fd = if let Some(items) = crate::ast::cache::without_scope_caches(|| {
                elab.materialize_function_body(resolved_key, fd_ref)
            }) {
                owned_fd = fd_ref.clone();
                owned_fd.items = items;
                &owned_fd
            } else {
                fd_ref
            };
            let mut argv = Vec::with_capacity(args.len());
            for a in args {
                // §6.24.1: a typedef cast in an actual (`num_operands(opgroup_e'(i))`,
                // including a generate-for genvar) is lowered to `$__xz_named_cast`.
                // The support check rejects that intrinsic, so the whole call
                // bailed and the localparam stayed 0 — fpnew's per-opgroup
                // operand count, and every width derived from it. Resolve the
                // cast to its declared type first, the same way the function
                // body does, and then judge the converted expression.
                let a = resolve_const_fn_cast_targets(a, params, elab);
                // §10.9.2, §13.5: a pattern actual of a packed-struct formal
                // is packed by the formal's members, by name or position
                // (#680); the support check below admits no pattern.
                if let Some(v) =
                    const_fn_struct_pattern_actual(fd.ports.get(argv.len()), &a, params, elab)
                {
                    argv.push(v);
                    continue;
                }
                if !const_fn_expr_supported(&a) {
                    return None;
                }
                let sa = sub(&a)?;
                if expr_has_call(&sa) {
                    return None;
                }
                argv.push(const_function_actual(
                    fd.ports.get(argv.len()),
                    &sa,
                    params,
                    elab,
                ));
            }
            let owner = const_fn_owner_package(&fname, scoped_key.as_deref(), &fd, elab);
            // §13.4.3/§6.24.1: a function the instance calls but does not
            // declare (a `$unit` one) casts to the typedefs of ITS scope.
            // Folded as the instance's own, `w_t'(x)` took the instance's
            // `w_t` when the body declared one of that name.
            let foreign = owner.is_none()
                && scoped_key.is_none()
                && CONST_FN_LOCAL_FUNCS
                    .with(|c| c.borrow().as_ref().is_some_and(|own| !own.contains(&fname)));
            let prev_in_unit = CONST_FN_IN_UNIT.with(|c| c.replace(foreign));
            let prev_owner = CONST_FN_PACKAGE.with(|c| c.replace(owner));
    let v = eval_const_user_function(&fd, &argv, params, elab, depth);
            CONST_FN_PACKAGE.with(|c| *c.borrow_mut() = prev_owner);
            CONST_FN_IN_UNIT.with(|c| c.set(prev_in_unit));
            let v = v?;
            // §13.4.1: preserve the declared return width and signedness,
            // including wide and four-state results used by another call.
            const_value_literal(&v, expr.span)?
        }
        ExprKind::Binary { op, left, right } => rebuild(ExprKind::Binary {
            op: *op,
            left: Box::new(sub(left)?),
            right: Box::new(sub(right)?),
        }),
        ExprKind::Unary { op, operand } => rebuild(ExprKind::Unary {
            op: *op,
            operand: Box::new(sub(operand)?),
        }),
        ExprKind::Paren(inner) => rebuild(ExprKind::Paren(Box::new(sub(inner)?))),
        ExprKind::Conditional {
            condition,
            then_expr,
            else_expr,
        } => rebuild(ExprKind::Conditional {
            condition: Box::new(sub(condition)?),
            then_expr: Box::new(sub(then_expr)?),
            else_expr: Box::new(sub(else_expr)?),
        }),
        ExprKind::Concatenation(items) => rebuild(ExprKind::Concatenation(
            items.iter().map(&sub).collect::<Option<Vec<_>>>()?,
        )),
        ExprKind::Replication { count, exprs } => rebuild(ExprKind::Replication {
            count: Box::new(sub(count)?),
            exprs: exprs.iter().map(&sub).collect::<Option<Vec<_>>>()?,
        }),
        ExprKind::SystemCall { name, args } => rebuild(ExprKind::SystemCall {
            name: name.clone(),
            args: args.iter().map(sub).collect::<Option<Vec<_>>>()?,
        }),
        // Leaves (idents, numbers, strings, …): unchanged.
        _ => expr.clone(),
    })
}

/// A signed decimal literal expression for elaboration-substituted values.
pub(super) fn make_i64_literal(v: i64, span: crate::ast::Span) -> Expression {
    let (txt, neg) = if v < 0 {
        ((-v).to_string(), true)
    } else {
        (v.to_string(), false)
    };
    let num = Expression::new(
        ExprKind::Number(crate::ast::expr::NumberLiteral::Integer {
            size: None,
            signed: true,
            base: crate::ast::expr::NumberBase::Decimal,
            value: txt,
            cached_val: crate::ast::cache::LiteralCache::new(None),
        }),
        span,
    );
    if neg {
        Expression::new(
            ExprKind::Unary {
                op: crate::ast::expr::UnaryOp::Minus,
                operand: Box::new(num),
            },
            span,
        )
    } else {
        num
    }
}
