use super::*;

/// §8.3/§8.23: the typedefs of nested classes that `pkg_scope` gave their
/// class-qualified spelling (`Outer::Inner::t`, a name declared elsewhere
/// too) are registered under that unique spelling, which is how every
/// reference to them is now written.
pub(super) fn register_nested_qualified_typedefs(
    c: &ClassDeclaration,
    elab: &mut ElaboratedModule,
) {
    for item in &c.items {
        if let ClassItem::Class(nc) = item {
            for it in &nc.items {
                if let ClassItem::Typedef(td) = it
                    && td.name.name.contains("::")
                    && !elab.typedefs.contains_key(&td.name.name)
                {
                    process_typedef(td, elab);
                }
            }
            register_nested_qualified_typedefs(nc, elab);
        }
    }
}

/// §8.23: register a class's typedefs under their CLASS-QUALIFIED keys so
/// a chained scope reference in a type position — `pkg::Cls::td`,
/// `Cls::td` (imported), and nested `pkg::Cls::Sub::td` — resolves.
/// `register_class_enum_members` registers only the BARE name, so a
/// class-scope reference had no key to hit and fell back to 32 bits (or
/// failed to resolve at all). `pkg` is the enclosing package's name when
/// the class lives in one; both the package-qualified and the imported
/// (class-chain-only) spellings are registered. Widths are sized against
/// the class's own value-parameter scope (the DEFAULT specialization);
/// a `Cls#(args)::td` reference is resolved at its use site by
/// `specialized_class_scope_width`.
pub fn register_class_scoped_typedef_aliases(
    c: &ClassDeclaration,
    pkg: Option<&str>,
    elab: &mut ElaboratedModule,
) {
    let mut prefixes: Vec<String> = Vec::new();
    if let Some(p) = pkg {
        prefixes.push(format!("{}::{}", p, c.name.name));
    }
    prefixes.push(c.name.name.clone());
    register_class_consts(c, &prefixes, elab);
    if c.items.iter().any(|i| {
        matches!(
            i,
            ClassItem::Typedef(_) | ClassItem::Nettype(_) | ClassItem::Class(_)
        )
    }) {
        let params = class_const_scope(c, Some(&elab.parameters));
        walk_class_typedefs(c, &prefixes, &params, elab);
    }
    type_trace_tls_refresh("class_scope_alias", &elab.typedefs);
    sync_typedefs_tls(&elab.typedefs);
}

/// Recursive worker for [`register_class_scoped_typedef_aliases`]: a
/// class's own typedefs under every prefix, then its NESTED classes under
/// the extended chain (§8.23 `pkg::Outer::Inner::td`).
fn walk_class_typedefs(
    c: &ClassDeclaration,
    prefixes: &[String],
    params: &HashMap<String, Value>,
    elab: &mut ElaboratedModule,
) {
    let mut local_td: HashMap<String, u32> = HashMap::default();
    for p in &c.params {
        if let crate::ast::decl::ParameterKind::Type { assignments } = &p.kind {
            for a in assignments {
                if let Some(dt) = &a.init {
                    let w = resolve_type_width(dt, Some(params), Some(&elab.typedefs));
                    local_td.insert(a.name.name.clone(), w);
                }
            }
        }
    }
    for item in &c.items {
        match item {
            ClassItem::Typedef(td) => {
                // A class with value parameters re-sizes per specialization;
                // fold only its design-wide scoped constants.
                let fold_class = !class_has_value_params(c);
                let sized =
                    size_struct_member_dims(&td.data_type, params, &elab.typedef_types, fold_class);
                let sized = fold_packed_dims_with(
                    sized.as_ref().unwrap_or(&td.data_type),
                    params,
                    &|l, r| !range_refs_class_header_param(c, l, r),
                )
                .or(sized);
                let dt = sized.as_ref().unwrap_or(&td.data_type);
                let w = if local_td.is_empty() {
                    resolve_type_width(dt, Some(params), Some(&elab.typedefs))
                } else {
                    let mut merged_td: HashMap<String, u32> =
                        elab.typedefs.iter().map(|(k, &v)| (k.clone(), v)).collect();
                    merged_td.extend(local_td.iter().map(|(k, &v)| (k.clone(), v)));
                    let w = resolve_type_width(dt, Some(params), Some(&merged_td));
                    local_td.insert(td.name.name.clone(), w);
                    w
                };
                for pfx in prefixes {
                    let key = format!("{}::{}", pfx, td.name.name);
                    typedefs_insert_traced(
                        &mut elab.typedefs,
                        "insert:class_scope_alias",
                        key.clone(),
                        w,
                    );
                    elab.typedef_types.insert(key.clone(), dt.clone());
                    if !td.dimensions.is_empty() {
                        elab.typedef_unpacked_dims
                            .insert(key.clone(), td.dimensions.clone());
                    }
                }
                if let DataType::Enum(et) = dt {
                    let enum_signed = is_type_signed_resolved(dt, &elab.typedef_types);
                    let base_width = et
                        .base_type
                        .as_ref()
                        .map(|bt| resolve_type_width(bt, Some(params), Some(&elab.typedefs)))
                        .unwrap_or(32);
                    let resolved = enums::enum_members_values(et, base_width, enum_signed, params);
                    let ordered: Vec<(String, u64)> = resolved
                        .iter()
                        .map(|(nm, val, _)| (nm.clone(), *val))
                        .collect();
                    for pfx in prefixes {
                        elab.enum_members
                            .insert(format!("{}::{}", pfx, td.name.name), ordered.clone());
                        for (nm, _, v) in &resolved {
                            elab.set_param(line!(), format!("{}::{}", pfx, nm), v.clone());
                        }
                    }
                }
            }
            ClassItem::Nettype(nd) => {
                let mut merged_td: HashMap<String, u32> =
                    elab.typedefs.iter().map(|(k, &v)| (k.clone(), v)).collect();
                merged_td.extend(local_td.iter().map(|(k, &v)| (k.clone(), v)));
                let w = resolve_type_width(&nd.data_type, Some(params), Some(&merged_td));
                local_td.insert(nd.name.name.clone(), w);
                let mut resolved_dt = nd.data_type.clone();
                if let DataType::TypeReference { name, .. } = &nd.data_type
                    && name.scopes.is_empty()
                {
                    for pfx in prefixes {
                        if let Some(target_dt) =
                            elab.typedef_types.get(&format!("{}::{}", pfx, name.name.name))
                        {
                            resolved_dt = target_dt.clone();
                            break;
                        }
                    }
                }
                if nd.name.name.contains("::") {
                    typedefs_insert_traced(
                        &mut elab.typedefs,
                        "insert:class_scope_alias",
                        nd.name.name.clone(),
                        w,
                    );
                    elab.typedef_types
                        .insert(nd.name.name.clone(), resolved_dt.clone());
                } else {
                    for pfx in prefixes {
                        let key = format!("{}::{}", pfx, nd.name.name);
                        typedefs_insert_traced(
                            &mut elab.typedefs,
                            "insert:class_scope_alias",
                            key.clone(),
                            w,
                        );
                        elab.typedef_types.insert(key, resolved_dt.clone());
                    }
                }
            }
            ClassItem::Class(sub) => {
                let nested: Vec<String> = prefixes
                    .iter()
                    .map(|p| format!("{}::{}", p, sub.name.name))
                    .collect();
                let mut sub_params = params.clone();
                for p in &sub.params {
                    if let crate::ast::decl::ParameterKind::Data { assignments, .. } = &p.kind {
                        for a in assignments {
                            if let Some(init) = &a.init {
                                let v = eval_const_expr_val(init, &sub_params);
                                sub_params.insert(a.name.name.clone(), v);
                            }
                        }
                    }
                }
                walk_class_typedefs(sub, &nested, &sub_params, elab);
            }
            _ => {}
        }
    }
}

/// §8.25.1: the width of a `Cls#(args)::td` (or `pkg::Cls#(args)::td`)
/// reference — a PARAMETERIZED class used as a scope prefix. The
/// string-keyed tables hold only the DEFAULT specialization, so the class
/// is walked from `elab.classes`, the `#(...)` args are bound to its
/// `param_order`, and the typedef's target is sized under those bindings
/// (`VecGen#(6)::vec_t` with `typedef logic [W-1:0] vec_t` → 6).
/// The prefix may also be a typedef of a specialization (`typedef
/// VecGen#(6) g_t;` ... `g_t::vec_t`, §6.18): it is followed to the
/// specialization it names.
/// Resolved specialized class typedef / parameterized member type.
#[derive(Debug, Clone)]
pub struct ResolvedClassTypedef {
    pub data_type: DataType,
    pub width: u32,
    pub elem_width: Option<u32>,
    pub unpacked_dims: Vec<UnpackedDimension>,
    pub signed: bool,
}

pub(crate) fn builtin_keyword_to_data_type(name: &str, span: Span) -> Option<DataType> {
    use crate::ast::types::{IntegerAtomType, IntegerVectorType, RealType, SimpleType};
    match name {
        "bit" => Some(DataType::IntegerVector {
            kind: IntegerVectorType::Bit,
            signing: None,
            dimensions: Vec::new(),
            span,
        }),
        "logic" => Some(DataType::IntegerVector {
            kind: IntegerVectorType::Logic,
            signing: None,
            dimensions: Vec::new(),
            span,
        }),
        "reg" => Some(DataType::IntegerVector {
            kind: IntegerVectorType::Reg,
            signing: None,
            dimensions: Vec::new(),
            span,
        }),
        "byte" => Some(DataType::IntegerAtom {
            kind: IntegerAtomType::Byte,
            signing: None,
            span,
        }),
        "shortint" => Some(DataType::IntegerAtom {
            kind: IntegerAtomType::ShortInt,
            signing: None,
            span,
        }),
        "int" => Some(DataType::IntegerAtom {
            kind: IntegerAtomType::Int,
            signing: None,
            span,
        }),
        "longint" => Some(DataType::IntegerAtom {
            kind: IntegerAtomType::LongInt,
            signing: None,
            span,
        }),
        "integer" => Some(DataType::IntegerAtom {
            kind: IntegerAtomType::Integer,
            signing: None,
            span,
        }),
        "time" => Some(DataType::IntegerAtom {
            kind: IntegerAtomType::Time,
            signing: None,
            span,
        }),
        "real" => Some(DataType::Real {
            kind: RealType::Real,
            span,
        }),
        "shortreal" => Some(DataType::Real {
            kind: RealType::ShortReal,
            span,
        }),
        "realtime" => Some(DataType::Real {
            kind: RealType::RealTime,
            span,
        }),
        "string" => Some(DataType::Simple {
            kind: SimpleType::String,
            span,
        }),
        "chandle" => Some(DataType::Simple {
            kind: SimpleType::Chandle,
            span,
        }),
        "void" => Some(DataType::Void(span)),
        _ => None,
    }
}

pub fn apply_outer_packed_dims_dt(
    base: DataType,
    outer: &[PackedDimension],
    params: &HashMap<String, Value>,
) -> DataType {
    use crate::ast::types::{IntegerAtomType, IntegerVectorType, Signing};
    if outer.is_empty() {
        return base;
    }
    let lit = |n: i64, span: Span| Box::new(int_literal(n, span));
    let folded_outer: Vec<PackedDimension> = outer
        .iter()
        .map(|d| {
            if let PackedDimension::Range { left, right, span } = d
                && let (Some(l), Some(r)) = (
                    const_eval_i64_with_params(left, Some(params)),
                    const_eval_i64_with_params(right, Some(params)),
                )
            {
                PackedDimension::Range {
                    left: lit(l, left.span),
                    right: lit(r, right.span),
                    span: *span,
                }
            } else {
                d.clone()
            }
        })
        .collect();

    match base {
        DataType::IntegerVector {
            kind,
            signing,
            mut dimensions,
            span,
        } => {
            let mut merged = folded_outer;
            merged.append(&mut dimensions);
            DataType::IntegerVector {
                kind,
                signing,
                dimensions: merged,
                span,
            }
        }
        DataType::Implicit {
            signing,
            mut dimensions,
            span,
        } => {
            let mut merged = folded_outer;
            merged.append(&mut dimensions);
            DataType::Implicit {
                signing,
                dimensions: merged,
                span,
            }
        }
        DataType::IntegerAtom {
            kind,
            signing,
            span,
        } => {
            let (vec_kind, def_signed, atom_w) = match kind {
                IntegerAtomType::Byte => (IntegerVectorType::Bit, true, 8i64),
                IntegerAtomType::ShortInt => (IntegerVectorType::Bit, true, 16),
                IntegerAtomType::Int => (IntegerVectorType::Bit, true, 32),
                IntegerAtomType::LongInt => (IntegerVectorType::Bit, true, 64),
                IntegerAtomType::Integer => (IntegerVectorType::Logic, true, 32),
                IntegerAtomType::Time => (IntegerVectorType::Logic, false, 64),
            };
            let eff_signing = signing.or(Some(if def_signed {
                Signing::Signed
            } else {
                Signing::Unsigned
            }));
            let mut merged = folded_outer;
            merged.push(PackedDimension::Range {
                left: lit(atom_w - 1, span),
                right: lit(0, span),
                span,
            });
            DataType::IntegerVector {
                kind: vec_kind,
                signing: eff_signing,
                dimensions: merged,
                span,
            }
        }
        DataType::Struct(mut su) => {
            let mut merged = folded_outer;
            merged.append(&mut su.dimensions);
            su.dimensions = merged;
            DataType::Struct(su)
        }
        DataType::Enum(mut et) => {
            let mut merged = folded_outer;
            merged.append(&mut et.dimensions);
            et.dimensions = merged;
            DataType::Enum(et)
        }
        DataType::TypeReference {
            name,
            mut dimensions,
            type_args,
            span,
        } => {
            let mut merged = folded_outer;
            merged.append(&mut dimensions);
            DataType::TypeReference {
                name,
                dimensions: merged,
                type_args,
                span,
            }
        }
        other => other,
    }
}

fn find_class_entry<'a>(
    scopes: &[crate::ast::types::TypeScope],
    idx: usize,
    elab: &'a ElaboratedModule,
) -> Option<(String, &'a ElaboratedClass)> {
    if idx > 0 {
        let full = scopes[..=idx]
            .iter()
            .map(|s| s.name.name.as_str())
            .collect::<Vec<_>>()
            .join("::");
        if let Some(c) = elab.classes.get(&full) {
            return Some((full, c.as_ref()));
        }
        let two = format!("{}::{}", scopes[idx - 1].name.name, scopes[idx].name.name);
        if let Some(c) = elab.classes.get(&two) {
            return Some((two, c.as_ref()));
        }
    }
    let bare = &scopes[idx].name.name;
    elab.classes.get(bare).map(|c| (bare.clone(), c.as_ref()))
}

fn find_class_key_for_typename(
    tn: &crate::ast::types::TypeName,
    elab: &ElaboratedModule,
) -> Option<String> {
    if !tn.scopes.is_empty() {
        let mut cands = Vec::new();
        let full = tn
            .scopes
            .iter()
            .map(|s| s.name.name.as_str())
            .chain(std::iter::once(tn.name.name.as_str()))
            .collect::<Vec<_>>()
            .join("::");
        cands.push(full);
        if let Some(last) = tn.scopes.last() {
            cands.push(format!("{}::{}", last.name.name, tn.name.name));
        }
        for k in cands {
            if elab.classes.contains_key(&k) {
                return Some(k);
            }
        }
    }
    elab.classes
        .contains_key(&tn.name.name)
        .then(|| tn.name.name.clone())
}

fn resolve_type_arg_expr_at(
    arg: &Expression,
    caller_params: &HashMap<String, Value>,
    elab: &ElaboratedModule,
    depth: u32,
) -> Option<(DataType, Vec<UnpackedDimension>)> {
    let inner = match &arg.kind {
        ExprKind::NamedArg { expr: Some(e), .. } => e.as_ref(),
        ExprKind::NamedArg { expr: None, .. } => return None,
        _ => arg,
    };
    match &inner.kind {
        ExprKind::TypeLiteral(dt) => {
            if let Some(res) =
                resolve_specialized_class_dt_depth(dt.as_ref(), caller_params, elab, depth + 1)
            {
                return Some((res.data_type, res.unpacked_dims));
            }
            if let DataType::TypeReference {
                name,
                dimensions,
                type_args,
                ..
            } = dt.as_ref()
                && name.scopes.is_empty()
                && type_args.is_empty()
                && let Some(base) = elab.typedef_types.get(&name.name.name)
                && !elab.classes.contains_key(&name.name.name)
            {
                let merged = apply_outer_packed_dims_dt(base.clone(), dimensions, caller_params);
                let folded =
                    fold_packed_dims_with(&merged, caller_params, &|_, _| true).unwrap_or(merged);
                let udims = elab
                    .typedef_unpacked_dims
                    .get(&name.name.name)
                    .cloned()
                    .unwrap_or_default();
                return Some((folded, udims));
            }
            let folded = fold_packed_dims_with(dt.as_ref(), caller_params, &|_, _| true)
                .unwrap_or_else(|| (**dt).clone());
            Some((folded, Vec::new()))
        }
        ExprKind::Ident(h) => {
            if h.path.len() == 1 && h.path[0].selects.is_empty() {
                let n = h.path[0].name.name.as_str();
                if let Some(dt) = builtin_keyword_to_data_type(n, inner.span) {
                    return Some((dt, Vec::new()));
                }
                if let Some(dt) = elab.typedef_types.get(n)
                    && !elab.classes.contains_key(n)
                {
                    let udims = elab
                        .typedef_unpacked_dims
                        .get(n)
                        .cloned()
                        .unwrap_or_default();
                    return Some((dt.clone(), udims));
                }
            }
            let mut scopes = Vec::new();
            for link in &h.path[..h.path.len().saturating_sub(1)] {
                scopes.push(crate::ast::types::TypeScope {
                    name: link.name.clone(),
                    type_args: Vec::new(),
                });
            }
            let last = h.path.last()?;
            let tn = crate::ast::types::TypeName {
                scopes,
                name: last.name.clone(),
                bound: Default::default(),
                span: last.name.span,
            };
            if let Some(res) = specialized_class_scope_resolve_at(&tn, &[], caller_params, elab, depth + 1)
            {
                return Some((res.data_type, res.unpacked_dims));
            }
            Some((
                DataType::TypeReference {
                    name: Box::new(tn),
                    dimensions: Vec::new(),
                    type_args: Vec::new(),
                    span: inner.span,
                },
                Vec::new(),
            ))
        }
        _ => None,
    }
}

fn eval_text_arg_as_dt(
    txt: &str,
    type_binds: &HashMap<String, DataType>,
    type_udims: &HashMap<String, Vec<UnpackedDimension>>,
    elab: &ElaboratedModule,
    span: Span,
) -> Option<(DataType, Vec<UnpackedDimension>)> {
    let trimmed = txt.trim();
    if let Some(dt) = type_binds.get(trimmed) {
        return Some((
            dt.clone(),
            type_udims.get(trimmed).cloned().unwrap_or_default(),
        ));
    }
    if let Some(dt) = builtin_keyword_to_data_type(trimmed, span) {
        return Some((dt, Vec::new()));
    }
    if let Some(dt) = elab.typedef_types.get(trimmed) {
        return Some((
            dt.clone(),
            elab.typedef_unpacked_dims
                .get(trimmed)
                .cloned()
                .unwrap_or_default(),
        ));
    }
    None
}

fn eval_text_arg_as_val(
    txt: &str,
    val_params: &HashMap<String, Value>,
    caller_params: &HashMap<String, Value>,
) -> Option<Value> {
    let trimmed = txt.trim();
    if let Some(v) = val_params.get(trimmed) {
        return Some(v.clone());
    }
    if let Ok(n) = trimmed.parse::<i64>() {
        let mut v = Value::from_u64(n as u64, 32);
        v.is_signed = true;
        return Some(v);
    }
    let expr = crate::parse_override_value(trimmed)?;
    let env = ParamEnv::Overlay {
        base: caller_params,
        top: val_params,
    };
    Some(eval_const_expr_val_env(&expr, &env))
}

fn subst_class_dt(
    dt: &DataType,
    cur_cls: &ElaboratedClass,
    val_params: &HashMap<String, Value>,
    type_binds: &HashMap<String, DataType>,
    type_udims: &HashMap<String, Vec<UnpackedDimension>>,
    caller_params: &HashMap<String, Value>,
    elab: &ElaboratedModule,
    visiting: &mut HashSet<String>,
    depth: u32,
) -> (DataType, Vec<UnpackedDimension>) {
    if depth >= 16 {
        return (dt.clone(), Vec::new());
    }
    match dt {
        DataType::TypeReference {
            name,
            type_args,
            ..
        } if name.has_scope()
            || (!type_args.is_empty() && elab.classes.contains_key(&name.name.name))
            || typedef_specialization(&name.name.name, elab).is_some() =>
        {
            let mut merged_params = caller_params.clone();
            for (k, v) in val_params {
                merged_params.insert(k.clone(), v.clone());
            }
            let rewritten_dt = subst_type_args_in_tr(dt, type_binds, &merged_params, elab);
            if let DataType::TypeReference {
                name: rname,
                dimensions: router,
                ..
            } = &rewritten_dt
                && let Some(res) = specialized_class_scope_resolve_at(
                    rname,
                    router,
                    &merged_params,
                    elab,
                    depth + 1,
                )
            {
                return (res.data_type, res.unpacked_dims);
            }
            let folded = fold_packed_dims_with(&rewritten_dt, val_params, &|_, _| true)
                .unwrap_or(rewritten_dt);
            (folded, Vec::new())
        }
        DataType::TypeReference {
            name,
            dimensions: outer_packed,
            type_args,
            ..
        } if name.scopes.is_empty() && type_args.is_empty() => {
            let sym = &name.name.name;
            if let Some(bound) = type_binds.get(sym) {
                let expanded = apply_outer_packed_dims_dt(bound.clone(), outer_packed, val_params);
                let folded = fold_packed_dims_with(&expanded, val_params, &|_, _| true)
                    .unwrap_or(expanded);
                let udims = type_udims.get(sym).cloned().unwrap_or_default();
                return (folded, udims);
            }
            if !visiting.contains(sym)
                && let Some(sib) = resolve_member_in_class_or_base(
                    cur_cls,
                    sym,
                    outer_packed,
                    val_params,
                    type_binds,
                    type_udims,
                    caller_params,
                    elab,
                    visiting,
                    depth + 1,
                )
            {
                return (sib.data_type, sib.unpacked_dims);
            }
            if !outer_packed.is_empty()
                && let Some(base) = elab.typedef_types.get(sym)
                && !elab.classes.contains_key(sym)
                && !matches!(base, DataType::Enum(_))
            {
                let expanded = apply_outer_packed_dims_dt(base.clone(), outer_packed, val_params);
                let folded = fold_packed_dims_with(&expanded, val_params, &|_, _| true)
                    .unwrap_or(expanded);
                let udims = elab
                    .typedef_unpacked_dims
                    .get(sym)
                    .cloned()
                    .unwrap_or_default();
                return (folded, udims);
            }
            let folded = fold_packed_dims_with(dt, val_params, &|_, _| true)
                .unwrap_or_else(|| dt.clone());
            (folded, Vec::new())
        }
        DataType::Struct(su) => {
            let mut s = su.clone();
            for m in &mut s.members {
                let (mdt, mudims) = subst_class_dt(
                    &m.data_type,
                    cur_cls,
                    val_params,
                    type_binds,
                    type_udims,
                    caller_params,
                    elab,
                    visiting,
                    depth + 1,
                );
                m.data_type = mdt;
                for decl in &mut m.declarators {
                    let mut d = fold_unpacked_dims(&decl.dimensions, val_params, &elab.typedef_types);
                    d.extend(mudims.clone());
                    decl.dimensions = d;
                }
            }
            let wrapped = DataType::Struct(s);
            let sized =
                size_struct_member_dims(&wrapped, val_params, &elab.typedef_types, true)
                    .unwrap_or(wrapped);
            let folded = fold_packed_dims_with(&sized, val_params, &|_, _| true).unwrap_or(sized);
            (folded, Vec::new())
        }
        DataType::Enum(et) => {
            let mut e = et.clone();
            if let Some(bt) = &e.base_type {
                let (bdt, _) = subst_class_dt(
                    bt,
                    cur_cls,
                    val_params,
                    type_binds,
                    type_udims,
                    caller_params,
                    elab,
                    visiting,
                    depth + 1,
                );
                e.base_type = Some(Box::new(bdt));
            }
            let wrapped = DataType::Enum(e);
            let folded =
                fold_packed_dims_with(&wrapped, val_params, &|_, _| true).unwrap_or(wrapped);
            (folded, Vec::new())
        }
        _ => {
            let folded =
                fold_packed_dims_with(dt, val_params, &|_, _| true).unwrap_or_else(|| dt.clone());
            (folded, Vec::new())
        }
    }
}

fn subst_type_args_in_tr(
    dt: &DataType,
    type_binds: &HashMap<String, DataType>,
    val_params: &HashMap<String, Value>,
    elab: &ElaboratedModule,
) -> DataType {
    let DataType::TypeReference {
        name,
        dimensions,
        type_args,
        span,
    } = dt
    else {
        return dt.clone();
    };
    let lit = |n: i64, sp: Span| int_literal(n, sp);
    let rewrite_args = |args: &[Expression]| -> Vec<Expression> {
        args.iter()
            .map(|a| match &a.kind {
                ExprKind::Ident(h) if h.path.len() == 1 && h.path[0].selects.is_empty() => {
                    let s = &h.path[0].name.name;
                    if let Some(bound_dt) = type_binds.get(s) {
                        Expression::new(ExprKind::TypeLiteral(Box::new(bound_dt.clone())), a.span)
                    } else if val_params.contains_key(s) {
                        let v = eval_const_expr_val(a, val_params);
                        if !v.has_xz() && !v.is_real && let Some(n) = v.to_i64() {
                            return lit(n, a.span);
                        }
                        a.clone()
                    } else {
                        a.clone()
                    }
                }
                ExprKind::TypeLiteral(inner_dt) => {
                    if let DataType::TypeReference {
                        name: tn,
                        dimensions: dims,
                        type_args: ta,
                        ..
                    } = inner_dt.as_ref()
                        && tn.scopes.is_empty()
                        && ta.is_empty()
                        && let Some(bound_dt) = type_binds.get(&tn.name.name)
                    {
                        let merged =
                            apply_outer_packed_dims_dt(bound_dt.clone(), dims, val_params);
                        Expression::new(ExprKind::TypeLiteral(Box::new(merged)), a.span)
                    } else {
                        let _ = elab;
                        a.clone()
                    }
                }
                _ => {
                    if const_eval_i64_with_params(a, None).is_none()
                        && let Some(n) = const_eval_i64_with_params(a, Some(val_params))
                    {
                        lit(n, a.span)
                    } else {
                        a.clone()
                    }
                }
            })
            .collect()
    };
    let mut new_name = name.clone();
    for s in &mut new_name.scopes {
        if !s.type_args.is_empty() {
            s.type_args = rewrite_args(&s.type_args);
        }
    }
    DataType::TypeReference {
        name: new_name,
        dimensions: dimensions.clone(),
        type_args: rewrite_args(type_args),
        span: *span,
    }
}

fn fill_class_type_param_defaults(
    cls: &ElaboratedClass,
    type_binds: &mut HashMap<String, DataType>,
    val_params: &HashMap<String, Value>,
    elab: &ElaboratedModule,
) {
    for (tpn, default_dt) in &cls.type_param_default_types {
        if !type_binds.contains_key(tpn) {
            let mut substituted = match default_dt {
                DataType::TypeReference {
                    name,
                    dimensions,
                    type_args,
                    ..
                } if name.scopes.is_empty() && type_args.is_empty() => {
                    if let Some(prev) = type_binds.get(&name.name.name) {
                        apply_outer_packed_dims_dt(prev.clone(), dimensions, val_params)
                    } else {
                        default_dt.clone()
                    }
                }
                other => other.clone(),
            };
            if let Some(folded) = fold_packed_dims_with(&substituted, val_params, &|_, _| true) {
                substituted = folded;
            }
            type_binds.insert(tpn.clone(), substituted);
        }
    }
    let _ = elab;
}

fn resolve_member_in_class_or_base(
    start_cls: &ElaboratedClass,
    leaf: &str,
    outer_packed: &[PackedDimension],
    val_params: &HashMap<String, Value>,
    type_binds: &HashMap<String, DataType>,
    type_udims: &HashMap<String, Vec<UnpackedDimension>>,
    caller_params: &HashMap<String, Value>,
    elab: &ElaboratedModule,
    visiting: &mut HashSet<String>,
    depth: u32,
) -> Option<ResolvedClassTypedef> {
    if depth >= 16 {
        return None;
    }
    let mut cur_cls = start_cls;
    let mut cur_vals = val_params.clone();
    let mut cur_tbinds = type_binds.clone();
    let mut cur_tudims = type_udims.clone();

    for _ in 0..16 {
        let target = cur_cls.typedef_targets.get(leaf).or_else(|| {
            let mut qualified = cur_cls
                .typedef_targets
                .iter()
                .filter(|(k, _)| k.rsplit_once("::").is_some_and(|(_, l)| l == leaf));
            let first = qualified.next()?;
            qualified.next().is_none().then_some(first.1)
        });
        if let Some(target) = target {
            let inserted = visiting.insert(leaf.to_string());
            let (mut resolved_dt, inner_udims) = subst_class_dt(
                target,
                cur_cls,
                &cur_vals,
                &cur_tbinds,
                &cur_tudims,
                caller_params,
                elab,
                visiting,
                depth + 1,
            );
            if inserted {
                visiting.remove(leaf);
            }
            resolved_dt = apply_outer_packed_dims_dt(resolved_dt, outer_packed, caller_params);
            let td_udims = cur_cls
                .typedef_unpacked_dims
                .get(leaf)
                .map(|d| fold_unpacked_dims(d, &cur_vals, &elab.typedef_types))
                .unwrap_or_default();
            let mut udims = td_udims;
            udims.extend(inner_udims);
            let w = resolve_type_width(&resolved_dt, Some(&cur_vals), Some(&elab.typedefs)).max(1);
            let elem_w = packed_inner_elem_width(&resolved_dt, &cur_vals, &elab.typedefs);
            let signed = is_type_signed_resolved(&resolved_dt, &elab.typedef_types);
            return Some(ResolvedClassTypedef {
                data_type: resolved_dt,
                width: w,
                elem_width: elem_w,
                unpacked_dims: udims,
                signed,
            });
        }
        let Some(base_name) = cur_cls.extends.as_deref() else {
            break;
        };
        let Some(base_cls) = elab.classes.get(base_name) else {
            break;
        };
        let (next_val_overrides, mut next_tbinds, mut next_tudims) = eval_extends_bindings(
            cur_cls,
            base_cls,
            &cur_vals,
            &cur_tbinds,
            &cur_tudims,
            caller_params,
            elab,
            visiting,
            depth,
        );
        cur_vals = class_val_params_with_extends(
            base_cls,
            &next_val_overrides,
            &mut next_tbinds,
            &mut next_tudims,
            caller_params,
            elab,
            visiting,
            depth + 1,
        );
        cur_tbinds = next_tbinds;
        cur_tudims = next_tudims;
        cur_cls = base_cls;
    }
    None
}

fn bind_extends_expr(
    pn: &str,
    expr: &Expression,
    base_cls: &ElaboratedClass,
    env: &ParamEnv<'_>,
    cur_cls: &ElaboratedClass,
    cur_vals: &HashMap<String, Value>,
    cur_tbinds: &HashMap<String, DataType>,
    cur_tudims: &HashMap<String, Vec<UnpackedDimension>>,
    caller_params: &HashMap<String, Value>,
    elab: &ElaboratedModule,
    visiting: &mut HashSet<String>,
    depth: u32,
    next_val_overrides: &mut HashMap<String, Value>,
    next_tbinds: &mut HashMap<String, DataType>,
    next_tudims: &mut HashMap<String, Vec<UnpackedDimension>>,
) {
    if base_cls.type_param_names.iter().any(|t| t == pn) {
        match &expr.kind {
            ExprKind::Ident(h) if h.path.len() == 1 && h.path[0].selects.is_empty() => {
                let sym = &h.path[0].name.name;
                if let Some(dt) = cur_tbinds.get(sym) {
                    next_tbinds.insert(pn.to_string(), dt.clone());
                    if let Some(ud) = cur_tudims.get(sym) {
                        next_tudims.insert(pn.to_string(), ud.clone());
                    }
                    return;
                }
            }
            ExprKind::TypeLiteral(dt) => {
                let (sdt, sud) = subst_class_dt(
                    dt.as_ref(),
                    cur_cls,
                    cur_vals,
                    cur_tbinds,
                    cur_tudims,
                    caller_params,
                    elab,
                    visiting,
                    depth + 1,
                );
                next_tbinds.insert(pn.to_string(), sdt);
                if !sud.is_empty() {
                    next_tudims.insert(pn.to_string(), sud);
                }
                return;
            }
            _ => {}
        }
        let mut merged = caller_params.clone();
        for (k, v) in cur_vals {
            merged.insert(k.clone(), v.clone());
        }
        if let Some((dt, ud)) = resolve_type_arg_expr_at(expr, &merged, elab, depth) {
            next_tbinds.insert(pn.to_string(), dt);
            if !ud.is_empty() {
                next_tudims.insert(pn.to_string(), ud);
            }
        }
    } else {
        let v = eval_const_expr_val_env(expr, env);
        next_val_overrides.insert(pn.to_string(), v);
    }
}

fn eval_extends_bindings(
    cur_cls: &ElaboratedClass,
    base_cls: &ElaboratedClass,
    cur_vals: &HashMap<String, Value>,
    cur_tbinds: &HashMap<String, DataType>,
    cur_tudims: &HashMap<String, Vec<UnpackedDimension>>,
    caller_params: &HashMap<String, Value>,
    elab: &ElaboratedModule,
    visiting: &mut HashSet<String>,
    depth: u32,
) -> (
    HashMap<String, Value>,
    HashMap<String, DataType>,
    HashMap<String, Vec<UnpackedDimension>>,
) {
    use crate::ast::decl::ParamValue;
    let mut next_val_overrides: HashMap<String, Value> = HashMap::default();
    let mut next_tbinds: HashMap<String, DataType> = HashMap::default();
    let mut next_tudims: HashMap<String, Vec<UnpackedDimension>> = HashMap::default();
    if !cur_cls.extends_param_values.is_empty() {
        let env = ParamEnv::Overlay {
            base: caller_params,
            top: cur_vals,
        };
        for (idx, pv) in cur_cls.extends_param_values.iter().enumerate() {
            match pv {
                ParamValue::Expr(e) => match &e.kind {
                    ExprKind::NamedArg {
                        name: pn,
                        expr: Some(inner),
                    } => bind_extends_expr(
                        &pn.name,
                        inner,
                        base_cls,
                        &env,
                        cur_cls,
                        cur_vals,
                        cur_tbinds,
                        cur_tudims,
                        caller_params,
                        elab,
                        visiting,
                        depth,
                        &mut next_val_overrides,
                        &mut next_tbinds,
                        &mut next_tudims,
                    ),
                    ExprKind::NamedArg { expr: None, .. } => {}
                    _ => {
                        if let Some(pn) = base_cls.param_order.get(idx) {
                            bind_extends_expr(
                                pn,
                                e,
                                base_cls,
                                &env,
                                cur_cls,
                                cur_vals,
                                cur_tbinds,
                                cur_tudims,
                                caller_params,
                                elab,
                                visiting,
                                depth,
                                &mut next_val_overrides,
                                &mut next_tbinds,
                                &mut next_tudims,
                            );
                        }
                    }
                },
                ParamValue::Type(dt) => {
                    if let Some(pn) = base_cls.param_order.get(idx)
                        && base_cls.type_param_names.iter().any(|t| t == pn)
                    {
                        let (sdt, sud) = subst_class_dt(
                            dt,
                            cur_cls,
                            cur_vals,
                            cur_tbinds,
                            cur_tudims,
                            caller_params,
                            elab,
                            visiting,
                            depth + 1,
                        );
                        next_tbinds.insert(pn.clone(), sdt);
                        if !sud.is_empty() {
                            next_tudims.insert(pn.clone(), sud);
                        }
                    }
                }
            }
        }
        return (next_val_overrides, next_tbinds, next_tudims);
    }

    for (idx, arg_txt) in cur_cls.extends_type_args.iter().enumerate() {
        let Some(pn) = base_cls.param_order.get(idx) else {
            continue;
        };
        if base_cls.type_param_names.iter().any(|t| t == pn) {
            if let Some((dt, ud)) =
                eval_text_arg_as_dt(arg_txt, cur_tbinds, cur_tudims, elab, Span::dummy())
            {
                next_tbinds.insert(pn.clone(), dt);
                if !ud.is_empty() {
                    next_tudims.insert(pn.clone(), ud);
                }
            }
        } else if let Some(v) = eval_text_arg_as_val(arg_txt, cur_vals, caller_params) {
            next_val_overrides.insert(pn.clone(), v);
        }
    }
    (next_val_overrides, next_tbinds, next_tudims)
}

fn class_val_params_with_extends(
    cls: &ElaboratedClass,
    bound: &HashMap<String, Value>,
    type_binds: &mut HashMap<String, DataType>,
    type_udims: &mut HashMap<String, Vec<UnpackedDimension>>,
    caller_params: &HashMap<String, Value>,
    elab: &ElaboratedModule,
    visiting: &mut HashSet<String>,
    depth: u32,
) -> HashMap<String, Value> {
    if depth >= 16 {
        fill_class_type_param_defaults(cls, type_binds, bound, elab);
        return class_default_values(cls, bound, caller_params);
    }
    let is_header_val = |pn: &String| {
        cls.param_order.iter().any(|p| p == pn)
            && !cls.type_param_names.iter().any(|t| t == pn)
    };
    let mut params: HashMap<String, Value> = bound.clone();
    for (pn, init) in &cls.param_defaults {
        if !is_header_val(pn) || params.contains_key(pn) {
            continue;
        }
        if let Some(init) = init {
            let v = eval_const_expr_val_env(
                init,
                &ParamEnv::Overlay {
                    base: caller_params,
                    top: &params,
                },
            );
            params.insert(pn.clone(), v);
        }
    }
    fill_class_type_param_defaults(cls, type_binds, &params, elab);
    if let Some(base_name) = cls.extends.as_deref()
        && let Some(base_cls) = elab.classes.get(base_name)
    {
        let (base_ov, mut base_tb, mut base_tu) = eval_extends_bindings(
            cls,
            base_cls,
            &params,
            type_binds,
            type_udims,
            caller_params,
            elab,
            visiting,
            depth,
        );
        let base_vals = class_val_params_with_extends(
            base_cls,
            &base_ov,
            &mut base_tb,
            &mut base_tu,
            caller_params,
            elab,
            visiting,
            depth + 1,
        );
        for (k, v) in base_vals {
            params.entry(k).or_insert(v);
        }
    }
    for (pn, init) in &cls.param_defaults {
        if is_header_val(pn) || bound.contains_key(pn) {
            continue;
        }
        if let Some(init) = init {
            let v = eval_const_expr_val_env(
                init,
                &ParamEnv::Overlay {
                    base: caller_params,
                    top: &params,
                },
            );
            params.insert(pn.clone(), v);
        }
    }
    params
}

pub fn specialized_class_scope_width(
    name: &crate::ast::types::TypeName,
    elab: &ElaboratedModule,
) -> Option<u32> {
    specialized_class_scope_resolve_at(name, &[], &elab.parameters, elab, 0).map(|r| r.width)
}

/// Resolve `C#(args)::T` (with optional `outer_packed` dimensions) using the
/// active caller parameter environment (`caller_params`) into a full
/// [`ResolvedClassTypedef`].
pub fn specialized_class_scope_resolve(
    name: &crate::ast::types::TypeName,
    outer_packed: &[PackedDimension],
    caller_params: &HashMap<String, Value>,
    elab: &ElaboratedModule,
) -> Option<ResolvedClassTypedef> {
    specialized_class_scope_resolve_at(name, outer_packed, caller_params, elab, 0)
}

/// Resolve any `DataType` that references a specialized class typedef (either
/// directly at top level or inside a packed/unpacked struct or enum base).
pub fn resolve_specialized_class_data_type(
    dt: &DataType,
    caller_params: &HashMap<String, Value>,
    elab: &ElaboratedModule,
) -> Option<ResolvedClassTypedef> {
    resolve_specialized_class_dt_depth(dt, caller_params, elab, 0)
}

fn resolve_specialized_class_dt_depth(
    dt: &DataType,
    caller_params: &HashMap<String, Value>,
    elab: &ElaboratedModule,
    depth: u32,
) -> Option<ResolvedClassTypedef> {
    if depth >= 8 {
        return None;
    }
    match dt {
        DataType::TypeReference {
            name, dimensions, ..
        } if name.has_scope() => {
            if declared_user_nettype(elab, dt).is_some() {
                return None;
            }
            specialized_class_scope_resolve_at(name, dimensions, caller_params, elab, depth)
        }
        DataType::Struct(su) => {
            let mut changed = false;
            let mut out = su.clone();
            for (mi, m) in su.members.iter().enumerate() {
                if let Some(sub) =
                    resolve_specialized_class_dt_depth(&m.data_type, caller_params, elab, depth + 1)
                {
                    changed = true;
                    out.members[mi].data_type = sub.data_type;
                    if !sub.unpacked_dims.is_empty() {
                        for decl in &mut out.members[mi].declarators {
                            decl.dimensions.extend(sub.unpacked_dims.clone());
                        }
                    }
                }
            }
            if !changed {
                return None;
            }
            let wrapped = DataType::Struct(out);
            let sized =
                size_struct_member_dims(&wrapped, caller_params, &elab.typedef_types, false)
                    .unwrap_or(wrapped);
            let folded =
                fold_packed_dims_with(&sized, caller_params, &|_, _| true).unwrap_or(sized);
            let w = resolve_type_width(&folded, Some(caller_params), Some(&elab.typedefs));
            let elem_w = packed_inner_elem_width(&folded, caller_params, &elab.typedefs);
            let signed = is_type_signed_resolved(&folded, &elab.typedef_types);
            Some(ResolvedClassTypedef {
                data_type: folded,
                width: w,
                elem_width: elem_w,
                unpacked_dims: Vec::new(),
                signed,
            })
        }
        DataType::Enum(et) => {
            let bt = et.base_type.as_ref()?;
            let sub = resolve_specialized_class_dt_depth(bt, caller_params, elab, depth + 1)?;
            let mut out = et.clone();
            out.base_type = Some(Box::new(sub.data_type));
            let wrapped = DataType::Enum(out);
            let folded =
                fold_packed_dims_with(&wrapped, caller_params, &|_, _| true).unwrap_or(wrapped);
            let w = resolve_type_width(&folded, Some(caller_params), Some(&elab.typedefs));
            let elem_w = packed_inner_elem_width(&folded, caller_params, &elab.typedefs);
            let signed = is_type_signed_resolved(&folded, &elab.typedef_types);
            Some(ResolvedClassTypedef {
                data_type: folded,
                width: w,
                elem_width: elem_w,
                unpacked_dims: Vec::new(),
                signed,
            })
        }
        _ => None,
    }
}

/// `specialized_class_scope_resolve` after `depth` rewrites of the name.
fn specialized_class_scope_resolve_at(
    name: &crate::ast::types::TypeName,
    outer_packed: &[PackedDimension],
    caller_params: &HashMap<String, Value>,
    elab: &ElaboratedModule,
    depth: u32,
) -> Option<ResolvedClassTypedef> {
    if depth < 8
        && let Some(alt) = class_scope_types::specialized(name).or_else(|| {
            (!elab.typedefs.contains_key(&name.qualified()))
                .then(|| class_scope_types::through_alias(name))
                .flatten()
        })
        && let Some(res) = specialized_class_scope_resolve_at(
            &alt,
            outer_packed,
            caller_params,
            elab,
            depth + 1,
        )
        .or_else(|| {
            let alt_is_param_class = alt.scopes.iter().enumerate().any(|(i, s)| {
                s.type_args.is_empty()
                    && !alt.bound.has_explicit_empty_spec(i)
                    && find_class_entry(&alt.scopes, i, elab)
                        .is_some_and(|(_, c)| !c.param_order.is_empty())
            });
            if alt_is_param_class {
                return None;
            }
            lookup_scoped_type(&alt, &elab.typedefs).copied().map(|w| {
                let dt = lookup_scoped_type(&alt, &elab.typedef_types)
                    .cloned()
                    .unwrap_or(DataType::TypeReference {
                        name: Box::new(alt.clone()),
                        dimensions: Vec::new(),
                        type_args: Vec::new(),
                        span: alt.name.span,
                    });
                let dt = apply_outer_packed_dims_dt(dt, outer_packed, caller_params);
                let final_w = if outer_packed.is_empty() {
                    w
                } else {
                    resolve_type_width(&dt, Some(caller_params), Some(&elab.typedefs)).max(w)
                };
                let elem_w = packed_inner_elem_width(&dt, caller_params, &elab.typedefs);
                let signed = is_type_signed_resolved(&dt, &elab.typedef_types);
                let udims = lookup_scoped_type(&alt, &elab.typedef_unpacked_dims)
                    .cloned()
                    .unwrap_or_default();
                ResolvedClassTypedef {
                    data_type: dt,
                    width: final_w,
                    elem_width: elem_w,
                    unpacked_dims: udims,
                    signed,
                }
            })
        })
    {
        return Some(res);
    }

    let (cls_key, cls, type_args, nested): (String, &ElaboratedClass, Vec<Expression>, Vec<&str>) =
        match name
            .scopes
            .iter()
            .enumerate()
            .rposition(|(i, s)| !s.type_args.is_empty() || name.bound.has_explicit_empty_spec(i))
        {
            Some(i) => {
                let (key, cls) = find_class_entry(&name.scopes, i, elab)?;
                let nested = name.scopes[i + 1..]
                    .iter()
                    .map(|s| s.name.name.as_str())
                    .collect();
                (key, cls, name.scopes[i].type_args.clone(), nested)
            }
            None => name.scopes.iter().enumerate().rev().find_map(|(i, s)| {
                let (c, a, mut n) = typedef_specialization(&s.name.name, elab)?;
                let cls = elab.classes.get(&c)?.as_ref();
                n.extend(name.scopes[i + 1..].iter().map(|s| s.name.name.as_str()));
                Some((c, cls, a.to_vec(), n))
            })?,
        };

    let mut val_overrides: HashMap<String, Value> = HashMap::default();
    let mut type_binds: HashMap<String, DataType> = HashMap::default();
    let mut type_udims: HashMap<String, Vec<UnpackedDimension>> = HashMap::default();
    for (i, arg) in type_args.iter().enumerate() {
        match &arg.kind {
            ExprKind::NamedArg { name: pn, expr } => {
                if let Some(e) = expr {
                    if cls.type_param_names.iter().any(|t| t == &pn.name) {
                        if let Some((dt, ud)) =
                            resolve_type_arg_expr_at(e, caller_params, elab, depth)
                        {
                            type_binds.insert(pn.name.clone(), dt);
                            if !ud.is_empty() {
                                type_udims.insert(pn.name.clone(), ud);
                            }
                        }
                    } else {
                        val_overrides.insert(pn.name.clone(), eval_const_expr_val(e, caller_params));
                    }
                }
            }
            _ => {
                if let Some(pn) = cls.param_order.get(i) {
                    if cls.type_param_names.iter().any(|t| t == pn) {
                        if let Some((dt, ud)) =
                            resolve_type_arg_expr_at(arg, caller_params, elab, depth)
                        {
                            type_binds.insert(pn.clone(), dt);
                            if !ud.is_empty() {
                                type_udims.insert(pn.clone(), ud);
                            }
                        }
                    } else {
                        val_overrides.insert(pn.clone(), eval_const_expr_val(arg, caller_params));
                    }
                }
            }
        }
    }

    let mut cur_cls = cls;
    let mut cur_key = cls_key;
    let mut type_binds = type_binds;
    let mut type_udims = type_udims;
    let mut visiting = HashSet::default();
    let mut val_params = class_val_params_with_extends(
        cur_cls,
        &val_overrides,
        &mut type_binds,
        &mut type_udims,
        caller_params,
        elab,
        &mut visiting,
        depth,
    );
    for n in &nested {
        let qualified = format!("{cur_key}::{n}");
        let (key, sub) = [qualified.as_str(), *n].into_iter().find_map(|k| {
            let c = elab.classes.get(k)?.as_ref();
            (k.contains("::") || c.enclosing.as_deref().is_none_or(|e| e == cur_key))
                .then_some((k.to_string(), c))
        })?;
        val_params = class_val_params_with_extends(
            sub,
            &val_params,
            &mut type_binds,
            &mut type_udims,
            caller_params,
            elab,
            &mut visiting,
            depth,
        );
        cur_cls = sub;
        cur_key = key;
    }

    resolve_member_in_class_or_base(
        cur_cls,
        &name.name.name,
        outer_packed,
        &val_params,
        &type_binds,
        &type_udims,
        caller_params,
        elab,
        &mut visiting,
        depth,
    )
}

/// The value parameters and body constants of `cls` in declaration order:
/// an entry of `bound` as given, any other from its default evaluated
/// under the ones before it (so a body `localparam N = W * 2` follows a
/// bound `W`), falling back to `base_params` for enclosing/package constants.
fn class_default_values(
    cls: &ElaboratedClass,
    bound: &HashMap<String, Value>,
    base_params: &HashMap<String, Value>,
) -> HashMap<String, Value> {
    let mut params: HashMap<String, Value> = bound.clone();
    for (pn, init) in &cls.param_defaults {
        if bound.contains_key(pn) {
            continue;
        }
        if let Some(init) = init {
            let v = eval_const_expr_val_env(
                init,
                &ParamEnv::Overlay {
                    base: base_params,
                    top: &params,
                },
            );
            params.insert(pn.clone(), v);
        }
    }
    params
}

/// §8.23, §8.25.1: the width of typedef `leaf` of class `cls_name` — or of
/// the class reached from it through the nested-class names `nested`
/// (`Outer#(6)::Inner::td`) — with the value parameters in `bound` taking
/// the place of their defaults. A nested class sees its enclosing classes'
/// parameters. None when a link names no such class or typedef.
pub fn class_scope_typedef_width(
    cls_name: &str,
    bound: &HashMap<String, Value>,
    nested: &[&str],
    leaf: &str,
    elab: &ElaboratedModule,
) -> Option<u32> {
    let mut cls = elab.classes.get(cls_name)?;
    let mut cur = cls_name.to_string();
    let mut type_binds: HashMap<String, DataType> = HashMap::default();
    let mut type_udims: HashMap<String, Vec<UnpackedDimension>> = HashMap::default();
    let mut visiting = HashSet::default();
    let mut params = class_val_params_with_extends(
        cls,
        bound,
        &mut type_binds,
        &mut type_udims,
        &elab.parameters,
        elab,
        &mut visiting,
        0,
    );
    for n in nested {
        let qualified = format!("{cur}::{n}");
        let (key, sub) = [qualified.as_str(), n].into_iter().find_map(|k| {
            let c = elab.classes.get(k)?;
            (k.contains("::") || c.enclosing.as_deref().is_none_or(|e| e == cur))
                .then_some((k.to_string(), c))
        })?;
        params = class_val_params_with_extends(
            sub,
            &params,
            &mut type_binds,
            &mut type_udims,
            &elab.parameters,
            elab,
            &mut visiting,
            0,
        );
        cls = sub;
        cur = key;
    }
    resolve_member_in_class_or_base(
        cls,
        leaf,
        &[],
        &params,
        &type_binds,
        &type_udims,
        &elab.parameters,
        elab,
        &mut visiting,
        0,
    )
    .map(|r| r.width)
}

/// §6.18/§8.25.1: the class and `#(...)` args a typedef names when it
/// aliases a class specialization (`typedef holder #(byte, 6) h_t;`),
/// following plain alias hops, and the classes nested in that
/// specialization the alias goes on to name (`typedef box #(6)::pay
/// p_t;`, §8.23); None for any other typedef.
fn typedef_specialization<'a>(
    name: &str,
    elab: &'a ElaboratedModule,
) -> Option<(String, &'a [Expression], Vec<&'a str>)> {
    let mut cur = elab.typedef_types.get(name)?;
    for _ in 0..16 {
        let DataType::TypeReference {
            name: tn,
            type_args,
            dimensions,
            ..
        } = cur
        else {
            return None;
        };
        if !dimensions.is_empty() {
            return None;
        }
        if !type_args.is_empty() {
            let key = find_class_key_for_typename(tn, elab)?;
            return Some((key, type_args.as_slice(), Vec::new()));
        }
        if !tn.scopes.is_empty()
            && let Some(i) = tn
                .scopes
                .iter()
                .enumerate()
                .rposition(|(idx, s)| !s.type_args.is_empty() || tn.bound.has_explicit_empty_spec(idx))
        {
            let (key, _) = find_class_entry(&tn.scopes, i, elab)?;
            let mut nested: Vec<&str> = tn.scopes[i + 1..]
                .iter()
                .map(|s| s.name.name.as_str())
                .collect();
            nested.push(tn.name.name.as_str());
            return Some((key, tn.scopes[i].type_args.as_slice(), nested));
        }
        // `typedef C#() c0_t;` / `typedef pkg::PC#() p0_t;` (no `#()` on scope links):
        // resolve to the class itself with empty overrides (defaults apply).
        if let Some(key) = find_class_key_for_typename(tn, elab) {
            return Some((key, &[], Vec::new()));
        }
        cur = elab.typedef_types.get(&tn.name.name)?;
    }
    None
}
