//! Hierarchical interface-port names refer to the connected instance (§25.3).

use super::*;
use std::borrow::Cow;

/// Replace the longest interface-port prefix, retaining selects and members.
/// The top's name is optional in flat keys. Bound the walk so malformed alias
/// cycles cannot hang a diagnostic or a runtime lookup.
pub fn resolve<'a>(name: &'a str, aliases: &HashMap<String, String>, top: &str) -> Cow<'a, str> {
    if aliases.is_empty() {
        return Cow::Borrowed(name);
    }
    let mut current = Cow::Borrowed(name);
    for _ in 0..aliases.len() {
        let flat = current
            .strip_prefix(top)
            .and_then(|s| s.strip_prefix('.'))
            .unwrap_or(&current);
        let found = std::iter::once(flat.len())
            .chain(
                flat.char_indices()
                    .rev()
                    .filter_map(|(i, c)| matches!(c, '.' | '[').then_some(i)),
            )
            .find_map(|end| aliases.get(&flat[..end]).map(|actual| (end, actual)));
        let Some((end, actual)) = found else { break };
        let next = format!("{actual}{}", &flat[end..]);
        if next == current {
            break;
        }
        current = Cow::Owned(next);
    }
    current
}

/// Concrete resolution of an interface-based typedef (`typedef p.data_t my_t;`
/// or `typedef p[0].data_t my_t [0:1];`).
#[derive(Debug, Clone)]
pub struct ResolvedInterfaceTypedef {
    pub data_type: DataType,
    pub width: u32,
    pub elem_width: Option<u32>,
    pub unpacked_dims: Vec<UnpackedDimension>,
    pub enum_members: Vec<(String, u64, Value)>,
    pub signed: bool,
}

fn find_port_interface_type<'a>(
    port_name: &str,
    ports: &'a PortList,
    items: &'a [ModuleItem],
) -> Option<(&'a str, &'a [Expression])> {
    if let PortList::Ansi(ps) = ports {
        for p in ps {
            if p.name.name == port_name
                && let Some(DataType::Interface {
                    name, type_args, ..
                }) = &p.data_type
            {
                return Some((name.name.as_str(), type_args.as_slice()));
            }
        }
    }
    for it in items {
        match it {
            ModuleItem::PortDeclaration(pd)
                if pd.declarators.iter().any(|d| d.name.name == port_name) =>
            {
                if let DataType::Interface {
                    name, type_args, ..
                } = &pd.data_type
                {
                    return Some((name.name.as_str(), type_args.as_slice()));
                }
            }
            ModuleItem::DataDeclaration(dd)
                if dd.declarators.iter().any(|d| d.name.name == port_name) =>
            {
                if let DataType::Interface {
                    name, type_args, ..
                } = &dd.data_type
                {
                    return Some((name.name.as_str(), type_args.as_slice()));
                }
            }
            _ => {}
        }
    }
    None
}

fn eval_iface_type_arg_dt(
    arg: &Expression,
    caller_params: &HashMap<String, Value>,
    elab: &ElaboratedModule,
) -> Option<DataType> {
    let inner = match &arg.kind {
        ExprKind::NamedArg { expr: Some(e), .. } => e.as_ref(),
        ExprKind::NamedArg { expr: None, .. } => return None,
        _ => arg,
    };
    match &inner.kind {
        ExprKind::TypeLiteral(dt) => {
            if let Some(res) =
                resolve_specialized_class_data_type(dt.as_ref(), caller_params, elab)
            {
                return Some(res.data_type);
            }
            Some(
                fold_packed_dims_with(dt.as_ref(), caller_params, &|_, _| true)
                    .unwrap_or_else(|| (**dt).clone()),
            )
        }
        ExprKind::Ident(h) if h.path.len() == 1 && h.path[0].selects.is_empty() => {
            let n = h.path[0].name.name.as_str();
            if let Some(dt) = builtin_keyword_to_data_type(n, inner.span) {
                Some(dt)
            } else if let Some(dt) = elab.typedef_types.get(n) {
                Some(dt.clone())
            } else {
                Some(DataType::TypeReference {
                    name: Box::new(crate::ast::types::TypeName {
                        scopes: Vec::new(),
                        name: h.path[0].name.clone(),
                        bound: Default::default(),
                        span: inner.span,
                    }),
                    dimensions: Vec::new(),
                    type_args: Vec::new(),
                    span: inner.span,
                })
            }
        }
        _ => None,
    }
}

fn collect_iface_param_env(
    idecl: &crate::ast::module::InterfaceDeclaration,
    inst_path: Option<&str>,
    port_type_args: &[Expression],
    caller_params: &HashMap<String, Value>,
    elab: &ElaboratedModule,
) -> (
    HashMap<String, Value>,
    SharedMap<DataType>,
    HashMap<String, u32>,
    HashSet<String>,
) {
    let mut iface_params: HashMap<String, Value> = HashMap::default();
    let mut iface_typedef_types = elab.typedef_types.clone();
    let mut iface_typedefs: HashMap<String, u32> =
        elab.typedefs.iter().map(|(k, &v)| (k.clone(), v)).collect();
    let mut overridden_type_params: HashSet<String> = HashSet::default();
    let mut iface_local_names: HashSet<String> = HashSet::default();

    // Seed from an already-elaborated interface instance when available.
    if let Some(prefix) = inst_path {
        let mut prefixes = Vec::new();
        prefixes.push(format!("{prefix}."));
        if !elab.name.is_empty() {
            prefixes.push(format!("{}.{prefix}.", elab.name));
        }
        if let Some((base, _)) = prefix.split_once('[') {
            prefixes.push(format!("{base}."));
            if !elab.name.is_empty() {
                prefixes.push(format!("{}.{base}.", elab.name));
            }
        }
        for pfx in &prefixes {
            for (k, v) in &elab.parameters {
                if let Some(rest) = k.strip_prefix(pfx)
                    && !rest.contains('.')
                {
                    iface_params.entry(rest.to_string()).or_insert_with(|| v.clone());
                }
            }
            for (k, dt) in elab.typedef_types.iter() {
                if let Some(rest) = k.strip_prefix(pfx)
                    && !rest.contains('.')
                {
                    iface_typedef_types.insert(rest.to_string(), dt.clone());
                    overridden_type_params.insert(rest.to_string());
                    iface_local_names.insert(rest.to_string());
                    let w = elab.typedefs.get(k).copied().unwrap_or_else(|| {
                        resolve_type_width(dt, Some(&iface_params), Some(&iface_typedefs))
                    });
                    iface_typedefs.insert(rest.to_string(), w);
                }
            }
        }
    }

    // Apply unelaborated port `#(...)` overrides (e.g. `bus_if #(16) p`), and
    // fill defaults / body localparams in declaration order.
    let mut order_names: Vec<String> = Vec::new();
    let mut is_type_param: HashSet<String> = HashSet::default();
    for pd in &idecl.params {
        match &pd.kind {
            ParameterKind::Data { assignments, .. } => {
                for a in assignments {
                    order_names.push(a.name.name.clone());
                }
            }
            ParameterKind::Type { assignments } => {
                for a in assignments {
                    order_names.push(a.name.name.clone());
                    is_type_param.insert(a.name.name.clone());
                    iface_local_names.insert(a.name.name.clone());
                }
            }
        }
    }
    for (idx, arg) in port_type_args.iter().enumerate() {
        match &arg.kind {
            ExprKind::NamedArg { name: pn, expr: Some(e) } => {
                if is_type_param.contains(&pn.name) {
                    if let Some(dt) = eval_iface_type_arg_dt(e, caller_params, elab) {
                        let w = resolve_type_width(&dt, Some(&iface_params), Some(&iface_typedefs));
                        iface_typedef_types.insert(pn.name.clone(), dt);
                        iface_typedefs.insert(pn.name.clone(), w);
                        overridden_type_params.insert(pn.name.clone());
                    }
                } else {
                    iface_params
                        .entry(pn.name.clone())
                        .or_insert_with(|| eval_const_expr_val(e, caller_params));
                }
            }
            _ => {
                if let Some(pn) = order_names.get(idx) {
                    if is_type_param.contains(pn) {
                        if let Some(dt) = eval_iface_type_arg_dt(arg, caller_params, elab) {
                            let w =
                                resolve_type_width(&dt, Some(&iface_params), Some(&iface_typedefs));
                            iface_typedef_types.insert(pn.clone(), dt);
                            iface_typedefs.insert(pn.clone(), w);
                            overridden_type_params.insert(pn.clone());
                        }
                    } else {
                        iface_params
                            .entry(pn.clone())
                            .or_insert_with(|| eval_const_expr_val(arg, caller_params));
                    }
                }
            }
        }
    }

    let empty_udims: HashMap<String, Vec<UnpackedDimension>> = HashMap::default();
    let apply_param_decl = |pd: &ParameterDeclaration,
                            iface_params: &mut HashMap<String, Value>,
                            iface_typedef_types: &mut SharedMap<DataType>,
                            iface_typedefs: &mut HashMap<String, u32>,
                            iface_local_names: &mut HashSet<String>| {
        match &pd.kind {
            ParameterKind::Data { assignments, .. } => {
                for a in assignments {
                    if !iface_params.contains_key(&a.name.name)
                        && let Some(init) = &a.init
                    {
                        let v = eval_const_expr_val(init, iface_params);
                        iface_params.insert(a.name.name.clone(), v);
                    }
                }
            }
            ParameterKind::Type { assignments } => {
                for a in assignments {
                    iface_local_names.insert(a.name.name.clone());
                    if let Some(init) = &a.init {
                        // Only reuse a pre-seeded type param if it was actually
                        // overridden on the instance/port; a global typedef of
                        // the same name must never suppress the default.
                        let dt = if overridden_type_params.contains(&a.name.name)
                            && let Some(prev) = iface_typedef_types.get(&a.name.name)
                        {
                            prev.clone()
                        } else {
                            let mut visiting = HashSet::default();
                            let (subst, _) = substitute_local_typedefs(
                                init,
                                iface_typedef_types,
                                &empty_udims,
                                iface_local_names,
                                iface_params,
                                &mut visiting,
                                0,
                            );
                            fold_packed_dims_with(&subst, iface_params, &|_, _| true)
                                .unwrap_or(subst)
                        };
                        let w = resolve_type_width(&dt, Some(iface_params), Some(iface_typedefs));
                        iface_typedef_types.insert(a.name.name.clone(), dt);
                        iface_typedefs.insert(a.name.name.clone(), w);
                    }
                }
            }
        }
    };

    for pd in &idecl.params {
        apply_param_decl(
            pd,
            &mut iface_params,
            &mut iface_typedef_types,
            &mut iface_typedefs,
            &mut iface_local_names,
        );
    }
    for item in &idecl.items {
        if let ModuleItem::ParameterDeclaration(pd) | ModuleItem::LocalparamDeclaration(pd) = item
        {
            apply_param_decl(
                pd,
                &mut iface_params,
                &mut iface_typedef_types,
                &mut iface_typedefs,
                &mut iface_local_names,
            );
        }
    }
    (
        iface_params,
        iface_typedef_types,
        iface_typedefs,
        iface_local_names,
    )
}

fn substitute_local_typedefs(
    dt: &DataType,
    local_dts: &SharedMap<DataType>,
    local_udims: &HashMap<String, Vec<UnpackedDimension>>,
    local_names: &HashSet<String>,
    params: &HashMap<String, Value>,
    visiting: &mut HashSet<String>,
    depth: u32,
) -> (DataType, Vec<UnpackedDimension>) {
    if depth >= 16 {
        return (dt.clone(), Vec::new());
    }
    match dt {
        DataType::TypeReference {
            name,
            dimensions,
            type_args,
            ..
        } if name.scopes.is_empty() && type_args.is_empty() => {
            if local_names.contains(&name.name.name)
                && !visiting.contains(&name.name.name)
                && let Some(inner) = local_dts.get(&name.name.name)
            {
                let inserted = visiting.insert(name.name.name.clone());
                let (resolved, inner_udims) = substitute_local_typedefs(
                    inner,
                    local_dts,
                    local_udims,
                    local_names,
                    params,
                    visiting,
                    depth + 1,
                );
                if inserted {
                    visiting.remove(&name.name.name);
                }
                let mut udims = local_udims
                    .get(&name.name.name)
                    .cloned()
                    .unwrap_or_default();
                if udims.is_empty() {
                    udims = inner_udims;
                }
                (apply_outer_packed_dims_dt(resolved, dimensions, params), udims)
            } else {
                (
                    fold_packed_dims_with(dt, params, &|_, _| true).unwrap_or_else(|| dt.clone()),
                    Vec::new(),
                )
            }
        }
        DataType::Struct(su) => {
            let mut s = su.clone();
            for m in &mut s.members {
                let (mdt, mudims) = substitute_local_typedefs(
                    &m.data_type,
                    local_dts,
                    local_udims,
                    local_names,
                    params,
                    visiting,
                    depth + 1,
                );
                m.data_type = mdt;
                for decl in &mut m.declarators {
                    let mut d = fold_unpacked_dims(&decl.dimensions, params, local_dts);
                    if !mudims.is_empty() {
                        d.extend(mudims.clone());
                    }
                    decl.dimensions = d;
                }
            }
            let wrapped = DataType::Struct(s);
            let sized = size_struct_member_dims(&wrapped, params, local_dts, true).unwrap_or(wrapped);
            (
                fold_packed_dims_with(&sized, params, &|_, _| true).unwrap_or(sized),
                Vec::new(),
            )
        }
        DataType::Enum(et) => {
            let mut e = et.clone();
            if let Some(bt) = &e.base_type {
                let (bdt, _) = substitute_local_typedefs(
                    bt,
                    local_dts,
                    local_udims,
                    local_names,
                    params,
                    visiting,
                    depth + 1,
                );
                e.base_type = Some(Box::new(bdt));
            }
            let wrapped = DataType::Enum(e);
            (
                fold_packed_dims_with(&wrapped, params, &|_, _| true).unwrap_or(wrapped),
                Vec::new(),
            )
        }
        _ => (
            fold_packed_dims_with(dt, params, &|_, _| true).unwrap_or_else(|| dt.clone()),
            Vec::new(),
        ),
    }
}

/// Resolve an interface-based typedef (`typedef p.data_t my_t;` or
/// `typedef p[0].data_t my_t;`) through connected instances, forwarded port
/// chains, interface arrays, or unelaborated port declarations (§6.18).
pub fn resolve_interface_port_typedef(
    td: &TypedefDeclaration,
    enclosing_ports: &PortList,
    enclosing_items: &[ModuleItem],
    caller_params: &HashMap<String, Value>,
    aliases: &HashMap<String, String>,
    elab: &ElaboratedModule,
    definitions: Option<&HashMap<String, Definition<'_>>>,
) -> Option<ResolvedInterfaceTypedef> {
    let (port_name, member_name) = match &td.data_type {
        DataType::Interface {
            name,
            modport: Some(member),
            ..
        } => (name.name.as_str(), member.name.as_str()),
        DataType::TypeReference {
            name,
            dimensions,
            type_args,
            ..
        } if td.iface_selects.is_empty()
            && dimensions.is_empty()
            && type_args.is_empty()
            && name.scopes.len() == 1 =>
        {
            let p = name.scopes[0].name.name.as_str();
            let is_iface_port = find_port_interface_type(p, enclosing_ports, enclosing_items)
                .is_some()
                || aliases.contains_key(p)
                || elab.interface_port_aliases.contains_key(p);
            if !is_iface_port {
                return None;
            }
            (p, name.name.name.as_str())
        }
        _ => return None,
    };

    let defs = definitions?;
    let mut port_key = port_name.to_string();
    for sel in &td.iface_selects {
        let idx = const_eval_i64_with_params(sel, Some(caller_params))?;
        port_key.push_str(&format!("[{idx}]"));
    }

    let first = resolve(&port_key, aliases, &elab.name);
    let second = if first.as_ref() == port_key || !aliases.contains_key(first.as_ref()) {
        resolve(first.as_ref(), &elab.interface_port_aliases, &elab.name)
    } else {
        first
    };
    let inst_path = second
        .strip_prefix(&format!("{}.", elab.name))
        .unwrap_or(second.as_ref());
    let base_inst = inst_path.split('[').next().unwrap_or(inst_path);

    let port_decl = find_port_interface_type(port_name, enclosing_ports, enclosing_items);
    let (idecl, port_args, active_inst_path): (
        &crate::ast::module::InterfaceDeclaration,
        &[Expression],
        Option<&str>,
    ) = if let Some(inst) = elab
        .instances
        .iter()
        .find(|i| i.path.as_str() == inst_path)
        .or_else(|| elab.instances.iter().find(|i| i.path.as_str() == base_inst))
    {
        let Some(Definition::Interface(idecl)) = defs.get(&*inst.def_name) else {
            return None;
        };
        (idecl, &[], Some(inst_path))
    } else if let Some((iface_name, args)) = port_decl {
        let Some(Definition::Interface(idecl)) = defs.get(iface_name) else {
            return None;
        };
        (idecl, args, None)
    } else {
        return None;
    };

    let (
        mut iface_params,
        mut iface_typedef_types,
        mut iface_typedefs,
        mut iface_local_names,
    ) = collect_iface_param_env(idecl, active_inst_path, port_args, caller_params, elab);
    let mut iface_udims: HashMap<String, Vec<UnpackedDimension>> = HashMap::default();
    let mut iface_enums: HashMap<String, Vec<(String, u64, Value)>> = HashMap::default();
    let mut found: Option<ResolvedInterfaceTypedef> = None;

    for item in &idecl.items {
        let ModuleItem::TypedefDeclaration(itd) = item else {
            continue;
        };
        if itd.forward {
            continue;
        }
        let mut visiting = HashSet::default();
        let (concrete_dt, inner_udims) = substitute_local_typedefs(
            &itd.data_type,
            &iface_typedef_types,
            &iface_udims,
            &iface_local_names,
            &iface_params,
            &mut visiting,
            0,
        );
        let mut item_udims = fold_unpacked_dims(&itd.dimensions, &iface_params, &iface_typedef_types);
        item_udims.extend(inner_udims);
        if !item_udims.is_empty() {
            iface_udims.insert(itd.name.name.clone(), item_udims.clone());
        }

        let signed = is_type_signed_resolved(&concrete_dt, &iface_typedef_types);
        let w = resolve_type_width(&concrete_dt, Some(&iface_params), Some(&iface_typedefs));
        let elem_w = packed_inner_elem_width(&concrete_dt, &iface_params, &iface_typedefs);
        let enum_members = if let DataType::Enum(et) = &concrete_dt {
            let mems = enums::enum_members_values(et, w, signed, &iface_params);
            for (nm, _, v) in &mems {
                iface_params.insert(nm.clone(), v.clone());
            }
            iface_enums.insert(itd.name.name.clone(), mems.clone());
            mems
        } else if let DataType::TypeReference { name, .. } = &itd.data_type
            && name.scopes.is_empty()
        {
            iface_enums
                .get(&name.name.name)
                .cloned()
                .unwrap_or_default()
        } else {
            Vec::new()
        };

        iface_local_names.insert(itd.name.name.clone());
        iface_typedef_types.insert(itd.name.name.clone(), concrete_dt.clone());
        iface_typedefs.insert(itd.name.name.clone(), w);

        if itd.name.name == member_name {
            let mut merged_udims =
                fold_unpacked_dims(&td.dimensions, caller_params, &elab.typedef_types);
            merged_udims.extend(item_udims);
            found = Some(ResolvedInterfaceTypedef {
                data_type: concrete_dt,
                width: w,
                elem_width: elem_w,
                unpacked_dims: merged_udims,
                enum_members,
                signed,
            });
        }
    }
    found
}
