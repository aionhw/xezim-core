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
    if c.items
        .iter()
        .any(|i| matches!(i, ClassItem::Typedef(_) | ClassItem::Class(_)))
    {
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
                for pfx in prefixes {
                    let key = format!("{}::{}", pfx, td.name.name);
                    let w = resolve_type_width(dt, Some(params), Some(&elab.typedefs));
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
pub fn specialized_class_scope_width(
    name: &crate::ast::types::TypeName,
    elab: &ElaboratedModule,
) -> Option<u32> {
    specialized_class_scope_width_at(name, elab, 0)
}

/// `specialized_class_scope_width` after `depth` rewrites of the name.
fn specialized_class_scope_width_at(
    name: &crate::ast::types::TypeName,
    elab: &ElaboratedModule,
    depth: u32,
) -> Option<u32> {
    // §8.25.1, §6.20.3: a typedef naming a member of a type parameter
    // (`typedef T::m t;`), or a scope that names a class through a type
    // parameter or typedef (`C::t`, `e_t::t`), is sized as the name it
    // stands for, which may be a specialization itself (`Cfg#(8)::m`).
    // The alias applies only where the scoped key is missing, as in
    // `lookup_scoped_type`.
    // When the rewritten name does not size, the forms below still apply.
    if depth < 8
        && let Some(alt) = class_scope_types::specialized(name).or_else(|| {
            (!elab.typedefs.contains_key(&name.qualified()))
                .then(|| class_scope_types::through_alias(name))
                .flatten()
        })
        && let Some(w) = specialized_class_scope_width_at(&alt, elab, depth + 1)
            .or_else(|| lookup_scoped_type(&alt, &elab.typedefs).copied())
    {
        return Some(w);
    }
    // The scope link carrying `#(...)` args names the specialized class;
    // without one, a link may be a typedef naming a specialization. The
    // links after it (and the classes the typedef nests into) name classes
    // nested in that specialization (§8.23).
    let (cls_name, type_args, nested): (&str, &[Expression], Vec<&str>) =
        match name.scopes.iter().rposition(|s| !s.type_args.is_empty()) {
            Some(i) => (
                &name.scopes[i].name.name,
                &name.scopes[i].type_args,
                name.scopes[i + 1..]
                    .iter()
                    .map(|s| s.name.name.as_str())
                    .collect(),
            ),
            None => name.scopes.iter().enumerate().rev().find_map(|(i, s)| {
                let (c, a, mut n) = typedef_specialization(&s.name.name, elab)?;
                n.extend(name.scopes[i + 1..].iter().map(|s| s.name.name.as_str()));
                Some((c, a, n))
            })?,
        };
    let cls = elab.classes.get(cls_name)?;
    // Bind the `#(...)` args: positional ones in `param_order` (type and
    // value params interleaved, §6.20.2), named ones by name (§8.25).
    let defaults = class_default_values(cls, &HashMap::default());
    let mut overrides: HashMap<String, Value> = HashMap::default();
    for (i, arg) in type_args.iter().enumerate() {
        match &arg.kind {
            ExprKind::NamedArg { name: pn, expr } => {
                if let Some(e) = expr
                    && !cls.type_param_names.iter().any(|t| t == &pn.name)
                {
                    overrides.insert(pn.name.clone(), eval_const_expr_val(e, &defaults));
                }
            }
            _ => {
                if let Some(pn) = cls.param_order.get(i)
                    && !cls.type_param_names.iter().any(|t| t == pn)
                {
                    overrides.insert(pn.clone(), eval_const_expr_val(arg, &defaults));
                }
            }
        }
    }
    // §8.25: a typedef of one of the class's TYPE parameters
    // (`typedef T elem_t;`) takes the type that argument binds.
    if nested.is_empty()
        && let Some(target) = cls.typedef_targets.get(&name.name.name)
        && let DataType::TypeReference {
            name: tn,
            dimensions,
            type_args: targs,
            ..
        } = target
        && tn.scopes.is_empty()
        && dimensions.is_empty()
        && targs.is_empty()
        && cls.type_param_names.iter().any(|t| t == &tn.name.name)
        && let Some(arg) = cls
            .param_order
            .iter()
            .position(|p| p == &tn.name.name)
            .and_then(|i| type_args.get(i))
    {
        let params = class_default_values(cls, &overrides);
        let w = match &arg.kind {
            ExprKind::TypeLiteral(dt) => {
                Some(resolve_type_width(dt, Some(&params), Some(&elab.typedefs)))
            }
            ExprKind::Ident(h) if h.path.len() == 1 && h.path[0].selects.is_empty() => {
                let n = h.path[0].name.name.as_str();
                atom_keyword_width(n).or_else(|| elab.typedefs.get(n).copied())
            }
            _ => None,
        };
        if let Some(w) = w.filter(|w| *w > 0) {
            return Some(w);
        }
    }
    class_scope_typedef_width(cls_name, &overrides, &nested, &name.name.name, elab)
}

/// The value parameters and body constants of `cls` in declaration order:
/// an entry of `bound` as given, any other from its default evaluated
/// under the ones before it (so a body `localparam N = W * 2` follows a
/// bound `W`).
fn class_default_values(
    cls: &ElaboratedClass,
    bound: &HashMap<String, Value>,
) -> HashMap<String, Value> {
    let mut params: HashMap<String, Value> = bound.clone();
    for (pn, init) in &cls.param_defaults {
        if bound.contains_key(pn) {
            continue;
        }
        if let Some(init) = init {
            let v = eval_const_expr_val(init, &params);
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
    let mut params = class_default_values(cls, bound);
    for n in nested {
        // A nested class another class also nests goes by its qualified
        // spelling; a reference may already carry it.
        let qualified = format!("{cur}::{n}");
        let (key, sub) = [qualified.as_str(), n]
            .into_iter()
            .find_map(|k| {
                let c = elab.classes.get(k)?;
                // `enclosing` is linked late in elaboration; before that a
                // class of this name with no enclosing class recorded is it.
                (k.contains("::") || c.enclosing.as_deref().is_none_or(|e| e == cur))
                    .then_some((k.to_string(), c))
            })?;
        params = class_default_values(sub, &params);
        cls = sub;
        cur = key;
    }
    // A typedef name several classes declare goes by its class-qualified
    // spelling (`Inner::td`), as a nested class name does.
    let target = cls.typedef_targets.get(leaf).or_else(|| {
        let mut qualified = cls
            .typedef_targets
            .iter()
            .filter(|(k, _)| k.rsplit_once("::").is_some_and(|(_, l)| l == leaf));
        let first = qualified.next()?;
        qualified.next().is_none().then_some(first.1)
    })?;
    let w = resolve_type_width(target, Some(&params), Some(&elab.typedefs));
    Some(w.max(1))
}

/// §6.18/§8.25.1: the class and `#(...)` args a typedef names when it
/// aliases a class specialization (`typedef holder #(byte, 6) h_t;`),
/// following plain alias hops, and the classes nested in that
/// specialization the alias goes on to name (`typedef box #(6)::pay
/// p_t;`, §8.23); None for any other typedef.
fn typedef_specialization<'a>(
    name: &str,
    elab: &'a ElaboratedModule,
) -> Option<(&'a str, &'a [Expression], Vec<&'a str>)> {
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
        if !tn.scopes.is_empty() {
            // `C#(args)::Inner`: the link with the args names the class.
            if !type_args.is_empty() {
                return None;
            }
            let i = tn.scopes.iter().rposition(|s| !s.type_args.is_empty())?;
            let link = &tn.scopes[i];
            if !elab.classes.contains_key(&link.name.name) {
                return None;
            }
            let mut nested: Vec<&str> = tn.scopes[i + 1..]
                .iter()
                .map(|s| s.name.name.as_str())
                .collect();
            nested.push(tn.name.name.as_str());
            return Some((link.name.name.as_str(), link.type_args.as_slice(), nested));
        }
        if !type_args.is_empty() {
            return elab
                .classes
                .contains_key(&tn.name.name)
                .then_some((tn.name.name.as_str(), type_args.as_slice(), Vec::new()));
        }
        cur = elab.typedef_types.get(&tn.name.name)?;
    }
    None
}
