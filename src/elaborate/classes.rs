use super::*;

/// Run `f` with the current thread-local typedef table, if one has been
/// installed. `elaborate_class` takes no typedef parameter and has eight
/// call sites; this reads the snapshot the typedef registration already
/// maintains rather than threading a table through all of them.
pub(super) fn typedefs_snapshot<R>(f: impl FnOnce(Option<&HashMap<String, u32>>) -> R) -> R {
    TYPEDEFS_TLS.with(|cell| f(cell.borrow().as_ref()))
}

/// §18.5.1: fill an `extern constraint name;` prototype with the body parsed
/// from an out-of-class `constraint Class::name { ... }` definition. Without
/// this the prototype stays empty and its constraints never reach the solver.
pub(super) fn install_ooc_constraint_body(
    elab: &mut ElaboratedModule,
    class_name: &str,
    constraint_name: &str,
    items: &[crate::ast::decl::ConstraintItem],
) {
    if items.is_empty() {
        return;
    }
    if let Some(cd) = elab
        .classes
        .get_mut(class_name)
        .map(std::sync::Arc::make_mut)
    {
        if let Some(existing) = cd.constraints.get_mut(constraint_name) {
            let existing = std::sync::Arc::make_mut(existing);
            existing.items = items.to_vec();
            existing.has_body = true;
        }
    }
}

pub fn elaborate_class(c: &ClassDeclaration) -> ElaboratedClass {
    elaborate_class_with_params(c, None)
}

/// §8.23 / §8.25.1: a class's constant declarations — header value
/// parameters, then body `localparam`/`parameter`s, in declaration order —
/// kept so a `C#(args)::N` reference outside the class can evaluate `N` for
/// that specialization.
pub(super) struct ClassConstDecl {
    /// Header parameter names (type and value) in order, for positional
    /// `#(...)` arguments.
    header_order: Vec<String>,
    /// Every value constant with its default initializer.
    values: Vec<(String, Option<Expression>)>,
    /// The base class (§8.13): its constants are visible through this
    /// class's scope too.
    extends: Option<String>,
    /// §8.25: the arguments the `extends Base#(...)` clause passes to the
    /// base, positional, evaluated in THIS class's parameter environment
    /// (`extends Base#(Q + 1)` reads the derived `Q`).
    extends_args: Vec<(Option<String>, Option<Expression>)>,
}

fn class_const_decl(c: &ClassDeclaration) -> ClassConstDecl {
    let mut header_order = Vec::new();
    let mut values = Vec::new();
    for p in &c.params {
        match &p.kind {
            ParameterKind::Data { assignments, .. } => {
                for a in assignments {
                    header_order.push(a.name.name.clone());
                    values.push((a.name.name.clone(), a.init.clone()));
                }
            }
            ParameterKind::Type { assignments } => {
                header_order.extend(assignments.iter().map(|a| a.name.name.clone()));
            }
        }
    }
    for item in &c.items {
        if let ClassItem::Parameter(pd) = item {
            if let ParameterKind::Data { assignments, .. } = &pd.kind {
                values.extend(
                    assignments
                        .iter()
                        .map(|a| (a.name.name.clone(), a.init.clone())),
                );
            }
        }
    }
    ClassConstDecl {
        header_order,
        values,
        extends: c.extends.as_ref().map(|e| e.name.name.clone()),
        extends_args: c
            .extends
            .as_ref()
            .map(|e| {
                e.args
                    .iter()
                    .map(|a| match a {
                        ParamValue::Expr(x) => (None, Some(x.clone())),
                        ParamValue::Type(_) => (None, None),
                    })
                    .collect()
            })
            .unwrap_or_default(),
    }
}

/// §8.13 / §8.23: the constants a class inherits — each ancestor's
/// registered `anc::N` value, nearest ancestor first, for the names the
/// class does not declare itself.
fn inherited_class_consts(
    c: &ClassDeclaration,
    params: &HashMap<String, Value>,
) -> Vec<(String, Value)> {
    let own: HashSet<String> = class_const_decl(c)
        .values
        .into_iter()
        .map(|v| v.0)
        .collect();
    let mut out: Vec<(String, Value)> = Vec::new();
    let mut cur = c.extends.as_ref().map(|e| e.name.name.clone());
    let mut guard = 0;
    while let Some(anc) = cur {
        guard += 1;
        let Some(decl) = CLASS_CONST_DECLS_TLS.with(|m| m.borrow().get(&anc).cloned()) else {
            break;
        };
        if guard > 64 {
            break;
        }
        for (n, _) in &decl.values {
            if own.contains(n) || out.iter().any(|(o, _)| o == n) {
                continue;
            }
            if let Some(v) = params
                .get(&format!("{}::{}", anc, n))
                .cloned()
                .or_else(|| param_fallback_get(&format!("{}::{}", anc, n)))
            {
                out.push((n.clone(), v));
            }
        }
        cur = decl.extends.clone();
    }
    out
}

/// §8.23: register a class's constants so a dimension or parameter outside
/// the class can name them through the class scope (`cls::N`,
/// `pkg::cls::N`, `Outer::Inner::N`). Each is stored in `elab.parameters`
/// under every scoped spelling; const-eval resolves a `::` chain against
/// those keys. A class with value parameters registers only its
/// declarations: its constants depend on the specialization, so
/// `C#(args)::N` evaluates them on demand (`class_spec_const`). Without
/// this, `rand logic [7:0] a[2 * model_c::BEATS]` elaborated to ZERO
/// elements (#316).
pub(super) fn register_class_consts(
    c: &ClassDeclaration,
    prefixes: &[String],
    elab: &mut ElaboratedModule,
) {
    for item in &c.items {
        if let ClassItem::Class(sub) = item {
            let mut nested: Vec<String> = prefixes
                .iter()
                .map(|p| format!("{}::{}", p, sub.name.name))
                .collect();
            nested.push(sub.name.name.clone());
            register_class_consts(sub, &nested, elab);
        }
    }
    let decl = class_const_decl(c);
    // §8.13: a base class's constants are reachable through the derived
    // class's scope (`der_c::B`).
    if c.extends.is_some() {
        for (n, v) in inherited_class_consts(c, &elab.parameters) {
            for pfx in prefixes {
                elab.set_param(line!(), format!("{}::{}", pfx, n), v.clone());
            }
        }
    }
    if !class_binds_values(c) {
        if c.extends.is_some() {
            CLASS_CONST_DECLS_TLS.with(|m| {
                m.borrow_mut().insert(c.name.name.clone(), Rc::new(decl));
            });
        }
        return;
    }
    if !class_has_value_params(c) {
        let consts = class_const_scope(c, Some(&elab.parameters));
        for (name, _) in &decl.values {
            let Some(v) = consts.get(name) else {
                continue;
            };
            for pfx in prefixes {
                elab.set_param(line!(), format!("{}::{}", pfx, name), v.clone());
            }
        }
    }
    CLASS_CONST_DECLS_TLS.with(|m| {
        m.borrow_mut().insert(c.name.name.clone(), Rc::new(decl));
    });
}

/// Register the constants of every `$unit` and package class before any
/// declaration is sized. Two passes: one class's constant may be defined
/// through another's (`localparam N = other_c::M`), and `defs` iterates in
/// hash order.
pub(super) fn hoist_class_consts(defs: &HashMap<String, Definition>, elab: &mut ElaboratedModule) {
    for _pass in 0..2 {
        for def in defs.values() {
            match def {
                Definition::Class(c) => {
                    register_class_consts(c, &[c.name.name.clone()], elab);
                }
                Definition::Package(p) => {
                    let has_class = p.items.iter().any(|i| {
                        matches!(i, PackageItem::Class(c) if class_binds_values(c)
                            || c.extends.is_some()
                            || c.items.iter().any(|ci| matches!(ci, ClassItem::Class(_))))
                    });
                    if !has_class {
                        continue;
                    }
                    let ov = overlay_pkg_params(p, elab);
                    for item in &p.items {
                        if let PackageItem::Class(c) = item {
                            let prefixes = [
                                format!("{}::{}", p.name.name, c.name.name),
                                c.name.name.clone(),
                            ];
                            register_class_consts(c, &prefixes, elab);
                        }
                    }
                    restore_overlay(elab, ov);
                }
                _ => {}
            }
        }
    }
}

/// §8.25.1: split a specialization's `#(...)` text (tokens joined by
/// spaces) into its arguments: `(Some(name), expr)` for `.name(expr)`,
/// `(None, expr)` for a positional one. A type argument does not parse as an
/// expression and yields `None` (its position still counts).
pub(super) fn parse_spec_args(text: &str) -> Vec<(Option<String>, Option<Expression>)> {
    let mut pieces: Vec<String> = Vec::new();
    let mut depth = 0i32;
    let mut cur = String::new();
    for ch in text.chars() {
        match ch {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            ',' if depth == 0 => {
                pieces.push(std::mem::take(&mut cur));
                continue;
            }
            _ => {}
        }
        cur.push(ch);
    }
    if !cur.trim().is_empty() || !pieces.is_empty() {
        pieces.push(cur);
    }
    pieces
        .into_iter()
        .map(|piece| {
            let t = piece.trim();
            if let Some(rest) = t.strip_prefix('.') {
                let rest = rest.trim_start();
                let (name, body) = match rest.find('(') {
                    Some(i) => (rest[..i].trim(), rest[i + 1..].trim_end()),
                    None => (rest.trim(), ""),
                };
                let body = body.strip_suffix(')').unwrap_or(body).trim();
                let e = (!body.is_empty())
                    .then(|| crate::parse_override_value(body))
                    .flatten();
                (Some(name.to_string()), e)
            } else {
                (None, crate::parse_override_value(t))
            }
        })
        .collect()
}

/// §8.25.1: constant `member` of the specialization `cls#(text)`: the header
/// parameters take the arguments (evaluated in the referencing scope), the
/// rest their defaults, and the body constants follow from them.
fn class_spec_const<P: ParamLookup>(
    cls: &str,
    args: &[(Option<String>, Option<Expression>)],
    member: &str,
    params: &P,
) -> Option<Value> {
    let mut consts = Vec::new();
    class_spec_consts(cls, args, &params.to_hashmap(), 0, &mut consts)?;
    consts
        .into_iter()
        .rev()
        .find(|(n, _)| n == member)
        .map(|(_, v)| v)
}

/// §8.25 / §8.13: every constant of the specialization `cls#(args)`, the
/// base chain's first (nearest ancestor last), each evaluated in its own
/// class's environment. The derived class's header parameters are bound
/// from `args`; the base's from the `extends Base#(...)` arguments, which
/// read the derived environment (`extends A#(Q + 1)`). A body constant
/// that names an inherited one (`LPB = Q + LPA`) sees the base's value for
/// THIS specialization, not the base's default.
pub(super) fn class_spec_consts(
    cls: &str,
    args: &[(Option<String>, Option<Expression>)],
    params: &HashMap<String, Value>,
    depth: usize,
    out: &mut Vec<(String, Value)>,
) -> Option<()> {
    if depth > 64 {
        return None;
    }
    let decl = CLASS_CONST_DECLS_TLS.with(|m| m.borrow().get(cls).cloned())?;
    let mut overrides: HashMap<String, Value> = HashMap::default();
    for (i, (name, e)) in args.iter().enumerate() {
        let Some(e) = e else {
            continue;
        };
        let pname = match name {
            Some(n) => n.clone(),
            None => match decl.header_order.get(i) {
                Some(n) => n.clone(),
                None => continue,
            },
        };
        overrides.insert(pname, eval_const_expr_val_inner(e, params, &mut const_context::Types::default()));
    }
    // Header parameters first: the base's arguments may read them.
    let mut env = params.clone();
    let mut own: Vec<(String, Value)> = Vec::new();
    let header_count = decl
        .values
        .iter()
        .take_while(|(n, _)| decl.header_order.contains(n))
        .count();
    for (n, init) in &decl.values[..header_count] {
        let v = match (overrides.remove(n), init) {
            (Some(v), _) => v,
            (None, Some(init)) => eval_const_expr_val(init, &env),
            (None, None) => continue,
        };
        env.insert(n.clone(), v.clone());
        own.push((n.clone(), v));
    }
    if let Some(base) = &decl.extends {
        let mut inherited = Vec::new();
        if class_spec_consts(base, &decl.extends_args, &env, depth + 1, &mut inherited).is_some() {
            for (n, v) in &inherited {
                env.insert(n.clone(), v.clone());
            }
            out.extend(inherited);
        }
    }
    for (n, init) in &decl.values[header_count..] {
        let v = match (overrides.remove(n), init) {
            (Some(v), _) => v,
            (None, Some(init)) => eval_const_expr_val(init, &env),
            (None, None) => continue,
        };
        env.insert(n.clone(), v.clone());
        own.push((n.clone(), v));
    }
    out.extend(own);
    Some(())
}

/// §8.23 / §8.25.1: the value of a class-scoped constant reference
/// `base::member` — `C::N`, `pkg::C::N`, `Outer::Inner::N` or `C#(args)::N`
/// — or `None` when `base` names no registered class scope.
pub(super) fn class_scoped_const<P: ParamLookup>(
    base: &Expression,
    member: &str,
    params: &P,
) -> Option<Value> {
    fn walk<'a>(e: &'a Expression, segs: &mut Vec<&'a str>) -> bool {
        match &e.kind {
            ExprKind::Ident(h) if h.path.iter().all(|s| s.selects.is_empty()) => {
                segs.extend(h.path.iter().map(|s| s.name.name.as_str()));
                true
            }
            ExprKind::MemberAccess { expr, member } => {
                walk(expr, segs) && {
                    segs.push(member.name.as_str());
                    true
                }
            }
            _ => false,
        }
    }
    let mut segs: Vec<&str> = Vec::new();
    if let ExprKind::Specialization {
        base: inner,
        type_args_text,
    } = &base.kind
    {
        if !walk(inner, &mut segs) {
            return None;
        }
        let args = parse_spec_args(type_args_text);
        return class_spec_const(segs.last()?, &args, member, params);
    }
    if !walk(base, &mut segs) || segs.is_empty() {
        return None;
    }
    let lookup = |k: &str| params.get(k).cloned().or_else(|| param_fallback_get(k));
    lookup(&format!("{}::{}", segs.join("::"), member))
        .or_else(|| {
            (segs.len() >= 2)
                .then(|| lookup(&format!("{}::{}", segs[segs.len() - 1], member)))
                .flatten()
        })
        .or_else(|| class_spec_const(segs.last()?, &[], member, params))
}

/// §8.23: `[cls::N]` — like `[N]` — parses as an associative dimension
/// keyed by a "type" named `cls::N` (the parser cannot tell a type from a
/// constant). The constant's value when the scoped name is a registered
/// class-scoped (or package) constant rather than a typedef.
fn scoped_type_name_const(name: &TypeName, params: &dyn ParamLookup) -> Option<Value> {
    if name.scopes.is_empty() {
        return None;
    }
    let mut chain: Vec<&str> = name.scopes.iter().map(|s| s.name.name.as_str()).collect();
    chain.push(name.name.name.as_str());
    let joined = chain.join("::");
    let leaf2 = chain[chain.len() - 2..].join("::");
    if typedefs_snapshot(|td| td.is_some_and(|t| t.contains_key(&joined) || t.contains_key(&leaf2)))
    {
        return None;
    }
    let last = name.scopes.last()?;
    if !last.type_args.is_empty() || name.scopes.iter().any(|s| !s.type_args.is_empty()) {
        let args: Vec<(Option<String>, Option<Expression>)> = last
            .type_args
            .iter()
            .map(|e| match &e.kind {
                ExprKind::NamedArg { name, expr } => {
                    (Some(name.name.clone()), expr.as_deref().cloned())
                }
                _ => (None, Some(e.clone())),
            })
            .collect();
        return class_spec_const(&last.name.name, &args, &name.name.name, &params);
    }
    let lookup = |k: &str| params.get(k).cloned().or_else(|| param_fallback_get(k));
    lookup(&joined)
        .or_else(|| lookup(&leaf2))
        // `C#()::N` keeps no args on its scope link: the default
        // specialization of a class with value parameters.
        .or_else(|| class_spec_const(&last.name.name, &[], &name.name.name, &params))
}

/// Rewrite an associative-looking `[cls::N]` dimension (see
/// [`scoped_type_name_const`]) to the fixed size it names; `None` when the
/// dimension has another shape or the name is no such constant.
pub(super) fn scoped_const_dim(
    d: &UnpackedDimension,
    params: &dyn ParamLookup,
) -> Option<UnpackedDimension> {
    let UnpackedDimension::Associative {
        data_type: Some(dt),
        span,
    } = d
    else {
        return None;
    };
    let DataType::TypeReference {
        name, dimensions, ..
    } = dt.as_ref()
    else {
        return None;
    };
    if !dimensions.is_empty() {
        return None;
    }
    let n = scoped_type_name_const(name, params)?.to_i64()?;
    Some(UnpackedDimension::Expression {
        expr: Box::new(int_literal(n, *span)),
        span: *span,
    })
}

/// A decimal integer literal expression for a folded constant.
pub(super) fn int_literal(n: i64, span: Span) -> Expression {
    Expression::new(
        ExprKind::Number(NumberLiteral::Integer {
            size: None,
            signed: true,
            base: NumberBase::Decimal,
            value: n.to_string(),
            cached_val: Default::default(),
        }),
        span,
    )
}

/// Fold `PackedDimension::Range` bounds to integer literals where `pred`
/// accepts the range and the bounds require `params` to evaluate (so ranges
/// that are already plain literals are untouched). Used for package typedefs
/// (whose imported parameters are not in the importer's bare parameter map)
/// and for class properties/typedefs sized by enclosing or localparam constants
/// rather than overridable class header parameters.
pub(super) fn fold_packed_dims_with(
    dt: &DataType,
    params: &HashMap<String, Value>,
    pred: &dyn Fn(&Expression, &Expression) -> bool,
) -> Option<DataType> {
    let lit = |n: i64, span: Span| Box::new(int_literal(n, span));
    let fold_dims = |dims: &[PackedDimension]| -> Option<Vec<PackedDimension>> {
        let mut out: Option<Vec<PackedDimension>> = None;
        for (i, d) in dims.iter().enumerate() {
            if let PackedDimension::Range { left, right, span } = d
                && pred(left, right)
                && (const_eval_i64_with_params(left, None).is_none()
                    || const_eval_i64_with_params(right, None).is_none())
                && let (Some(l), Some(r)) = (
                    const_eval_i64_with_params(left, Some(params)),
                    const_eval_i64_with_params(right, Some(params)),
                )
            {
                out.get_or_insert_with(|| dims.to_vec())[i] = PackedDimension::Range {
                    left: lit(l, left.span),
                    right: lit(r, right.span),
                    span: *span,
                };
            }
        }
        out
    };
    match dt {
        DataType::IntegerVector {
            kind,
            signing,
            dimensions,
            span,
        } => fold_dims(dimensions).map(|dimensions| DataType::IntegerVector {
            kind: *kind,
            signing: *signing,
            dimensions,
            span: *span,
        }),
        DataType::Implicit {
            signing,
            dimensions,
            span,
        } => fold_dims(dimensions).map(|dimensions| DataType::Implicit {
            signing: *signing,
            dimensions,
            span: *span,
        }),
        DataType::TypeReference { dimensions, .. } => fold_dims(dimensions).map(|dims| {
            let mut copy = dt.clone();
            if let DataType::TypeReference { dimensions, .. } = &mut copy {
                *dimensions = dims;
            }
            copy
        }),
        DataType::Struct(su) => {
            let mut out = fold_dims(&su.dimensions).map(|dims| {
                let mut s = su.clone();
                s.dimensions = dims;
                s
            });
            for (mi, m) in su.members.iter().enumerate() {
                if let Some(inner) = fold_packed_dims_with(&m.data_type, params, pred) {
                    out.get_or_insert_with(|| su.clone()).members[mi].data_type = inner;
                }
            }
            out.map(DataType::Struct)
        }
        DataType::Enum(et) => {
            let mut out = fold_dims(&et.dimensions).map(|dims| {
                let mut e = et.clone();
                e.dimensions = dims;
                e
            });
            if let Some(base) = &et.base_type
                && let Some(inner) = fold_packed_dims_with(base, params, pred)
            {
                out.get_or_insert_with(|| et.clone()).base_type = Some(Box::new(inner));
            }
            out.map(DataType::Enum)
        }
        _ => None,
    }
}

pub(super) fn fold_unpacked_dims(
    dims: &[UnpackedDimension],
    params: &HashMap<String, Value>,
    typedef_types: &HashMap<String, DataType>,
) -> Vec<UnpackedDimension> {
    let lit = |n: i64, span: Span| Box::new(int_literal(n, span));
    normalize_unpacked_dims(dims, params, typedef_types)
        .into_iter()
        .map(|d| match d {
            UnpackedDimension::Expression { expr, span }
                if const_eval_i64_with_params(&expr, None).is_none() =>
            {
                match const_eval_i64_with_params(&expr, Some(params)) {
                    Some(n) => UnpackedDimension::Expression {
                        expr: lit(n, expr.span),
                        span,
                    },
                    None => UnpackedDimension::Expression { expr, span },
                }
            }
            UnpackedDimension::Range { left, right, span }
                if const_eval_i64_with_params(&left, None).is_none()
                    || const_eval_i64_with_params(&right, None).is_none() =>
            {
                match (
                    const_eval_i64_with_params(&left, Some(params)),
                    const_eval_i64_with_params(&right, Some(params)),
                ) {
                    (Some(l), Some(r)) => UnpackedDimension::Range {
                        left: lit(l, left.span),
                        right: lit(r, right.span),
                        span,
                    },
                    _ => UnpackedDimension::Range { left, right, span },
                }
            }
            other => other,
        })
        .collect()
}

/// §7.4.2 / §8.23: an unpacked STRUCT member `m[N]` / `m[cls::N]` parses
/// with an associative dimension keyed by a "type" `N` (see
/// `normalize_unpacked_dims`); a struct type records it so, and every later
/// reader took the member for an associative array — `$size` read 0 and the
/// width came out one element. Size such dimensions where the typedef is
/// recorded. `None` when nothing changes.
pub(super) fn size_struct_member_dims(
    dt: &DataType,
    params: &HashMap<String, Value>,
    typedef_types: &HashMap<String, DataType>,
    class_scope: bool,
) -> Option<DataType> {
    let DataType::Struct(su) = dt else {
        return None;
    };
    let lit = |n: i64, span: Span| Box::new(int_literal(n, span));
    // One dimension folded to literals when it needs `params` to size.
    let fold = |d: &UnpackedDimension| -> Option<UnpackedDimension> {
        match d {
            // Outside a class only a SCOPED name (`cls::N`, `pkg::N`) is
            // folded: it is one constant design-wide, while a bare module
            // parameter may differ per instance and is sized where used.
            UnpackedDimension::Associative {
                data_type: Some(dt),
                ..
            } if class_scope
                || matches!(dt.as_ref(), DataType::TypeReference { name, .. }
                    if !name.scopes.is_empty()) =>
            {
                match normalize_unpacked_dims(std::slice::from_ref(d), params, typedef_types)
                    .pop()?
                {
                    UnpackedDimension::Expression { expr, span } => {
                        let n = const_eval_i64_with_params(&expr, Some(params))?;
                        Some(UnpackedDimension::Expression {
                            expr: lit(n, expr.span),
                            span,
                        })
                    }
                    _ => None,
                }
            }
            UnpackedDimension::Expression { expr, span }
                if class_scope && const_eval_i64_with_params(expr, None).is_none() =>
            {
                let n = const_eval_i64_with_params(expr, Some(params))?;
                Some(UnpackedDimension::Expression {
                    expr: lit(n, expr.span),
                    span: *span,
                })
            }
            UnpackedDimension::Range { left, right, span }
                if class_scope
                    && (const_eval_i64_with_params(left, None).is_none()
                        || const_eval_i64_with_params(right, None).is_none()) =>
            {
                let l = const_eval_i64_with_params(left, Some(params))?;
                let r = const_eval_i64_with_params(right, Some(params))?;
                Some(UnpackedDimension::Range {
                    left: lit(l, left.span),
                    right: lit(r, right.span),
                    span: *span,
                })
            }
            _ => None,
        }
    };
    let mut out: Option<StructUnionType> = None;
    for (mi, m) in su.members.iter().enumerate() {
        if let Some(inner) =
            size_struct_member_dims(&m.data_type, params, typedef_types, class_scope)
        {
            out.get_or_insert_with(|| su.clone()).members[mi].data_type = inner;
        }
        for (di, d) in m.declarators.iter().enumerate() {
            for (k, dim) in d.dimensions.iter().enumerate() {
                if let Some(f) = fold(dim) {
                    out.get_or_insert_with(|| su.clone()).members[mi].declarators[di].dimensions
                        [k] = f;
                }
            }
        }
    }
    out.map(DataType::Struct)
}

/// Collect the constant bindings visible to a class's own declarations:
/// the enclosing scope's parameters (module / package / `$unit`) overlaid
/// with the class's own value parameters and body `localparam`s, each
/// evaluated in declaration order so a later default may reference an
/// earlier one (§6.20.2).
///
/// Without this, `class box #(parameter int W = 8); bit [W-1:0] data;` sized
/// `data` with NO parameters in scope: `const_eval_i64_with_params` returned
/// `None` for `W-1`, `resolve_type_width` silently skipped the dimension, and
/// the property came out **1 bit** — truncating every store through
/// `fit_class_prop` and reporting `$bits() == 1`. The same held for any
/// module/package/`$unit` parameter used in a class property's packed range.
/// Keep only directly mentioned outer bindings when all dimensions/defaults
/// are self-contained. §6.20/§8.13: inheritance, calls and named types can
/// read hidden declarations and deliberately retain the complete environment.
pub(super) fn class_enclosing_scope(
    c: &ClassDeclaration,
    scope_params: Option<&HashMap<String, Value>>,
) -> HashMap<String, Value> {
    let Some(scope) = scope_params else { return HashMap::default() };
    let reads = c.extends.is_none()
        .then(|| crate::unit_subroutine_usage::direct_parameter_reads(c))
        .flatten();
    let Some(reads) = reads else { return scope.clone() };
    scope.iter().filter(|(name, _)| {
        reads.contains(name.as_str())
            || name.split(['.', ':', '[', ']']).any(|part| reads.contains(part))
    }).map(|(name, value)| (name.clone(), value.clone())).collect()
}

pub(super) fn class_const_scope(
    c: &ClassDeclaration,
    scope_params: Option<&HashMap<String, Value>>,
) -> HashMap<String, Value> {
    let mut params = class_enclosing_scope(c, scope_params);
    // §8.13: inherited constants, overridden below by the class's own.
    if c.extends.is_some() {
        for (n, v) in inherited_class_consts(c, &params) {
            params.insert(n, v);
        }
    }
    let mut bind = |name: &str, init: Option<&crate::ast::expr::Expression>| {
        // A parameter with no default (`#(parameter int W)`) contributes
        // nothing — leave it unbound so the dimension stays unresolved
        // rather than silently binding zero.
        if let Some(init) = init {
            let v = eval_const_expr_val(init, &params);
            params.insert(name.to_string(), v);
        }
    };
    for p in &c.params {
        if let crate::ast::decl::ParameterKind::Data { assignments, .. } = &p.kind {
            for a in assignments {
                bind(&a.name.name, a.init.as_ref());
            }
        }
    }
    // Class-body `localparam`s are class constants and may be used to size a
    // property declared after them.
    for item in &c.items {
        if let ClassItem::Parameter(pd) = item {
            if let crate::ast::decl::ParameterKind::Data { assignments, .. } = &pd.kind {
                for a in assignments {
                    bind(&a.name.name, a.init.as_ref());
                }
            }
        }
    }
    params
}

/// Elaborate a class, sizing its declarations against `scope_params` (the
/// enclosing module/package parameter map) in addition to the class's own
/// parameters. Callers without a parameter map in scope use
/// [`elaborate_class`].
pub fn elaborate_class_with_params(
    c: &ClassDeclaration,
    scope_params: Option<&HashMap<String, Value>>,
) -> ElaboratedClass {
    // §8.25: the generic declaration is its default specialization, so a type
    // parameter stands for its DEFAULT type — `$bits(T)` in a class constant
    // (`localparam M = {$bits(T) - 1{1'b1}};`) reads that type's width.
    // Unbound it read 0, and `0 - 1` replicated ~4 G bits.
    let type_defaults: Vec<(String, u32)> = typedefs_snapshot(|td| {
        let mut v = Vec::new();
        for p in &c.params {
            if let crate::ast::decl::ParameterKind::Type { assignments } = &p.kind {
                for a in assignments {
                    if let Some(dt) = &a.init {
                        v.push((
                            a.name.name.clone(),
                            resolve_type_width(dt, scope_params, td),
                        ));
                    }
                }
            }
        }
        v
    });
    if type_defaults.is_empty() {
        return elaborate_class_in_scope(c, scope_params);
    }
    let mut table = typedefs_snapshot(|td| td.cloned()).unwrap_or_default();
    table.extend(type_defaults);
    with_typedefs_owned(table, || elaborate_class_in_scope(c, scope_params))
}

/// Whether a class header declares a VALUE parameter (`class C #(int W)`):
/// its constants then depend on the specialization.
pub(super) fn class_has_value_params(c: &ClassDeclaration) -> bool {
    c.params
        .iter()
        .any(|p| matches!(p.kind, ParameterKind::Data { .. }))
}

/// Whether a class binds any VALUE parameter or body `localparam` of its own
/// — otherwise its constant scope is exactly the enclosing one.
pub(super) fn class_binds_values(c: &ClassDeclaration) -> bool {
    c.params
        .iter()
        .any(|p| matches!(p.kind, crate::ast::decl::ParameterKind::Data { .. }))
        || c.items.iter().any(|item| {
            matches!(item, ClassItem::Parameter(pd)
                if matches!(pd.kind, crate::ast::decl::ParameterKind::Data { .. }))
        })
}

/// The target of the class-local typedef chain `t` names (`mem_addr_t` in
/// `logic [7:0] m[mem_addr_t]`), at most `n` aliases deep, so its width follows
/// this class's parameters (§6.18, §8.25); `t` itself for any other type.
fn class_local_typedef_target<'a>(c: &'a ClassDeclaration, t: &'a DataType, n: u8) -> &'a DataType {
    if let DataType::TypeReference {
        name,
        dimensions,
        type_args,
        ..
    } = t
        && n > 0
        && dimensions.is_empty()
        && type_args.is_empty()
        && !name.has_scope()
    {
        for item in &c.items {
            if let ClassItem::Typedef(td) = item
                && td.name.name == name.name.name
                && td.dimensions.is_empty()
            {
                return class_local_typedef_target(c, &td.data_type, n - 1);
            }
        }
    }
    t
}

fn expr_names_any(e: &Expression, names: &HashSet<String>) -> bool {
    let mut hit = false;
    for_each_sub_expr(e, &mut |x| {
        hit |= matches!(&x.kind, ExprKind::Ident(h)
            if h.path.len() == 1 && names.contains(&h.path[0].name.name));
    });
    hit
}

/// Whether a range depends on a header parameter, also through a constant
/// function (`$clog2(N)`) or a class-body localparam (§8.25, §6.20.1).
pub(super) fn range_refs_class_header_param(
    c: &ClassDeclaration,
    l: &Expression,
    r: &Expression,
) -> bool {
    let mut params = HashSet::default();
    c.params.iter().for_each(|p| decl_param_names(p, &mut params));
    for item in &c.items {
        if let ClassItem::Parameter(pd) = item
            && let ParameterKind::Data { assignments, .. } = &pd.kind
        {
            for a in assignments {
                if a.init.as_ref().is_some_and(|e| expr_names_any(e, &params)) {
                    params.insert(a.name.name.clone());
                }
            }
        }
    }
    expr_names_any(l, &params) || expr_names_any(r, &params)
}

/// The unpacked dimensions a class property's element typedef adds after
/// the declarator's own (§7.4.5): the class's typedef of that name, else an
/// enclosing module, `$unit` or package typedef (`p::q_t qq[$];`, §26.3).
/// Empty for any other type.
fn typedef_row_dims(
    data_type: &DataType,
    local_typedef_dims: &HashMap<String, Vec<UnpackedDimension>>,
) -> Vec<UnpackedDimension> {
    let DataType::TypeReference {
        name, dimensions, ..
    } = data_type
    else {
        return Vec::new();
    };
    if !dimensions.is_empty() {
        return Vec::new();
    }
    name.scopes
        .is_empty()
        .then(|| local_typedef_dims.get(&name.name.name).cloned())
        .flatten()
        .or_else(|| TYPEDEF_SHAPES_TLS.with(|c| lookup_scoped_type(name, &c.borrow().1).cloned()))
        .unwrap_or_default()
}

fn elaborate_class_in_scope(
    c: &ClassDeclaration,
    scope_params: Option<&HashMap<String, Value>>,
) -> ElaboratedClass {
    // Both scopes below start from a copy of the enclosing parameters; a
    // class that binds nothing of its own (most of them) borrows those
    // parameters instead of copying the whole map twice.
    let empty_scope: HashMap<String, Value>;
    let enclosing: &HashMap<String, Value> = match scope_params {
        Some(p) => p,
        None => {
            empty_scope = HashMap::default();
            &empty_scope
        }
    };
    // §8.13: constants inherited from a base class size declarations too.
    let inherited = if c.extends.is_some() {
        inherited_class_consts(c, enclosing)
    } else {
        Vec::new()
    };
    let binds_values = class_binds_values(c) || !inherited.is_empty();
    let owned_const_scope: HashMap<String, Value>;
    let const_scope: &HashMap<String, Value> = if binds_values {
        owned_const_scope = class_const_scope(c, scope_params);
        &owned_const_scope
    } else {
        enclosing
    };
    let class_params = Some(const_scope);
    // Scope for sizing UNPACKED dimensions (`bit [7:0] mem [N];`): the
    // enclosing scope's parameters plus class-body localparams — both fixed
    // per class. Header VALUE parameters are deliberately EXCLUDED: they can
    // differ per specialization, and one ElaboratedClass records one array
    // shape, so sizing from the default would give an overridden
    // specialization a wrong FIXED size. Such properties stay queue-backed
    // (indexing works; `size()`/`foreach` see the pushed elements only).
    let owned_unpacked_scope: HashMap<String, Value>;
    let unpacked_scope: &HashMap<String, Value> = if !class_has_value_params(c) {
        // §8.25/§6.20: only header value parameters distinguish these scopes.
        // Localparam-only and inherited-constant classes can reuse the same
        // evaluated bindings rather than copy every enclosing parameter twice.
        const_scope
    } else {
        owned_unpacked_scope = {
            let mut m = class_enclosing_scope(c, scope_params);
            m.extend(inherited.iter().cloned());
            for item in &c.items {
                if let ClassItem::Parameter(pd) = item {
                    if let crate::ast::decl::ParameterKind::Data { assignments, .. } = &pd.kind {
                        for a in assignments {
                            if let Some(init) = &a.init {
                                let v = eval_const_expr_val(init, &m);
                                m.insert(a.name.name.clone(), v);
                            }
                        }
                    }
                }
            }
            m
        };
        &owned_unpacked_scope
    };
    let unpacked_params = Some(unpacked_scope);
    // Declared type of each property, retained so the runtime can re-size a
    // property whose packed range depends on a class parameter for a
    // specialization other than the default (`box#(16)` vs `box#(8)`).
    // `Signal::width` below holds the DEFAULT-specialization width.
    let mut property_types: HashMap<String, DataType> = HashMap::default();
    let mut properties = HashMap::default();
    let mut property_order: Vec<String> = Vec::new();
    let mut string_properties: HashSet<String> = HashSet::default();
    let mut methods = HashMap::default();
    let mut random_properties = HashSet::default();
    let mut randc_properties = HashSet::default();
    let mut protected_properties = HashSet::default();
    let mut local_properties = HashSet::default();
    let mut virtual_iface_properties: HashMap<String, (String, Option<String>)> =
        HashMap::default();
    let mut static_properties = HashSet::default();
    let mut static_methods = HashSet::default();
    let mut assoc_properties: HashMap<String, bool> = HashMap::default();
    let mut assoc_key_types: HashMap<String, String> = HashMap::default();
    let mut assoc_index_props: HashMap<String, (u32, bool)> = HashMap::default();
    let mut assoc_key_decl_types: HashMap<String, DataType> = HashMap::default();
    let mut queue_properties: HashMap<String, (u32, Option<u32>)> = HashMap::default();
    let mut queue_property_names = HashSet::default();
    let mut array_properties: HashMap<String, (i64, i64, u32)> = HashMap::default();
    let mut param_sized_props: HashMap<String, Vec<UnpackedDimension>> = HashMap::default();
    let mut array_nd_properties: HashMap<String, (Vec<(i64, i64)>, u32)> = HashMap::default();
    let mut array_of_coll_properties: HashMap<String, (Vec<(i64, i64)>, u32, CollDimKind)> =
        HashMap::default();
    let mut dynamic_assoc_properties: HashMap<String, Vec<UnpackedDimension>> = HashMap::default();
    let mut dynamic_tail_properties: HashMap<String, Vec<UnpackedDimension>> = HashMap::default();
    let mut prop_coll_shapes: HashMap<String, CollShape> = HashMap::default();
    let mut array_prop_decl_dims: HashMap<String, Vec<(i64, i64)>> = HashMap::default();
    let mut property_type_args: HashMap<String, Vec<Expression>> = HashMap::default();
    let mut static_collections: Vec<(String, bool, u32)> = Vec::new();
    let mut static_assoc_key_types: HashMap<String, String> = HashMap::default();
    let mut static_assoc_index_props: HashMap<String, (u32, bool)> = HashMap::default();
    let mut static_fixed_arrays: Vec<(String, i64, i64, u32)> = Vec::new();
    let mut property_inits: HashMap<String, crate::ast::expr::Expression> = HashMap::default();
    let mut constraints = HashMap::default();
    // Class-local typedefs carrying unpacked dimensions
    // (`typedef bit edges_t[uvm_phase];`). A property `edges_t m;` inherits
    // these so it's classified as an associative/queue/array member
    // (IEEE 1800-2017 §6.18). UVM's phase graph (`edges_t m_successors`,
    // `m_predecessors`) relies on this.
    let mut local_typedef_dims: HashMap<String, Vec<UnpackedDimension>> = HashMap::default();
    for item in &c.items {
        if let ClassItem::Typedef(td) = item {
            if !td.dimensions.is_empty() {
                local_typedef_dims.insert(td.name.name.clone(), td.dimensions.clone());
            }
        }
    }
    for item in &c.items {
        match item {
            ClassItem::Property(p) => {
                // Resolve against the typedef table, not `None`. A property
                // declared with a typedef'd type (`u2_t v;`) hits
                // `resolve_type_width`'s TypeReference branch, which returns a
                // flat 32 when it has no table — so every such property was
                // recorded 32 bits wide however narrow its type.
                // §6.18, §8.25: a type the class itself declares is sized by
                // its declaration in the class's constant scope. The bare
                // typedef table was sized in the enclosing scope, which has
                // no class `localparam`, so `typedef logic [W-1:0] t;` read
                // one bit there.
                let width_dt = class_local_typedef_target(c, &p.data_type, u8::MAX);
                let width = typedefs_snapshot(|td| resolve_type_width(width_dt, class_params, td));
                // §6.20.3 / §6.18: a body type alias retains its signedness.
                let is_signed = TYPEDEF_SHAPES_TLS
                    .with(|types| is_type_signed_resolved(&p.data_type, &types.borrow().0));
                let is_rand = p.qualifiers.contains(&ClassQualifier::Rand)
                    || p.qualifiers.contains(&ClassQualifier::Randc);
                let is_randc = p.qualifiers.contains(&ClassQualifier::Randc);
                let is_static = p.qualifiers.contains(&ClassQualifier::Static);
                let _is_const = p.qualifiers.contains(&ClassQualifier::Const);
                let is_virtual_iface = p.qualifiers.contains(&ClassQualifier::Virtual);
                let virtual_iface_info: Option<(String, Option<String>)> = if is_virtual_iface {
                    // `virtual <iface_t> name;` parses as TypeReference;
                    // `virtual <iface_t>.<modport> name;` parses as
                    // DataType::Interface { name, modport }.
                    match &p.data_type {
                        DataType::Interface { name, modport, .. } => {
                            Some((name.name.clone(), modport.as_ref().map(|m| m.name.clone())))
                        }
                        _ => get_type_name(&p.data_type).map(|n| (n, None)),
                    }
                } else {
                    None
                };
                // §6.18: a property of a typedef'd real type is a real, whether
                // the class or an enclosing scope declares the alias. A name
                // the class header rebinds (a type parameter, §8.25) is
                // decided by the specialization at run time.
                let is_real = match width_dt {
                    DataType::TypeReference { name, .. } if !name.has_scope() && {
                        let mut header = HashSet::default();
                        c.params.iter().for_each(|p| decl_param_names(p, &mut header));
                        header.contains(&name.name.name)
                    } =>
                    {
                        false
                    }
                    _ => TYPEDEF_SHAPES_TLS
                        .with(|types| is_type_real_resolved(width_dt, &types.borrow().0)),
                };
                // Named types (class handles, enums, typedefs) default to
                // 0 — a class handle's default is `null`.
                let is_named_type = get_type_name(&p.data_type).is_some();
                for decl in &p.declarators {
                    // A property typed by an unpacked-dimension typedef
                    // (`edges_t m;`) inherits the typedef's dims when it
                    // declares none of its own.
                    let effective_dims: Vec<UnpackedDimension> = if decl.dimensions.is_empty() {
                        match &p.data_type {
                            DataType::TypeReference { name, .. } => local_typedef_dims
                                .get(&name.name.name)
                                .cloned()
                                .unwrap_or_default(),
                            _ => Vec::new(),
                        }
                    } else {
                        // §7.4.5: with dimensions of its own (`q_t qq[$];`)
                        // they come first, then the typedef's — from the
                        // class's typedefs, else the enclosing scope's — as
                        // at module scope. The typedef's were dropped, so the
                        // rows of `qq` held one scalar each.
                        let mut d = decl.dimensions.clone();
                        d.extend(typedef_row_dims(&p.data_type, &local_typedef_dims));
                        d
                    };
                    if matches!(
                        effective_dims.first(),
                        Some(UnpackedDimension::Queue { .. })
                    ) {
                        queue_property_names.insert(decl.name.name.clone());
                    }
                    // `mem[N]` parses as an ASSOCIATIVE dimension keyed by
                    // "type N" (a bare identifier before `]` reads as a type).
                    // When `N` is a known constant and NOT a typedef, rewrite
                    // it to a fixed dimension — the class-property twin of
                    // `normalize_unpacked_dims`. Without this the property was
                    // classified associative/queue-backed: indexing worked but
                    // `size()` lied and `foreach` iterated ZERO times.
                    let effective_dims: Vec<UnpackedDimension> = effective_dims
                        .into_iter()
                        .map(|d| match d {
                            UnpackedDimension::Associative {
                                data_type: Some(dt),
                                span,
                            } => {
                                // §8.23: `[cls::N]` names a class constant.
                                if let Some(fixed) = scoped_const_dim(
                                    &UnpackedDimension::Associative {
                                        data_type: Some(dt.clone()),
                                        span,
                                    },
                                    const_scope,
                                ) {
                                    return fixed;
                                }
                                if let DataType::TypeReference { name, .. } = dt.as_ref() {
                                    let n = name.name.name.clone();
                                    let is_type = typedefs_snapshot(|td| {
                                        td.is_some_and(|t| t.contains_key(&n))
                                    });
                                    // §8.25: a header VALUE parameter (`int
                                    // items[N]` in `class C #(int N)`) sizes a
                                    // fixed dimension too; see
                                    // `param_sized_props`.
                                    if !is_type && const_scope.contains_key(&n) {
                                        return UnpackedDimension::Expression {
                                            expr: Box::new(make_ident_expr(&n)),
                                            span,
                                        };
                                    }
                                }
                                UnpackedDimension::Associative {
                                    data_type: Some(dt),
                                    span,
                                }
                            }
                            other => other,
                        })
                        .collect();
                    // Track virtual-interface properties for L4 binding +
                    // late-dispatch. See the comment on
                    // `ElaboratedClass::virtual_iface_properties`.
                    if let Some(info) = &virtual_iface_info {
                        virtual_iface_properties.insert(decl.name.name.clone(), info.clone());
                    }
                    // Retained for per-specialization re-sizing; see
                    // `ElaboratedClass::property_types`. Fold any packed
                    // ranges that do not depend on a class header parameter
                    // so imported package constants (`bit [AW-1:0] p;`) do
                    // not remain raw identifiers at runtime.
                    let prop_dt = fold_packed_dims_with(
                        &p.data_type,
                        const_scope,
                        &|l, r| !range_refs_class_header_param(c, l, r),
                    )
                    .unwrap_or_else(|| p.data_type.clone());
                    property_types.insert(decl.name.name.clone(), prop_dt);
                    // Static member collections share one global store; route
                    // them out of the per-instance maps.
                    if is_static {
                        // Second field is `is_associative` (NOT key-is-string).
                        match effective_dims.first() {
                            Some(UnpackedDimension::Associative {
                                data_type: key_dt, ..
                            }) => {
                                static_collections.push((
                                    decl.name.name.clone(),
                                    true,
                                    width.max(1),
                                ));
                                // §7.8.2: record the static assoc member's KEY
                                // type in `static_assoc_key_types` (a plain
                                // `string` is recorded as the literal "string").
                                // This lets the runtime hash/store string keys
                                // as strings and iterate/foreach them correctly.
                                static_assoc_key_types.insert(
                                    decl.name.name.clone(),
                                    match key_dt.as_deref() {
                                        Some(DataType::TypeReference { name: kt, .. }) => {
                                            kt.name.name.clone()
                                        }
                                        Some(DataType::Simple {
                                            kind: SimpleType::String,
                                            ..
                                        }) => "string".to_string(),
                                        _ => "int".to_string(),
                                    },
                                );
                                // §7.8.2: record the static assoc member's
                                // INDEX width + signedness (skipping a plain
                                // string key — the full text key is handled
                                // by the string branch). Mirrors the per-
                                // instance `assoc_index_props` recording below
                                // but in the STATIC-specific map.
                                if let Some(kdt) = key_dt.as_ref() {
                                    if !matches!(
                                        kdt.as_ref(),
                                        DataType::Simple {
                                            kind: SimpleType::String,
                                            ..
                                        }
                                    ) {
                                        // A typedef'd key (`k12_t`) resolves through the
                                        // installed typedef table; without it the
                                        // index width fell back to 32 bits.
                                        let kt = class_local_typedef_target(c, kdt, u8::MAX);
                                        let kw = typedefs_snapshot(|td| {
                                            resolve_type_width(kt, class_params, td)
                                        });
                                        if kw > 0 {
                                            static_assoc_index_props.insert(
                                                decl.name.name.clone(),
                                                (kw, is_type_signed(kdt)),
                                            );
                                        }
                                    }
                                }
                            }
                            Some(UnpackedDimension::Queue { .. })
                            | Some(UnpackedDimension::Unsized(_)) => {
                                static_collections.push((
                                    decl.name.name.clone(),
                                    false,
                                    width.max(1),
                                ));
                            }
                            // A FIXED-size static array (`static int S[3]`,
                            // `static bit m[2:0]`) used to fall through here
                            // registering nothing at all: the whole
                            // `array_properties` block below is gated to
                            // non-statics, so the member collapsed onto the
                            // scalar cell built further down. That made
                            // element reads return x, writes bit-selects into
                            // a 32-bit scalar, `$size` report the scalar's
                            // WIDTH (32, not 3), and `foreach` bind a single
                            // garbage element — and the cross-instance
                            // sharing §8.9 promises never happened. Record
                            // the constant bounds so startup can build one
                            // shared global store, the same way the
                            // queue/assoc statics above get one.
                            Some(UnpackedDimension::Expression { expr, .. }) => {
                                if let Some(n) = const_eval_i64_with_params(expr, unpacked_params) {
                                    if n > 0 {
                                        static_fixed_arrays.push((
                                            decl.name.name.clone(),
                                            0,
                                            n - 1,
                                            width.max(1),
                                        ));
                                    }
                                }
                            }
                            Some(UnpackedDimension::Range { left, right, .. }) => {
                                if let (Some(l), Some(r)) = (
                                    const_eval_i64_with_params(left, unpacked_params),
                                    const_eval_i64_with_params(right, unpacked_params),
                                ) {
                                    static_fixed_arrays.push((
                                        decl.name.name.clone(),
                                        l.min(r),
                                        l.max(r),
                                        width.max(1),
                                    ));
                                    if l > r {
                                        array_prop_decl_dims
                                            .insert(decl.name.name.clone(), vec![(l, r)]);
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                    // A typedef'd key (`k12_t`) resolves through the class's
                    // own typedefs and the installed typedef table.
                    if let Some(shape) = CollShape::of(&effective_dims, None, |kdt| {
                        let kt = kdt.map(|k| class_local_typedef_target(c, k, u8::MAX));
                        typedefs_snapshot(|td| coll_key_kind(kt, unpacked_params, td, None))
                    }) {
                        prop_coll_shapes.insert(decl.name.name.clone(), shape);
                    }
                    if !is_static {
                        if matches!(effective_dims.first(), Some(UnpackedDimension::Unsized(_)))
                            && effective_dims.len() > 1
                            && effective_dims[1..]
                                .iter()
                                .all(|d| matches!(d, UnpackedDimension::Associative { .. }))
                        {
                            dynamic_assoc_properties
                                .insert(decl.name.name.clone(), effective_dims[1..].to_vec());
                        }
                        if matches!(
                            effective_dims.first(),
                            Some(UnpackedDimension::Unsized(_) | UnpackedDimension::Queue { .. })
                        ) && effective_dims.len() > 1
                            && effective_dims[1..].iter().all(|d| {
                                matches!(
                                    d,
                                    UnpackedDimension::Range { .. }
                                        | UnpackedDimension::Expression { .. }
                                        | UnpackedDimension::Unsized(_)
                                        | UnpackedDimension::Queue { .. }
                                )
                            })
                        {
                            dynamic_tail_properties
                                .insert(decl.name.name.clone(), effective_dims[1..].to_vec());
                        }
                        // §8.25: a fixed array sized by a header VALUE
                        // parameter (`int items[N]`) is a fixed array in every
                        // specialization, just of a different size. Classify
                        // it at the default values and record its dimensions
                        // so each object is re-sized from its own bindings;
                        // it used to stay queue-backed (`'{}`, `$size` 1).
                        let dims_fixed = |p: Option<&HashMap<String, Value>>| {
                            !effective_dims.is_empty()
                                && effective_dims.iter().all(|d| match d {
                                    UnpackedDimension::Range { left, right, .. } => {
                                        const_eval_i64_with_params(left, p).is_some()
                                            && const_eval_i64_with_params(right, p).is_some()
                                    }
                                    UnpackedDimension::Expression { expr, .. } => {
                                        const_eval_i64_with_params(expr, p).is_some_and(|n| n > 0)
                                    }
                                    _ => false,
                                })
                        };
                        let unpacked_params = if binds_values
                            && !dims_fixed(unpacked_params)
                            && dims_fixed(class_params)
                        {
                            param_sized_props
                                .insert(decl.name.name.clone(), effective_dims.clone());
                            class_params
                        } else {
                            unpacked_params
                        };
                        if let Some(UnpackedDimension::Associative {
                            data_type: key_dt, ..
                        }) = effective_dims.first()
                        {
                            let is_string_key = key_dt.as_ref().is_some_and(|dt| {
                                matches!(
                                    dt.as_ref(),
                                    DataType::Simple {
                                        kind: SimpleType::String,
                                        ..
                                    }
                                )
                            });
                            assoc_properties.insert(decl.name.name.clone(), is_string_key);
                            // §6.19.6: record a NAMED key type so `foreach` binds
                            // the index variable with it (enum `.name()` etc.).
                            if let Some(DataType::TypeReference { name: kt, .. }) =
                                key_dt.as_deref()
                            {
                                assoc_key_types
                                    .insert(decl.name.name.clone(), kt.name.name.clone());
                            }
                            // §7.8.2: record the declared key width + signedness
                            // so the runtime narrows a wider index expression.
                            if !is_string_key {
                                if let Some(kdt) = key_dt.as_ref() {
                                    // A typedef'd key (`k12_t`) resolves through the
                                    // installed typedef table; without it the
                                    // index width fell back to 32 bits.
                                    let kt = class_local_typedef_target(c, kdt, u8::MAX);
                                    let kw = typedefs_snapshot(|td| {
                                        resolve_type_width(kt, class_params, td)
                                    });
                                    if kw > 0 {
                                        assoc_index_props.insert(
                                            decl.name.name.clone(),
                                            (kw, is_type_signed(kdt)),
                                        );
                                    }
                                    if let DataType::IntegerVector { dimensions, .. }
                                    | DataType::Implicit { dimensions, .. } = kt
                                        && dimensions.iter().any(|d| {
                                            matches!(d, PackedDimension::Range { left, right, .. }
                                                if range_refs_class_header_param(c, left, right))
                                        })
                                    {
                                        assoc_key_decl_types
                                            .insert(decl.name.name.clone(), kt.clone());
                                    }
                                }
                            }
                        }
                        // Queue (`m[$]`) / dynamic-array (`m[]`) member — track so
                        // it gets independent per-instance storage. Bounded queues
                        // (`m[$:N]`) record their cap.
                        // MULTI-dimensional fixed member (`test_t foo[0:3][0:7]`):
                        // record the FULL shape. The single-dim match below keeps
                        // only `effective_dims.first()`, silently dropping inner
                        // dimensions — `foo[i][j]` writes then miss and multi-var
                        // `foreach` never binds the inner index.
                        // §7.4.5: FIXED outer dimensions with a COLLECTION as the
                        // innermost one (`int q[3][$]`, `int d[3][]`,
                        // `int a[2][2][int]`). Neither branch below can express
                        // this: `nd_shape` needs constant bounds on every
                        // dimension and a queue dimension has none, so it bails
                        // and the fallback keeps only `effective_dims.first()` —
                        // the member becomes a fixed array of SCALARS and the
                        // element collections get no storage at all. Claim the
                        // shape here, before either.
                        let coll_split = coll_elem_split(&effective_dims);
                        let coll_elem_kind = match coll_split.map(|k| &effective_dims[k]) {
                            Some(UnpackedDimension::Queue { max_size, .. }) => {
                                Some(CollDimKind::Queue(
                                    max_size
                                        .as_ref()
                                        .and_then(|e| {
                                            const_eval_i64_with_params(e, unpacked_params)
                                        })
                                        .map(|n| (n + 1).max(1) as u32),
                                ))
                            }
                            Some(UnpackedDimension::Unsized(_)) => Some(CollDimKind::Dyn),
                            Some(UnpackedDimension::Associative { data_type: kdt, .. }) => {
                                Some(CollDimKind::Assoc {
                                    string_key: kdt.as_ref().is_some_and(|dt| {
                                        matches!(
                                            dt.as_ref(),
                                            DataType::Simple {
                                                kind: SimpleType::String,
                                                ..
                                            }
                                        )
                                    }),
                                })
                            }
                            _ => None,
                        };
                        let outer_shape: Option<Vec<(i64, i64)>> =
                            coll_elem_kind.as_ref().and_then(|_| {
                                effective_dims[..coll_split.unwrap_or(0)]
                                    .iter()
                                    .map(|dm| match dm {
                                        UnpackedDimension::Range { left, right, .. } => match (
                                            const_eval_i64_with_params(left, unpacked_params),
                                            const_eval_i64_with_params(right, unpacked_params),
                                        ) {
                                            (Some(l), Some(r)) => Some((l, r)),
                                            _ => None,
                                        },
                                        UnpackedDimension::Expression { expr, .. } => {
                                            match const_eval_i64_with_params(expr, unpacked_params)
                                            {
                                                Some(n) if n > 0 => Some((0, n - 1)),
                                                _ => None,
                                            }
                                        }
                                        _ => None,
                                    })
                                    .collect()
                            });
                        if let (Some(kind), Some(shape)) = (coll_elem_kind, outer_shape) {
                            if shape.iter().any(|&(l, r)| l > r) {
                                array_prop_decl_dims.insert(decl.name.name.clone(), shape.clone());
                            }
                            let shape: Vec<_> =
                                shape.iter().map(|&(l, r)| (l.min(r), l.max(r))).collect();
                            // The OUTER shape still goes into the ordinary fixed-
                            // array maps: every existing consumer of a class
                            // property's shape ($size, foreach, %p, the randomizer)
                            // reads them, and the outer dimensions really are a
                            // fixed array. `array_of_coll_properties` is additive —
                            // it says what the ELEMENT is, which is the part that
                            // had nowhere to live.
                            if shape.len() == 1 {
                                array_properties.insert(
                                    decl.name.name.clone(),
                                    (shape[0].0, shape[0].1, width.max(1)),
                                );
                            } else {
                                array_nd_properties
                                    .insert(decl.name.name.clone(), (shape.clone(), width.max(1)));
                            }
                            // Element storage, mirroring the module-scope model
                            // (`int q[3][$]` at module scope registers the flat
                            // element keys `q[0]`..`q[2]`): every element gets its
                            // own queue/dyn/assoc property under the flat name the
                            // receiver resolver builds for `q[i][j].method()`, so
                            // `push_back`, `new[n]`, `[key] =` and reads find a
                            // store instead of silently doing nothing.
                            for suffix in index_tuples(&shape) {
                                let en = format!("{}{}", decl.name.name, suffix);
                                match &kind {
                                    CollDimKind::Assoc { string_key } => {
                                        if let UnpackedDimension::Associative {
                                            data_type, ..
                                        } = &effective_dims[coll_split.unwrap()]
                                        {
                                            if let Some(kdt) = data_type.as_deref() {
                                                if !string_key {
                                                    let kw = typedefs_snapshot(|td| {
                                                        resolve_type_width(kdt, class_params, td)
                                                    });
                                                    if kw > 0 {
                                                        assoc_index_props.insert(
                                                            en.clone(),
                                                            (kw, is_type_signed(kdt)),
                                                        );
                                                    }
                                                }
                                                if let DataType::TypeReference { name, .. } = kdt {
                                                    assoc_key_types
                                                        .insert(en.clone(), name.name.name.clone());
                                                }
                                            }
                                        }
                                        assoc_properties.insert(en, *string_key);
                                    }
                                    CollDimKind::Queue(cap) => {
                                        queue_properties.insert(en, (width.max(1), *cap));
                                    }
                                    CollDimKind::Dyn => {
                                        queue_properties.insert(en, (width.max(1), None));
                                    }
                                }
                            }
                            array_of_coll_properties
                                .insert(decl.name.name.clone(), (shape, width.max(1), kind));
                        } else {
                            let nd_shape: Option<Vec<(i64, i64)>> = if effective_dims.len() >= 2 {
                                effective_dims
                                    .iter()
                                    .map(|dm| match dm {
                                        UnpackedDimension::Range { left, right, .. } => {
                                            match (
                                                const_eval_i64_with_params(left, unpacked_params),
                                                const_eval_i64_with_params(right, unpacked_params),
                                            ) {
                                                (Some(l), Some(r)) => Some((l.min(r), l.max(r))),
                                                _ => None,
                                            }
                                        }
                                        UnpackedDimension::Expression { expr, .. } => {
                                            match const_eval_i64_with_params(expr, unpacked_params)
                                            {
                                                Some(n) if n > 0 => Some((0, n - 1)),
                                                _ => None,
                                            }
                                        }
                                        _ => None,
                                    })
                                    .collect()
                            } else {
                                None
                            };
                            // §7.4.2: keep the declared direction of a
                            // descending dimension (see `array_prop_decl_dims`).
                            let decl_dims: Option<Vec<(i64, i64)>> = effective_dims
                                .iter()
                                .map(|dm| match dm {
                                    UnpackedDimension::Range { left, right, .. } => {
                                        match (
                                            const_eval_i64_with_params(left, unpacked_params),
                                            const_eval_i64_with_params(right, unpacked_params),
                                        ) {
                                            (Some(l), Some(r)) => Some((l, r)),
                                            _ => None,
                                        }
                                    }
                                    UnpackedDimension::Expression { expr, .. } => {
                                        match const_eval_i64_with_params(expr, unpacked_params) {
                                            Some(n) if n > 0 => Some((0, n - 1)),
                                            _ => None,
                                        }
                                    }
                                    _ => None,
                                })
                                .collect();
                            if let Some(dd) = decl_dims.filter(|d| d.iter().any(|&(l, r)| l > r)) {
                                array_prop_decl_dims.insert(decl.name.name.clone(), dd);
                            }
                            if let Some(shape) = nd_shape {
                                array_nd_properties
                                    .insert(decl.name.name.clone(), (shape, width.max(1)));
                            } else {
                                match effective_dims.first() {
                                    Some(UnpackedDimension::Queue { max_size, .. }) => {
                                        let cap = max_size
                                            .as_ref()
                                            .and_then(|e| {
                                                const_eval_i64_with_params(e, unpacked_params)
                                            })
                                            .map(|n| (n + 1).max(1) as u32);
                                        queue_properties
                                            .insert(decl.name.name.clone(), (width.max(1), cap));
                                    }
                                    Some(UnpackedDimension::Unsized(_)) => {
                                        queue_properties
                                            .insert(decl.name.name.clone(), (width.max(1), None));
                                    }
                                    // A member array sized by an expression (e.g.
                                    // `seq m[NUM_HARTS]`) cannot be sized here — class
                                    // elaboration has no parameter table, so the dimension
                                    // would resolve to 0 and indexing would be out of
                                    // bounds. Give it independent per-instance storage like
                                    // a queue (indexed writes land in the 0..63 buffer).
                                    // A *constant*-sized `[N]` IS resolvable, so register it
                                    // as a real fixed array (so `gpr[0]` defaults to its
                                    // element value, not an empty-queue read of 0).
                                    Some(UnpackedDimension::Expression { expr, .. }) => {
                                        match const_eval_i64_with_params(expr, unpacked_params) {
                                            Some(n) if n > 0 => {
                                                array_properties.insert(
                                                    decl.name.name.clone(),
                                                    (0, n - 1, width.max(1)),
                                                );
                                            }
                                            _ => {
                                                queue_properties.insert(
                                                    decl.name.name.clone(),
                                                    (width.max(1), None),
                                                );
                                            }
                                        }
                                    }
                                    // `m[lo:hi]` fixed unpacked array with constant bounds.
                                    Some(UnpackedDimension::Range { left, right, .. }) => {
                                        if let (Some(l), Some(r)) = (
                                            const_eval_i64_with_params(left, unpacked_params),
                                            const_eval_i64_with_params(right, unpacked_params),
                                        ) {
                                            array_properties.insert(
                                                decl.name.name.clone(),
                                                (l.min(r), l.max(r), width.max(1)),
                                            );
                                        }
                                    }
                                    _ => {}
                                }
                            } // end `else` (single-dim)
                        } // end `else` (not an array-of-collections)
                    } // end `if !is_static`
                    // Remember scalar initializers so instantiation can re-eval
                    // them with the live parameter table (e.g. `= NUM_HARTS`).
                    if let Some(init) = &decl.init {
                        property_inits.insert(decl.name.name.clone(), init.as_ref().clone());
                    }
                    let mut v = if let Some(init) = &decl.init {
                        let mut val =
                            eval_init_for_target(init, &HashMap::default(), width, is_real);
                        if is_real {
                            val = Value::from_f64(val.to_f64());
                        }
                        val
                    } else if is_real {
                        Value::from_f64(0.0)
                    } else if is_named_type {
                        Value::zero(width)
                    } else {
                        default_value_for_type(&p.data_type, width)
                    };
                    // §11.8.1: the DECLARED type decides signedness, and an
                    // initializer's sign must not leak into it. This only ever
                    // SET the flag, so `bit [15:0] u = -1` kept the literal's
                    // signedness and `c.u > 0` compared as -1 instead of
                    // 65535 — the same shape as the parameter bug, one level
                    // in. A real keeps its own representation.
                    if !is_real {
                        v.is_signed = is_signed;
                    }
                    // Track source order for `%p` (§21.2.1.7).
                    if !property_order.contains(&decl.name.name) {
                        property_order.push(decl.name.name.clone());
                    }
                    if matches!(
                        &p.data_type,
                        DataType::Simple {
                            kind: SimpleType::String,
                            ..
                        }
                    ) {
                        string_properties.insert(decl.name.name.clone());
                    }
                    // Record a property's declared `#(...)` specialization
                    // args so a later `this.prop = new(...)` constructs the
                    // right specialization (binding value parameters).
                    if let DataType::TypeReference { type_args, .. } = &p.data_type {
                        if !type_args.is_empty() {
                            property_type_args.insert(decl.name.name.clone(), type_args.clone());
                        }
                    }
                    properties.insert(
                        decl.name.name.clone(),
                        Signal {
                            is_const: false,
                            name: decl.name.name.clone().into(),
                            width,
                            is_signed,
                            is_real,
                            direction: None,
                            value: v,
                            type_name: get_type_name(&p.data_type),
                        },
                    );
                    if is_rand {
                        random_properties.insert(decl.name.name.clone());
                    }
                    if is_randc {
                        randc_properties.insert(decl.name.name.clone());
                    }
                    if is_static {
                        static_properties.insert(decl.name.name.clone());
                    }
                    // IEEE 1800 §8.2: capture `local`/`protected` visibility so
                    // the compile-time member-visibility pass can reject illegal
                    // out-of-class accesses.
                    if p.qualifiers.contains(&ClassQualifier::Protected) {
                        protected_properties.insert(decl.name.name.clone());
                    }
                    if p.qualifiers.contains(&ClassQualifier::Local) {
                        local_properties.insert(decl.name.name.clone());
                    }
                }
            }
            // §19.3: a covergroup declared in a class body implicitly declares
            // a variable of that covergroup type with the same name, which
            // the constructor's `cg = new` assigns. Without the property the
            // assignment had no target: the handle stayed x and every
            // `cg.sample()` was a silent no-op.
            ClassItem::Covergroup(cg) => {
                let cg_name = cg.name.name.clone();
                if !properties.contains_key(&cg_name) {
                    property_types.insert(
                        cg_name.clone(),
                        DataType::TypeReference {
                            name: TypeName {
                                scopes: Vec::new(),
                                name: Identifier {
                                    name: cg_name.clone(),
                                    span: cg.name.span,
                                },
                                span: cg.name.span,
                                bound: Default::default(),
                            },
                            dimensions: Vec::new(),
                            type_args: Vec::new(),
                            span: cg.name.span,
                        },
                    );
                    properties.insert(
                        cg_name.clone(),
                        Signal {
                            is_const: false,
                            name: cg_name.clone().into(),
                            width: 32,
                            is_signed: false,
                            is_real: false,
                            direction: None,
                            value: Value::new(32),
                            type_name: Some(cg_name.clone()),
                        },
                    );
                    property_order.push(cg_name);
                }
            }
            ClassItem::Method(m) => {
                // §8.24 (#842): a scoped body written here belongs to a
                // nested class, not to this class under the same bare name.
                // The extern linker attaches it after all classes exist.
                if matches!(&m.kind, ClassMethodKind::Function(f) if f.name.has_scope())
                    || matches!(&m.kind, ClassMethodKind::Task(t) if t.name.has_scope())
                {
                    continue;
                }
                let name = match &m.kind {
                    ClassMethodKind::Function(f) => f.name.name.name.clone(),
                    ClassMethodKind::Task(t) => t.name.name.name.clone(),
                    ClassMethodKind::PureVirtual(f) => f.name.name.name.clone(),
                    ClassMethodKind::Extern(f) => f.name.name.name.clone(),
                };
                if m.qualifiers.contains(&ClassQualifier::Static) {
                    static_methods.insert(name.clone());
                }
                methods.insert(name, m.clone());
            }
            ClassItem::Constraint(con) => {
                constraints.insert(con.name.name.clone(), con.clone());
            }
            _ => {}
        }
    }
    // Collect class parameters (name + optional default expression).
    let mut param_defaults: Vec<(String, Option<crate::ast::expr::Expression>)> = Vec::new();
    for p in &c.params {
        if let crate::ast::decl::ParameterKind::Data {
            data_type,
            assignments,
            ..
        } = &p.kind
        {
            for a in assignments {
                param_defaults.push((a.name.name.clone(), a.init.clone()));
                // A value parameter is bound as an INSTANCE PROPERTY at
                // construction (§8.25), so record its declared type in the same
                // map — that is what lets an indexed read of a packed-array
                // parameter (`parameter bit [1:0][7:0] V;` … `obj.V[1]`) select
                // an element rather than a bit.
                property_types
                    .entry(a.name.name.clone())
                    .or_insert_with(|| data_type.clone());
                // §6.20.2/§8.25 (issue #423): a header VALUE parameter
                // declared with UNPACKED dimensions (`class C #(int unsigned
                // TBL [4] = '{1, 2, 3, 4})`) is a constant ARRAY whose
                // elements every specialization binds for itself — from its
                // own `#(...)` argument when given, else this initializer.
                // The scalar fold above stays (default lookups, instance
                // property seeding); register the declared shape and the
                // re-evaluable initializer exactly the way a class-body
                // localparam array registers (the ClassItem::Parameter loop
                // below), so the runtime can materialize the
                // per-specialization elements for `C#(..)::TBL[i]` and bare
                // `TBL[i]` reads inside static methods. No `properties`
                // entry: a value parameter is bound as an INSTANCE property
                // at construction (§8.25), and the class-scope read path
                // materializes its own per-spec storage.
                if !a.dimensions.is_empty() {
                    if let Some((lo, hi)) = const_unpacked_bounds(&a.dimensions, class_params) {
                        let ew = resolve_type_width(data_type, Some(const_scope), None).max(1);
                        array_properties.insert(a.name.name.clone(), (lo, hi, ew));
                        // §8.25: keep the declaration so both bounds and the
                        // element type can be resolved for each specialization.
                        property_types.insert(a.name.name.clone(), data_type.clone());
                        param_sized_props.insert(a.name.name.clone(), a.dimensions.clone());
                        if let Some((left, right)) =
                            const_unpacked_decl_bounds(&a.dimensions, class_params)
                            && left > right
                        {
                            array_prop_decl_dims.insert(a.name.name.clone(), vec![(left, right)]);
                        }
                        if let Some(init) = &a.init {
                            property_inits.insert(a.name.name.clone(), init.clone());
                        }
                    }
                }
            }
        }
    }
    // Also collect class-body `localparam` declarations (e.g. UVM 2020.3.1's
    // `localparam string prefix = "+uvm_set_verbosity="`). These are class
    // constants accessible as static members, so they need entries in both
    // `param_defaults` (for value lookup) and `static_properties` (for
    // name resolution) as well as `properties` (for initial value seeding).
    for item in &c.items {
        if let ClassItem::Parameter(pd) = item {
            if let crate::ast::decl::ParameterKind::Data {
                data_type,
                assignments,
                ..
            } = &pd.kind
            {
                for a in assignments {
                    // §6.20.2: a class-scope `localparam`/`parameter` carrying an
                    // UNPACKED dimension is a constant ARRAY, not a scalar. The
                    // dimension used to be dropped here, collapsing the whole
                    // array into a single element-width scalar — so `Arr[i]` was
                    // a BIT select (reading 0), `$size` reported the bit width
                    // (32 for `int`, 96 for a 3-deep one), and `foreach` had no
                    // shape at all: the sync path ran one iteration, the async
                    // path ran none, both silently. Register it exactly the way a
                    // `const` array PROPERTY is registered — declared bounds plus
                    // a re-evaluable initializer — which every downstream consumer
                    // (element read, `$size`, both `foreach` paths) already
                    // handles correctly.
                    if !a.dimensions.is_empty() {
                        if let Some((lo, hi)) = const_unpacked_bounds(&a.dimensions, class_params) {
                            let ew = resolve_type_width(data_type, Some(const_scope), None).max(1);
                            array_properties.insert(a.name.name.clone(), (lo, hi, ew));
                            // §8.25: keep the declaration so both bounds and the
                            // element type can be resolved for each specialization.
                            property_types.insert(a.name.name.clone(), data_type.clone());
                            param_sized_props.insert(a.name.name.clone(), a.dimensions.clone());
                            if let Some((left, right)) =
                                const_unpacked_decl_bounds(&a.dimensions, class_params)
                                && left > right
                            {
                                array_prop_decl_dims
                                    .insert(a.name.name.clone(), vec![(left, right)]);
                            }
                            if let Some(init) = &a.init {
                                property_inits.insert(a.name.name.clone(), init.clone());
                            }

                            properties.insert(
                                a.name.name.clone(),
                                Signal {
                                    is_const: true,
                                    name: a.name.name.clone().into(),
                                    width: ew,
                                    is_signed: is_type_signed(data_type),
                                    is_real: false,
                                    direction: None,
                                    value: Value::zero(ew),
                                    type_name: get_type_name(data_type),
                                },
                            );
                            continue;
                        }
                    }
                    param_defaults.push((a.name.name.clone(), a.init.clone()));
                    static_properties.insert(a.name.name.clone());
                    // Evaluate the initial value for the property against the
                    // class's CONSTANT SCOPE (header parameter defaults plus
                    // earlier body localparams). An empty map was used, so
                    // `localparam int MYW = W;` in `class C #(parameter int
                    // W = 8)` baked in 0 for every specialization.
                    // §6.20.2: an UNTYPED parameter takes the type of its
                    // value — an unsized decimal is signed 32-bit. Sizing it
                    // with `resolve_type_width` gave an implicit-no-dims type
                    // ONE bit, so a class `parameter A = 1;` stored 1'b1 and
                    // read back -1 inside a method, while `localparam B = 2;`
                    // truncated to 0 (ivtest sv_class_localparam). Module- and
                    // package-scope parameters already use this rule.
                    let implicit_no_dims = matches!(
                        data_type,
                        DataType::Implicit { dimensions, .. } if dimensions.is_empty()
                    );
                    let width = if implicit_no_dims {
                        a.init
                            .as_ref()
                            .and_then(|i| untyped_param_width(i, const_scope))
                            .unwrap_or(32)
                    } else {
                        resolve_type_width(data_type, Some(const_scope), None)
                    };
                    let is_string = matches!(
                        data_type,
                        crate::ast::types::DataType::Simple {
                            kind: crate::ast::types::SimpleType::String,
                            ..
                        }
                    );
                    let v = if is_string {
                        // String localparams: evaluate using the const-eval path.
                        if let Some(init) = &a.init {
                            eval_const_expr_val(init, const_scope)
                        } else {
                            Value::from_string("")
                        }
                    } else if let Some(init) = &a.init {
                        eval_param_init(data_type, init, const_scope, &HashMap::default(), width)
                    } else {
                        Value::zero(width)
                    };
                    properties.insert(
                        a.name.name.clone(),
                        Signal {
                            is_const: true,
                            name: a.name.name.clone().into(),
                            width,
                            is_signed: implicit_no_dims || is_type_signed(data_type),
                            is_real: false,
                            direction: None,
                            value: v,
                            type_name: get_type_name(data_type),
                        },
                    );
                }
            }
        }
    }
    let has_pure_virtual = c.items.iter().any(|it|
        matches!(it, ClassItem::Method(m) if matches!(m.kind, ClassMethodKind::PureVirtual(_))));
    let mut type_param_names = Vec::new();
    let mut type_param_defaults: Vec<(String, String)> = Vec::new();
    let mut type_param_default_types: Vec<(String, crate::ast::types::DataType)> = Vec::new();
    let mut param_order: Vec<String> = Vec::new();
    for p in &c.params {
        match &p.kind {
            crate::ast::decl::ParameterKind::Type { assignments } => {
                for a in assignments {
                    type_param_names.push(a.name.name.clone());
                    param_order.push(a.name.name.clone());
                    // Capture the default type as a textual fragment, and
                    // the AST itself for per-specialization width resolution.
                    if let Some(dt) = &a.init {
                        if let Some(frag) = data_type_to_spec_fragment(dt) {
                            type_param_defaults.push((a.name.name.clone(), frag));
                        }
                        type_param_default_types.push((a.name.name.clone(), dt.clone()));
                    }
                }
            }
            crate::ast::decl::ParameterKind::Data { assignments, .. } => {
                for a in assignments {
                    param_order.push(a.name.name.clone());
                }
            }
        }
    }
    ElaboratedClass {
        name: c.name.name.clone(),
        enclosing: None,
        declaring_module: None,
        extends: c.extends.as_ref().map(|e| e.name.name.clone()),
        extends_args: c
            .extends
            .as_ref()
            .map(|e| {
                e.args
                    .iter()
                    .filter_map(|a| match a {
                        ParamValue::Expr(ex) => Some(ex.clone()),
                        ParamValue::Type(_) => None,
                    })
                    .collect()
            })
            .unwrap_or_default(),
        extends_type_args: c
            .extends
            .as_ref()
            .map(|e| e.args.iter().map(param_value_to_arg_string).collect())
            .unwrap_or_default(),
        properties,
        property_types,
        property_order,
        string_properties,
        methods: std::sync::Arc::new(methods),
        random_properties,
        protected_properties,
        local_properties,
        virtual_iface_properties,
        randc_properties,
        constraints,
        param_defaults,
        is_interface: c.is_interface,
        is_virtual: c.virtual_kw,
        is_final: c.is_final,
        has_pure_virtual,
        implements: c.implements.iter().map(|i| i.name.clone()).collect(),
        type_param_names,
        type_param_defaults,
        type_param_default_types,
        param_order,
        property_type_args,
        typedef_names: c
            .items
            .iter()
            .filter_map(|it| match it {
                ClassItem::Typedef(td) => Some(td.name.name.clone()),
                _ => None,
            })
            .collect(),
        typedef_targets: c
            .items
            .iter()
            .filter_map(|it| match it {
                // §8.23: a struct member sized by a constant (`m[Q]`).
                ClassItem::Typedef(td) => {
                    let dt = size_struct_member_dims(
                        &td.data_type,
                        const_scope,
                        &HashMap::default(),
                        !class_has_value_params(c),
                    )
                    .unwrap_or_else(|| td.data_type.clone());
                    let dt = fold_packed_dims_with(
                        &dt,
                        const_scope,
                        &|l, r| !range_refs_class_header_param(c, l, r),
                    )
                    .unwrap_or(dt);
                    Some((td.name.name.clone(), dt))
                }
                _ => None,
            })
            .collect(),
        typedef_unpacked_dims: c
            .items
            .iter()
            .filter_map(|it| match it {
                ClassItem::Typedef(td) if !td.dimensions.is_empty() => {
                    Some((td.name.name.clone(), td.dimensions.clone()))
                }
                _ => None,
            })
            .collect(),
        static_properties,
        static_methods,
        assoc_properties,
        assoc_key_types,
        assoc_index_props,
        assoc_key_decl_types,
        queue_properties,
        queue_property_names,
        property_inits,
        static_collections,
        static_assoc_key_types,
        static_assoc_index_props,
        static_fixed_arrays,
        array_properties,
        param_sized_props,
        array_nd_properties,
        array_of_coll_properties,
        dynamic_assoc_properties,
        dynamic_tail_properties,
        prop_coll_shapes,
        array_prop_decl_dims,
    }
}
