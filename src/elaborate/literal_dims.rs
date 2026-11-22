use super::*;

/// §6.20.2/§23.10: fold this instance's parameters into the dimensions of
/// declarations that live INSIDE a statement — task and function locals, named
/// blocks, fork branches.
///
/// Such a declaration is sized long after elaboration, from the flat
/// design-wide parameter map — where a submodule's parameters live under their
/// INSTANCE-QUALIFIED keys (`u_fifo.DW`). The bare `DW` the declaration spells
/// missed that map, `const_eval_i64_with_params` returned None, and
/// `resolve_type_width` then silently SKIPPED the dimension, leaving the local
/// ONE BIT wide: every value stored in it was truncated to its LSB. A
/// module-level declaration escapes this only because elaboration sizes it
/// while the instance's parameters are still bound to their bare names.
///
/// Running the fold here fixes both consumers at once — the bytecode compiler
/// and the AST interpreter read the same declaration, and after this pass its
/// range is a literal. `prepare_module_items` caches per (module,
/// parameter-set), so two instances with different parameters get different
/// constants.
///
/// A name the body declares itself is left alone: it shadows the parameter.
pub(super) fn literalize_stmt_decl_dims(items: &mut [ModuleItem], params: &HashMap<String, Value>) {
    // The module's own typedefs, with this instance's parameters already
    // folded in. A statement-local declaration spelled with one of these names
    // cannot be resolved after elaboration either: the bare typedef key is
    // REMOVED once the module is finished (only the instance-scoped `u.vl_t`
    // survives, and the declaration does not spell that), so the lookup missed
    // and `resolve_type_width` fell back to its 32-bit default — silently
    // truncating every local of a wider typedef. Same asymmetry as the
    // parameters above: a module-level declaration is sized while the bare
    // name is still bound, a statement-local one is not.
    let mut tds: HashMap<String, DataType> = HashMap::default();
    for item in items.iter() {
        if let ModuleItem::TypedefDeclaration(td) = item {
            // §6.18: an UNPACKED-array typedef (`typedef u8_t u8a_t [0:7]`)
            // keeps its name like every unpacked aggregate: its dimensions
            // are on the declaration, not in `data_type`, so substituting
            // the element type made `u8a_t r;` a single element.
            if !td.dimensions.is_empty() {
                continue;
            }
            let mut dt = td.data_type.clone();
            lsdd_data_type(&mut dt, params);
            tds.insert(td.name.name.clone(), dt);
        }
    }
    if params.is_empty() && tds.is_empty() {
        return;
    }
    lsdd_items(items, params, &tds);
}

fn lsdd_items(
    items: &mut [ModuleItem],
    params: &HashMap<String, Value>,
    tds: &HashMap<String, DataType>,
) {
    for item in items.iter_mut() {
        match item {
            ModuleItem::AlwaysConstruct(ac) => {
                lsdd_body(std::slice::from_mut(&mut ac.stmt), params, tds)
            }
            ModuleItem::InitialConstruct(ic) => {
                lsdd_body(std::slice::from_mut(&mut ic.stmt), params, tds)
            }
            ModuleItem::FinalConstruct(fc) => {
                lsdd_body(std::slice::from_mut(&mut fc.stmt), params, tds)
            }
            ModuleItem::TaskDeclaration(td) => lsdd_shared_body(&mut td.items, params, tds),
            ModuleItem::FunctionDeclaration(fd) => lsdd_shared_body(&mut fd.items, params, tds),
            ModuleItem::ClassDeclaration(cd) => lsdd_class(cd, params, tds),
            // A module-level typedef is resolved for its own WIDTH while the
            // parameters are still bare-bound, but its member LAYOUT is built
            // later from the flat map — so a `logic [DW-1:0]` member still
            // needs the fold.
            ModuleItem::TypedefDeclaration(td) => lsdd_data_type(&mut td.data_type, params),
            ModuleItem::GenerateFor(gf) => lsdd_items(&mut gf.items, params, tds),
            ModuleItem::GenerateRegion(gr) => lsdd_items(&mut gr.items, params, tds),
            ModuleItem::GenerateIf(gi) => {
                for (_c, its) in gi.branches.iter_mut() {
                    lsdd_items(its, params, tds);
                }
            }
            ModuleItem::GenerateCase(gc) => {
                for arm in gc.arms.iter_mut() {
                    lsdd_items(&mut arm.items, params, tds);
                }
            }
            _ => {}
        }
    }
}

fn lsdd_class(
    c: &mut crate::ast::decl::ClassDeclaration,
    params: &HashMap<String, Value>,
    tds: &HashMap<String, DataType>,
) {
    use crate::ast::decl::{ClassItem, ClassMethodKind};
    for item in &mut c.items {
        match item {
            ClassItem::Method(m) => match &mut m.kind {
                ClassMethodKind::Function(fd)
                | ClassMethodKind::PureVirtual(fd)
                | ClassMethodKind::Extern(fd) => lsdd_shared_body(&mut fd.items, params, tds),
                ClassMethodKind::Task(td) => lsdd_shared_body(&mut td.items, params, tds),
            },
            ClassItem::Class(nc) => lsdd_class(nc, params, tds),
            _ => {}
        }
    }
}

/// Replace member types of a (substituted) packed struct that name one of the
/// module's own typedefs with the resolved type, recursively.
fn lsdd_subst_struct_members(su: &mut StructUnionType, tds: &HashMap<String, DataType>) {
    for m in su.members.iter_mut() {
        if let Some(rt) = lsdd_resolve_local_typedef(&m.data_type, tds) {
            m.data_type = rt;
        } else if let DataType::Struct(inner) = &mut m.data_type {
            lsdd_subst_struct_members(inner, tds);
        }
    }
}

/// Replace a reference to one of this module's own typedefs with the type it
/// names, when that type is a shape whose width would otherwise silently
/// default to 32 bits. Deliberately narrow: enums, classes, strings and
/// unpacked aggregates keep their named form, since only packed vectors and
/// packed structs showed the truncation.
fn lsdd_resolve_local_typedef(dt: &DataType, tds: &HashMap<String, DataType>) -> Option<DataType> {
    // Dimensions written on the REFERENCE are outer relative to the type they
    // qualify: `vl_t [1:0]` is `logic [1:0][127:0]`. Collect them outermost
    // first as the chain is walked, then put them in front of the target's own.
    let mut outer: Vec<PackedDimension> = Vec::new();
    let mut cur = dt.clone();
    let mut hops = 0;
    loop {
        let DataType::TypeReference {
            name, dimensions, ..
        } = &cur
        else {
            break;
        };
        if name.has_scope() {
            break;
        }
        let Some(next) = tds.get(&name.name.name) else {
            break;
        };
        outer.extend(dimensions.iter().cloned());
        cur = next.clone();
        hops += 1;
        // A typedef of a typedef is legal; a cycle is not, so cap the walk.
        if hops > 8 {
            return None;
        }
    }
    if hops == 0 {
        return None;
    }
    match &mut cur {
        DataType::IntegerVector { dimensions, .. } => {
            if dimensions.is_empty() && outer.is_empty() {
                return None;
            }
            outer.extend(dimensions.iter().cloned());
            *dimensions = outer;
        }
        DataType::Struct(su) if su.packed => {
            outer.extend(su.dimensions.iter().cloned());
            su.dimensions = outer;
            // The MEMBERS may name this module's typedefs too (`in_t q;`).
            // Left as references they resolve to the 32-bit default at run
            // time in a submodule (the bare typedef key is gone), and every
            // member laid out above them lands at the wrong offset.
            lsdd_subst_struct_members(su, tds);
        }
        // An enum keeps its members, so inlining it preserves `.name()` and
        // `$cast` — which a bare 32-bit fallback had already lost anyway.
        DataType::Enum(et) => {
            outer.extend(et.dimensions.iter().cloned());
            et.dimensions = outer;
        }
        _ => return None,
    }
    Some(cur)
}

/// §13.3/§13.4, §6.20.2: inspect shared bodies before mutable access.
/// Skip copy-on-write when local declarations need no folding.
fn lsdd_shared_body(
    stmts: &mut crate::ast::shared_vec::SharedVec<Statement>,
    params: &HashMap<String, Value>,
    tds: &HashMap<String, DataType>,
) {
    if stmts.iter().any(lsdd_may_fold_decl) {
        lsdd_body(stmts, params, tds);
    }
}

/// Mirror `lsdd_stmt`; preserve scoped folding for dimensions and named types.
/// Scalar bindings matter only when another declaration needs folding.
fn lsdd_may_fold_decl(s: &Statement) -> bool {
    match &s.kind {
        StatementKind::VarDecl {
            data_type,
            declarators,
            ..
        }
        | StatementKind::ParamDecl {
            data_type,
            declarators,
            ..
        } => {
            lsdd_may_fold_type(data_type)
                || declarators.iter().any(|d| {
                    d.dimensions.iter().any(|dim| match dim {
                        UnpackedDimension::Range { left, right, .. } => {
                            lsdd_may_fold_expr(left) || lsdd_may_fold_expr(right)
                        }
                        UnpackedDimension::Expression { expr, .. } => lsdd_may_fold_expr(expr),
                        _ => false,
                    })
                })
        }
        StatementKind::Typedef(td) => lsdd_may_fold_type(&td.data_type),
        StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
            stmts.iter().any(lsdd_may_fold_decl)
        }
        StatementKind::TimingControl { stmt, .. } | StatementKind::Wait { stmt, .. } => {
            lsdd_may_fold_decl(stmt)
        }
        StatementKind::If {
            then_stmt,
            else_stmt,
            ..
        } => {
            lsdd_may_fold_decl(then_stmt)
                || else_stmt.as_ref().is_some_and(|s| lsdd_may_fold_decl(s))
        }
        StatementKind::For { body, .. }
        | StatementKind::Foreach { body, .. }
        | StatementKind::While { body, .. }
        | StatementKind::DoWhile { body, .. }
        | StatementKind::Repeat { body, .. }
        | StatementKind::Forever { body, .. } => lsdd_may_fold_decl(body),
        StatementKind::Case { items, .. } => items.iter().any(|it| lsdd_may_fold_decl(&it.stmt)),
        _ => false,
    }
}

fn lsdd_may_fold_type(dt: &DataType) -> bool {
    match dt {
        DataType::IntegerVector { dimensions, .. } | DataType::Implicit { dimensions, .. } => {
            dimensions.iter().any(|dim| match dim {
                PackedDimension::Range { left, right, .. } => {
                    lsdd_may_fold_expr(left) || lsdd_may_fold_expr(right)
                }
                _ => false,
            })
        }
        DataType::TypeReference { .. } | DataType::Struct(_) | DataType::Enum(_) => true,
        _ => false,
    }
}

/// Match `lsdd_expr`: literal and name-free endpoints are already immutable.
fn lsdd_may_fold_expr(expr: &Expression) -> bool {
    !matches!(expr.kind, ExprKind::Number(_)) && lsdd_names_value(expr)
}

/// Whether a dimension endpoint names a value the fold can bind. §20.8,
/// §20.9: the argument of a system function (`$clog2(P)`, `$signed(P)`, a
/// cast, `$bits(P)`) is such a name too; `[$clog2(P)-1:0]` in an instance
/// otherwise kept its bare `P`, which the design-wide map holds only as
/// `u.P`, and the local was one bit wide.
fn lsdd_names_value(expr: &Expression) -> bool {
    let mut names = Vec::new();
    lsdd_all_names(expr, &mut names);
    !names.is_empty()
}

/// Every identifier name in `expr`, the arguments of its system calls
/// included (`collect_ident_names` does not look inside them).
fn lsdd_all_names(expr: &Expression, names: &mut Vec<String>) {
    collect_ident_names(expr, names);
    for_each_sub_expr(expr, &mut |e| {
        if let ExprKind::SystemCall { args, .. } = &e.kind {
            for a in args {
                collect_ident_names(a, names);
            }
        }
    });
}

/// §20.6, §20.7: whether `expr` holds a query of a declaration (`$bits(v)`,
/// `$size(a)`) whose argument names anything but this scope's parameters
/// (`env`). Such a name is a variable or a type, which a block local may
/// shadow; the query is left to the run time.
fn lsdd_queries_a_declaration(expr: &Expression, env: &HashMap<String, Value>) -> bool {
    let mut found = false;
    for_each_sub_expr(expr, &mut |e| {
        if let ExprKind::SystemCall { name, args } = &e.kind
            && lsdd_is_decl_query(name)
        {
            let mut names = Vec::new();
            for a in args {
                lsdd_all_names(a, &mut names);
            }
            found |= names.is_empty() || names.iter().any(|n| !env.contains_key(n));
        }
    });
    found
}

/// Bind values in the arithmetic around a declaration query without evaluating
/// the query against the parameter-only scope. Preserve each substituted
/// parameter's original width and sign for enclosing casts and operations.
fn lsdd_bind_query_operands(e: &mut Expression, env: &HashMap<String, Value>) {
    match &mut e.kind {
        ExprKind::Ident(h) if h.root.is_none() && h.path.len() == 1 && h.path[0].selects.is_empty() => {
            if let Some(bound) = env.get(&h.path[0].name.name).and_then(|v| const_value_literal(v, e.span)) {
                *e = bound;
            }
        }
        ExprKind::Unary { operand, .. } | ExprKind::Paren(operand) => lsdd_bind_query_operands(operand, env),
        ExprKind::Binary { left, right, .. } => {
            lsdd_bind_query_operands(left, env);
            lsdd_bind_query_operands(right, env);
        }
        ExprKind::Conditional { condition, then_expr, else_expr } => {
            for part in [condition, then_expr, else_expr] {
                lsdd_bind_query_operands(part, env);
            }
        }
        ExprKind::SystemCall { name, args } if !lsdd_is_decl_query(name) => {
            for arg in args {
                lsdd_bind_query_operands(arg, env);
            }
        }
        _ => {}
    }
}

/// §20.6, §20.7: system functions that query a declaration rather than
/// compute from a value.
fn lsdd_is_decl_query(name: &str) -> bool {
    matches!(
        name,
        "$bits"
            | "$size"
            | "$left"
            | "$right"
            | "$low"
            | "$high"
            | "$increment"
            | "$dimensions"
            | "$unpacked_dimensions"
            | "$isunbounded"
            | "$typename"
    )
}

/// A decimal literal the i64 dimension evaluators read back as `v`.
fn lsdd_literal(v: i64) -> ExprKind {
    ExprKind::Number(crate::ast::expr::NumberLiteral::Integer {
        size: None,
        signed: true,
        base: crate::ast::expr::NumberBase::Decimal,
        value: v.to_string(),
        cached_val: crate::ast::cache::LiteralCache::new(None),
    })
}

/// Const-evaluate a dimension endpoint in this scope. §11.7: `$signed(x)`
/// and `$unsigned(x)` reinterpret `x` at its own width (`$signed` of an
/// 8-bit `8'hff` is -1), and §20.6.2 sizes `$bits(P)` by the parameter's
/// type, which `const_eval_i64_with_params` does not model: an endpoint with
/// either is evaluated on sized values, and folded only when that value is
/// fully known.
fn lsdd_eval(e: &Expression, env: &HashMap<String, Value>) -> Option<i64> {
    let mut sized = false;
    let mut call = false;
    for_each_sub_expr(e, &mut |x| {
        sized |= matches!(&x.kind, ExprKind::SystemCall { name, .. }
            if name == "$signed" || name == "$unsigned" || lsdd_is_decl_query(name));
        call |= matches!(x.kind, ExprKind::Call { .. });
    });
    // The plain reading must resolve too: the sized evaluator reads what it
    // does not model as a known 0. With a constant function call in it, a
    // sized endpoint is left for the run time.
    let plain = const_eval_i64_with_params(e, Some(env))?;
    if !sized {
        return Some(plain);
    }
    if call {
        return None;
    }
    let v = eval_const_expr_val(e, env);
    if v.is_real || v.has_xz() || !(1..=64).contains(&v.width) {
        return None;
    }
    v.to_i64()
}

/// One subroutine/process body. The fold runs against a lexically scoped
/// environment seeded from the instance's parameters — see `lsdd_scope`.
fn lsdd_body(
    stmts: &mut [Statement],
    params: &HashMap<String, Value>,
    tds: &HashMap<String, DataType>,
) {
    let mut env = params.clone();
    lsdd_scope(stmts, &mut env, tds);
}

/// Fold one lexical scope, having first bound what the scope itself declares.
///
/// §6.20.4: a block-scope `localparam`/`parameter` shadows any outer parameter
/// of the same name for sizing declarations in that block; a `VarDecl` un-binds
/// the name so an enclosing parameter is not folded in where a variable shadows it.
///
/// Bindings are pushed and popped on one map (rather than cloning it per
/// block) because this walks every statement of every module.
fn lsdd_scope(
    stmts: &mut [Statement],
    env: &mut HashMap<String, Value>,
    tds: &HashMap<String, DataType>,
) {
    let mut saved: Vec<(String, Option<Value>)> = Vec::new();
    for s in stmts.iter() {
        match &s.kind {
            StatementKind::ParamDecl { declarators, .. } => {
                for d in declarators {
                    let cv = d
                        .init
                        .as_ref()
                        .and_then(|i| const_eval_i64_with_params(i, Some(env)));
                    saved.push((d.name.name.clone(), env.get(&d.name.name).cloned()));
                    match cv {
                        Some(v) => {
                            let mut val = Value::from_u64(v as u64, 64);
                            val.is_signed = true;
                            env.insert(d.name.name.clone(), val);
                        }
                        None => {
                            env.remove(&d.name.name);
                        }
                    }
                }
            }
            StatementKind::VarDecl { declarators, .. } => {
                for d in declarators {
                    saved.push((d.name.name.clone(), env.get(&d.name.name).cloned()));
                    env.remove(&d.name.name);
                }
            }
            _ => {}
        }
    }
    for s in stmts.iter_mut() {
        lsdd_stmt(s, env, tds);
    }
    for (k, prev) in saved.into_iter().rev() {
        match prev {
            Some(v) => {
                env.insert(k, v);
            }
            None => {
                env.remove(&k);
            }
        }
    }
}

fn lsdd_stmt(s: &mut Statement, env: &mut HashMap<String, Value>, tds: &HashMap<String, DataType>) {
    match &mut s.kind {
        StatementKind::VarDecl {
            data_type,
            declarators,
            ..
        }
        | StatementKind::ParamDecl {
            data_type,
            declarators,
            ..
        } => {
            if let Some(rt) = lsdd_resolve_local_typedef(data_type, tds) {
                *data_type = rt;
            } else if let DataType::Struct(su) = data_type {
                // A struct written INLINE in the declaration: its members
                // may still name the module's typedefs.
                lsdd_subst_struct_members(su, tds);
            }
            lsdd_data_type(data_type, env);
            for d in declarators.iter_mut() {
                for dim in d.dimensions.iter_mut() {
                    match dim {
                        UnpackedDimension::Range { left, right, .. } => {
                            lsdd_expr(left, env);
                            lsdd_expr(right, env);
                        }
                        UnpackedDimension::Expression { expr, .. } => lsdd_expr(expr, env),
                        _ => {}
                    }
                }
            }
        }
        // §6.18: a typedef declared inside a block sizes from the same scope.
        StatementKind::Typedef(td) => {
            if let Some(rt) = lsdd_resolve_local_typedef(&td.data_type, tds) {
                td.data_type = rt;
            } else if let DataType::Struct(su) = &mut td.data_type {
                lsdd_subst_struct_members(su, tds);
            }
            lsdd_data_type(&mut td.data_type, env)
        }
        // A named block is a new scope; the loop/branch forms below are not.
        StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
            lsdd_scope(stmts, env, tds)
        }
        StatementKind::TimingControl { stmt, .. } | StatementKind::Wait { stmt, .. } => {
            lsdd_stmt(stmt, env, tds)
        }
        StatementKind::If {
            then_stmt,
            else_stmt,
            ..
        } => {
            lsdd_stmt(then_stmt, env, tds);
            if let Some(e) = else_stmt {
                lsdd_stmt(e, env, tds);
            }
        }
        StatementKind::For { body, .. }
        | StatementKind::Foreach { body, .. }
        | StatementKind::While { body, .. }
        | StatementKind::DoWhile { body, .. }
        | StatementKind::Repeat { body, .. }
        | StatementKind::Forever { body, .. } => lsdd_stmt(body, env, tds),
        StatementKind::Case { items, .. } => {
            for it in items.iter_mut() {
                lsdd_stmt(&mut it.stmt, env, tds);
            }
        }
        _ => {}
    }
}

pub(super) fn lsdd_data_type(dt: &mut DataType, env: &HashMap<String, Value>) {
    // A packed struct/union sizes its MEMBERS from the same parameters, and a
    // member left unresolved collapses the whole layout — the aggregate is
    // then short and every member above the bad one reads x.
    if let DataType::Struct(su) = dt {
        for m in su.members.iter_mut() {
            lsdd_data_type(&mut m.data_type, env);
            for d in m.declarators.iter_mut() {
                for dim in d.dimensions.iter_mut() {
                    match dim {
                        UnpackedDimension::Range { left, right, .. } => {
                            lsdd_expr(left, env);
                            lsdd_expr(right, env);
                        }
                        UnpackedDimension::Expression { expr, .. } => lsdd_expr(expr, env),
                        _ => {}
                    }
                }
            }
        }
    }
    // An enum's BASE type carries the width. Left unresolved it collapses to
    // one bit, and the §6.19 member-width check then REJECTS the design —
    // `enum logic [DW-1:0] {…}` in any submodule was unusable.
    if let DataType::Enum(et) = dt {
        if let Some(bt) = et.base_type.as_mut() {
            lsdd_data_type(bt, env);
        }
    }
    let dims = match dt {
        DataType::IntegerVector { dimensions, .. }
        | DataType::Implicit { dimensions, .. }
        | DataType::TypeReference { dimensions, .. }
        | DataType::Struct(StructUnionType { dimensions, .. })
        | DataType::Enum(EnumType { dimensions, .. }) => dimensions,
        _ => return,
    };
    for dim in dims.iter_mut() {
        if let PackedDimension::Range { left, right, .. } = dim {
            lsdd_expr(left, env);
            lsdd_expr(right, env);
        }
    }
}

/// Replace one dimension endpoint with its constant value, when it is not
/// already a literal and it const-evaluates in this scope.
pub(super) fn lsdd_expr(e: &mut Expression, env: &HashMap<String, Value>) {
    if matches!(e.kind, ExprKind::Number(_)) {
        return;
    }
    if lsdd_queries_a_declaration(e, env) {
        lsdd_bind_query_operands(e, env);
        return;
    }
    if !lsdd_names_value(e) {
        return;
    }
    let Some(v) = lsdd_eval(e, env) else {
        return;
    };
    e.kind = lsdd_literal(v);
}

#[cfg(test)]
mod prepared_callable_ownership_tests {
    use super::*;
    use std::sync::Arc;

    fn module_items(source: &str) -> Vec<ModuleItem> {
        let parsed = crate::parse(source);
        assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
        let crate::ast::Description::Module(module) = &parsed.source.descriptions[0] else {
            panic!("module expected");
        };
        module.items.clone()
    }

    fn callable_bodies(items: &[ModuleItem]) -> Vec<Arc<Vec<Statement>>> {
        let mut bodies = Vec::new();
        for item in items {
            match item {
                ModuleItem::FunctionDeclaration(f) => bodies.push(Arc::clone(f.items.as_arc())),
                ModuleItem::TaskDeclaration(t) => bodies.push(Arc::clone(t.items.as_arc())),
                ModuleItem::ClassDeclaration(c) => {
                    for item in &c.items {
                        if let crate::ast::decl::ClassItem::Method(m) = item {
                            match &m.kind {
                                crate::ast::decl::ClassMethodKind::Function(f)
                                | crate::ast::decl::ClassMethodKind::PureVirtual(f)
                                | crate::ast::decl::ClassMethodKind::Extern(f) => {
                                    bodies.push(Arc::clone(f.items.as_arc()));
                                }
                                crate::ast::decl::ClassMethodKind::Task(t) => {
                                    bodies.push(Arc::clone(t.items.as_arc()));
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        bodies
    }

    /// §13.3/§13.4 and §23.10: unrelated parameter bindings must not copy
    /// subroutine syntax without foldable declarations into every prepared instance.
    #[test]
    fn dimension_fold_keeps_unchanged_callable_bodies_shared() {
        let original = module_items(
            "module leaf #(parameter ID=0);
               function int f(input int a); if (a) return a+1; else return 0; endfunction
               task t(input int a); begin repeat (2) $display(a); end endtask
               function int scalar(input int a);
                 int acc; localparam ID=3; acc=a+ID; return acc;
               endfunction
               class C;
                 function int f(input int a); return a+2; endfunction
                 task t(input int a); $display(a); endtask
               endclass
             endmodule",
        );
        let source_bodies = callable_bodies(&original);
        assert_eq!(source_bodies.len(), 5);
        for id in [1, 7, 123] {
            let mut prepared = original.clone();
            literalize_stmt_decl_dims(
                &mut prepared,
                &HashMap::from_iter([("ID".into(), Value::from_u64(id, 32))]),
            );
            for (source, body) in source_bodies.iter().zip(callable_bodies(&prepared)) {
                assert!(Arc::ptr_eq(source, &body), "unchanged body was copied");
            }
        }
    }

    /// §7.4/§13.4: fixed local dimensions must not copy a shared body.
    #[test]
    fn dimension_fold_keeps_name_free_local_dimensions_shared() {
        let original = module_items(
            "module leaf #(parameter ID=0);
               function int f(input int value);
                 logic [31:0] a;
                 logic [8*4-1:0] b;
                 int c[4]; int d[0:2+1]; int dyn[]; int q[$];
                 a=value; b=a; return b;
               endfunction
               task t(); typedef logic [15:0] local_t; endtask
               class C;
                 function int f(input int value);
                   logic [31:0] a[4]; return value;
                 endfunction
               endclass
             endmodule",
        );
        let source_bodies = callable_bodies(&original);
        assert_eq!(source_bodies.len(), 3);
        for id in [1, 7, 123] {
            let mut prepared = original.clone();
            literalize_stmt_decl_dims(
                &mut prepared,
                &HashMap::from_iter([("ID".into(), Value::from_u64(id, 32))]),
            );
            for (source, body) in source_bodies.iter().zip(callable_bodies(&prepared)) {
                assert!(
                    Arc::ptr_eq(source, &body),
                    "fixed local dimensions were copied"
                );
            }
        }
    }

    /// §7.4/§6.20.2: named unpacked dimensions still fold per instance.
    #[test]
    fn dimension_fold_preserves_named_unpacked_dimensions() {
        let original = module_items(
            "module leaf #(parameter N=1);
               task t(); int a[N+0]; int b[N-1:0]; endtask
             endmodule",
        );
        let source_body = callable_bodies(&original).remove(0);
        for size in [3, 7] {
            let mut prepared = original.clone();
            literalize_stmt_decl_dims(
                &mut prepared,
                &HashMap::from_iter([("N".into(), Value::from_u64(size, 32))]),
            );
            let body = callable_bodies(&prepared).remove(0);
            assert!(!Arc::ptr_eq(&source_body, &body));
            for (index, stmt) in body.iter().enumerate() {
                let StatementKind::VarDecl { declarators, .. } = &stmt.kind else {
                    panic!("local declaration expected");
                };
                match &declarators[0].dimensions[0] {
                    UnpackedDimension::Expression { expr, .. } if index == 0 => {
                        assert_eq!(const_eval_i64_with_params(expr, None), Some(size as i64));
                    }
                    UnpackedDimension::Range { left, right, .. } if index == 1 => {
                        assert_eq!(
                            const_eval_i64_with_params(left, None),
                            Some(size as i64 - 1)
                        );
                        assert_eq!(const_eval_i64_with_params(right, None), Some(0));
                    }
                    _ => panic!("unpacked dimension expected"),
                }
            }
        }
    }

    /// §20.8.1, §11.7, §20.6.2: a value system function of a parameter folds
    /// per instance; `$signed`/`$unsigned` reinterpret the operand at its own
    /// width (`$signed` of an 8-bit `8'hff` is -1); a query of a parameter
    /// folds to its type's width, and a query of a variable is left to the
    /// run time.
    #[test]
    fn dimension_fold_value_system_functions() {
        let original = module_items(
            "module leaf #(parameter logic [7:0] P = 8'hff, parameter int N = 1);
               task t();
                 logic [$clog2(N)-1:0] a;
                 logic [($signed(P) < 0 ? 8 : 4)-1:0] b;
                 logic [$unsigned(P)-1:0] c;
                 logic [$bits($signed(N))-1:0] d;
                 logic [$countones($signed(P))-1:0] e;
                 logic [($signed(N) > 0 ? 6 : 2)-1:0] f;
                 logic [7:0] w;
                 logic [$bits(w)-1:0] g;
                 logic [$bits(w) + $clog2(P)-1:0] mixed;
               endtask
             endmodule",
        );
        for n in [256u64, 64] {
            let mut prepared = original.clone();
            literalize_stmt_decl_dims(
                &mut prepared,
                &HashMap::from_iter([
                    ("P".into(), Value::from_u64(0xff, 8)),
                    ("N".into(), Value::from_u64(n, 32)),
                ]),
            );
            let body = callable_bodies(&prepared).remove(0);
            let left = |index: usize| {
                let StatementKind::VarDecl { data_type, .. } = &body[index].kind else {
                    panic!("local declaration expected");
                };
                let DataType::IntegerVector { dimensions, .. } = data_type else {
                    panic!("vector type expected");
                };
                let PackedDimension::Range { left, .. } = &dimensions[0] else {
                    panic!("packed range expected");
                };
                left.clone()
            };
            let folded = |index: usize| match &left(index).kind {
                ExprKind::Number(_) => const_eval_i64_with_params(&left(index), None),
                _ => None,
            };
            assert_eq!(folded(0), Some(n.trailing_zeros() as i64 - 1));
            assert_eq!(folded(1), Some(7), "$signed of 8'hff is -1, not 255");
            assert_eq!(folded(2), Some(254));
            assert_eq!(folded(3), Some(31), "$bits of the 32-bit N");
            assert_eq!(
                folded(4),
                Some(7),
                "$countones($signed(8'hff)) counts 8 bits"
            );
            assert_eq!(folded(5), Some(5));
            assert_eq!(
                folded(7),
                None,
                "a query of a variable stays for the run time"
            );
            // A value name outside the query enables folding. The inner
            // declaration still belongs to the runtime scope.
            assert_eq!(folded(8), None);
            let mut remaining = Vec::new();
            for_each_sub_expr(&left(8), &mut |x| {
                if let ExprKind::Ident(h) = &x.kind {
                    remaining.push(h.path[0].name.name.clone());
                }
            });
            assert_eq!(remaining, ["w"]);
        }
    }

    /// §6.20.2/§6.20.4: a shared body containing declarations still folds
    /// instance widths independently and respects a block's shadowing binding.
    #[test]
    fn dimension_fold_copies_declarations_and_preserves_lexical_bindings() {
        let original = module_items(
            "module leaf #(parameter DW=1);
               function int f();
                 logic [DW-1:0] outer_value;
                 begin : nested
                   localparam DW=5;
                   logic [DW-1:0] inner_value;
                 end
                 return 0;
               endfunction
             endmodule",
        );
        let source_bodies = callable_bodies(&original);
        let original_debug = format!("{:?}", original);
        for width in [12, 65] {
            let mut prepared = original.clone();
            literalize_stmt_decl_dims(
                &mut prepared,
                &HashMap::from_iter([("DW".into(), Value::from_u64(width, 32))]),
            );
            let bodies = callable_bodies(&prepared);
            assert!(!Arc::ptr_eq(&source_bodies[0], &bodies[0]));
            let body = &bodies[0];
            let StatementKind::VarDecl { data_type, .. } = &body[0].kind else {
                panic!("outer declaration expected");
            };
            assert_eq!(resolve_type_width(data_type, None, None), width as u32);
            let StatementKind::SeqBlock { stmts, .. } = &body[1].kind else {
                panic!("nested block expected");
            };
            let StatementKind::VarDecl { data_type, .. } = &stmts[1].kind else {
                panic!("inner declaration expected");
            };
            assert_eq!(resolve_type_width(data_type, None, None), 5);
        }
        assert_eq!(format!("{:?}", original), original_debug);
    }

    /// §6.18/§6.20.2 and §9/§12: declaration discovery must reach nested
    /// control-flow bodies, including typedefs that need instance widths.
    #[test]
    fn dimension_fold_finds_nested_task_declarations_and_typedefs() {
        for wrapper in [
            "begin BODY end",
            "fork BODY join",
            "#1 BODY",
            "wait (1) BODY",
            "if (1) BODY",
            "if (0) ; else BODY",
            "for (int i=0;i<1;i++) BODY",
            "foreach (a[i]) BODY",
            "while (0) BODY",
            "do BODY while (0);",
            "repeat (1) BODY",
            "forever BODY",
            "case (1) 1: BODY endcase",
        ] {
            for declaration in ["word_t value;", "typedef logic [DW-1:0] local_t;"] {
                let nested = wrapper.replace("BODY", &format!("begin {declaration} end"));
                let original = module_items(&format!(
                    "module leaf #(parameter DW=1);
                       typedef logic [DW-1:0] word_t;
                       int a[2];
                       task t(); {nested} endtask
                     endmodule"
                ));
                let source_body = callable_bodies(&original).remove(0);
                for width in [12, 65] {
                    let mut prepared = original.clone();
                    literalize_stmt_decl_dims(
                        &mut prepared,
                        &HashMap::from_iter([("DW".into(), Value::from_u64(width, 32))]),
                    );
                    let body = callable_bodies(&prepared).remove(0);
                    assert!(!Arc::ptr_eq(&source_body, &body), "{wrapper}");
                    fn declared_width(s: &Statement) -> Option<u32> {
                        match &s.kind {
                            StatementKind::VarDecl { data_type, .. } | StatementKind::ParamDecl { data_type, .. } => {
                                Some(resolve_type_width(data_type, None, None))
                            }
                            StatementKind::Typedef(td) => {
                                Some(resolve_type_width(&td.data_type, None, None))
                            }
                            StatementKind::SeqBlock { stmts, .. }
                            | StatementKind::ParBlock { stmts, .. } => {
                                stmts.iter().find_map(declared_width)
                            }
                            StatementKind::TimingControl { stmt, .. }
                            | StatementKind::Wait { stmt, .. } => declared_width(stmt),
                            StatementKind::If {
                                then_stmt,
                                else_stmt,
                                ..
                            } => declared_width(then_stmt)
                                .or_else(|| else_stmt.as_ref().and_then(|s| declared_width(s))),
                            StatementKind::For { body, .. }
                            | StatementKind::Foreach { body, .. }
                            | StatementKind::While { body, .. }
                            | StatementKind::DoWhile { body, .. }
                            | StatementKind::Repeat { body, .. }
                            | StatementKind::Forever { body, .. } => declared_width(body),
                            StatementKind::Case { items, .. } => {
                                items.iter().find_map(|it| declared_width(&it.stmt))
                            }
                            _ => None,
                        }
                    }
                    assert_eq!(
                        body.iter().find_map(declared_width),
                        Some(width as u32),
                        "{wrapper}"
                    );
                }
            }
        }
    }
}
