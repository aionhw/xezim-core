use super::*;

impl DeclaredModuleNames {
    pub(super) fn contains(&self, name: &str) -> bool {
        self.0.contains(name)
    }

    pub(super) fn insert(&mut self, name: String) -> bool {
        Rc::make_mut(&mut self.0).insert(name)
    }
}

/// IEEE 1800-2017 §6.5: data shall be declared before use, except implicit
/// nets (§6.10). Only names actually declared as module data are checked;
/// unresolved names remain the responsibility of implicit-net/name resolution.
/// Lexical scopes shield their own names, while hierarchical and explicitly
/// scoped references retain their separate lookup rules (§23.6, §26).
pub(super) fn check_module_use_before_decl(
    module: &Definition,
    all_defs: Option<&HashMap<String, Definition>>,
    top_level_imports: &[ImportDeclaration],
    design_has_classes: bool,
) -> Vec<String> {
    #[derive(Clone, Default)]
    struct Scope {
        declared: DeclaredModuleNames,
        locals: HashSet<String>,
        objects: HashMap<String, String>,
        constraint_caller: Option<HashSet<String>>,
        unknown_constraint_scope: bool,
        owner: String,
    }
    struct Check<'a, 'b> {
        data: HashSet<String>,
        found: HashSet<String>,
        defs: Option<&'a HashMap<String, Definition<'b>>>,
        root_items: &'b [ModuleItem],
        top_imports: &'a [ImportDeclaration],
        classes: std::cell::OnceCell<ClassIndex<'b>>,
        has_classes: bool,
    }
    #[derive(Default)]
    struct ClassIndex<'a> {
        classes: HashMap<String, &'a ClassDeclaration>,
        owners: HashMap<usize, String>,
        imports: HashMap<String, Vec<ImportItem>>,
    }
    impl<'a> ClassIndex<'a> {
        fn class(&mut self, c: &'a ClassDeclaration, owner: &str) {
            // Package collision normalization may already qualify the class
            // name; keep one owner prefix for explicit imports (§26.3).
            let prefix = format!("{owner}::");
            let name = c.name.name.strip_prefix(&prefix).unwrap_or(&c.name.name);
            let path = format!("{prefix}{name}");
            self.classes.insert(path.clone(), c);
            self.owners
                .insert(c as *const ClassDeclaration as usize, path.clone());
            for it in &c.items {
                match it {
                    ClassItem::Import(i) => self
                        .imports
                        .entry(path.clone())
                        .or_default()
                        .extend(i.items.clone()),
                    ClassItem::Class(c) => self.class(c, &path),
                    _ => {}
                }
            }
        }
        fn items(&mut self, items: &'a [ModuleItem], owner: &str) {
            for it in items {
                match it {
                    ModuleItem::ClassDeclaration(c) => self.class(c, owner),
                    ModuleItem::ImportDeclaration(i) => self
                        .imports
                        .entry(owner.to_string())
                        .or_default()
                        .extend(i.items.clone()),
                    ModuleItem::GenerateRegion(g) => self.items(&g.items, owner),
                    ModuleItem::CheckerDeclaration(c) => {
                        self.items(&c.items, &format!("{owner}::$checker{}", c.span.start))
                    }
                    ModuleItem::GenerateIf(g) => {
                        for (i, (_, items)) in g.branches.iter().enumerate() {
                            self.items(items, &format!("{owner}::$if{}_{}", g.span.start, i));
                        }
                    }
                    ModuleItem::GenerateFor(g) => {
                        self.items(&g.items, &format!("{owner}::$for{}", g.span.start))
                    }
                    ModuleItem::GenerateCase(g) => {
                        for (i, arm) in g.arms.iter().enumerate() {
                            self.items(
                                &arm.items,
                                &format!("{owner}::$case{}_{}", g.span.start, i),
                            );
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    impl<'a, 'b> Check<'a, 'b> {
        fn name(&mut self, name: &str, scope: &Scope) {
            if crate::sv_parser::strip_unit_scope_name(name).is_some() {
                return;
            }
            if !scope.unknown_constraint_scope
                && self.data.contains(name)
                && !scope.declared.contains(name)
                && !scope.locals.contains(name)
            {
                self.found.insert(name.to_string());
            }
        }

        fn expr(&mut self, e: &Expression, scope: &Scope) {
            match &e.kind {
                ExprKind::Ident(h) => {
                    // A dotted root can be either an instance or a data
                    // receiver (§23.6). Only a known module data root counts.
                    // $unit::x/pkg::x and this/super have their own scopes.
                    if let Some(first) = h.path.first() {
                        if h.root.is_none() {
                            self.name(&first.name.name, scope);
                        } else if h.root.as_deref() == Some(LOCAL_SCOPE_ROOT) {
                            let mut caller = scope.clone();
                            if let Some(locals) = &scope.constraint_caller {
                                caller.locals = locals.clone();
                            }
                            caller.unknown_constraint_scope = false;
                            self.name(&first.name.name, &caller);
                        }
                    }
                    for s in h.path.iter().flat_map(|s| &s.selects) {
                        self.expr(s, scope);
                    }
                }
                ExprKind::Unary { operand: x, .. }
                | ExprKind::Paren(x)
                | ExprKind::MemberAccess { expr: x, .. }
                | ExprKind::Specialization { base: x, .. }
                | ExprKind::ShallowCopy { source: x }
                | ExprKind::NamedArg { expr: Some(x), .. }
                | ExprKind::Tagged { inner: Some(x), .. } => self.expr(x, scope),
                ExprKind::Matches { expr, pattern } => {
                    self.expr(expr, scope);
                    self.pattern(pattern, scope);
                }
                ExprKind::Binary {
                    op: BinaryOp::LogAnd,
                    left,
                    right,
                } => {
                    self.expr(left, scope);
                    let mut inner = scope.clone();
                    condition_bindings(left, &mut inner.locals);
                    self.expr(right, &inner);
                }
                ExprKind::Binary { left, right, .. }
                | ExprKind::Range(left, right)
                | ExprKind::Index {
                    expr: left,
                    index: right,
                }
                | ExprKind::AssignExpr {
                    lvalue: left,
                    rvalue: right,
                } => {
                    self.expr(left, scope);
                    self.expr(right, scope);
                }
                ExprKind::Conditional {
                    condition,
                    then_expr,
                    else_expr,
                } => {
                    self.expr(condition, scope);
                    let mut inner = scope.clone();
                    condition_bindings(condition, &mut inner.locals);
                    self.expr(then_expr, &inner);
                    self.expr(else_expr, scope);
                }
                ExprKind::RangeSelect {
                    expr, left, right, ..
                } => {
                    self.expr(expr, scope);
                    self.expr(left, scope);
                    self.expr(right, scope);
                }
                ExprKind::Replication { count, exprs } => {
                    self.expr(count, scope);
                    for x in exprs {
                        self.expr(x, scope);
                    }
                }
                ExprKind::Inside { expr, ranges } => {
                    self.expr(expr, scope);
                    for x in ranges {
                        self.expr(x, scope);
                    }
                }
                ExprKind::Concatenation(xs) => {
                    for x in xs {
                        self.expr(x, scope);
                    }
                }
                ExprKind::StreamOp {
                    slice_size, exprs, ..
                } => {
                    if let Some(x) = slice_size {
                        self.expr(x, scope);
                    }
                    for x in exprs {
                        self.expr(x, scope);
                    }
                }
                ExprKind::AssignmentPattern(items) => {
                    for it in items {
                        match it {
                            AssignmentPatternItem::Ordered(x)
                            | AssignmentPatternItem::Named(_, x)
                            | AssignmentPatternItem::Default(x) => self.expr(x, scope),
                            AssignmentPatternItem::Typed(ty, x) => {
                                self.ty(ty, scope);
                                self.expr(x, scope);
                            }
                            AssignmentPatternItem::Keyed(k, x) => {
                                self.expr(k, scope);
                                self.expr(x, scope);
                            }
                        }
                    }
                }
                ExprKind::Call { func, args } => {
                    // A bare callee names a subroutine/constructor, not data.
                    // Member receivers and hierarchy selects still read data.
                    match &func.kind {
                        ExprKind::Ident(h) if h.path.len() == 1 => {
                            for s in &h.path[0].selects {
                                self.expr(s, scope);
                            }
                        }
                        _ => self.expr(func, scope),
                    }
                    if let Some(inner) = self.randomize_scope(func, scope) {
                        // §18.11: object randomize actuals name its properties,
                        // while std::randomize actuals name caller data.
                        for x in args {
                            self.expr(x, &inner);
                        }
                    } else {
                        for x in args {
                            self.expr(x, scope);
                        }
                    }
                }
                ExprKind::SystemCall { name, args } if name == "$sva_locals" => {
                    // §16.10: parser markers retain property/sequence local
                    // declarations. Their identifier operands bind names.
                    let mut inner = scope.clone();
                    if let Some((body, decls)) = args.split_last() {
                        for d in decls {
                            if let ExprKind::SystemCall { name, args } = &d.kind
                                && name == "$sva_local"
                                && let Some(Expression {
                                    kind: ExprKind::Ident(h),
                                    ..
                                }) = args.get(1)
                                && let Some(first) = h.path.first()
                            {
                                inner.locals.insert(first.name.name.clone());
                            }
                        }
                        for d in decls {
                            if let ExprKind::SystemCall { name, args } = &d.kind
                                && name == "$sva_local"
                            {
                                for (i, e) in args.iter().enumerate() {
                                    if i != 1 {
                                        self.expr(e, &inner);
                                    }
                                }
                            } else {
                                self.expr(d, &inner);
                            }
                        }
                        self.expr(body, &inner);
                    }
                }
                ExprKind::SystemCall { args, .. } => {
                    // Casts also lower to system-call nodes; their operands
                    // follow the same §6.5 declaration rule as other reads.
                    for x in args {
                        self.expr(x, scope);
                    }
                }
                ExprKind::WithClause { expr, filter } => {
                    let mut inner = scope.clone();
                    // §7.12.1: a simple method argument before `with` names
                    // the iterator, rather than evaluating a data argument.
                    if let ExprKind::Call { func, args } = &expr.kind
                        && array_with_method(func)
                        && let [arg] = args.as_slice()
                        && let ExprKind::Ident(h) = &arg.kind
                        && h.root.is_none()
                        && h.path.len() == 1
                        && h.path[0].selects.is_empty()
                    {
                        inner.locals.insert(h.path[0].name.name.clone());
                        self.expr(func, scope);
                    } else {
                        inner.locals.insert("item".to_string());
                        self.expr(expr, scope);
                    }
                    self.expr(filter, &inner);
                }
                ExprKind::RandomizeWith { call, constraints } => {
                    self.expr(call, scope);
                    let mut inner = scope.clone();
                    inner.constraint_caller = Some(scope.locals.clone());
                    if let ExprKind::Call { func, .. } = &call.kind
                        && let Some(object_scope) = self.randomize_scope(func, scope)
                    {
                        inner.locals = object_scope.locals;
                        inner.unknown_constraint_scope = object_scope.unknown_constraint_scope;
                    }
                    for c in constraints {
                        self.constraint(c, &inner);
                    }
                }
                ExprKind::SvaClocked { events, body } => {
                    for ev in events {
                        self.event_expr(ev, scope);
                    }
                    self.expr(body, scope);
                }
                ExprKind::TypeLiteral(ty) => self.ty(ty, scope),
                ExprKind::TypedPattern { ty, pattern } => {
                    self.ty(ty, scope);
                    self.expr(pattern, scope);
                }
                _ => {}
            }
        }

        fn packed(&mut self, dims: &[PackedDimension], scope: &Scope) {
            for d in dims {
                if let PackedDimension::Range { left, right, .. } = d {
                    self.expr(left, scope);
                    self.expr(right, scope);
                }
            }
        }
        fn unpacked(&mut self, dims: &[UnpackedDimension], scope: &Scope) {
            for d in dims {
                match d {
                    UnpackedDimension::Range { left, right, .. } => {
                        self.expr(left, scope);
                        self.expr(right, scope);
                    }
                    UnpackedDimension::Expression { expr, .. } => self.expr(expr, scope),
                    UnpackedDimension::Queue {
                        max_size: Some(x), ..
                    } => self.expr(x, scope),
                    UnpackedDimension::Associative {
                        data_type: Some(ty),
                        ..
                    } => self.ty(ty, scope),
                    _ => {}
                }
            }
        }
        fn ty(&mut self, ty: &DataType, scope: &Scope) {
            match ty {
                DataType::IntegerVector { dimensions, .. }
                | DataType::Implicit { dimensions, .. } => self.packed(dimensions, scope),
                DataType::TypeReference {
                    name,
                    dimensions,
                    type_args,
                    ..
                } => {
                    self.packed(dimensions, scope);
                    for arg in name
                        .scopes
                        .iter()
                        .flat_map(|s| &s.type_args)
                        .chain(type_args)
                    {
                        self.expr(arg, scope);
                    }
                }
                DataType::Interface { type_args, .. } => {
                    for arg in type_args {
                        self.expr(arg, scope);
                    }
                }
                DataType::Struct(s) => {
                    self.packed(&s.dimensions, scope);
                    for m in &s.members {
                        self.ty(&m.data_type, scope);
                        for d in &m.declarators {
                            self.unpacked(&d.dimensions, scope);
                            if let Some(x) = &d.init {
                                self.expr(x, scope);
                            }
                        }
                    }
                }
                DataType::Enum(e) => {
                    if let Some(ty) = &e.base_type {
                        self.ty(ty, scope);
                    }
                    self.packed(&e.dimensions, scope);
                    let mut inner = scope.clone();
                    for m in &e.members {
                        inner.locals.insert(m.name.name.clone());
                        if let Some((lo, hi)) = &m.range {
                            self.expr(lo, &inner);
                            self.expr(hi, &inner);
                        }
                        if let Some(x) = &m.init {
                            self.expr(x, &inner);
                        }
                    }
                }
                _ => {}
            }
        }
        fn parameter(&mut self, p: &ParameterDeclaration, scope: &Scope) {
            match &p.kind {
                ParameterKind::Data {
                    data_type,
                    assignments,
                } => {
                    self.ty(data_type, scope);
                    for a in assignments {
                        self.unpacked(&a.dimensions, scope);
                        if let Some(e) = &a.init {
                            self.expr(e, scope);
                        }
                    }
                }
                ParameterKind::Type { assignments } => {
                    for a in assignments {
                        if let Some(ty) = &a.init {
                            self.ty(ty, scope);
                        }
                    }
                }
            }
        }
        fn param_value(&mut self, v: &ParamValue, scope: &Scope) {
            match v {
                ParamValue::Expr(e) => self.expr(e, scope),
                ParamValue::Type(ty) => self.ty(ty, scope),
            }
        }
        fn var(&mut self, d: &VarDeclarator, scope: &Scope) {
            self.unpacked(&d.dimensions, scope);
            if let Some(x) = &d.init {
                self.expr(x, scope);
            }
        }
        fn typedef(&mut self, td: &TypedefDeclaration, scope: &Scope) {
            self.ty(&td.data_type, scope);
            self.unpacked(&td.dimensions, scope);
        }
        fn event_expr(&mut self, ev: &EventExpr, scope: &Scope) {
            self.expr(&ev.expr, scope);
            if let Some(x) = &ev.iff {
                self.expr(x, scope);
            }
        }
        fn event(&mut self, ev: &EventControl, scope: &Scope) {
            match ev {
                EventControl::Identifier(id) => self.name(&id.name, scope),
                EventControl::HierIdentifier(e) => self.expr(e, scope),
                EventControl::EventExpr(evs) => {
                    for ev in evs {
                        self.event_expr(ev, scope);
                    }
                }
                _ => {}
            }
        }
        fn pattern(&mut self, p: &Pattern, scope: &Scope) {
            match p {
                Pattern::Expr(e) => self.expr(e, scope),
                Pattern::Tagged { inner: Some(p), .. } => self.pattern(p, scope),
                Pattern::Struct(items) => {
                    for (_, p) in items {
                        self.pattern(p, scope);
                    }
                }
                _ => {}
            }
        }
        fn assertion(&mut self, a: &AssertionStatement, scope: &Scope) {
            self.expr(&a.expr, scope);
            if let Some(ev) = &a.inferred_clock {
                self.event_expr(ev, scope);
            }
            for s in [&a.action, &a.else_action].into_iter().flatten() {
                self.stmt(s, scope);
            }
        }
        fn stmts(&mut self, stmts: &[Statement], scope: &Scope) {
            let mut inner = scope.clone();
            // These names belong to the block, even when their own local
            // declaration order is invalid. This pass checks MODULE data,
            // not the separate ordering of local declarations (§6.21).
            for s in stmts {
                match &s.kind {
                    StatementKind::VarDecl {
                        declarators,
                        data_type,
                        ..
                    }
                    | StatementKind::ParamDecl {
                        declarators,
                        data_type,
                        ..
                    } => {
                        for d in declarators {
                            inner.locals.insert(d.name.name.clone());
                            self.object(&d.name.name, data_type, &mut inner);
                        }
                        enum_names(data_type, &mut inner.locals);
                    }
                    StatementKind::Typedef(td) => {
                        inner.locals.insert(td.name.name.clone());
                        enum_names(&td.data_type, &mut inner.locals);
                    }
                    _ => {}
                }
            }
            for s in stmts {
                self.stmt(s, &inner);
            }
        }
        fn stmt(&mut self, st: &Statement, scope: &Scope) {
            use StatementKind as K;
            match &st.kind {
                K::Expr(e) | K::Return(Some(e)) | K::Coverpoint { expr: e, .. } => {
                    self.expr(e, scope)
                }
                K::BlockingAssign { lvalue, rvalue }
                | K::ProceduralContinuous(
                    ProceduralContinuous::Assign { lvalue, rvalue }
                    | ProceduralContinuous::Force { lvalue, rvalue },
                ) => {
                    self.expr(lvalue, scope);
                    self.expr(rvalue, scope);
                }
                K::ProceduralContinuous(
                    ProceduralContinuous::Deassign(e) | ProceduralContinuous::Release(e),
                ) => self.expr(e, scope),
                K::NonblockingAssign {
                    lvalue,
                    delay,
                    rvalue,
                } => {
                    self.expr(lvalue, scope);
                    if let Some(d) = delay {
                        self.expr(d, scope);
                    }
                    self.expr(rvalue, scope);
                }
                K::VarDecl {
                    data_type,
                    declarators,
                    ..
                }
                | K::ParamDecl {
                    data_type,
                    declarators,
                    ..
                } => {
                    self.ty(data_type, scope);
                    for d in declarators {
                        self.var(d, scope);
                    }
                }
                K::For {
                    init,
                    condition,
                    step,
                    body,
                } => {
                    let mut inner = scope.clone();
                    for i in init {
                        match i {
                            ForInit::VarDecl {
                                data_type,
                                name,
                                init,
                            } => {
                                self.ty(data_type, &inner);
                                // §12.7.1: the declared iterator owns its
                                // initializer as well as the loop body.
                                inner.locals.insert(name.name.clone());
                                self.object(&name.name, data_type, &mut inner);
                                self.expr(init, &inner);
                            }
                            ForInit::Assign { lvalue, rvalue } => {
                                self.expr(lvalue, &inner);
                                self.expr(rvalue, &inner);
                            }
                        }
                    }
                    if let Some(c) = condition {
                        self.expr(c, &inner);
                    }
                    for e in step {
                        self.expr(e, &inner);
                    }
                    self.stmt(body, &inner);
                }
                K::Foreach { array, vars, body } => {
                    self.expr(array, scope);
                    let mut inner = scope.clone();
                    for v in vars.iter().flatten() {
                        inner.locals.insert(v.name.clone());
                    }
                    self.stmt(body, &inner);
                }
                K::ForeachTail { body, .. }
                | K::Forever { body }
                | K::ForeverTail { body }
                | K::RsAction { body } => self.stmt(body, scope),
                K::SeqBlock { stmts, .. } | K::ParBlock { stmts, .. } => self.stmts(stmts, scope),
                K::TimingControl { control, stmt } => {
                    match control {
                        TimingControl::Delay(e) => self.expr(e, scope),
                        TimingControl::Event(ev) => self.event(ev, scope),
                    }
                    self.stmt(stmt, scope);
                }
                K::If {
                    condition,
                    then_stmt,
                    else_stmt,
                    ..
                } => {
                    self.expr(condition, scope);
                    let mut inner = scope.clone();
                    condition_bindings(condition, &mut inner.locals);
                    self.stmt(then_stmt, &inner);
                    if let Some(s) = else_stmt {
                        self.stmt(s, scope);
                    }
                }
                K::Case { expr, items, .. } => {
                    self.expr(expr, scope);
                    for it in items {
                        let mut inner = scope.clone();
                        if let Some(p) = &it.pattern {
                            self.pattern(p, scope);
                            let mut bindings = Vec::new();
                            collect_pattern_bindings(p, &mut bindings);
                            inner.locals.extend(bindings);
                        } else {
                            for p in &it.patterns {
                                self.expr(p, scope);
                            }
                        }
                        if let Some(g) = &it.guard {
                            self.expr(g, &inner);
                        }
                        self.stmt(&it.stmt, &inner);
                    }
                }
                K::While { condition, body }
                | K::DoWhile { condition, body }
                | K::Repeat {
                    count: condition,
                    body,
                } => {
                    self.expr(condition, scope);
                    self.stmt(body, scope);
                }
                K::Wait { condition, stmt } => {
                    self.expr(condition, scope);
                    self.stmt(stmt, scope);
                }
                K::RandCase { items } => {
                    for (e, s) in items {
                        self.expr(e, scope);
                        self.stmt(s, scope);
                    }
                }
                K::EventTrigger { name, target, .. } => {
                    if let Some(e) = target {
                        self.expr(e, scope);
                    } else {
                        self.name(&name.name, scope);
                    }
                }
                K::WaitOrder {
                    events, pass, fail, ..
                } => {
                    for id in events {
                        self.name(&id.name, scope);
                    }
                    for s in [pass, fail].into_iter().flatten() {
                        self.stmt(s, scope);
                    }
                }
                K::Assertion(a) => self.assertion(a, scope),
                K::Typedef(td) => self.typedef(td, scope),
                K::Cross { items, .. } => {
                    for e in items {
                        self.expr(e, scope);
                    }
                }
                _ => {}
            }
        }
        fn ports(&mut self, ports: &[FunctionPort], scope: &mut Scope) {
            // §13.5.3: defaults resolve in the declaration's containing
            // scope; a same-named formal cannot hide enclosing module data.
            for p in ports {
                self.ty(&p.data_type, scope);
                self.unpacked(&p.dimensions, scope);
                if let Some(e) = &p.default {
                    self.expr(e, scope);
                }
            }
            for p in ports {
                scope.locals.insert(p.name.name.clone());
                self.object(&p.name.name, &p.data_type, scope);
            }
        }
        fn function(&mut self, f: &FunctionDeclaration, scope: &Scope) {
            let mut inner = scope.clone();
            inner.locals.insert(f.name.name.name.clone());
            self.ports(&f.ports, &mut inner);
            self.ty(&f.return_type, &inner);
            self.stmts(&f.items, &inner);
        }
        fn task(&mut self, t: &TaskDeclaration, scope: &Scope) {
            let mut inner = scope.clone();
            inner.locals.insert(t.name.name.name.clone());
            self.ports(&t.ports, &mut inner);
            self.stmts(&t.items, &inner);
        }
        fn range(&mut self, r: &ConstraintRange, scope: &Scope) {
            match r {
                ConstraintRange::Value(e) => self.expr(e, scope),
                ConstraintRange::Range { lo, hi } => {
                    self.expr(lo, scope);
                    self.expr(hi, scope);
                }
            }
        }
        fn constraint(&mut self, c: &ConstraintItem, scope: &Scope) {
            match c {
                ConstraintItem::Expr(e) => self.expr(e, scope),
                ConstraintItem::Inside {
                    expr,
                    range,
                    dist_weights,
                    ..
                } => {
                    self.expr(expr, scope);
                    for r in range {
                        self.range(r, scope);
                    }
                    for w in dist_weights.iter().flatten() {
                        let (DistWeight::Each(e) | DistWeight::Total(e)) = w;
                        self.expr(e, scope);
                    }
                }
                ConstraintItem::Implication {
                    condition,
                    constraint,
                    ..
                } => {
                    self.expr(condition, scope);
                    self.constraint(constraint, scope);
                }
                ConstraintItem::IfElse {
                    condition,
                    then_item,
                    else_item,
                    ..
                } => {
                    self.expr(condition, scope);
                    self.constraint(then_item, scope);
                    if let Some(c) = else_item {
                        self.constraint(c, scope);
                    }
                }
                ConstraintItem::Foreach {
                    array, vars, item, ..
                } => {
                    self.expr(array, scope);
                    let mut inner = scope.clone();
                    for v in vars.iter().flatten() {
                        inner.locals.insert(v.name.clone());
                    }
                    self.constraint(item, &inner);
                }
                ConstraintItem::Solve {
                    before,
                    after,
                    before_paths,
                    after_paths,
                    ..
                } => {
                    for id in before.iter().chain(after) {
                        self.name(&id.name, scope);
                    }
                    for e in before_paths.iter().chain(after_paths) {
                        self.expr(e, scope);
                    }
                }
                ConstraintItem::Soft(c) => self.constraint(c, scope),
                ConstraintItem::Block(cs) => {
                    for c in cs {
                        self.constraint(c, scope);
                    }
                }
                ConstraintItem::Unique { exprs, .. } => {
                    for e in exprs {
                        self.expr(e, scope);
                    }
                }
            }
        }
        fn class_scope(&self, c: &ClassDeclaration, scope: &Scope, static_only: bool) -> Scope {
            let mut inner = scope.clone();
            inner.owner = self.class_owner(c).to_string();
            // §8.4/§8.16/§8.24: later/inherited members and imports belong
            // to the class, including in its out-of-block definitions.
            self.members(
                c,
                &mut inner.locals,
                &mut HashSet::default(),
                false,
                static_only,
            );
            self.member_objects(c, &mut inner, static_only);
            for it in &c.items {
                if let ClassItem::Import(i) = it {
                    self.import_names(i, &mut inner.locals, &mut HashSet::default());
                }
            }
            inner
        }
        fn class(&mut self, c: &ClassDeclaration, scope: &Scope) {
            let mut inner = self.class_scope(c, scope, false);
            for p in &c.params {
                self.parameter(p, &inner);
            }
            if let Some(ext) = &c.extends {
                for a in &ext.args {
                    self.param_value(a, &inner);
                }
            }
            for it in &c.items {
                match it {
                    ClassItem::Property(p) => {
                        self.ty(&p.data_type, &inner);
                        for d in &p.declarators {
                            self.object(&d.name.name, &p.data_type, &mut inner);
                            self.var(d, &inner);
                        }
                    }
                    ClassItem::Method(m) => match &m.kind {
                        ClassMethodKind::Function(f)
                        | ClassMethodKind::PureVirtual(f)
                        | ClassMethodKind::Extern(f) => self.function(f, &inner),
                        ClassMethodKind::Task(t) => self.task(t, &inner),
                    },
                    ClassItem::Constraint(c) => {
                        for c in &c.items {
                            self.constraint(c, &inner);
                        }
                    }
                    ClassItem::Typedef(td) => self.typedef(td, &inner),
                    ClassItem::Parameter(p) => self.parameter(p, &inner),
                    ClassItem::Class(nested) => {
                        // §8.23: nested classes inherit lexical access to
                        // outer static members/parameters, not instance data.
                        let outer = self.class_scope(c, scope, true);
                        self.class(nested, &outer);
                    }
                    ClassItem::Covergroup(cg) => self.covergroup(cg, &inner),
                    ClassItem::Import(i) => {
                        self.import_names(i, &mut inner.locals, &mut HashSet::default())
                    }
                    _ => {}
                }
            }
        }
        fn cross_select(&mut self, s: &CrossSelect, scope: &Scope) {
            match s {
                CrossSelect::Binsof { intersect, .. } => {
                    for r in intersect.iter().flatten() {
                        self.range(r, scope);
                    }
                }
                CrossSelect::Not(s) => self.cross_select(s, scope),
                CrossSelect::And(a, b) | CrossSelect::Or(a, b) => {
                    self.cross_select(a, scope);
                    self.cross_select(b, scope);
                }
                CrossSelect::With(s, e) => {
                    self.cross_select(s, scope);
                    self.expr(e, scope);
                }
                CrossSelect::All => {}
            }
        }
        fn covergroup(&mut self, cg: &CovergroupDeclaration, scope: &Scope) {
            let mut inner = scope.clone();
            self.ports(&cg.ports, &mut inner);
            self.ports(&cg.sample_ports, &mut inner);
            for it in &cg.items {
                match it {
                    CovergroupItem::Coverpoint(cp) => {
                        if let Some(n) = &cp.name {
                            inner.locals.insert(n.name.clone());
                        }
                    }
                    CovergroupItem::Cross(c) => {
                        if let Some(n) = &c.name {
                            inner.locals.insert(n.name.clone());
                        }
                    }
                    _ => {}
                }
            }
            if let Some(ev) = &cg.event {
                self.event(ev, &inner);
            }
            for it in &cg.items {
                match it {
                    CovergroupItem::Option { val, .. } | CovergroupItem::TypeOption { val, .. } => {
                        self.expr(val, &inner)
                    }
                    CovergroupItem::Coverpoint(cp) => {
                        // The sampled expression is outside its label's
                        // namespace; `w: coverpoint w` samples module w.
                        let mut sampled = inner.clone();
                        if let Some(n) = &cp.name
                            && !scope.locals.contains(&n.name)
                        {
                            sampled.locals.remove(&n.name);
                        }
                        self.expr(&cp.expr, &sampled);
                        if let Some(e) = &cp.iff_guard {
                            self.expr(e, &inner);
                        }
                        for (_, e) in &cp.options {
                            self.expr(e, &inner);
                        }
                        for b in &cp.bins {
                            for r in &b.values {
                                self.range(r, &inner);
                            }
                            for e in [&b.array_size, &b.iff_guard].into_iter().flatten() {
                                self.expr(e, &inner);
                            }
                            let mut filter_scope = inner.clone();
                            filter_scope.locals.insert("item".to_string());
                            if let Some(e) = &b.with_filter {
                                self.expr(e, &filter_scope);
                            }
                            for steps in &b.transitions {
                                for step in steps {
                                    for r in &step.values {
                                        self.range(r, &inner);
                                    }
                                    if let Some(r) = &step.repeat {
                                        self.expr(&r.lo, &inner);
                                        if let Some(e) = &r.hi {
                                            self.expr(e, &inner);
                                        }
                                    }
                                }
                            }
                        }
                    }
                    CovergroupItem::Cross(c) => {
                        for id in &c.items {
                            self.name(&id.name, &inner);
                        }
                        if let Some(e) = &c.iff_guard {
                            self.expr(e, &inner);
                        }
                        for (_, e) in &c.options {
                            self.expr(e, &inner);
                        }
                        for b in &c.bins {
                            self.cross_select(&b.select, &inner);
                            if let Some(e) = &b.iff_guard {
                                self.expr(e, &inner);
                            }
                        }
                    }
                }
            }
        }
        fn instantiation(&mut self, mi: &ModuleInstantiation, scope: &Scope) {
            for p in mi.params.iter().flatten() {
                match p {
                    ParamConnection::Ordered(Some(v))
                    | ParamConnection::Named { value: Some(v), .. } => self.param_value(v, scope),
                    _ => {}
                }
            }
            for i in &mi.instances {
                self.unpacked(&i.dimensions, scope);
                for c in &i.connections {
                    match c {
                        PortConnection::Ordered(Some(e))
                        | PortConnection::Named { expr: Some(e), .. } => self.expr(e, scope),
                        PortConnection::Named {
                            name,
                            expr: None,
                            implicit: true,
                        } => self.name(&name.name, scope),
                        _ => {}
                    }
                }
            }
        }
        fn generated(&mut self, items: &[ModuleItem], scope: &Scope, tag: &str) {
            let mut inner = scope.clone();
            inner.owner = format!("{}::{tag}", scope.owner);
            item_names(items, &mut inner.locals);
            self.item_import_names(items, &mut inner.locals);
            self.items(items, &mut inner);
        }
        fn items(&mut self, items: &[ModuleItem], scope: &mut Scope) {
            for it in items {
                match it {
                    ModuleItem::NetDeclaration(d) => {
                        self.ty(&d.data_type, scope);
                        for e in [&d.delay, &d.delay_fall, &d.delay_off]
                            .into_iter()
                            .flatten()
                        {
                            self.expr(e, scope);
                        }
                        for d in &d.declarators {
                            // §6.5: earlier declarators may be used, later
                            // declarators in the SAME declaration may not.
                            scope.declared.insert(d.name.name.clone());
                            self.unpacked(&d.dimensions, scope);
                            if let Some(e) = &d.init {
                                self.expr(e, scope);
                            }
                        }
                    }
                    ModuleItem::DataDeclaration(d) => {
                        self.ty(&d.data_type, scope);
                        let data_type = &d.data_type;
                        for d in &d.declarators {
                            scope.declared.insert(d.name.name.clone());
                            self.object(&d.name.name, data_type, scope);
                            self.var(d, scope);
                        }
                    }
                    ModuleItem::PortDeclaration(d) => {
                        self.ty(&d.data_type, scope);
                        let data_type = &d.data_type;
                        for d in &d.declarators {
                            scope.declared.insert(d.name.name.clone());
                            self.object(&d.name.name, data_type, scope);
                            self.var(d, scope);
                        }
                    }
                    ModuleItem::ParameterDeclaration(p) | ModuleItem::LocalparamDeclaration(p) => {
                        self.parameter(p, scope)
                    }
                    ModuleItem::TypedefDeclaration(td) => self.typedef(td, scope),
                    ModuleItem::InitialConstruct(c) => self.stmt(&c.stmt, scope),
                    ModuleItem::AlwaysConstruct(c) => self.stmt(&c.stmt, scope),
                    ModuleItem::FinalConstruct(c) => self.stmt(&c.stmt, scope),
                    ModuleItem::ContinuousAssign(c) => {
                        for e in [&c.delay, &c.delay_fall, &c.delay_off]
                            .into_iter()
                            .flatten()
                        {
                            self.expr(e, scope);
                        }
                        for (lhs, rhs) in &c.assignments {
                            self.expr(lhs, scope);
                            self.expr(rhs, scope);
                        }
                    }
                    ModuleItem::ModuleInstantiation(mi) => self.instantiation(mi, scope),
                    ModuleItem::GateInstantiation(g) => {
                        for e in [&g.delay, &g.delay_fall, &g.delay_off].into_iter().flatten() {
                            self.expr(e, scope);
                        }
                        for e in g.instances.iter().flat_map(|i| &i.terminals) {
                            self.expr(e, scope);
                        }
                    }
                    // §8.24: out-of-block bodies resolve class members in
                    // their class scope, including later/inherited members.
                    ModuleItem::TaskDeclaration(t) if !t.name.scopes.is_empty() => {
                        if let Some(c) = self.class_named(&t.name.scope_prefix(), &scope.owner) {
                            let inner = self.class_scope(c, scope, false);
                            self.task(t, &inner);
                        }
                    }
                    ModuleItem::FunctionDeclaration(f) if !f.name.scopes.is_empty() => {
                        if let Some(c) = self.class_named(&f.name.scope_prefix(), &scope.owner) {
                            let inner = self.class_scope(c, scope, false);
                            self.function(f, &inner);
                        }
                    }
                    ModuleItem::OutOfClassConstraint {
                        class_name, items, ..
                    } => {
                        if let Some(c) = self.class_named(class_name, &scope.owner) {
                            // The AST retains only the owner's leaf for this
                            // form. When several owners share it, the original
                            // qualification cannot be reconstructed safely.
                            let ambiguous = !class_name.contains("::")
                                && self.class_index().classes.values().any(|other| {
                                    other.name.name == *class_name && !std::ptr::eq(*other, c)
                                });
                            if !ambiguous {
                                let inner = self.class_scope(c, scope, false);
                                for c in items {
                                    self.constraint(c, &inner);
                                }
                            }
                        }
                    }
                    ModuleItem::CheckerDeclaration(c) => {
                        // §17.2: checker formals/declarations have their own
                        // scope; unqualified free names retain lexical lookup.
                        let mut inner = scope.clone();
                        inner.owner = format!("{}::$checker{}", scope.owner, c.span.start);
                        item_names(&c.items, &mut inner.locals);
                        self.item_import_names(&c.items, &mut inner.locals);
                        match &c.ports {
                            PortList::Ansi(ports) => {
                                for p in ports {
                                    inner.locals.insert(p.name.name.clone());
                                }
                                for p in ports {
                                    if let Some(ty) = &p.data_type {
                                        self.ty(ty, &inner);
                                        self.object(&p.name.name, ty, &mut inner);
                                    }
                                    self.unpacked(&p.dimensions, &inner);
                                    if let Some(e) = &p.default {
                                        self.expr(e, &inner);
                                    }
                                }
                            }
                            PortList::NonAnsi(names) => {
                                for name in names {
                                    inner.locals.insert(name.name.clone());
                                }
                            }
                            PortList::Empty => {}
                        }
                        self.items(&c.items, &mut inner);
                    }
                    ModuleItem::TaskDeclaration(t) => self.task(t, scope),
                    ModuleItem::FunctionDeclaration(f) => self.function(f, scope),
                    // A generate REGION is not a new scope (§27); named or
                    // unnamed generate BLOCKS below introduce lexical scopes.
                    ModuleItem::GenerateRegion(g) => self.items(&g.items, scope),
                    ModuleItem::GenerateIf(g) => {
                        for (i, (c, items)) in g.branches.iter().enumerate() {
                            if let Some(c) = c {
                                self.expr(c, scope);
                            }
                            self.generated(items, scope, &format!("$if{}_{}", g.span.start, i));
                        }
                    }
                    ModuleItem::GenerateFor(g) => {
                        let mut inner = scope.clone();
                        // §27.4: the loop genvar becomes an implicit localparam
                        // inside every generated iteration's scope.
                        inner.locals.insert(g.var.clone());
                        if let Some(e) = &g.init {
                            self.expr(e, &inner);
                        }
                        self.expr(&g.cond, &inner);
                        self.expr(&g.incr, &inner);
                        self.generated(&g.items, &inner, &format!("$for{}", g.span.start));
                    }
                    ModuleItem::GenerateCase(g) => {
                        self.expr(&g.selector, scope);
                        for (i, arm) in g.arms.iter().enumerate() {
                            for e in &arm.values {
                                self.expr(e, scope);
                            }
                            self.generated(
                                &arm.items,
                                scope,
                                &format!("$case{}_{}", g.span.start, i),
                            );
                        }
                    }
                    ModuleItem::ClassDeclaration(c) => self.class(c, scope),
                    ModuleItem::AssertionItem(a) => self.assertion(a, scope),
                    ModuleItem::PropertyDeclaration(p) => {
                        let mut inner = scope.clone();
                        for p in &p.ports {
                            inner.locals.insert(p.name.clone());
                        }
                        self.stmts(&p.items, &inner);
                        if let Some(e) = &p.body {
                            self.expr(e, &inner);
                        }
                    }
                    ModuleItem::SequenceDeclaration(p) => {
                        let mut inner = scope.clone();
                        for p in &p.ports {
                            inner.locals.insert(p.name.clone());
                        }
                        self.stmts(&p.items, &inner);
                        if let Some(e) = &p.body {
                            self.expr(e, &inner);
                        }
                    }
                    ModuleItem::LetDeclaration(l) => {
                        let mut inner = scope.clone();
                        for (name, _, _) in l.formals() {
                            inner.locals.insert(name.name.clone());
                        }
                        for (_, ty, e) in l.formals() {
                            if let Some(ty) = ty {
                                self.ty(ty, &inner);
                            }
                            if let Some(e) = e {
                                self.expr(e, &inner);
                            }
                        }
                        self.expr(&l.expr, &inner);
                    }
                    ModuleItem::NettypeDeclaration(n) => self.ty(&n.data_type, scope),
                    ModuleItem::ModportDeclaration(m) => {
                        for p in m.items.iter().flat_map(|i| &i.ports) {
                            if let Some(e) = &p.expr {
                                self.expr(e, scope);
                            } else {
                                self.name(&p.name.name, scope);
                            }
                        }
                    }
                    ModuleItem::ClockingDeclaration(c) => {
                        if let Some(id) = &c.clock_signal {
                            self.name(&id.name, scope);
                        }
                        for e in [&c.default_input_skew, &c.default_output_skew]
                            .into_iter()
                            .flatten()
                        {
                            self.expr(e, scope);
                        }
                        for s in &c.signals {
                            if let Some(e) = &s.bound_to {
                                self.expr(e, scope);
                            } else {
                                self.name(&s.name.name, scope);
                            }
                            if let Some(e) = &s.skew {
                                self.expr(e, scope);
                            }
                        }
                        let mut inner = scope.clone();
                        for s in &c.signals {
                            inner.locals.insert(s.name.name.clone());
                        }
                        self.stmts(&c.items, &inner);
                    }
                    ModuleItem::CovergroupDeclaration(cg) => self.covergroup(cg, scope),
                    ModuleItem::SpecifyBlock(s) => {
                        for p in &s.paths {
                            for id in p.srcs.iter().chain(&p.dsts) {
                                self.name(&id.name, scope);
                            }
                            if let Some(e) = &p.cond {
                                self.expr(e, scope);
                            }
                            for e in &p.delays {
                                self.expr(e, scope);
                            }
                        }
                        for a in s.timing_checks.iter().flat_map(|c| c.args.iter().flatten()) {
                            self.expr(&a.expr, scope);
                            if let Some(e) = &a.cond {
                                self.expr(e, scope);
                            }
                        }
                    }
                    ModuleItem::Defparam(pairs) => {
                        for (lhs, rhs) in pairs {
                            self.expr(lhs, scope);
                            self.expr(rhs, scope);
                        }
                    }
                    ModuleItem::AliasDecl(es) => {
                        for e in es {
                            self.expr(e, scope);
                        }
                    }
                    // A bound instance's actuals resolve in its TARGET scope,
                    // rather than where the bind directive appears (§23.11).
                    // Nested definitions are checked in their own elaboration.
                    _ => {}
                }
            }
        }
        fn class_index(&self) -> &ClassIndex<'b> {
            self.classes.get_or_init(|| {
                let mut index = ClassIndex::default();
                index.imports.insert(
                    "$unit".to_string(),
                    self.top_imports
                        .iter()
                        .flat_map(|i| i.items.clone())
                        .collect(),
                );
                if let Some(defs) = self.defs {
                    for def in defs.values() {
                        match def {
                            Definition::Class(c) => index.class(c, "$unit"),
                            Definition::Package(p) => {
                                for it in &p.items {
                                    match it {
                                        PackageItem::Class(c) => index.class(c, &p.name.name),
                                        PackageItem::Import(i) => index
                                            .imports
                                            .entry(p.name.name.clone())
                                            .or_default()
                                            .extend(i.items.clone()),
                                        _ => {}
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                }
                index.items(self.root_items, "$module");
                index
            })
        }
        fn class_owner(&self, c: &ClassDeclaration) -> &str {
            self.class_index()
                .owners
                .get(&(c as *const ClassDeclaration as usize))
                .map(String::as_str)
                .unwrap_or("$unit")
        }
        fn class_named(&self, name: &str, owner: &str) -> Option<&'b ClassDeclaration> {
            let index = self.class_index();
            let mut context = Some(owner);
            while let Some(path) = context {
                if let Some(c) = index.classes.get(&format!("{path}::{name}")) {
                    return Some(*c);
                }
                if let Some(imports) = index.imports.get(path) {
                    let head = name.split("::").next().unwrap_or(name);
                    for i in imports {
                        if i.item.as_ref().is_none_or(|n| n.name == head)
                            && let Some(c) =
                                index.classes.get(&format!("{}::{name}", i.package.name))
                        {
                            return Some(*c);
                        }
                    }
                }
                context = path
                    .rsplit_once("::")
                    .map(|(parent, _)| parent)
                    .or_else(|| (path != "$unit").then_some("$unit"));
            }
            // Explicit package scopes are design roots. Unqualified fallback
            // is compilation-unit scope, never an arbitrary package leaf.
            index
                .classes
                .get(name)
                .or_else(|| index.classes.get(&format!("$unit::{name}")))
                .copied()
        }
        fn object(&self, name: &str, ty: &DataType, scope: &mut Scope) {
            // A nearer declaration must discard any outer object's type,
            // including when this declaration's alias is not yet resolved.
            scope.objects.remove(name);
            if !self.has_classes {
                return;
            }
            if let DataType::TypeReference { name: ty, .. } = ty
                && let Some(c) = self.class_named(&ty.qualified(), &scope.owner)
            {
                scope
                    .objects
                    .insert(name.to_string(), self.class_owner(c).to_string());
            }
        }
        fn randomize_scope(&self, func: &Expression, scope: &Scope) -> Option<Scope> {
            let ExprKind::MemberAccess { expr, member } = &func.kind else {
                return None;
            };
            if member.name != "randomize" {
                return None;
            }
            // §18.12: std::randomize names caller variables. The parser's
            // member-access node also represents the `::` separator.
            if matches!(&expr.kind, ExprKind::Ident(h)
                if h.root.is_none() && h.path.len() == 1
                    && h.path[0].name.name == "std" && h.path[0].selects.is_empty())
                && !scope.objects.contains_key("std")
            {
                return None;
            }
            let mut inner = scope.clone();
            if matches!(expr.kind, ExprKind::This) {
                return Some(inner);
            }
            let class = match &expr.kind {
                ExprKind::Ident(h) if h.root.is_none() && h.path.len() == 1 => {
                    scope.objects.get(&h.path[0].name.name)
                }
                _ => None,
            }
            .and_then(|name| self.class_index().classes.get(name));
            if let Some(c) = class {
                self.members(c, &mut inner.locals, &mut HashSet::default(), false, false);
            } else {
                // §18.7/§18.11: unknown object members cannot safely be
                // attributed to enclosing module data by this source pass.
                inner.unknown_constraint_scope = true;
            }
            Some(inner)
        }
        fn item_import_names(&self, items: &[ModuleItem], names: &mut HashSet<String>) {
            for it in items {
                match it {
                    ModuleItem::ImportDeclaration(i) => {
                        self.import_names(i, names, &mut HashSet::default())
                    }
                    ModuleItem::GenerateRegion(g) => self.item_import_names(&g.items, names),
                    _ => {}
                }
            }
        }
        fn import_names(
            &self,
            import: &ImportDeclaration,
            names: &mut HashSet<String>,
            seen: &mut HashSet<String>,
        ) {
            for i in &import.items {
                if let Some(name) = &i.item {
                    names.insert(name.name.clone());
                } else if seen.insert(i.package.name.clone())
                    && let Some(Definition::Package(p)) =
                        self.defs.and_then(|d| d.get(&i.package.name))
                {
                    for it in &p.items {
                        match it {
                            PackageItem::Data(d) => {
                                for d in &d.declarators {
                                    names.insert(d.name.name.clone());
                                }
                                enum_names(&d.data_type, names);
                            }
                            PackageItem::Net(d) => {
                                for d in &d.declarators {
                                    names.insert(d.name.name.clone());
                                }
                            }
                            PackageItem::Parameter(p) => parameter_names(p, names),
                            PackageItem::Typedef(td) => {
                                names.insert(td.name.name.clone());
                                enum_names(&td.data_type, names);
                            }
                            PackageItem::Function(f) => {
                                names.insert(f.name.name.name.clone());
                            }
                            PackageItem::Task(t) => {
                                names.insert(t.name.name.name.clone());
                            }
                            PackageItem::Class(c) => {
                                names.insert(c.name.name.clone());
                            }
                            PackageItem::Let(l) => {
                                names.insert(l.name.name.clone());
                            }
                            PackageItem::Property(p) => {
                                names.insert(p.name.name.clone());
                            }
                            PackageItem::Sequence(s) => {
                                names.insert(s.name.name.clone());
                            }
                            PackageItem::Nettype(n) => {
                                names.insert(n.name.name.clone());
                            }
                            PackageItem::Export(e) => self.import_names(e, names, seen),
                            _ => {}
                        }
                    }
                }
            }
        }
        fn member_objects(&self, c: &ClassDeclaration, scope: &mut Scope, static_only: bool) {
            let mut names = HashSet::default();
            self.members(c, &mut names, &mut HashSet::default(), false, static_only);
            for name in names {
                scope.objects.remove(&name);
            }
            let owner = std::mem::replace(&mut scope.owner, self.class_owner(c).to_string());
            for it in &c.items {
                if let ClassItem::Property(p) = it
                    && (!static_only || p.qualifiers.contains(&ClassQualifier::Static))
                {
                    for d in &p.declarators {
                        self.object(&d.name.name, &p.data_type, scope);
                    }
                }
            }
            scope.owner = owner;
        }
        fn members(
            &self,
            c: &ClassDeclaration,
            names: &mut HashSet<String>,
            seen: &mut HashSet<usize>,
            inherited: bool,
            static_only: bool,
        ) {
            if !seen.insert(c as *const ClassDeclaration as usize) {
                return;
            }
            for p in &c.params {
                parameter_names(p, names);
            }
            for it in &c.items {
                match it {
                    ClassItem::Property(p)
                        if (!inherited || !p.qualifiers.contains(&ClassQualifier::Local))
                            && (!static_only || p.qualifiers.contains(&ClassQualifier::Static)) =>
                    {
                        for d in &p.declarators {
                            names.insert(d.name.name.clone());
                        }
                        enum_names(&p.data_type, names);
                    }
                    ClassItem::Method(m)
                        if (!inherited || !m.qualifiers.contains(&ClassQualifier::Local))
                            && (!static_only || m.qualifiers.contains(&ClassQualifier::Static)) =>
                    {
                        let name = match &m.kind {
                            ClassMethodKind::Function(f)
                            | ClassMethodKind::PureVirtual(f)
                            | ClassMethodKind::Extern(f) => &f.name.name.name,
                            ClassMethodKind::Task(t) => &t.name.name.name,
                        };
                        names.insert(name.clone());
                    }
                    ClassItem::Parameter(p) => parameter_names(p, names),
                    ClassItem::Typedef(td) => {
                        names.insert(td.name.name.clone());
                        enum_names(&td.data_type, names);
                    }
                    ClassItem::Class(c) => {
                        names.insert(c.name.name.clone());
                    }
                    _ => {}
                }
            }
            if let Some(ext) = &c.extends {
                let mut name = ext
                    .scopes
                    .iter()
                    .map(|s| s.name.as_str())
                    .collect::<Vec<_>>();
                name.push(&ext.name.name);
                let owner = self.class_owner(c);
                let containing = owner.rsplit_once("::").map_or("$unit", |(owner, _)| owner);
                let parent = self.class_named(&name.join("::"), containing);
                if let Some(parent) = parent {
                    self.members(parent, names, seen, true, static_only);
                }
            }
        }
    }
    fn parameter_names(p: &ParameterDeclaration, names: &mut HashSet<String>) {
        match &p.kind {
            ParameterKind::Data {
                assignments,
                data_type,
            } => {
                for a in assignments {
                    names.insert(a.name.name.clone());
                }
                enum_names(data_type, names);
            }
            ParameterKind::Type { assignments } => {
                for a in assignments {
                    names.insert(a.name.name.clone());
                }
            }
        }
    }
    fn array_with_method(func: &Expression) -> bool {
        let name = match &func.kind {
            ExprKind::MemberAccess { member, .. } => member.name.as_str(),
            ExprKind::Ident(h) if h.path.len() > 1 => h.path.last().unwrap().name.name.as_str(),
            _ => return false,
        };
        matches!(
            name,
            "find"
                | "find_index"
                | "find_first"
                | "find_first_index"
                | "find_last"
                | "find_last_index"
                | "min"
                | "max"
                | "unique"
                | "unique_index"
                | "sort"
                | "rsort"
                | "sum"
                | "product"
                | "and"
                | "or"
                | "xor"
        )
    }
    fn condition_bindings(e: &Expression, names: &mut HashSet<String>) {
        match &e.kind {
            ExprKind::Matches { pattern, .. } => {
                let mut bindings = Vec::new();
                collect_pattern_bindings(pattern, &mut bindings);
                names.extend(bindings);
            }
            ExprKind::Paren(e) => condition_bindings(e, names),
            ExprKind::Binary {
                op: BinaryOp::LogAnd,
                left,
                right,
            } => {
                condition_bindings(left, names);
                condition_bindings(right, names);
            }
            _ => {}
        }
    }
    fn enum_names(ty: &DataType, names: &mut HashSet<String>) {
        if let DataType::Enum(e) = ty {
            for m in &e.members {
                names.insert(m.name.name.clone());
            }
        }
    }
    fn item_names(items: &[ModuleItem], names: &mut HashSet<String>) {
        for it in items {
            match it {
                ModuleItem::NetDeclaration(d) => {
                    for d in &d.declarators {
                        names.insert(d.name.name.clone());
                    }
                    enum_names(&d.data_type, names);
                }
                ModuleItem::DataDeclaration(d) => {
                    for d in &d.declarators {
                        names.insert(d.name.name.clone());
                    }
                    enum_names(&d.data_type, names);
                }
                ModuleItem::PortDeclaration(d) => {
                    for d in &d.declarators {
                        names.insert(d.name.name.clone());
                    }
                    enum_names(&d.data_type, names);
                }
                ModuleItem::ParameterDeclaration(p) | ModuleItem::LocalparamDeclaration(p) => {
                    match &p.kind {
                        ParameterKind::Data {
                            assignments,
                            data_type,
                        } => {
                            for a in assignments {
                                names.insert(a.name.name.clone());
                            }
                            enum_names(data_type, names);
                        }
                        ParameterKind::Type { assignments } => {
                            for a in assignments {
                                names.insert(a.name.name.clone());
                            }
                        }
                    }
                }
                ModuleItem::TypedefDeclaration(td) => {
                    names.insert(td.name.name.clone());
                    enum_names(&td.data_type, names);
                }
                ModuleItem::GenvarDeclaration(g) => {
                    for n in &g.names {
                        names.insert(n.name.clone());
                    }
                }
                ModuleItem::TaskDeclaration(t) => {
                    names.insert(t.name.name.name.clone());
                }
                ModuleItem::FunctionDeclaration(f) => {
                    names.insert(f.name.name.name.clone());
                }
                ModuleItem::ClassDeclaration(c) => {
                    names.insert(c.name.name.clone());
                }
                ModuleItem::GenerateRegion(g) => item_names(&g.items, names),
                _ => {}
            }
        }
    }
    fn local_classes(items: &[ModuleItem]) -> bool {
        items.iter().any(|it| match it {
            ModuleItem::ClassDeclaration(_) => true,
            ModuleItem::GenerateRegion(g) => local_classes(&g.items),
            ModuleItem::CheckerDeclaration(c) => local_classes(&c.items),
            ModuleItem::GenerateIf(g) => g.branches.iter().any(|(_, items)| local_classes(items)),
            ModuleItem::GenerateFor(g) => local_classes(&g.items),
            ModuleItem::GenerateCase(g) => g.arms.iter().any(|arm| local_classes(&arm.items)),
            _ => false,
        })
    }
    fn collect_data(items: &[ModuleItem], names: &mut HashSet<String>) {
        for it in items {
            match it {
                ModuleItem::NetDeclaration(d) => {
                    for d in &d.declarators {
                        names.insert(d.name.name.clone());
                    }
                }
                ModuleItem::DataDeclaration(d) => {
                    for d in &d.declarators {
                        names.insert(d.name.name.clone());
                    }
                }
                ModuleItem::PortDeclaration(d) => {
                    for d in &d.declarators {
                        names.insert(d.name.name.clone());
                    }
                }
                ModuleItem::GenerateRegion(g) => collect_data(&g.items, names),
                _ => {}
            }
        }
    }
    let mut data = HashSet::default();
    collect_data(module.items(), &mut data);
    let ports = match module {
        Definition::Module(m) => Some(&m.ports),
        Definition::Interface(i) => Some(&i.ports),
        Definition::Program(p) => Some(&p.ports),
        _ => None,
    };
    if let Some(PortList::Ansi(ports)) = ports {
        for p in ports {
            data.insert(p.name.name.clone());
        }
    }
    if data.is_empty() {
        return Vec::new();
    }
    let mut check = Check {
        data,
        found: HashSet::default(),
        defs: all_defs,
        root_items: module.items(),
        top_imports: top_level_imports,
        classes: std::cell::OnceCell::new(),
        has_classes: design_has_classes || local_classes(module.items()),
    };
    let mut scope = Scope {
        owner: "$unit".to_string(),
        ..Scope::default()
    };
    // Unit handles retain their declaring type even when a nearer module
    // declares a same-named class. Only types are needed, not copied bodies.
    let unit_types = DECLARATION_ORDER_RUN.with(|run| {
        run.borrow()
            .as_ref()
            .map(|run| run.unit_types.clone())
            .unwrap_or_default()
    });
    for (name, ty) in unit_types {
        check.object(&name, &ty, &mut scope);
    }
    scope.owner = "$module".to_string();
    for p in module.params() {
        check.parameter(p, &scope);
    }
    if let Some(PortList::Ansi(ports)) = ports {
        for p in ports {
            if let Some(ty) = &p.data_type {
                check.ty(ty, &scope);
            }
            scope.declared.insert(p.name.name.clone());
            if let Some(ty) = &p.data_type {
                check.object(&p.name.name, ty, &mut scope);
            }
            check.unpacked(&p.dimensions, &scope);
            if let Some(e) = &p.default {
                check.expr(e, &scope);
            }
        }
    }
    check.items(module.items(), &mut scope);
    let mut out: Vec<String> = check.found.into_iter().collect();
    out.sort();
    out
}

#[derive(Default)]
struct DeclarationOrderRun {
    checked: HashSet<String>,
    unit_types: Vec<(String, DataType)>,
}
thread_local! {
    static DECLARATION_ORDER_RUN: std::cell::RefCell<Option<DeclarationOrderRun>> =
        const { std::cell::RefCell::new(None) };
}

thread_local! {
    pub(super) static UNIT_BIND_INSTANCES: std::cell::RefCell<UnitBindInstances> =
        std::cell::RefCell::new(UnitBindInstances::default());
}

/// Holds the compilation-unit binds' instances for one elaboration and
/// restores the previous set for nested or later library calls.
pub(crate) struct UnitBindInstancesGuard(UnitBindInstances);
impl Drop for UnitBindInstancesGuard {
    fn drop(&mut self) {
        UNIT_BIND_INSTANCES.with(|s| *s.borrow_mut() = std::mem::take(&mut self.0));
    }
}
pub(crate) fn unit_bind_instances_scope(binds: &[BindDirective]) -> UnitBindInstancesGuard {
    let mut set = UnitBindInstances::default();
    for b in binds {
        for hi in &b.instantiation.instances {
            set.names.insert(hi.name.name.clone());
            if b.target_path.is_empty() {
                set.by_module
                    .entry(b.target_module.name.clone())
                    .or_default()
                    .insert(hi.name.name.clone());
            }
        }
    }
    UnitBindInstancesGuard(UNIT_BIND_INSTANCES.with(|s| s.replace(set)))
}
/// Whether a compilation-unit bind adds an instance `name` to every instance
/// of `module`.
pub(super) fn is_unit_bind_instance_of(module: &str, name: &str) -> bool {
    UNIT_BIND_INSTANCES.with(|s| {
        s.borrow()
            .by_module
            .get(module)
            .is_some_and(|names| names.contains(name))
    })
}

/// §3.12.1/§6.5: validate source definitions before copying compilation-unit
/// items into module storage. The scope keeps bind retries from checking the
/// synthetic copies, and restores state for nested or later library calls.
pub(crate) struct DeclarationOrderGuard(Option<DeclarationOrderRun>);
impl Drop for DeclarationOrderGuard {
    fn drop(&mut self) {
        DECLARATION_ORDER_RUN.with(|run| {
            *run.borrow_mut() = self.0.take();
        });
    }
}
pub(crate) fn declaration_order_scope() -> DeclarationOrderGuard {
    DeclarationOrderGuard(
        DECLARATION_ORDER_RUN.with(|run| run.replace(Some(DeclarationOrderRun::default()))),
    )
}
pub(crate) fn declaration_order_unit_types(vars: &[DataDeclaration]) {
    DECLARATION_ORDER_RUN.with(|run| {
        if let Some(run) = run.borrow_mut().as_mut() {
            run.unit_types = vars
                .iter()
                .filter(|d| matches!(d.data_type, DataType::TypeReference { .. }))
                .flat_map(|d| {
                    d.declarators
                        .iter()
                        .map(|v| (v.name.name.clone(), d.data_type.clone()))
                })
                .collect();
        }
    });
}
pub(crate) fn validate_module_data_declarations(
    module: Option<Definition>,
    all_defs: Option<&HashMap<String, Definition>>,
    top_level_imports: &[ImportDeclaration],
) -> Result<(), String> {
    // Inlining does not re-enter this function for each child. Check source
    // definitions once, including children of a synthetic multiple-top root,
    // rather than silently accepting their premature data uses (§6.5).
    let mut definitions: Vec<_> = module.into_iter().collect();
    if let Some(defs) = all_defs {
        let mut others: Vec<_> = defs
            .iter()
            .filter(|(_, def)| {
                module.is_none_or(|module| def.name() != module.name())
                    && matches!(
                        def,
                        Definition::Module(_) | Definition::Interface(_) | Definition::Program(_)
                    )
            })
            .collect();
        others.sort_by(|(a, _), (b, _)| a.cmp(b));
        definitions.extend(others.into_iter().map(|(_, def)| *def));
    }
    // Most RTL designs have no classes: avoid indexing all definitions for
    // each typedef-typed signal in each checked module.
    let design_has_classes = all_defs.is_some_and(|defs| {
        defs.values().any(|def| match def {
            Definition::Class(_) => true,
            Definition::Package(p) => p.items.iter().any(|it| matches!(it, PackageItem::Class(_))),
            _ => false,
        })
    });
    let mut checked = HashSet::default();
    for definition in definitions {
        if !checked.insert(definition.name().to_string()) {
            continue;
        }
        if DECLARATION_ORDER_RUN.with(|run| {
            run.borrow()
                .as_ref()
                .is_some_and(|run| run.checked.contains(definition.name()))
        }) {
            continue;
        }
        let early = check_module_use_before_decl(
            &definition,
            all_defs,
            top_level_imports,
            design_has_classes,
        );
        if crate::sv_parser::RELAX_USE_BEFORE_DECL.get() {
            // Deduplicate per definition in this run, not across independent
            // designs compiled through the public library API in one process.
            for name in &early {
                crate::elab_diag(format!(
                    "[xezim][warning] '{}' is used before its declaration in module '{}' \
                     (§6.5); accepted because --relax-use-before-decl is in effect",
                    name,
                    definition.name()
                ));
            }
        } else if let Some(name) = early.first() {
            return Err(format!(
                "Undefined variable '{}': referenced before its declaration in module '{}' \
                 (IEEE 1800-2017 §6.5/§10; implicit nets §6.10 do not apply to a name \
                 declared later in the same scope).\n  \
                 fix: declare it ahead of its first use, \
                 or accept it as-is: --relax-use-before-decl (env XEZIM_RELAX_USE_BEFORE_DECL=1)",
                name,
                definition.name()
            ));
        }
        DECLARATION_ORDER_RUN.with(|run| {
            if let Some(run) = run.borrow_mut().as_mut() {
                run.checked.insert(definition.name().to_string());
            }
        });
    }
    Ok(())
}
