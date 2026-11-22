use super::*;

/// Every name DECLARED anywhere in the design: ports, nets, variables,
/// parameters, typedefs and their enum members, genvars, subroutines, class
/// properties and methods, clocking/let/property/sequence/covergroup names —
/// across modules, interfaces, programs, packages, classes, generate blocks.
fn decl_enum_member_names(dt: &DataType, out: &mut HashSet<String>) {
    if let DataType::Enum(e) = dt {
        for m in &e.members {
            out.insert(m.name.name.clone());
        }
    }
}
pub(super) fn decl_param_names(p: &ParameterDeclaration, out: &mut HashSet<String>) {
    match &p.kind {
        ParameterKind::Data {
            data_type,
            assignments,
        } => {
            decl_enum_member_names(data_type, out);
            for a in assignments {
                out.insert(a.name.name.clone());
            }
        }
        // `parameter type T` — `$bits(T)` names it like a value.
        ParameterKind::Type { assignments } => {
            for a in assignments {
                out.insert(a.name.name.clone());
            }
        }
    }
}
fn decl_typedef_names(t: &crate::ast::decl::TypedefDeclaration, out: &mut HashSet<String>) {
    out.insert(t.name.name.clone());
    decl_enum_member_names(&t.data_type, out);
}
fn decl_port_names(pl: &PortList, out: &mut HashSet<String>) {
    match pl {
        PortList::Ansi(ps) => {
            for p in ps {
                out.insert(p.name.name.clone());
            }
        }
        PortList::NonAnsi(ids) => {
            for id in ids {
                out.insert(id.name.clone());
            }
        }
        PortList::Empty => {}
    }
}
/// Every name a class declares for bare use inside its own methods.
pub(super) fn decl_class_member_names(
    c: &crate::ast::decl::ClassDeclaration,
    out: &mut HashSet<String>,
) {
    use crate::ast::decl::ClassItem as CI;
    out.insert(c.name.name.clone());
    for p in &c.params {
        decl_param_names(p, out);
    }
    for it in &c.items {
        match it {
            CI::Property(p) => {
                decl_enum_member_names(&p.data_type, out);
                for d in &p.declarators {
                    out.insert(d.name.name.clone());
                }
            }
            CI::Method(m) => match &m.kind {
                crate::ast::decl::ClassMethodKind::Function(fd)
                | crate::ast::decl::ClassMethodKind::PureVirtual(fd) => {
                    out.insert(fd.name.name.name.clone());
                }
                crate::ast::decl::ClassMethodKind::Task(td) => {
                    out.insert(td.name.name.name.clone());
                }
                #[allow(unreachable_patterns)]
                _ => {}
            },
            CI::Typedef(t) => decl_typedef_names(t, out),
            CI::Parameter(p) => decl_param_names(p, out),
            CI::Class(inner) => decl_class_member_names(inner, out),
            CI::Covergroup(cg) => {
                out.insert(cg.name.name.clone());
            }
            // `c_addr.constraint_mode(0)` inside a method.
            CI::Constraint(c) => {
                out.insert(c.name.name.clone());
            }
            _ => {}
        }
    }
}
/// Names declared anywhere in the design. Without `class_members`, a class
/// contributes only its own name: its members are visible bare only inside
/// its own hierarchy (see `validate_subroutine_bodies`).
pub(super) fn collect_design_declared_names(
    definitions: &HashMap<String, Definition>,
    class_members: bool,
) -> HashSet<String> {
    /// A class's own name, and with `members` everything it declares.
    fn class_names(
        c: &crate::ast::decl::ClassDeclaration,
        out: &mut HashSet<String>,
        members: bool,
    ) {
        if members {
            decl_class_member_names(c, out);
        } else {
            out.insert(c.name.name.clone());
        }
    }
    fn dpi_name(di: &crate::ast::decl::DPIImport) -> String {
        match &di.proto {
            crate::ast::decl::DPIProto::Function(fd) => fd.name.name.name.clone(),
            crate::ast::decl::DPIProto::Task(td) => td.name.name.name.clone(),
        }
    }
    fn module_items(items: &[ModuleItem], out: &mut HashSet<String>, members: bool) {
        for it in items {
            match it {
                ModuleItem::PortDeclaration(pd) => {
                    decl_enum_member_names(&pd.data_type, out);
                    for d in &pd.declarators {
                        out.insert(d.name.name.clone());
                    }
                }
                ModuleItem::NetDeclaration(nd) => {
                    decl_enum_member_names(&nd.data_type, out);
                    for d in &nd.declarators {
                        out.insert(d.name.name.clone());
                    }
                }
                ModuleItem::DataDeclaration(dd) => {
                    decl_enum_member_names(&dd.data_type, out);
                    for d in &dd.declarators {
                        out.insert(d.name.name.clone());
                    }
                }
                ModuleItem::ParameterDeclaration(p) | ModuleItem::LocalparamDeclaration(p) => {
                    decl_param_names(p, out);
                }
                ModuleItem::TypedefDeclaration(t) => decl_typedef_names(t, out),
                ModuleItem::GenvarDeclaration(g) => {
                    for n in &g.names {
                        out.insert(n.name.clone());
                    }
                }
                ModuleItem::FunctionDeclaration(fd) => {
                    out.insert(fd.name.name.name.clone());
                }
                ModuleItem::TaskDeclaration(td) => {
                    out.insert(td.name.name.name.clone());
                }
                ModuleItem::DPIImport(di) => {
                    out.insert(dpi_name(di));
                }
                ModuleItem::ClassDeclaration(c) => class_names(c, out, members),
                ModuleItem::ClockingDeclaration(c) => {
                    out.insert(c.name.name.clone());
                }
                ModuleItem::LetDeclaration(l) => {
                    out.insert(l.name.name.clone());
                }
                ModuleItem::PropertyDeclaration(p) => {
                    out.insert(p.name.name.clone());
                }
                ModuleItem::SequenceDeclaration(sq) => {
                    out.insert(sq.name.name.clone());
                }
                ModuleItem::CovergroupDeclaration(cg) => {
                    out.insert(cg.name.name.clone());
                }
                ModuleItem::NettypeDeclaration(n) => {
                    out.insert(n.name.name.clone());
                }
                ModuleItem::ModuleInstantiation(mi) => {
                    for hi in &mi.instances {
                        out.insert(hi.name.name.clone());
                    }
                }
                ModuleItem::GenerateRegion(gr) => module_items(&gr.items, out, members),
                // §27.6: a generate block's label is a scope name, legal as the
                // root of a hierarchical reference (`blk.f(0)`, `g[i-1].t`).
                ModuleItem::GenerateIf(gi) => {
                    out.extend(gi.branch_labels.iter().flatten().cloned());
                    for (_, items) in &gi.branches {
                        module_items(items, out, members);
                    }
                }
                ModuleItem::GenerateFor(gf) => {
                    out.insert(gf.var.clone());
                    out.extend(gf.name.iter().cloned());
                    module_items(&gf.items, out, members);
                }
                ModuleItem::GenerateCase(gc) => {
                    for arm in &gc.arms {
                        out.extend(arm.label.iter().cloned());
                        module_items(&arm.items, out, members);
                    }
                }
                ModuleItem::NestedModule(m) => {
                    for p in &m.params {
                        decl_param_names(p, out);
                    }
                    decl_port_names(&m.ports, out);
                    module_items(&m.items, out, members);
                }
                ModuleItem::ModportDeclaration(md) => {
                    for mi in &md.items {
                        out.insert(mi.name.name.clone());
                    }
                }
                ModuleItem::CheckerDeclaration(cd) => {
                    out.insert(cd.name.name.clone());
                    decl_port_names(&cd.ports, out);
                    module_items(&cd.items, out, members);
                }
                ModuleItem::Bind(b) => {
                    for hi in &b.instantiation.instances {
                        out.insert(hi.name.name.clone());
                    }
                }
                _ => {}
            }
        }
    }
    let mut out = HashSet::default();
    for def in definitions.values() {
        out.insert(def.name().to_string());
        for p in def.params() {
            decl_param_names(p, &mut out);
        }
        decl_port_names(def.ports(), &mut out);
        match def {
            Definition::Module(_) | Definition::Interface(_) | Definition::Program(_) => {
                module_items(def.items(), &mut out, class_members);
            }
            Definition::Package(p) => {
                use crate::ast::decl::PackageItem as PI;
                for it in &p.items {
                    match it {
                        PI::Parameter(pd) => decl_param_names(pd, &mut out),
                        PI::Typedef(t) => decl_typedef_names(t, &mut out),
                        PI::Function(fd) => {
                            out.insert(fd.name.name.name.clone());
                        }
                        PI::Task(td) => {
                            out.insert(td.name.name.name.clone());
                        }
                        PI::DPIImport(di) => {
                            out.insert(dpi_name(di));
                        }
                        PI::Data(dd) => {
                            decl_enum_member_names(&dd.data_type, &mut out);
                            for d in &dd.declarators {
                                out.insert(d.name.name.clone());
                            }
                        }
                        PI::Class(c) => class_names(c, &mut out, class_members),
                        PI::Let(l) => {
                            out.insert(l.name.name.clone());
                        }
                        PI::Nettype(n) => {
                            out.insert(n.name.name.clone());
                        }
                        PI::Property(pr) => {
                            out.insert(pr.name.name.clone());
                        }
                        PI::Sequence(sq) => {
                            out.insert(sq.name.name.clone());
                        }
                        _ => {}
                    }
                }
            }
            Definition::Class(c) => class_names(c, &mut out, class_members),
            Definition::Typedef(t) => decl_typedef_names(t, &mut out),
            _ => {}
        }
    }
    out
}

/// Names a statement itself declares — block-local variables, for/foreach
/// loop variables, named blocks. Flow-insensitive: a name declared anywhere
/// in the body counts everywhere in it.
/// The labels of the named blocks (sequential and parallel) in `stmt`.
pub(super) fn collect_block_labels<S: std::hash::BuildHasher>(
    stmt: &Statement,
    out: &mut std::collections::HashSet<String, S>,
) {
    use crate::ast::stmt::StatementKind as K;
    match &stmt.kind {
        K::SeqBlock { name, stmts } | K::ParBlock { name, stmts, .. } => {
            if let Some(n) = name {
                out.insert(n.name.clone());
            }
            for st in stmts {
                collect_block_labels(st, out);
            }
        }
        K::If {
            then_stmt,
            else_stmt,
            ..
        } => {
            collect_block_labels(then_stmt, out);
            if let Some(e) = else_stmt {
                collect_block_labels(e, out);
            }
        }
        K::Case { items, .. } => {
            for it in items {
                collect_block_labels(&it.stmt, out);
            }
        }
        K::For { body, .. }
        | K::Foreach { body, .. }
        | K::While { body, .. }
        | K::DoWhile { body, .. }
        | K::Repeat { body, .. }
        | K::Forever { body }
        | K::TimingControl { stmt: body, .. }
        | K::Wait { stmt: body, .. } => collect_block_labels(body, out),
        _ => {}
    }
}

pub(super) fn collect_stmt_declared_names(stmt: &Statement, out: &mut HashSet<String>) {
    use crate::ast::stmt::StatementKind as K;
    match &stmt.kind {
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
            for d in declarators {
                out.insert(d.name.name.clone());
            }
            if let DataType::Enum(e) = data_type {
                for m in &e.members {
                    out.insert(m.name.name.clone());
                }
            }
        }
        K::For { init, body, .. } => {
            for i in init {
                if let crate::ast::stmt::ForInit::VarDecl { name, .. } = i {
                    out.insert(name.name.clone());
                }
            }
            collect_stmt_declared_names(body, out);
        }
        K::Foreach { vars, body, .. } => {
            for v in vars.iter().flatten() {
                out.insert(v.name.clone());
            }
            collect_stmt_declared_names(body, out);
        }
        K::ForeachTail {
            loop_var,
            body,
            keys,
            ..
        } => {
            if let Some(v) = loop_var {
                out.insert(v.clone());
            }
            for k in keys {
                out.insert(k.clone());
            }
            collect_stmt_declared_names(body, out);
        }
        K::If {
            condition,
            then_stmt,
            else_stmt,
            ..
        } => {
            // §12.6.2: `if (e matches tagged Valid .n)` declares `n`.
            if let ExprKind::Matches { pattern, .. } = &condition.kind {
                let mut bound = Vec::new();
                collect_pattern_bindings(pattern, &mut bound);
                out.extend(bound);
            }
            collect_stmt_declared_names(then_stmt, out);
            if let Some(e) = else_stmt {
                collect_stmt_declared_names(e, out);
            }
        }
        K::Case { items, .. } => {
            for it in items {
                // §12.6.1: a `case … matches` item's `.v` bindings.
                if let Some(pat) = &it.pattern {
                    let mut bound = Vec::new();
                    collect_pattern_bindings(pat, &mut bound);
                    out.extend(bound);
                }
                collect_stmt_declared_names(&it.stmt, out);
            }
        }
        K::While { body, .. }
        | K::DoWhile { body, .. }
        | K::Repeat { body, .. }
        | K::Forever { body }
        | K::ForeverTail { body }
        | K::RsAction { body } => collect_stmt_declared_names(body, out),
        K::SeqBlock { name, stmts } | K::ParBlock { name, stmts, .. } => {
            if let Some(n) = name {
                out.insert(n.name.clone());
            }
            for st in stmts {
                collect_stmt_declared_names(st, out);
            }
        }
        K::TimingControl { stmt, .. } | K::Wait { stmt, .. } => {
            collect_stmt_declared_names(stmt, out);
        }
        // §16 immediate/concurrent assertions: the `pass` / `else` statements
        // may declare block-locals (e.g. `assert (c) else begin int e; ... end`
        // after macro expansion), which later statements in the same body may
        // reference. Mirror the `K::If` recursion so those names are collected.
        K::Assertion(a) => {
            if let Some(s) = &a.action {
                collect_stmt_declared_names(s, out);
            }
            if let Some(s) = &a.else_action {
                collect_stmt_declared_names(s, out);
            }
        }
        K::RandCase { items } => {
            for (_, st) in items {
                collect_stmt_declared_names(st, out);
            }
        }
        K::Typedef(t) => {
            out.insert(t.name.name.clone());
            if let DataType::Enum(e) = &t.data_type {
                for m in &e.members {
                    out.insert(m.name.name.clone());
                }
            }
        }
        _ => {}
    }
}
