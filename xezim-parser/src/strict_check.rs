//! Strict negative-test checks — a *second* validation pass that runs
//! ALONGSIDE the permissive main parser without modifying it. The main parser
//! deliberately accepts/recovers from many LRM-illegal constructs to maximize
//! pass rate on valid designs. This pass walks the parsed AST and reports
//! violations a conformance checker must diagnose.
//!
//! Gated by [`crate::strict_checks`] (the `--strict` switch, on by default;
//! `--no-strict` disables it). It runs on EVERY source, so each check must be
//! precise — a false positive rejects a valid design. Working on the AST (not
//! the token stream) gives each task/function/etc. a well-scoped node, so
//! checks don't suffer the scope ambiguity a token scan does (e.g. DPI/extern
//! functions are distinct nodes, not open scopes).

use crate::ast::Description;
use crate::ast::decl::{
    ClassItem, ClassMethodKind, FunctionDeclaration, FunctionPort, ModuleItem, PackageItem,
    ParamConnection, ParamValue, ParameterDeclaration, ParameterKind, TaskDeclaration,
};
use crate::ast::expr::{ExprKind, Expression};
use crate::ast::stmt::{Statement, StatementKind};
use crate::diagnostics::Diagnostic;
use std::collections::{HashMap, HashSet};

/// Run all enabled strict checks over one file's parsed descriptions. Returns
/// human-readable violation messages (empty = clean). No-op when disabled.
pub fn strict_violations(descriptions: &[Description]) -> Vec<String> {
    strict_diagnostics(descriptions)
        .into_iter()
        .map(|d| d.message)
        .collect()
}

/// As [`strict_violations`], as error diagnostics spanning the offending
/// construct.
pub fn strict_diagnostics(descriptions: &[Description]) -> Vec<Diagnostic> {
    if !crate::strict_checks() {
        return Vec::new();
    }
    let mut out = Vec::new();
    for d in descriptions {
        match d {
            Description::Module(m) => walk_module_items(&m.items, &mut out),
            Description::Program(p) => walk_module_items(&p.items, &mut out),
            Description::Interface(i) => walk_module_items(&i.items, &mut out),
            Description::Package(p) => walk_package_items(&p.items, &mut out),
            Description::Class(c) => walk_class_items(&c.items, &mut out),
            Description::PackageItem(pi) => walk_package_item(pi, &mut out),
            _ => {}
        }
    }
    // §6.20.2 / §23.10: a named parameter override or a defparam must name an
    // *overridable* parameter (not a localparam, and it must exist). Built
    // from the modules declared in THIS file; instantiations of modules
    // defined elsewhere are skipped (can't resolve, so no false positive).
    let overridable = build_module_overridable_params(descriptions);
    for d in descriptions {
        if let Description::Module(m) = d {
            check_param_overrides(&m.items, &overridable, &mut out);
            if let Some(own) = overridable.get(&m.name.name) {
                check_local_defparams(&m.items, own, &mut out);
            }
        }
    }
    out
}

/// §23.10: a defparam naming a parameter of this module (`defparam foo = 3;`)
/// or of one of its generate blocks (`defparam loop[0].A = 10;`) must name an
/// overridable one. A module-level name that is no such parameter is not
/// found, and a parameter declared in a generate block is a local parameter
/// (§27.2).
fn check_local_defparams(items: &[ModuleItem], own: &ModuleParams, out: &mut Vec<Diagnostic>) {
    // generate-for label -> parameters declared directly in its block
    fn collect<'a>(items: &'a [ModuleItem], out: &mut HashMap<&'a str, HashSet<&'a str>>) {
        for it in items {
            match it {
                ModuleItem::GenerateFor(gf) => {
                    let Some(label) = &gf.name else { continue };
                    let names = out.entry(label.as_str()).or_default();
                    for bi in &gf.items {
                        if let ModuleItem::ParameterDeclaration(pd)
                        | ModuleItem::LocalparamDeclaration(pd) = bi
                            && let ParameterKind::Data { assignments, .. } = &pd.kind
                        {
                            names.extend(assignments.iter().map(|a| a.name.name.as_str()));
                        }
                    }
                }
                ModuleItem::GenerateRegion(gr) => collect(&gr.items, out),
                _ => {}
            }
        }
    }
    let mut block_params: HashMap<&str, HashSet<&str>> = HashMap::new();
    collect(items, &mut block_params);
    fn bare(e: &Expression) -> Option<&str> {
        match &e.kind {
            ExprKind::Ident(h) if h.root.is_none() && h.path.len() == 1 => {
                Some(h.path[0].name.name.as_str())
            }
            _ => None,
        }
    }
    for it in items {
        let ModuleItem::Defparam(list) = it else {
            continue;
        };
        for (target, _) in list {
            match &target.kind {
                ExprKind::Ident(h)
                    if h.root.is_none() && h.path.len() == 1 && h.path[0].selects.is_empty() =>
                {
                    let n = &h.path[0].name;
                    if !own.overridable.contains(&n.name) {
                        out.push(Diagnostic::error(
                            format!(
                                "defparam target '{}' is not an overridable parameter of this \
                                 module (IEEE 1800-2017 §23.10)",
                                n.name
                            ),
                            n.span,
                        ));
                    }
                }
                ExprKind::MemberAccess { expr, member } => {
                    let scope = match &expr.kind {
                        ExprKind::Index { expr, .. } => bare(expr),
                        _ => bare(expr),
                    };
                    if let Some(scope) = scope
                        && block_params
                            .get(scope)
                            .is_some_and(|ps| ps.contains(member.name.as_str()))
                    {
                        out.push(Diagnostic::error(
                            format!(
                                "defparam cannot override '{}': a parameter declared in a \
                                 generate block is a local parameter (IEEE 1800-2017 §27.2)",
                                member.name
                            ),
                            member.span,
                        ));
                    }
                }
                _ => {}
            }
        }
    }
}

/// The parameters of one module, as an instantiation sees them.
#[derive(Default)]
struct ModuleParams {
    /// Overridable parameter names (not localparams).
    overridable: HashSet<String>,
    /// `parameter type` names.
    types: HashSet<String>,
    /// Header parameters in order (a positional override binds by position),
    /// with whether each has a default value.
    header: Vec<(String, bool)>,
}

/// name -> parameters for every module in this file. "Overridable" excludes
/// localparams (header `localparam` / body `localparam`) and, when the module
/// has a parameter port list, body `parameter`s too: §6.20.1 makes those
/// local parameters.
fn build_module_overridable_params(descriptions: &[Description]) -> HashMap<String, ModuleParams> {
    let mut map = HashMap::new();
    for d in descriptions {
        if let Description::Module(m) = d {
            let mut params = ModuleParams {
                overridable: overridable_param_slots(&m.params, &m.items)
                    .into_iter()
                    .map(str::to_string)
                    .collect(),
                ..ModuleParams::default()
            };
            for pd in &m.params {
                add_type_param_names(pd, &mut params.types);
                if !pd.local {
                    if let ParameterKind::Data { assignments, .. } = &pd.kind {
                        for a in assignments {
                            params.header.push((a.name.name.clone(), a.init.is_some()));
                        }
                    }
                    if let ParameterKind::Type { assignments } = &pd.kind {
                        for a in assignments {
                            params.header.push((a.name.name.clone(), a.init.is_some()));
                        }
                    }
                }
            }
            for it in &m.items {
                if let ModuleItem::ParameterDeclaration(pd) = it {
                    add_type_param_names(pd, &mut params.types);
                }
            }
            map.insert(m.name.name.clone(), params);
        }
    }
    map
}

fn add_type_param_names(pd: &ParameterDeclaration, out: &mut HashSet<String>) {
    if let ParameterKind::Type { assignments } = &pd.kind {
        for a in assignments {
            out.insert(a.name.name.clone());
        }
    }
}

/// The parameters an instance's override list can set, in the order ordered
/// values bind to them: the non-local parameters of the parameter port list,
/// data and type alike and flattened, so `parameter A = 1, B = 2` is two.
/// Body `parameter`s count only when there is no parameter port list at all:
/// §6.20.1 makes them local otherwise, even if the list holds only localparams.
pub fn overridable_param_slots<'a>(
    params: &'a [ParameterDeclaration],
    items: &'a [ModuleItem],
) -> Vec<&'a str> {
    // §27.3: a `generate ... endgenerate` region only wraps module items, so
    // a parameter in one is a body parameter too.
    fn body_params<'a>(items: &'a [ModuleItem], out: &mut Vec<&'a ParameterDeclaration>) {
        for it in items {
            match it {
                ModuleItem::ParameterDeclaration(pd) => out.push(pd),
                ModuleItem::GenerateRegion(gr) => body_params(&gr.items, out),
                _ => {}
            }
        }
    }
    let mut body = Vec::new();
    if params.is_empty() {
        body_params(items, &mut body);
    }
    params
        .iter()
        .chain(body)
        .filter(|pd| !pd.local)
        .flat_map(|pd| -> Vec<&'a str> {
            match &pd.kind {
                ParameterKind::Data { assignments, .. } => {
                    assignments.iter().map(|a| a.name.name.as_str()).collect()
                }
                ParameterKind::Type { assignments } => {
                    assignments.iter().map(|a| a.name.name.as_str()).collect()
                }
            }
        })
        .collect()
}

fn check_param_overrides(
    items: &[ModuleItem],
    overridable: &HashMap<String, ModuleParams>,
    out: &mut Vec<Diagnostic>,
) {
    // `defparam inst.P = v;` targets, by instance name.
    let mut defparams: HashMap<&str, Vec<(&str, &Expression)>> = HashMap::new();
    for it in items {
        if let ModuleItem::Defparam(list) = it {
            for (target, _) in list {
                if let ExprKind::MemberAccess { expr, member } = &target.kind
                    && let ExprKind::Ident(h) = &expr.kind
                    && h.root.is_none()
                    && h.path.len() == 1
                    && h.path[0].selects.is_empty()
                {
                    defparams
                        .entry(h.path[0].name.name.as_str())
                        .or_default()
                        .push((member.name.as_str(), target));
                }
            }
        }
    }
    for it in items {
        if let ModuleItem::ModuleInstantiation(inst) = it {
            // Only check when the target module is defined in this file.
            let Some(params) = overridable.get(&inst.module_name.name) else {
                continue;
            };
            let mut given: HashSet<&str> = HashSet::new();
            if let Some(conns) = &inst.params {
                let mut pos = 0usize;
                for c in conns {
                    match c {
                        ParamConnection::Named { name, value } => {
                            given.insert(name.name.as_str());
                            if !params.overridable.contains(&name.name) {
                                out.push(Diagnostic::error(
                                    format!(
                                        "cannot override '{}' of module '{}' — not an overridable parameter",
                                        name.name, inst.module_name.name
                                    ),
                                    name.span,
                                ));
                            } else if params.types.contains(&name.name)
                                && matches!(value, Some(ParamValue::Expr(e))
                                    if matches!(e.kind, ExprKind::Number(_)))
                            {
                                out.push(Diagnostic::error(
                                    format!(
                                        "type parameter '{}' of module '{}' takes a data type, \
                                         not a value (IEEE 1800-2017 §6.20.3)",
                                        name.name, inst.module_name.name
                                    ),
                                    name.span,
                                ));
                            }
                        }
                        ParamConnection::Ordered(_) => {
                            if let Some((n, _)) = params.header.get(pos) {
                                given.insert(n.as_str());
                            }
                            pos += 1;
                        }
                    }
                }
            }
            for hi in &inst.instances {
                let dps = defparams.get(hi.name.name.as_str());
                for (p, target) in dps.into_iter().flatten() {
                    if !params.overridable.contains(*p) {
                        out.push(Diagnostic::error(
                            format!(
                                "defparam cannot override '{}' of module '{}' — not an \
                                 overridable parameter (IEEE 1800-2017 §23.10.1)",
                                p, inst.module_name.name
                            ),
                            target.span,
                        ));
                    } else if params.types.contains(*p) {
                        out.push(Diagnostic::error(
                            format!(
                                "defparam cannot override type parameter '{}' of module '{}' \
                                 (IEEE 1800-2017 §23.10.1)",
                                p, inst.module_name.name
                            ),
                            target.span,
                        ));
                    }
                }
                // §6.20.1: a parameter declared without a default must get a
                // value from every instantiation.
                for (n, has_default) in &params.header {
                    let by_defparam = dps.is_some_and(|d| d.iter().any(|(p, _)| p == n));
                    if !has_default && !given.contains(n.as_str()) && !by_defparam {
                        out.push(Diagnostic::error(
                            format!(
                                "parameter '{}' of module '{}' has no default value, and \
                                 instance '{}' does not override it (IEEE 1800-2017 §6.20.1)",
                                n, inst.module_name.name, hi.name.name
                            ),
                            hi.span,
                        ));
                    }
                }
            }
        }
    }
}

fn walk_module_items(items: &[ModuleItem], out: &mut Vec<Diagnostic>) {
    for it in items {
        match it {
            ModuleItem::FunctionDeclaration(fd) => check_function(fd, out),
            ModuleItem::TaskDeclaration(td) => check_task(td, out),
            ModuleItem::ClassDeclaration(c) => walk_class_items(&c.items, out),
            ModuleItem::InitialConstruct(ic) => check_decl_order_stmt(&ic.stmt, out),
            ModuleItem::AlwaysConstruct(ac) => check_decl_order_stmt(&ac.stmt, out),
            ModuleItem::FinalConstruct(fc) => check_decl_order_stmt(&fc.stmt, out),
            ModuleItem::GenerateRegion(g) => walk_module_items(&g.items, out),
            ModuleItem::GenerateFor(g) => walk_module_items(&g.items, out),
            ModuleItem::GenerateIf(g) => {
                for (_, items) in &g.branches {
                    walk_module_items(items, out);
                }
            }
            ModuleItem::GenerateCase(g) => {
                for arm in &g.arms {
                    walk_module_items(&arm.items, out);
                }
            }
            _ => {}
        }
    }
}

fn walk_package_items(items: &[PackageItem], out: &mut Vec<Diagnostic>) {
    for it in items {
        walk_package_item(it, out);
    }
}

fn walk_package_item(it: &PackageItem, out: &mut Vec<Diagnostic>) {
    match it {
        PackageItem::Function(fd) => check_function(fd, out),
        PackageItem::Task(td) => check_task(td, out),
        PackageItem::Class(c) => walk_class_items(&c.items, out),
        _ => {}
    }
}

fn walk_class_items(items: &[ClassItem], out: &mut Vec<Diagnostic>) {
    for it in items {
        if let ClassItem::Method(m) = it {
            match &m.kind {
                ClassMethodKind::Function(fd)
                | ClassMethodKind::PureVirtual(fd)
                | ClassMethodKind::Extern(fd) => check_function(fd, out),
                ClassMethodKind::Task(td) => check_task(td, out),
            }
        }
    }
}

fn check_function(fd: &FunctionDeclaration, out: &mut Vec<Diagnostic>) {
    check_dup_ports(
        "function",
        &fd.name.name.name,
        &fd.ports,
        &fd.strict_body_ports,
        out,
    );
    check_decl_order_list(&fd.items, out);
}

fn check_task(td: &TaskDeclaration, out: &mut Vec<Diagnostic>) {
    check_dup_ports(
        "task",
        &td.name.name.name,
        &td.ports,
        &td.strict_body_ports,
        out,
    );
    check_decl_order_list(&td.items, out);
}

/// §9.3.1 / §9.3.2 / §13: in a `begin`-`end` or `fork`-`join` block and in a
/// subroutine body, every block item declaration precedes the first
/// statement. A null statement does not end the declaration region here (a
/// stray `;` between declarations is common and harmless), nor do the
/// parser's internal lowering nodes.
fn check_decl_order_list(stmts: &[Statement], out: &mut Vec<Diagnostic>) {
    let mut seen_stmt = false;
    for st in stmts {
        match &st.kind {
            StatementKind::VarDecl { declarators, .. } => {
                if seen_stmt {
                    let name = declarators
                        .first()
                        .map(|d| d.name.name.as_str())
                        .unwrap_or("");
                    let span = declarators.first().map_or(st.span, |d| d.name.span);
                    out.push(Diagnostic::error(
                        format!(
                            "declaration of '{name}' follows a statement; block item declarations must precede the statements of a block (§9.3.1)"
                        ),
                        span,
                    ));
                }
            }
            StatementKind::Typedef(_) => {
                if seen_stmt {
                    out.push(Diagnostic::error(
                        "typedef follows a statement; block item declarations must precede the statements of a block (§9.3.1)",
                        st.span,
                    ));
                }
            }
            StatementKind::Null
            | StatementKind::ScopePop
            | StatementKind::LoopStep
            | StatementKind::ForeachTail { .. }
            | StatementKind::ForeverTail { .. } => {}
            _ => seen_stmt = true,
        }
        check_decl_order_stmt(st, out);
    }
}

fn check_decl_order_stmt(st: &Statement, out: &mut Vec<Diagnostic>) {
    match &st.kind {
        StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => {
            check_decl_order_list(stmts, out)
        }
        StatementKind::If {
            then_stmt,
            else_stmt,
            ..
        } => {
            check_decl_order_stmt(then_stmt, out);
            if let Some(e) = else_stmt {
                check_decl_order_stmt(e, out);
            }
        }
        StatementKind::Case { items, .. } => {
            for it in items {
                check_decl_order_stmt(&it.stmt, out);
            }
        }
        StatementKind::For { body, .. }
        | StatementKind::Foreach { body, .. }
        | StatementKind::While { body, .. }
        | StatementKind::DoWhile { body, .. }
        | StatementKind::Repeat { body, .. }
        | StatementKind::Forever { body } => check_decl_order_stmt(body, out),
        StatementKind::TimingControl { stmt, .. } | StatementKind::Wait { stmt, .. } => {
            check_decl_order_stmt(stmt, out)
        }
        _ => {}
    }
}

/// §13.3/§13.4: a subroutine must not declare the same port twice. Combines the
/// ANSI port list with the retained non-ANSI body declarations.
fn check_dup_ports(
    kind: &str,
    sub_name: &str,
    ports: &[FunctionPort],
    body_ports: &[crate::ast::Identifier],
    out: &mut Vec<Diagnostic>,
) {
    let mut seen: Vec<&str> = Vec::new();
    let names = ports.iter().map(|p| &p.name).chain(body_ports.iter());
    for id in names {
        let n = id.name.as_str();
        if n.is_empty() {
            continue;
        }
        if seen.contains(&n) {
            out.push(Diagnostic::error(
                format!("duplicate port '{}' in {} '{}'", n, kind, sub_name),
                id.span,
            ));
        } else {
            seen.push(n);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::overridable_param_slots;
    use crate::ast::Description;

    fn slots(src: &str) -> Vec<String> {
        let parsed = crate::parse(src);
        assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
        let Some(Description::Module(m)) = parsed.source.descriptions.into_iter().next() else {
            panic!("no module");
        };
        overridable_param_slots(&m.params, &m.items)
            .into_iter()
            .map(str::to_string)
            .collect()
    }

    #[test]
    fn header_parameters_flatten_in_order() {
        let s = slots("module m #(parameter A = 1, B = 2, parameter type T = int); endmodule");
        assert_eq!(s, ["A", "B", "T"]);
    }

    #[test]
    fn body_parameters_count_without_a_header() {
        let s = slots("module m; parameter A = 1, B = 2; localparam L = 3; endmodule");
        assert_eq!(s, ["A", "B"]);
    }

    /// §6.20.1: a parameter port list makes a body `parameter` local.
    #[test]
    fn a_header_makes_body_parameters_local() {
        let s = slots("module m #(parameter A = 1); parameter B = 2; endmodule");
        assert_eq!(s, ["A"]);
    }

    #[test]
    fn a_header_of_only_localparams_leaves_no_slots() {
        let s = slots("module m #(localparam X = 1); parameter B = 2; endmodule");
        assert!(s.is_empty(), "{s:?}");
    }
}
