//! Templates: a class template, or a module template with a type
//! parameter, is instantiated per argument list. Each instantiation is
//! lowered as its own class or module (`fifo<int, 4>` → `fifo__int32__4`),
//! with its parameters bound to the arguments: types, and constants for
//! the value parameters. A module template with value parameters only stays
//! one SV module with SV parameters.
//!
//! The instantiations are found before anything is lowered (module
//! interfaces need every child's): every type the program names is
//! resolved, and each new instantiation's own code searched in turn.

use std::collections::BTreeMap;

use super::lower::Lw;
use super::module::visit_stmt_exprs;
use super::types::*;
use crate::sv_parser::systemc::ast as sc;

/// The templates instantiated per argument list: class templates, and
/// module templates with a type parameter.
pub fn templates(lw: &Lw) -> BTreeMap<String, Vec<sc::TemplateParam>> {
    let mut out = BTreeMap::new();
    for (n, (_, c, tps)) in &lw.prog.classes {
        let has_type = tps
            .iter()
            .any(|p| matches!(p, sc::TemplateParam::Type { .. }));
        if !tps.is_empty() && (!c.sc_module || has_type) {
            out.insert(n.clone(), tps.clone());
        }
    }
    out
}

/// The parameter bindings of an instantiation; the template's own name
/// inside it (the injected class name) is the instantiation.
pub fn bindings(lw: &Lw, inst: &str) -> BTreeMap<String, TParam> {
    let mut out = BTreeMap::new();
    let Some(i) = lw.env.instances.borrow().get(inst).cloned() else {
        return out;
    };
    let Some((_, c, tps)) = lw.prog.classes.get(&i.template) else {
        return out;
    };
    for (p, a) in tps.iter().zip(&i.args) {
        let name = match p {
            sc::TemplateParam::Type { name, .. } | sc::TemplateParam::Value { name, .. } => name,
        };
        if let Some(n) = name {
            out.insert(
                n.name.clone(),
                match a {
                    TArg::Ty(t) => TParam::Type(t.clone()),
                    TArg::Val(v) => TParam::Const(*v),
                },
            );
        }
    }
    if !c.sc_module {
        out.insert(
            i.template.clone(),
            TParam::Type(Ty::Class(format!("sc_c_{}", inst))),
        );
    }
    out
}

/// Find every instantiation the program uses.
pub fn discover(lw: &mut Lw) {
    let saved = std::mem::take(&mut lw.env.tparams);
    // Code outside templates.
    let prog = lw.prog;
    for (n, (_, c, tps)) in &prog.classes {
        if lw.env.templates.contains_key(n) || !tps.is_empty() && !c.sc_module {
            continue;
        }
        // A value-parameter module template: its parameters are SV
        // parameters.
        for tp in tps {
            if let sc::TemplateParam::Value { name: Some(p), .. } = tp {
                lw.env
                    .tparams
                    .insert(p.name.clone(), TParam::Value(p.name.clone()));
            }
        }
        scan_class(lw, n, c);
        lw.env.tparams.clear();
    }
    for (_, f) in prog.free_fns.values() {
        scan_fn(lw, f);
    }
    if let Some((_, f)) = prog.sc_main {
        scan_fn(lw, f);
    }
    // Each instantiation's own code, until no new one appears.
    let mut done = std::collections::BTreeSet::new();
    loop {
        let todo: Vec<String> = lw
            .env
            .instances
            .borrow()
            .keys()
            .filter(|k| !done.contains(*k))
            .cloned()
            .collect();
        if todo.is_empty() {
            break;
        }
        for inst in todo {
            done.insert(inst.clone());
            let template = lw.env.instances.borrow()[&inst].template.clone();
            let Some((_, c, _)) = prog.classes.get(&template) else {
                continue;
            };
            lw.env.tparams = bindings(lw, &inst);
            scan_class(lw, &template, c);
        }
    }
    lw.env.tparams = saved;
}

fn note(lw: &Lw, q: &sc::QualifiedName) {
    if q.last_args().is_some() && lw.env.templates.contains_key(q.last_name()) {
        // Errors (an argument that is not a constant) are reported where
        // the type is lowered.
        let _ = instantiate(q, &lw.env, &|e| lw.const_eval(e));
    }
}

fn scan_name(lw: &Lw, q: &sc::QualifiedName) {
    note(lw, q);
    for seg in &q.segments {
        for a in seg.template_args.iter().flatten() {
            match a {
                sc::TemplateArg::Type(t) => scan_type(lw, t),
                sc::TemplateArg::Expr(e) => scan_expr(lw, e),
            }
        }
    }
}

fn scan_type(lw: &Lw, t: &sc::Type) {
    match &t.base {
        sc::TypeName::Named(q) | sc::TypeName::Elaborated { name: q, .. } => scan_name(lw, q),
        _ => {}
    }
}

fn scan_expr(lw: &Lw, e: &sc::Expr) {
    super::module::visit_expr(e, &mut |x| match &x.kind {
        sc::ExprKind::Name(q) => scan_name(lw, q),
        sc::ExprKind::New { ty, .. }
        | sc::ExprKind::Cast { ty, .. }
        | sc::ExprKind::SizeofType(ty) => scan_type(lw, ty),
        _ => {}
    });
}

fn scan_stmts(lw: &Lw, stmts: &[sc::Stmt]) {
    for s in stmts {
        scan_stmt(lw, s);
    }
}

fn scan_stmt(lw: &Lw, s: &sc::Stmt) {
    fn decls(s: &sc::Stmt, out: &mut Vec<sc::VarDecl>) {
        use sc::Stmt as S;
        match s {
            S::Decl(v) => out.push(v.clone()),
            S::Block(b) => b.stmts.iter().for_each(|s| decls(s, out)),
            S::If {
                init,
                then_branch,
                else_branch,
                ..
            } => {
                if let Some(i) = init {
                    decls(i, out);
                }
                decls(then_branch, out);
                if let Some(e) = else_branch {
                    decls(e, out);
                }
            }
            S::For { init, body, .. } => {
                if let Some(i) = init {
                    decls(i, out);
                }
                decls(body, out);
            }
            S::RangeFor { body, .. } | S::While { body, .. } | S::DoWhile { body, .. } => {
                decls(body, out)
            }
            S::Switch { arms, .. } => {
                for a in arms {
                    a.body.iter().for_each(|s| decls(s, out));
                }
            }
            _ => {}
        }
    }
    let mut vs = Vec::new();
    decls(s, &mut vs);
    for v in &vs {
        scan_type(lw, &v.ty);
    }
    visit_stmt_exprs(s, &mut |e| scan_expr(lw, e));
}

fn scan_fn(lw: &Lw, f: &sc::FunctionDecl) {
    if let Some(t) = &f.return_type {
        scan_type(lw, t);
    }
    for p in &f.params {
        scan_type(lw, &p.ty);
    }
    for mi in &f.initializers {
        scan_name(lw, &mi.name);
        mi.args.iter().for_each(|a| scan_expr(lw, a));
    }
    if let Some(b) = &f.body {
        scan_stmts(lw, &b.stmts);
    }
}

fn scan_class(lw: &Lw, name: &str, c: &sc::ClassDecl) {
    for b in &c.bases {
        scan_name(lw, &b.name);
    }
    for m in &c.members {
        match m {
            sc::Member::Field(v) => {
                scan_type(lw, &v.ty);
                for d in &v.declarators {
                    match &d.init {
                        Some(sc::Initializer::Assign(e)) => scan_expr(lw, e),
                        Some(sc::Initializer::Paren(a) | sc::Initializer::Brace(a)) => {
                            a.iter().for_each(|e| scan_expr(lw, e))
                        }
                        None => {}
                    }
                }
            }
            sc::Member::Method(f) | sc::Member::Constructor(f) => scan_fn(lw, f),
            sc::Member::Typedef(t) => scan_type(lw, &t.ty),
            _ => {}
        }
    }
    for (_, f) in lw.prog.out_of_class.get(name).into_iter().flatten() {
        scan_fn(lw, f);
    }
}
