//! IEEE 1800-2023 §13.4.3: the locals a constant function call starts from.
//!
//! `eval_const_user_function` runs a call over a map of locals that began as
//! a copy of `ElaboratedModule::parameters`, which holds every parameter of
//! every instance elaborated so far, so a design that calls a constant
//! function once per instance took time quadratic in its instance count. The
//! interpreter reads that map only by exact key, so a body whose reads can be
//! listed starts from just the entries it can read; any other body keeps the
//! whole copy, and its result cannot differ from before.

use super::{CONST_FN_PACKAGE, ElaboratedModule, const_fn_call_name};
use crate::ast::decl::FunctionDeclaration;
use crate::ast::expr::{BinaryOp, ExprKind, Expression, UnaryOp};
use crate::ast::stmt::{ForInit, Statement, StatementKind as SK};
use crate::ast::types::{DataType, PackedDimension};
use crate::hasher::HashMap;
use crate::value::Value;

/// The locals a call of `fd` starts from: the entries of `elab.parameters`
/// its body can read (all of them when `read_names` cannot list them), with
/// `caller_params` laid over them. A caller whose scope is the table itself
/// (a call from the top module or a package) adds nothing to it.
pub(super) fn initial_locals(
    fd: &FunctionDeclaration,
    caller_params: &HashMap<String, Value>,
    elab: &ElaboratedModule,
) -> HashMap<String, Value> {
    let mut locals = match read_names(fd, elab) {
        Some(names) => {
            // Inside a function of package `pkg`, `eval_const_expr_val` also
            // reads a name `n` as `pkg::n` and `pkg.n`.
            let pkg = CONST_FN_PACKAGE.with(|c| c.borrow().clone());
            let mut locals = HashMap::default();
            let mut take = |key: String| {
                if let Some(value) = elab.parameters.get(&key) {
                    locals.insert(key, value.clone());
                }
            };
            for name in names {
                if let Some(pkg) = &pkg {
                    take(format!("{pkg}::{name}"));
                    take(format!("{pkg}.{name}"));
                }
                take(name);
            }
            locals
        }
        None => elab.parameters.clone(),
    };
    if !std::ptr::eq(caller_params, &elab.parameters) {
        locals.extend(
            caller_params
                .iter()
                .map(|(name, value)| (name.clone(), value.clone())),
        );
    }
    locals
}

/// Every key a call of `fd` can read from its locals, or `None` when the
/// body holds a construct whose reads are not listed here: a select, a
/// member access, a cast, `$bits` or another system function, a statement
/// the interpreter does not run, or a type whose width is not literal.
///
/// `eval_const_expr_val` reads `n` as `n`, and `a.b` / `a::b` as `a`,
/// `a::b`, `a.b` and `b`; an assignment reads its target's old width. With
/// literal widths, sizing and binding the formals, the locals and the return
/// variable (`ConstFnStructLayouts`, `ConstFnPackedElems`) read nothing. A
/// nested call converts each actual to the callee's formal type over these
/// locals, so the callee's formals must be literal too; the callee then
/// starts from its own keys, with these locals laid over them.
fn read_names(fd: &FunctionDeclaration, elab: &ElaboratedModule) -> Option<Vec<String>> {
    if !literal_type(&fd.return_type) || !literal_formals(fd) {
        return None;
    }
    let mut names = Vec::new();
    for st in &fd.items {
        stmt(st, elab, &mut names)?;
    }
    Some(names)
}

/// `int`, `real`, `logic`, `bit [7:0]`, `[3:0]`: a type whose width and
/// signing follow from the type itself.
fn literal_type(dt: &DataType) -> bool {
    let literal = |e: &Expression| matches!(e.kind, ExprKind::Number(_));
    match dt {
        DataType::IntegerAtom { .. } | DataType::Real { .. } => true,
        DataType::IntegerVector { dimensions, .. } | DataType::Implicit { dimensions, .. } => {
            dimensions.iter().all(|d| {
                matches!(d, PackedDimension::Range { left, right, .. }
                    if literal(left) && literal(right))
            })
        }
        _ => false,
    }
}

fn literal_formals(fd: &FunctionDeclaration) -> bool {
    fd.ports
        .iter()
        .all(|p| p.dimensions.is_empty() && literal_type(&p.data_type))
}

fn stmt(st: &Statement, elab: &ElaboratedModule, names: &mut Vec<String>) -> Option<()> {
    match &st.kind {
        SK::Null => {}
        SK::SeqBlock { stmts, .. } => {
            for st in stmts {
                stmt(st, elab, names)?;
            }
        }
        SK::VarDecl {
            data_type,
            declarators,
            ..
        } => {
            if !literal_type(data_type) {
                return None;
            }
            for d in declarators {
                if let Some(init) = &d.init {
                    expr(init, elab, names)?;
                }
            }
        }
        SK::BlockingAssign { lvalue, rvalue } => {
            target(lvalue, names)?;
            expr(rvalue, elab, names)?;
        }
        SK::If {
            condition,
            then_stmt,
            else_stmt,
            ..
        } => {
            expr(condition, elab, names)?;
            stmt(then_stmt, elab, names)?;
            if let Some(else_stmt) = else_stmt {
                stmt(else_stmt, elab, names)?;
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
                    ForInit::VarDecl { init, .. } => expr(init, elab, names)?,
                    ForInit::Assign { lvalue, rvalue } => {
                        target(lvalue, names)?;
                        expr(rvalue, elab, names)?;
                    }
                }
            }
            if let Some(condition) = condition {
                expr(condition, elab, names)?;
            }
            for e in step {
                step_expr(e, elab, names)?;
            }
            stmt(body, elab, names)?;
        }
        SK::While { condition, body } => {
            expr(condition, elab, names)?;
            stmt(body, elab, names)?;
        }
        SK::Case {
            expr: sel, items, ..
        } => {
            expr(sel, elab, names)?;
            for item in items {
                if item.pattern.is_some() || item.guard.is_some() {
                    return None;
                }
                for p in &item.patterns {
                    expr(p, elab, names)?;
                }
                stmt(&item.stmt, elab, names)?;
            }
        }
        SK::Return(e) => {
            if let Some(e) = e {
                expr(e, elab, names)?;
            }
        }
        SK::Expr(e) => step_expr(e, elab, names)?,
        _ => return None,
    }
    Some(())
}

/// `i++` / `i--` and `i = e`, the expressions a `for` step (or an
/// expression statement) runs.
fn step_expr(e: &Expression, elab: &ElaboratedModule, names: &mut Vec<String>) -> Option<()> {
    match &e.kind {
        ExprKind::Unary {
            op: UnaryOp::PostIncr | UnaryOp::PreIncr | UnaryOp::PostDecr | UnaryOp::PreDecr,
            operand,
        } => target(operand, names),
        ExprKind::Binary {
            op: BinaryOp::Assign,
            left,
            right,
        }
        | ExprKind::AssignExpr {
            lvalue: left,
            rvalue: right,
        } => {
            target(left, names)?;
            expr(right, elab, names)
        }
        _ => None,
    }
}

/// A whole variable written by name; anything else is not listed.
fn target(e: &Expression, names: &mut Vec<String>) -> Option<()> {
    match &e.kind {
        ExprKind::Ident(h) if h.path.len() == 1 && h.path[0].selects.is_empty() => {
            names.push(h.path[0].name.name.clone());
            Some(())
        }
        _ => None,
    }
}

fn expr(e: &Expression, elab: &ElaboratedModule, names: &mut Vec<String>) -> Option<()> {
    match &e.kind {
        ExprKind::Number(_) => {}
        ExprKind::Ident(h) if h.path.iter().all(|s| s.selects.is_empty()) => {
            match h.path.as_slice() {
                [n] => names.push(n.name.name.clone()),
                [a, b] => {
                    let (a, b) = (&a.name.name, &b.name.name);
                    names.extend([
                        a.clone(),
                        b.clone(),
                        format!("{a}::{b}"),
                        format!("{a}.{b}"),
                    ]);
                }
                _ => return None,
            }
        }
        ExprKind::Paren(inner) => expr(inner, elab, names)?,
        ExprKind::Unary { operand, .. } => expr(operand, elab, names)?,
        ExprKind::Binary { left, right, .. } => {
            expr(left, elab, names)?;
            expr(right, elab, names)?;
        }
        ExprKind::Conditional {
            condition,
            then_expr,
            else_expr,
        } => {
            expr(condition, elab, names)?;
            expr(then_expr, elab, names)?;
            expr(else_expr, elab, names)?;
        }
        ExprKind::SystemCall { name, args }
            if matches!(name.as_str(), "$clog2" | "$signed" | "$unsigned") =>
        {
            for a in args {
                expr(a, elab, names)?;
            }
        }
        // The callee as `substitute_const_fn_calls` resolves it.
        ExprKind::Call { func, args } => {
            let (fname, scoped) = const_fn_call_name(func)?;
            let callee = scoped
                .as_deref()
                .and_then(|k| elab.functions.get(k))
                .or_else(|| elab.functions.get(&fname))?;
            if !literal_formals(callee) {
                return None;
            }
            for a in args {
                expr(a, elab, names)?;
            }
        }
        _ => return None,
    }
    Some(())
}

#[cfg(test)]
mod tests {
    use super::read_names;
    use crate::ast::Description;
    use crate::elaborate::{Definition, elaborate_module};
    use crate::hasher::HashMap;

    /// The shapes #737 measured take the listed path; `$bits` keeps the copy.
    #[test]
    fn listed_bodies_name_what_they_read() {
        let parsed = crate::parse_str(
            "
module top;
  localparam int K = 2;
  function automatic int iter(input int v);
    int r;
    r = 0;
    while ((1 << r) < v) r++;
    return r + K;
  endfunction
  function automatic int rec(input int v);
    return (v <= 1) ? 0 : 1 + rec((v + 1) / 2);
  endfunction
  function automatic int bits(input int v);
    return v + $bits(v);
  endfunction
  localparam int A = iter(5) + rec(5) + bits(5);
endmodule
",
        )
        .expect("parse");
        let Description::Module(module) = &parsed.source.descriptions[0] else {
            panic!("module");
        };
        let model =
            elaborate_module(Definition::Module(module), &HashMap::default()).expect("elaborate");
        let names = |f: &str| read_names(&model.functions[f], &model);
        assert!(names("iter").is_some_and(|n| n.iter().any(|n| n == "K")));
        assert_eq!(names("rec"), Some(vec!["v".to_string(), "v".to_string()]));
        assert_eq!(names("bits"), None);
        assert_eq!(model.parameters["A"].to_u64(), Some(5 + 3 + 37));
    }
}
