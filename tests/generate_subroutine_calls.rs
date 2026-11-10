//! §27.4, §23.9: a generate-for iteration's functions and tasks are named
//! `<scope>.<name>` (`g[0].f`); a bare call to one from inside the iteration
//! is renamed with it. The call was left bare and failed elaboration as an
//! undeclared identifier. Run-time results are pinned in xezim's
//! `tests/hierarchy/generate_block_subroutines.rs`.

fn elaborate(source: &str) -> Result<xezim_core::ElaboratedModule, String> {
    xezim_core::parse_and_elaborate_multi(
        &[source.to_string()],
        Some("t"),
        &[],
        &["t.sv".to_string()],
        &[],
    )
    .map(|r| r.1)
}

#[test]
fn a_call_inside_the_iteration_names_its_own_copy() {
    let design = elaborate(
        "module t;
           for (genvar i = 0; i < 2; i++) begin : g
             function automatic int f(); return i; endfunction
             function automatic int r(); r = f() + 1; endfunction
             task automatic k(); endtask
             int v;
             initial begin v = r(); k(); end
             if (1) begin : h initial v = f(); end
           end
         endmodule",
    )
    .unwrap_or_else(|e| panic!("rejected: {e}"));
    for name in ["g[0].f", "g[1].f", "g[0].r", "g[1].r"] {
        assert!(design.functions.contains_key(name), "no function {name}");
    }
    for name in ["g[0].k", "g[1].k"] {
        assert!(design.tasks.contains_key(name), "no task {name}");
    }
}

#[test]
fn an_iteration_with_subroutines_but_no_data_is_renamed() {
    elaborate(
        "module t;
           for (genvar i = 0; i < 2; i++) begin : g
             function automatic int f(); return i; endfunction
             initial $display(\"%0d\", f());
           end
         endmodule",
    )
    .unwrap_or_else(|e| panic!("rejected: {e}"));
}

// §23.9 / §27.6 (#897): a conditional generate block's functions and tasks
// are the block's own, like its data. The declaration is registered as
// `<block>.f`, a bare call from inside the block names that copy, and a call
// from outside the block (or at module level) never reaches it. Two labelled
// blocks declaring `look` used to share one flat entry (the last block's body
// answered every call), and a block's `t` was a false duplicate of the
// module's `t`.

fn design(source: &str) -> xezim_core::ElaboratedModule {
    let mut d = elaborate(source).unwrap_or_else(|e| panic!("rejected: {e}"));
    // The processes of an inlined instance are materialized on demand.
    d.materialize_pending();
    d
}

/// The callee names of every call in `stmts`, in source order.
fn call_names(stmts: &[xezim_core::ast::stmt::Statement]) -> Vec<String> {
    use xezim_core::ast::expr::ExprKind;
    use xezim_core::ast::stmt::StatementKind as SK;
    fn in_expr(e: &xezim_core::ast::expr::Expression, out: &mut Vec<String>) {
        match &e.kind {
            ExprKind::Call { func, args } => {
                if let ExprKind::Ident(h) = &func.kind {
                    out.push(
                        h.path
                            .iter()
                            .map(|s| s.name.name.as_str())
                            .collect::<Vec<_>>()
                            .join("."),
                    );
                }
                for a in args {
                    in_expr(a, out);
                }
            }
            ExprKind::Binary { left, right, .. } => {
                in_expr(left, out);
                in_expr(right, out);
            }
            ExprKind::Conditional {
                condition,
                then_expr,
                else_expr,
            } => {
                in_expr(condition, out);
                in_expr(then_expr, out);
                in_expr(else_expr, out);
            }
            ExprKind::Paren(x) | ExprKind::Unary { operand: x, .. } => in_expr(x, out),
            _ => {}
        }
    }
    fn in_stmt(s: &xezim_core::ast::stmt::Statement, out: &mut Vec<String>) {
        match &s.kind {
            SK::Expr(e) | SK::Return(Some(e)) => in_expr(e, out),
            SK::BlockingAssign { lvalue, rvalue } => {
                in_expr(lvalue, out);
                in_expr(rvalue, out);
            }
            SK::SeqBlock { stmts, .. } | SK::ParBlock { stmts, .. } => {
                for st in stmts {
                    in_stmt(st, out);
                }
            }
            SK::TimingControl { stmt, .. } => in_stmt(stmt, out),
            SK::Disable(h) => out.push(format!("disable {}", xezim_core::ast::stmt::disable_name(h))),
            _ => {}
        }
    }
    let mut out = Vec::new();
    for st in stmts {
        in_stmt(st, &mut out);
    }
    out
}

fn sorted_task_keys(d: &xezim_core::ElaboratedModule) -> Vec<&str> {
    let mut v: Vec<&str> = d.tasks.keys().map(String::as_str).collect();
    v.sort();
    v
}

fn sorted_fn_keys(d: &xezim_core::ElaboratedModule) -> Vec<&str> {
    let mut v: Vec<&str> = d.functions.keys().map(String::as_str).collect();
    v.sort();
    v
}

#[test]
fn labelled_blocks_each_own_their_task() {
    let d = design(
        "module t;
           if (1) begin : g_a int seen; task automatic look(); seen = 3; endtask initial look(); end
           if (1) begin : g_b int seen; task automatic look(); seen = 9; endtask initial look(); end
         endmodule",
    );
    assert_eq!(sorted_task_keys(&d), ["g_a.look", "g_b.look"]);
    let calls: Vec<Vec<String>> = d
        .initial_blocks
        .iter()
        .map(|b| call_names(std::slice::from_ref(&b.stmt)))
        .collect();
    assert_eq!(calls, [["g_a.look"], ["g_b.look"]]);
    // The task body writes the block's own `seen`.
    let body = &d.tasks["g_a.look"].items;
    let xezim_core::ast::stmt::StatementKind::BlockingAssign { lvalue, .. } = &body[0].kind else {
        panic!("unexpected body {:?}", body[0].kind);
    };
    let xezim_core::ast::expr::ExprKind::Ident(h) = &lvalue.kind else {
        panic!("unexpected lvalue");
    };
    assert_eq!(h.path[0].name.name, "g_a.seen");
}

#[test]
fn labelled_case_arms_each_own_their_function() {
    let d = design(
        "module t;
           case (1) 1: begin : g_a function automatic int f(); return 3; endfunction int v; initial v = f(); end endcase
           case (2) 2: begin : g_b function automatic int f(); return 9; endfunction int v; initial v = f(); end endcase
         endmodule",
    );
    assert_eq!(sorted_fn_keys(&d), ["g_a.f", "g_b.f"]);
}

#[test]
fn nested_blocks_sharing_a_label_compose_their_scopes() {
    let d = design(
        "module t;
           if (1) begin : a if (1) begin : n int s; task automatic t(); s = 1; endtask initial t(); end end
           if (1) begin : b if (1) begin : n int s; task automatic t(); s = 2; endtask initial t(); end end
         endmodule",
    );
    assert_eq!(sorted_task_keys(&d), ["a.n.t", "b.n.t"]);
    let calls: Vec<Vec<String>> = d
        .initial_blocks
        .iter()
        .map(|b| call_names(std::slice::from_ref(&b.stmt)))
        .collect();
    assert_eq!(calls, [["a.n.t"], ["b.n.t"]]);
}

#[test]
fn unlabelled_blocks_scope_their_functions_under_genblk() {
    let d = design(
        "module t;
           int a, b;
           if (1) begin function automatic int f(); return 1; endfunction initial a = f(); end
           if (1) begin function automatic int f(); return 2; endfunction initial b = f(); end
         endmodule",
    );
    assert_eq!(sorted_fn_keys(&d), ["genblk1.f", "genblk2.f"]);
    let calls: Vec<Vec<String>> = d
        .initial_blocks
        .iter()
        .map(|b| call_names(std::slice::from_ref(&b.stmt)))
        .collect();
    assert_eq!(calls, [["genblk1.f"], ["genblk2.f"]]);
}

#[test]
fn a_continuous_assign_calls_the_blocks_function() {
    let d = design(
        "module t;
           if (1) begin : g_a function automatic int f(); return 1; endfunction wire [31:0] v; assign v = f(); end
           if (1) begin : g_b function automatic int f(); return 2; endfunction wire [31:0] v; assign v = f(); end
         endmodule",
    );
    let mut rhs: Vec<Vec<String>> = d
        .continuous_assigns
        .iter()
        .map(|ca| {
            let st = xezim_core::ast::stmt::Statement::new(
                xezim_core::ast::stmt::StatementKind::Expr(ca.rhs.clone()),
                ca.rhs.span,
            );
            call_names(std::slice::from_ref(&st))
        })
        .collect();
    rhs.sort();
    assert_eq!(rhs, [["g_a.f"], ["g_b.f"]]);
}

#[test]
fn a_blocks_function_calls_its_sibling_by_the_blocks_name() {
    let d = design(
        "module t;
           if (1) begin : g_a
             function automatic int h(); return 1; endfunction
             function automatic int f(); return h(); endfunction
           end
           if (1) begin : g_b
             function automatic int h(); return 2; endfunction
             function automatic int f(); return h(); endfunction
           end
         endmodule",
    );
    assert_eq!(call_names(&d.functions["g_a.f"].items), ["g_a.h"]);
    assert_eq!(call_names(&d.functions["g_b.f"].items), ["g_b.h"]);
}

#[test]
fn a_module_level_call_does_not_see_a_blocks_task() {
    let d = design(
        "module t;
           int a, b;
           task automatic t(); a = 1; endtask
           if (1) begin : g task automatic t(); b = 2; endtask initial t(); end
           initial t();
         endmodule",
    );
    assert_eq!(sorted_task_keys(&d), ["g.t", "t"]);
    let calls: Vec<Vec<String>> = d
        .initial_blocks
        .iter()
        .map(|b| call_names(std::slice::from_ref(&b.stmt)))
        .collect();
    assert_eq!(calls, [["g.t"], ["t"]]);
}

#[test]
fn a_block_task_before_a_same_named_module_task_is_no_duplicate() {
    let d = design(
        "module t;
           int r;
           if (1) begin : g
             task automatic t(); r = 2; endtask
             if (1) begin : h initial t(); end
           end
           task automatic t(); r = 1; endtask
         endmodule",
    );
    assert_eq!(sorted_task_keys(&d), ["g.t", "t"]);
    assert_eq!(
        call_names(std::slice::from_ref(&d.initial_blocks[0].stmt)),
        ["g.t"]
    );
}

#[test]
fn disable_of_a_block_task_names_the_blocks_copy() {
    let d = design(
        "module t;
           int a = 0, b = 0;
           if (1) begin : g_a
             task automatic t(); #5 a = 1; endtask
             initial begin fork t(); #1 disable t; join end
           end
           if (1) begin : g_b
             task automatic t(); #5 b = 1; endtask
             initial t();
           end
         endmodule",
    );
    assert_eq!(
        call_names(std::slice::from_ref(&d.initial_blocks[0].stmt)),
        ["g_a.t", "disable g_a.t"]
    );
}

#[test]
fn a_disable_by_path_names_the_block_tasks_key_and_a_label_keeps_its_name() {
    // §9.6.2, §23.9, §9.3.4.
    let d = design(
        "module t;
           if (1) begin : g
             if (1) begin : h task automatic t(); endtask end
             task automatic t(); endtask
             initial begin disable h.t; fork begin : t #1; end join_none disable t; end
           end
           initial disable g.h.t;
         endmodule",
    );
    let mut got: Vec<String> = d
        .initial_blocks
        .iter()
        .flat_map(|b| call_names(std::slice::from_ref(&b.stmt)))
        .collect();
    got.sort();
    assert_eq!(got, ["disable g.h.t", "disable g.h.t", "disable t"]);
}

#[test]
fn a_formal_shadows_the_blocks_data_in_the_body() {
    let d = design(
        "module t;
           if (1) begin : g
             int x = 5;
             function automatic int f(int x); int y; y = x; return y + 1; endfunction
             initial x = f(1);
           end
         endmodule",
    );
    let body = &d.functions["g.f"].items;
    let names: Vec<String> = body
        .iter()
        .filter_map(|s| match &s.kind {
            xezim_core::ast::stmt::StatementKind::BlockingAssign { lvalue, rvalue } => {
                let n = |e: &xezim_core::ast::expr::Expression| match &e.kind {
                    xezim_core::ast::expr::ExprKind::Ident(h) => h.path[0].name.name.clone(),
                    _ => String::new(),
                };
                Some(format!("{}={}", n(lvalue), n(rvalue)))
            }
            _ => None,
        })
        .collect();
    assert_eq!(names, ["y=x"]);
    assert!(d.signals.contains_key("g.x"));
}

#[test]
fn a_blocks_subroutines_in_an_instance_carry_the_instance_path() {
    let d = design(
        "module m;
           if (1) begin : g_a int seen; task automatic look(); seen = 3; endtask initial look(); end
           if (1) begin : g_b int seen; task automatic look(); seen = 9; endtask initial look(); end
           if (1) begin function automatic int f(); return 1; endfunction int a; initial a = f(); end
           for (genvar i = 0; i < 2; i++) begin : g
             int seen;
             task automatic look(); seen = 10 + i; endtask
             initial look();
           end
         endmodule
         module t; m u(); endmodule",
    );
    assert_eq!(
        sorted_task_keys(&d),
        ["u.g[0].look", "u.g[1].look", "u.g_a.look", "u.g_b.look"]
    );
    assert_eq!(sorted_fn_keys(&d), ["u.genblk3.f"]);
    let mut calls: Vec<Vec<String>> = d
        .initial_blocks
        .iter()
        .map(|b| call_names(std::slice::from_ref(&b.stmt)))
        .collect();
    calls.sort();
    assert_eq!(
        calls,
        [
            vec!["u.g[0].look"],
            vec!["u.g[1].look"],
            vec!["u.g_a.look"],
            vec!["u.g_b.look"],
            vec!["u.genblk3.f"]
        ]
    );
}

#[test]
fn a_nested_loop_in_a_labelled_block_composes_the_function_path() {
    let d = design(
        "module t;
           if (1) begin : g
             function automatic int f(); return 100; endfunction
             int a; initial a = f();
             for (genvar i = 0; i < 2; i++) begin : l
               function automatic int f(); return 10 + i; endfunction
               int v; initial v = f();
               if (1) begin : h int w; initial w = f(); end
             end
           end
         endmodule",
    );
    assert_eq!(sorted_fn_keys(&d), ["g.f", "g.l[0].f", "g.l[1].f"]);
    let mut calls: Vec<Vec<String>> = d
        .initial_blocks
        .iter()
        .map(|b| call_names(std::slice::from_ref(&b.stmt)))
        .collect();
    calls.sort();
    assert_eq!(
        calls,
        [
            vec!["g.f"],
            vec!["g.l[0].f"],
            vec!["g.l[0].f"],
            vec!["g.l[1].f"],
            vec!["g.l[1].f"]
        ]
    );
}

#[test]
fn an_unlabelled_block_inside_a_labelled_one_hides_the_outer_function() {
    let d = design(
        "module t;
           if (1) begin : g
             function automatic int f(); return 1; endfunction
             int a, b;
             initial a = f();
             if (1) begin
               function automatic int f(); return 2; endfunction
               initial b = f();
             end
           end
         endmodule",
    );
    assert_eq!(sorted_fn_keys(&d), ["g.f", "g.genblk1.f"]);
    let calls: Vec<Vec<String>> = d
        .initial_blocks
        .iter()
        .map(|b| call_names(std::slice::from_ref(&b.stmt)))
        .collect();
    assert_eq!(calls, [["g.f"], ["g.genblk1.f"]]);
}
