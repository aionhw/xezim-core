use xezim_core::ast::{Description, decl::ModuleItem, expr::ExprKind};
use xezim_core::elaborate::{for_each_stmt_expr, for_each_sub_expr};
use xezim_core::hasher::HashSet;

/// §9.4/§16.4: inspect controls, assertion actions and procedural targets.
#[test]
fn statement_expressions_include_controls_actions_and_targets() {
    let parsed = xezim_core::parse_str(
        r#"
module top;
  int x, driven, arr[4];
  initial begin
    #(delay_value) x=delay_rhs;
    @(posedge edge_value iff gate_value) x=edge_rhs;
    wait(wait_value) x=wait_rhs;
    foreach(arr[i]) x=arr[i];
    assert(assert_value) x=pass_value; else x=fail_value;
    force driven=force_value;
    release driven;
    assign driven=assign_value;
    deassign driven;
    x=arr[select_value];
  end
endmodule
"#,
    )
    .expect("parse");
    let Description::Module(module) = &parsed.source.descriptions[0] else {
        panic!("module");
    };
    let mut names = HashSet::default();
    let mut target_visits = 0;
    for item in &module.items {
        if let ModuleItem::InitialConstruct(initial) = item {
            for_each_stmt_expr(&initial.stmt, &mut |expr| {
                for_each_sub_expr(expr, &mut |expr| {
                    if let ExprKind::Ident(hier) = &expr.kind {
                        for segment in &hier.path {
                            names.insert(segment.name.name.clone());
                            target_visits += usize::from(segment.name.name == "driven");
                        }
                    }
                });
            });
        }
    }
    for expected in [
        "delay_value",
        "delay_rhs",
        "edge_value",
        "gate_value",
        "edge_rhs",
        "wait_value",
        "wait_rhs",
        "arr",
        "i",
        "assert_value",
        "pass_value",
        "fail_value",
        "driven",
        "force_value",
        "assign_value",
        "select_value",
    ] {
        assert!(names.contains(expected), "missing {expected}: {names:?}");
    }
    assert_eq!(target_visits, 4);
}

/// §7.3.2/§11.4.14/§12.6: runtime payloads remain visible to read-only scans.
#[test]
fn expression_visits_include_runtime_payloads() {
    use xezim_core::ast::{
        Identifier, Span,
        expr::{AssignmentPatternItem, Expression},
        stmt::Pattern,
    };
    let expr = |kind| Expression::new(kind, Span::dummy());
    let leaf = |name: &str| expr(ExprKind::StringLiteral(name.into()));
    let root = expr(ExprKind::Concatenation(vec![
        expr(ExprKind::StreamOp {
            left_to_right: true,
            slice_size: Some(Box::new(leaf("slice"))),
            exprs: vec![leaf("stream")],
        }),
        expr(ExprKind::Matches {
            expr: Box::new(leaf("subject")),
            pattern: Box::new(Pattern::Binding(Identifier {
                name: "binding".into(),
                span: Span::dummy(),
            })),
        }),
        expr(ExprKind::Tagged {
            tag: Identifier {
                name: "tag".into(),
                span: Span::dummy(),
            },
            inner: Some(Box::new(leaf("tagged"))),
        }),
        expr(ExprKind::AssignmentPattern(vec![
            AssignmentPatternItem::Keyed(leaf("key"), leaf("value")),
        ])),
    ]));
    let mut leaves = Vec::new();
    for_each_sub_expr(&root, &mut |expr| {
        if let ExprKind::StringLiteral(name) = &expr.kind {
            leaves.push(name.clone());
        }
    });
    assert_eq!(
        leaves,
        ["slice", "stream", "subject", "tagged", "key", "value"]
    );
}
