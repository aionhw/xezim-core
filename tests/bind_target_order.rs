//! IEEE 1800-2023 §23.11 (#194): a bound instance is elaborated as if it were
//! written at the end of its target's items, also when its target was itself
//! created by a bind. A design that reaches its hierarchy through nested binds
//! elaborates to the same instance, process and continuous-assignment order
//! as the design that writes those instances out.

fn elaborate(src: &str) -> xezim_core::ElaboratedModule {
    let (_, mut m) = xezim_core::parse_and_elaborate_multi(
        &[src.to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .expect("elaborate");
    m.materialize_pending();
    m
}

/// `watch0` .. `watch3` in a chain under every `element`: written into the
/// modules, or bound into each one in turn.
fn source(bound: bool) -> String {
    let mut src = String::new();
    for k in 0..4 {
        let child = if !bound && k < 3 {
            format!("watch{} w();", k + 1)
        } else {
            String::new()
        };
        src.push_str(&format!(
            "module watch{k}(); wire flag = 1; initial $display(\"%m\"); {child} endmodule\n"
        ));
    }
    src.push_str("module element(); wire [3:0] x = 4'd3; initial $display(\"%m\");\n");
    if !bound {
        src.push_str("watch0 w();\n");
    }
    src.push_str("endmodule\nmodule other(); wire y = 1; endmodule\n");
    if bound {
        src.push_str("bind element watch0 w();\n");
        for k in 0..3 {
            src.push_str(&format!("bind watch{k} watch{} w();\n", k + 1));
        }
    }
    src.push_str(
        "module top; element a(); other o(); element b();
         for (genvar i = 0; i < 2; i++) begin : g element u(); other v(); end endmodule\n",
    );
    src
}

fn instance_paths(m: &xezim_core::ElaboratedModule) -> Vec<String> {
    m.instances.iter().map(|i| i.path.clone()).collect()
}

fn initial_scopes(m: &xezim_core::ElaboratedModule) -> Vec<String> {
    m.initial_blocks.iter().map(|b| b.scope.clone()).collect()
}

fn assign_targets(m: &xezim_core::ElaboratedModule) -> Vec<String> {
    m.continuous_assigns
        .iter()
        .map(|c| match &c.lhs.kind {
            xezim_core::ast::expr::ExprKind::Ident(h) => h
                .path
                .iter()
                .map(|s| s.name.name.as_str())
                .collect::<Vec<_>>()
                .join("."),
            other => panic!("assignment target {other:?}"),
        })
        .collect()
}

#[test]
fn nested_bound_instances_follow_their_target_items() {
    let written = elaborate(&source(false));
    let bound = elaborate(&source(true));
    let paths = instance_paths(&bound);
    assert_eq!(paths, instance_paths(&written));
    let at = |p: &str| paths.iter().position(|q| q == p).expect(p);
    assert!(at("a.w.w.w.w") < at("o"));
    assert!(at("g[0].u.w.w.w.w") < at("g[0].v"));
    assert_eq!(initial_scopes(&bound), initial_scopes(&written));
    assert_eq!(assign_targets(&bound), assign_targets(&written));
}
