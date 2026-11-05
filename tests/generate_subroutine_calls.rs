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
