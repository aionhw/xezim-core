//! §23.8.1: a bare call that names no subroutine of its own definition, its
//! compilation unit or its imports is looked up from the scope of its
//! instantiation, then from each enclosing instance's. The inliner rewrites
//! it to the key of the subroutine found there (`g.f`, `u.f`, `u.g[1].f`).
//! Run-time results are pinned in xezim's
//! `tests/hierarchy/upward_subroutine_calls.rs`.

use xezim_core::ast::expr::{ExprKind, Expression};
use xezim_core::elaborate::ElaboratedModule;

fn elab(src: &str) -> ElaboratedModule {
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

/// The callee of the call driving `lhs`.
fn callee_of(m: &ElaboratedModule, lhs: &str) -> String {
    let name = |e: &Expression| match &e.kind {
        ExprKind::Ident(h) => h
            .path
            .iter()
            .map(|s| s.name.name.as_str())
            .collect::<Vec<_>>()
            .join("."),
        other => panic!("not an identifier: {other:?}"),
    };
    let ca = m
        .continuous_assigns
        .iter()
        .find(|ca| name(&ca.lhs) == lhs)
        .unwrap_or_else(|| {
            panic!(
                "no continuous assign drives {lhs}; have {:?}",
                m.continuous_assigns
                    .iter()
                    .map(|ca| name(&ca.lhs))
                    .collect::<Vec<_>>()
            )
        });
    match &ca.rhs.kind {
        ExprKind::Call { func, .. } => name(func),
        other => panic!("not a call: {other:?}"),
    }
}

const CHILD: &str = "module c; wire [7:0] w; assign w = f(); endmodule";

#[test]
fn a_call_from_a_child_names_the_block_function_of_its_instantiation() {
    let m = elab(&format!(
        "{CHILD}
         module top; function automatic int f(); return 100; endfunction
           if (1) begin : g function automatic int f(); return 1; endfunction c x(); end
           if (1) begin c y(); end
         endmodule"
    ));
    assert_eq!(callee_of(&m, "g.x.w"), "g.f");
    // The module's own function keeps its spelling.
    assert_eq!(callee_of(&m, "genblk2.y.w"), "f");
}

#[test]
fn a_call_from_a_child_names_its_parent_instances_function() {
    let m = elab(&format!(
        "{CHILD}
         module m #(parameter P = 0); function automatic int f(); return P; endfunction
           c x(); endmodule
         module top; function automatic int f(); return 100; endfunction
           m #(5) v(); m #(3) u(); endmodule"
    ));
    assert_eq!(callee_of(&m, "v.x.w"), "v.f");
    assert_eq!(callee_of(&m, "u.x.w"), "u.f");
}

#[test]
fn a_call_from_a_child_in_a_generate_loop_names_its_iterations_function() {
    let m = elab(&format!(
        "{CHILD}
         module m; for (genvar i = 0; i < 2; i++) begin : g
           function automatic int f(); return i; endfunction
           for (genvar j = 0; j < 2; j++) begin : h c x(); end end endmodule
         module top; m u(); endmodule"
    ));
    assert_eq!(callee_of(&m, "u.g[0].h[1].x.w"), "u.g[0].f");
    assert_eq!(callee_of(&m, "u.g[1].h[0].x.w"), "u.g[1].f");
}

#[test]
fn a_call_from_a_grandchild_and_a_bound_instance_searches_each_enclosing_instance() {
    let m = elab(&format!(
        "{CHILD}
         module mid; c z(); endmodule
         module m; function automatic int f(); return 2; endfunction endmodule
         module top; if (1) begin : g function automatic int f(); return 1; endfunction
           mid x(); end
           m u(); bind m c k(); endmodule"
    ));
    assert_eq!(callee_of(&m, "g.x.z.w"), "g.f");
    // §23.11: a bound instance sits in its target's scope.
    assert_eq!(callee_of(&m, "u.k.w"), "u.f");
}

#[test]
fn the_unit_and_an_import_stop_the_upward_search_and_a_parents_data_does_not() {
    let m = elab(
        "package p; function automatic int f(); return 7; endfunction endpackage
         function automatic int h(); return 42; endfunction
         module c; wire [7:0] w; assign w = h(); endmodule
         module ci; import p::*; wire [7:0] w; assign w = f(); endmodule
         module cd; wire [7:0] w; assign w = f(); endmodule
         module md; int f = 5; cd x(); endmodule
         module top; function automatic int f(); return 100; endfunction
           if (1) begin : g function automatic int f(); return 1; endfunction
             function automatic int h(); return 1; endfunction
             c x(); ci y(); end
           md u(); endmodule",
    );
    // §23.8.1: the compilation unit, then §26.3: the child's own import.
    // The unit function is spelled as the child's own copy, not the block's.
    assert_ne!(callee_of(&m, "g.x.w"), "g.h");
    assert_eq!(callee_of(&m, "g.y.w"), "f");
    // §23.8.1: the search is for a scope named `f`; `md`'s data is none, so
    // it goes on to the top's `f`, whose key is its name.
    assert_eq!(callee_of(&m, "u.x.w"), "f");
}

#[test]
fn a_variable_in_the_parents_block_does_not_stop_the_upward_search() {
    // §23.8.1: `m`'s function, past the block's `int f`.
    let m = elab(
        "module cd; wire [7:0] w; assign w = f(); endmodule
         module m; function automatic int f(); return 3; endfunction
           if (1) begin : g int f = 9; cd x(); end endmodule
         module top; function automatic int f(); return 100; endfunction
           m u(); endmodule",
    );
    assert_eq!(callee_of(&m, "u.g.x.w"), "u.f");
}

#[test]
fn an_import_of_an_enclosing_scope_is_not_visible_to_the_upward_search() {
    // §26.3: an imported name is not visible by hierarchical reference.
    let m = elab(&format!(
        "{CHILD}
         package p; function automatic int f(); return 7; endfunction endpackage
         module m; import p::*; c x(); endmodule
         module top; if (1) begin : g function automatic int f(); return 1; endfunction
           m u(); end endmodule"
    ));
    assert_eq!(callee_of(&m, "g.u.x.w"), "g.f");
}
