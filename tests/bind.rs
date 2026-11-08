//! Lexical binding: §23.9 innermost scope first, §26.3 imports, §8 and §13 hiding,
//! §23.8.1 upward. Each test asserts what a name binds to and what the generate
//! rename made of it. `disagree` marks where the two differ.

use xezim_core::ast::Description;
use xezim_core::ast::binding::{Bound, DeclKind};
use xezim_core::ast::decl::ModuleItem;
use xezim_core::ast::expr::ExprKind;
use xezim_core::ast::stmt::StatementKind;
use xezim_core::elaborate::bind::{AuditLine, Disagree, Hide, Outcome, audit_design};
use xezim_core::scope_tree::{build_design, tree_of};

fn audit(src: &str) -> Vec<AuditLine> {
    let parsed = xezim_core::parse(src);
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
    let mut descs = parsed.source.descriptions;
    audit_design(&mut descs)
}

/// The `nth` mention of `name` in walk order.
fn at<'a>(lines: &'a [AuditLine], name: &str, nth: usize) -> &'a AuditLine {
    lines
        .iter()
        .filter(|l| l.name == name)
        .nth(nth)
        .unwrap_or_else(|| panic!("mention {nth} of {name} not in {lines:#?}"))
}

fn check(l: &AuditLine, binding: &str, renamed: Option<&str>, disagree: Option<Disagree>) {
    assert_eq!(l.binding, binding, "{l:?}");
    assert_eq!(l.renamed.as_deref(), renamed, "{l:?}");
    assert_eq!(l.disagree, disagree, "{l:?}");
}

const BLOCK_F: &str = "function automatic int f(); return 5; endfunction";

// Agreement with the rename.

#[test]
fn a_bare_call_binds_to_the_function_of_its_block() {
    let src =
        format!("module top; if (1) begin : g {BLOCK_F} initial $display(f()); end endmodule");
    check(
        at(&audit(&src), "f", 0),
        "Decl(top.g, Function)",
        Some("g.f"),
        None,
    );
}

#[test]
fn the_innermost_block_that_declares_the_name_wins() {
    let src = "module top;
      function int f(); return 1; endfunction
      if (1) begin : g
        function int f(); return 2; endfunction
        if (1) begin : h
          function int f(); return 3; endfunction
          initial $display(f());
        end
        initial $display(f());
      end
      initial $display(f());
    endmodule";
    let l = audit(src);
    check(
        at(&l, "f", 0),
        "Decl(top.g.h, Function)",
        Some("g.h.f"),
        None,
    );
    check(at(&l, "f", 1), "Decl(top.g, Function)", Some("g.f"), None);
    check(at(&l, "f", 2), "Decl(top, Function)", None, None);
}

#[test]
fn a_call_from_a_nested_block_binds_to_the_enclosing_blocks_function() {
    let src = format!(
        "module top; if (1) begin : g {BLOCK_F} if (1) begin : h initial $display(f()); end end endmodule"
    );
    check(
        at(&audit(&src), "f", 0),
        "Decl(top.g, Function)",
        Some("g.f"),
        None,
    );
}

#[test]
fn a_subroutine_of_an_unlabelled_block_is_named_by_its_implicit_scope() {
    let src = format!("module top; if (1) begin {BLOCK_F} initial $display(f()); end endmodule");
    check(
        at(&audit(&src), "f", 0),
        "Decl(top.genblk1, Function)",
        Some("genblk1.f"),
        None,
    );
}

#[test]
fn data_of_an_unlabelled_block_is_named_by_its_implicit_scope() {
    let src = "module top; if (1) begin int x; initial x = 1; end endmodule";
    check(
        at(&audit(src), "x", 0),
        "Decl(top.genblk1, Data)",
        Some("genblk1.x"),
        None,
    );
}

#[test]
fn data_of_a_labelled_block_inside_an_unlabelled_one_takes_both_scopes() {
    let src = "module top; if (1) begin if (1) begin : h int x; initial x = 1; end end endmodule";
    check(
        at(&audit(src), "x", 0),
        "Decl(top.genblk1.h, Data)",
        Some("genblk1.h.x"),
        None,
    );
}

#[test]
fn a_directly_nested_branch_opens_no_scope() {
    let src = format!(
        "module top; if (1) if (1) begin : d {BLOCK_F} initial $display(f()); end endmodule"
    );
    check(
        at(&audit(&src), "f", 0),
        "Decl(top.d, Function)",
        Some("d.f"),
        None,
    );
}

#[test]
fn a_generate_loop_scope_is_indexed_and_its_variable_is_not_bound() {
    let src = "module top; for (genvar i = 0; i < 2; i++) begin : g
        int x; function int f(); return i; endfunction
        initial x = f();
      end endmodule";
    let l = audit(src);
    check(at(&l, "x", 0), "Decl(top.g[@], Data)", Some("g[@].x"), None);
    check(
        at(&l, "f", 0),
        "Decl(top.g[@], Function)",
        Some("g[@].f"),
        None,
    );
    assert_eq!(at(&l, "i", 0).outcome, Outcome::None(Hide::Loop));
}

#[test]
fn an_unlabelled_loop_renames_data_under_its_implicit_name() {
    let src =
        "module top; for (genvar i = 0; i < 2; i++) begin int x; initial x = 1; end endmodule";
    check(
        at(&audit(src), "x", 0),
        "Decl(top.genblk1[@], Data)",
        Some("genblk1[@].x"),
        None,
    );
}

#[test]
fn a_case_arm_is_a_scope_of_its_own() {
    let src = "module top; parameter P = 1;
      case (P)
        1: begin : a int x; initial x = 1; end
        default: begin : b int x; initial x = 2; end
      endcase
    endmodule";
    let l = audit(src);
    check(at(&l, "x", 0), "Decl(top.a, Data)", Some("a.x"), None);
    check(at(&l, "x", 1), "Decl(top.b, Data)", Some("b.x"), None);
    check(at(&l, "P", 0), "Decl(top, Param)", None, None);
}

#[test]
fn a_block_label_binds_in_the_enclosing_scope_as_a_path_head() {
    let src =
        format!("module top; if (1) begin : g {BLOCK_F} end initial $display(g.f()); endmodule");
    check(at(&audit(&src), "g", 0), "Decl(top, Label)", None, None);
}

#[test]
fn an_instance_in_a_block_binds_as_a_path_head() {
    let src = "module c; int n; endmodule
      module top; if (1) begin : g c u(); initial u.n = 1; end endmodule";
    check(
        at(&audit(src), "u", 0),
        "Decl(top.g, Instance)",
        Some("g.u"),
        None,
    );
}

#[test]
fn a_gate_instance_and_a_type_are_names_the_rename_leaves_alone() {
    let src = "module top; wire a, b;
      if (1) begin : g
        typedef int t_t; t_t v;
        buf u(a, b);
        initial $display(u.n);
      end endmodule";
    let l = audit(src);
    check(at(&l, "t_t", 0), "Decl(top.g, Typedef)", None, None);
    check(at(&l, "u", 0), "Decl(top.g, Gate)", None, None);
}

#[test]
fn a_function_body_names_its_result_through_the_functions_own_declaration() {
    // §13.4.1, for an assignment and for a member of the return value.
    let src = "module top; typedef struct { int a; } s_t;
      if (1) begin : g
        function automatic s_t f(); f.a = 1; endfunction
        function automatic int h(); h = 2; endfunction
      end endmodule";
    let l = audit(src);
    check(at(&l, "f", 0), "Decl(top.g, Function)", Some("g.f"), None);
    check(at(&l, "h", 0), "Decl(top.g, Function)", Some("g.h"), None);
}

#[test]
fn a_recursive_call_binds_to_the_function_itself() {
    let src = "module top; if (1) begin : g
        function automatic int f(int n); return n ? f(n - 1) : 0; endfunction
      end endmodule";
    check(
        at(&audit(src), "f", 0),
        "Decl(top.g, Function)",
        Some("g.f"),
        None,
    );
}

#[test]
fn a_formal_hides_a_block_function_in_the_body() {
    let src = format!(
        "module top; if (1) begin : g {BLOCK_F}
           function automatic int h(int f); return f; endfunction end endmodule"
    );
    let l = at_outcome(&src, "f");
    assert_eq!(l.outcome, Outcome::None(Hide::Formal));
    check(&l, "none", None, None);
}

fn at_outcome(src: &str, name: &str) -> AuditLine {
    at(&audit(src), name, 0).clone()
}

#[test]
fn a_formal_default_binds_in_the_declaring_scope_not_among_the_formals() {
    // §13.5.3.
    let src = "module top; if (1) begin : g int b;
        function automatic int f(int a = b, int b = 1); return a + b; endfunction
      end endmodule";
    let l = audit(src);
    check(at(&l, "b", 0), "Decl(top.g, Data)", Some("g.b"), None);
    assert_eq!(at(&l, "b", 1).outcome, Outcome::None(Hide::Formal));
    check(at(&l, "b", 1), "none", None, None);
}

#[test]
fn a_subroutine_local_hides_a_block_function_with_the_rename_agreeing() {
    let src = format!(
        "module top; if (1) begin : g {BLOCK_F}
           function automatic int h(); int f = 1; return f; endfunction end endmodule"
    );
    let l = at_outcome(&src, "f");
    assert_eq!(l.outcome, Outcome::None(Hide::Local));
    check(&l, "none", None, None);
}

#[test]
fn a_for_variable_hides_a_block_declaration_in_the_loop() {
    let src = "module top; if (1) begin : g int i;
        initial for (int i = 0; i < 2; i++) $display(i);
      end endmodule";
    let l = audit(src);
    for nth in 0..3 {
        assert_eq!(at(&l, "i", nth).outcome, Outcome::None(Hide::Loop));
        check(at(&l, "i", nth), "none", None, None);
    }
}

#[test]
fn a_foreach_variable_hides_a_block_declaration_in_the_loop() {
    let src = "module top; if (1) begin : g int i; int a[2];
        initial foreach (a[i]) $display(i);
      end endmodule";
    let l = audit(src);
    assert_eq!(at(&l, "i", 0).outcome, Outcome::None(Hide::Loop));
    check(at(&l, "i", 0), "none", None, None);
    check(at(&l, "a", 0), "Decl(top.g, Data)", Some("g.a"), None);
}

#[test]
fn an_inner_block_import_is_found_after_the_blocks_own_names() {
    // §23.8.1 Example 2: the block's own function wins over a wildcard import.
    let src = format!(
        "package p; function automatic int f(); return 100; endfunction endpackage
         module top; if (1) begin : g import p::*; {BLOCK_F} initial $display(f()); end endmodule"
    );
    check(
        at(&audit(&src), "f", 0),
        "Decl(top.g, Function)",
        Some("g.f"),
        None,
    );
}

#[test]
fn the_block_function_wins_over_a_wildcard_import_of_the_module() {
    let src = format!(
        "package p; function automatic int f(); return 100; endfunction endpackage
         module top; import p::*; if (1) begin : g {BLOCK_F} initial $display(f()); end endmodule"
    );
    check(
        at(&audit(&src), "f", 0),
        "Decl(top.g, Function)",
        Some("g.f"),
        None,
    );
}

#[test]
fn a_wildcard_import_answers_only_for_a_name_its_package_declares() {
    let src = "package p; function automatic int f(); return 100; endfunction endpackage
      module top; import p::*; initial begin $display(f()); $display(q()); end endmodule";
    let l = audit(src);
    assert_eq!(at(&l, "f", 0).outcome, Outcome::None(Hide::Import));
    check(at(&l, "f", 0), "none", None, None);
    check(at(&l, "q", 0), "Upward", None, None);
}

#[test]
fn a_name_in_an_exported_package_is_visible_through_the_exporter() {
    // §26.6.
    let src = "package a; function automatic int f(); return 1; endfunction endpackage
      package b; import a::*; export a::f; endpackage
      module top; import b::*; initial $display(f()); endmodule";
    assert_eq!(at(&audit(src), "f", 0).outcome, Outcome::None(Hide::Import));
}

#[test]
fn a_compilation_unit_name_is_not_upward() {
    // §3.12.1.
    let src = "function automatic int f(); return 1; endfunction
      int v;
      module top; initial $display(f(), v); endmodule";
    let l = audit(src);
    assert_eq!(at(&l, "f", 0).outcome, Outcome::None(Hide::Import));
    assert_eq!(at(&l, "v", 0).outcome, Outcome::None(Hide::Import));
}

#[test]
fn a_rooted_or_scoped_name_takes_no_lexical_lookup() {
    let src = "package p; int x; endpackage
      module top; int y; initial $display($root.top.y, p::x); endmodule";
    let l = audit(src);
    for m in &l {
        assert_eq!(m.outcome, Outcome::None(Hide::Qualified), "{m:?}");
    }
    assert_eq!(l.len(), 2, "{l:#?}");
}

#[test]
fn a_name_nothing_declares_binds_upward() {
    // §23.8.1.
    let src = "module c; initial $display(f()); endmodule
      module top; function automatic int f(); return 1; endfunction c u(); endmodule";
    check(at(&audit(src), "f", 0), "Upward", None, None);
}

#[test]
fn a_nested_module_finds_the_enclosing_modules_names_upward() {
    let src = "module top; int x; module inner; initial x = 1; endmodule inner u(); endmodule";
    check(at(&audit(src), "x", 0), "Upward", None, None);
}

#[test]
fn same_named_nested_modules_in_two_parents_keep_their_own_trees() {
    // §23.4.
    let src = "module a; module inner; int x; initial x = 1; endmodule inner u(); endmodule
      module b; module inner; int y; initial y = 1; endmodule inner u(); endmodule";
    let l = audit(src);
    check(at(&l, "x", 0), "Decl(a.inner, Data)", None, None);
    check(at(&l, "y", 0), "Decl(b.inner, Data)", None, None);

    let parsed = xezim_core::parse(src);
    let mut descs = parsed.source.descriptions;
    build_design(&mut descs);
    let of = |d: &str| tree_of(d).unwrap_or_else(|| panic!("no tree of {d}"));
    assert!(of("a.inner").decls.iter().any(|d| d.name == "x"));
    assert!(of("b.inner").decls.iter().any(|d| d.name == "y"));
    assert!(tree_of("inner").is_none());
}

#[test]
fn a_checker_in_a_generate_block_is_keyed_by_the_block() {
    // §17.2.
    let src = "module top;
      if (1) begin : g checker ck; int x; initial x = 1; endchecker end
      if (1) begin : h checker ck; int y; initial y = 1; endchecker end
    endmodule";
    let l = audit(src);
    check(at(&l, "x", 0), "Decl(top.g.ck, Data)", None, None);
    check(at(&l, "y", 0), "Decl(top.h.ck, Data)", None, None);
}

#[test]
fn a_subroutine_of_a_block_in_a_nested_module_is_renamed_like_any_other() {
    let src = format!(
        "module top; module inner; if (1) begin : a {BLOCK_F} initial $display(f()); end endmodule inner u(); endmodule"
    );
    check(
        at(&audit(&src), "f", 0),
        "Decl(top.inner.a, Function)",
        Some("a.f"),
        None,
    );
}

#[test]
fn a_scope_randomization_has_no_class_to_search_first() {
    // §18.12: `f` names the block's function though a class has a member `f`.
    let src = format!(
        "module top; if (1) begin : g {BLOCK_F}
           class C; int f; endclass
           initial begin int v, ok; ok = std::randomize(v) with {{ v == f(); }}; end
         end endmodule"
    );
    check(
        at(&audit(&src), "f", 0),
        "Decl(top.g, Function)",
        Some("g.f"),
        None,
    );
}

#[test]
fn a_path_through_the_outer_block_binds_at_its_head_and_the_rename_takes_it_for_the_inner_function()
{
    // The rename's dotted key `g.f` is the inner block's: not a hiding case.
    // §23.6: `g.f` names the outer function from the inner block.
    let src = "module top; if (1) begin : g
        function automatic int f(); return 1; endfunction
        if (1) begin : h
          function automatic int f(); return g.f(); endfunction
        end
      end endmodule";
    check(
        at(&audit(src), "g", 0),
        "Decl(top, Label)",
        Some("g.h.f"),
        Some(Disagree::Other),
    );
}

#[test]
fn a_local_data_type_and_a_shallow_copy_are_positions_the_rename_misses() {
    let src = "module top; if (1) begin : g
        localparam W = 2; class C; endclass C o;
        initial begin logic [W:0] v; C n; n = new o; end
      end endmodule";
    let l = audit(src);
    check(
        at(&l, "W", 0),
        "Decl(top.g, Param)",
        None,
        Some(Disagree::Unvisited),
    );
    assert_eq!(at(&l, "W", 0).pos, "local-dim");
    check(
        at(&l, "o", 0),
        "Decl(top.g, Data)",
        None,
        Some(Disagree::Unvisited),
    );
    assert_eq!(at(&l, "o", 0).pos, "shallow-copy");
}

#[test]
fn parameter_values_dimensions_and_generate_conditions_bind_in_the_enclosing_scope() {
    let src = "module c #(parameter W = 1); endmodule
      module top; parameter N = 2; localparam M = N + 1;
      logic [N-1:0] v [M];
      if (N) begin : g localparam L = N; c #(.W(L)) u(); end
      for (genvar i = 0; i < N; i++) begin : l logic [N:0] w; end
    endmodule";
    let l = audit(src);
    assert_eq!(l.iter().filter(|m| m.name == "N").count(), 6);
    for m in l.iter().filter(|m| m.name == "N") {
        check(m, "Decl(top, Param)", None, None);
    }
    check(at(&l, "M", 0), "Decl(top, Param)", None, None);
    check(at(&l, "L", 0), "Decl(top.g, Param)", Some("g.L"), None);
}

#[test]
fn header_parameters_and_ports_bind_in_the_definition() {
    let src = "module top #(parameter A = 1, parameter B = A) (input logic [A:0] p); endmodule";
    let l = audit(src);
    check(at(&l, "A", 0), "Decl(top, Param)", None, None);
    check(at(&l, "A", 1), "Decl(top, Param)", None, None);
}

// Hiding: a subroutine name an inner scope hides keeps its spelling. Group A:
// the rename still rewrites hidden data.

#[test]
fn a_block_local_hides_a_block_function_of_the_same_name() {
    let src = format!(
        "module top; if (1) begin : g {BLOCK_F}
           initial begin int f = 7; $display(f); end end endmodule"
    );
    let l = at_outcome(&src, "f");
    assert_eq!(l.outcome, Outcome::None(Hide::Local));
    check(&l, "none", None, None);
}

#[test]
fn a_local_hides_only_from_its_declaration() {
    // §6.5: the initializer of `a` sees the block's function.
    let src = format!(
        "module top; if (1) begin : g {BLOCK_F}
           initial begin int a = f(); int f = 7; $display(a, f); end end endmodule"
    );
    let l = audit(&src);
    check(at(&l, "f", 0), "Decl(top.g, Function)", Some("g.f"), None);
    assert_eq!(at(&l, "f", 1).outcome, Outcome::None(Hide::Local));
    assert_eq!(at(&l, "f", 1).renamed, None);
    assert_eq!(at(&l, "f", 1).disagree, None);
}

#[test]
fn a_block_local_hides_block_data_of_the_same_name() {
    let src = "module top; if (1) begin : g int x = 5;
        initial begin int x = 7; $display(x); end end endmodule";
    let l = at_outcome(src, "x");
    assert_eq!(l.outcome, Outcome::None(Hide::Local));
    check(&l, "none", Some("g.x"), Some(Disagree::Hiding));
}

#[test]
fn a_local_enum_label_hides_a_block_function() {
    let src = format!(
        "module top; if (1) begin : g {BLOCK_F}
           initial begin enum {{f = 9}} e; $display(f); end end endmodule"
    );
    let l = at_outcome(&src, "f");
    assert_eq!(l.outcome, Outcome::None(Hide::Type));
    check(&l, "none", None, None);
}

#[test]
fn an_enum_label_of_an_inner_block_hides_a_block_function() {
    let src = format!(
        "module top; if (1) begin : g {BLOCK_F}
           if (1) begin : h typedef enum {{f = 9}} e_t; initial $display(f); end
         end endmodule"
    );
    check(
        at(&audit(&src), "f", 0),
        "Decl(top.g.h, EnumMember)",
        None,
        None,
    );
}

#[test]
fn an_enum_label_inside_a_struct_is_a_name_of_the_block() {
    // §6.19.
    let src = "module top; if (1) begin : g
        struct { enum { A, B } e; } s;
        initial $display(A);
      end endmodule";
    check(
        at(&audit(src), "A", 0),
        "Decl(top.g, EnumMember)",
        None,
        None,
    );
}

#[test]
fn an_explicit_import_in_an_inner_block_hides_a_block_function() {
    let src = format!(
        "package p; function automatic int f(); return 100; endfunction endpackage
         module top; if (1) begin : g {BLOCK_F}
           if (1) begin : h import p::f; initial $display(f()); end
         end endmodule"
    );
    let l = at_outcome(&src, "f");
    assert_eq!(l.outcome, Outcome::None(Hide::Import));
    check(&l, "none", None, None);
}

#[test]
fn a_wildcard_import_in_an_inner_block_comes_before_the_outer_block() {
    // §26.3.
    let src = format!(
        "package p; function automatic int f(); return 100; endfunction endpackage
         module top; if (1) begin : g {BLOCK_F}
           if (1) begin : h import p::*; initial $display(f()); end
         end endmodule"
    );
    let l = at_outcome(&src, "f");
    assert_eq!(l.outcome, Outcome::None(Hide::Import));
    check(&l, "none", None, None);
}

#[test]
fn an_inner_clocking_block_hides_a_block_function() {
    let src = format!(
        "module top; logic clk; if (1) begin : g {BLOCK_F}
           if (1) begin : h
             clocking f @(posedge clk); endclocking
             initial @(f) $display(1);
           end
         end endmodule"
    );
    let l = audit(&src);
    let m = l
        .iter()
        .find(|m| m.name == "f" && m.pos == "process")
        .expect("the event");
    check(m, "Decl(top.g.h, Clocking)", None, None);
}

#[test]
fn a_named_block_hides_a_block_task_for_a_disable_inside_it() {
    // §9.3.5, §9.6.2.
    let src = "module top; if (1) begin : g
        task automatic t(); endtask
        initial begin begin : t #1 disable t; end end
      end endmodule";
    let l = at_outcome(src, "t");
    assert_eq!(l.outcome, Outcome::None(Hide::Label));
    check(&l, "none", None, None);
}

#[test]
fn a_class_member_wins_over_a_block_function_in_a_randomize_with() {
    // §18.7.
    let src = format!(
        "module top; if (1) begin : g {BLOCK_F}
           class C; rand int x; function int f(); return 9; endfunction endclass
           C c = new;
           initial begin int ok; ok = c.randomize() with {{ x == f(); }}; end
         end endmodule"
    );
    let l = at_outcome(&src, "f");
    assert_eq!(l.outcome, Outcome::None(Hide::Member));
    check(&l, "none", None, None);
}

#[test]
fn a_name_no_class_declares_binds_lexically_in_a_randomize_with() {
    let src = format!(
        "module top; if (1) begin : g {BLOCK_F}
           class C; rand int x; endclass
           C c = new;
           initial begin int ok; ok = c.randomize() with {{ x == f(); }}; end
         end endmodule"
    );
    let l = audit(&src);
    check(at(&l, "f", 0), "Decl(top.g, Function)", Some("g.f"), None);
    assert_eq!(at(&l, "x", 0).outcome, Outcome::None(Hide::Member));
}

#[test]
fn a_with_clause_filter_hides_only_its_iterators() {
    // §7.12.
    let src = "module top; if (1) begin : g int item; int q[$]; int z[$]; int k;
        initial begin z = q.find(k) with (k > item); z = q.find with (item > 0); end
      end endmodule";
    let l = audit(src);
    assert_eq!(at(&l, "k", 0).outcome, Outcome::None(Hide::Iterator));
    assert_eq!(at(&l, "item", 0).outcome, Outcome::None(Hide::Iterator));
    assert_eq!(at(&l, "q", 0).binding, "Decl(top.g, Data)");
}

#[test]
fn a_matches_variable_hides_in_the_true_branch_only() {
    // §12.6.2.
    let src = "module top; typedef union tagged { int a; } u_t;
      if (1) begin : g int v; u_t s;
        initial if (s matches tagged a .v) $display(v); else $display(v);
      end endmodule";
    let l = audit(src);
    assert_eq!(at(&l, "v", 0).outcome, Outcome::None(Hide::Pattern));
    check(at(&l, "v", 1), "Decl(top.g, Data)", Some("g.v"), None);
}

// Classes.

#[test]
fn a_class_member_wins_over_a_block_function() {
    // §8.
    let src = format!(
        "module top; if (1) begin : g {BLOCK_F}
           class C;
             function int f(); return 1; endfunction
             function int m(); return f(); endfunction
           endclass
         end endmodule"
    );
    let l = at_outcome(&src, "f");
    assert_eq!(l.outcome, Outcome::None(Hide::Member));
    check(&l, "none", None, None);
}

#[test]
fn a_class_enum_label_hides_a_block_function() {
    let src = format!(
        "module top; if (1) begin : g {BLOCK_F}
           class C; typedef enum {{ f = 9 }} e_t;
             function int m(); return f; endfunction
           endclass
         end endmodule"
    );
    let l = at_outcome(&src, "f");
    assert_eq!(l.outcome, Outcome::None(Hide::Member));
}

#[test]
fn an_inherited_member_hides_a_block_function() {
    // §8.13.
    let src = format!(
        "class B; function int f(); return 1; endfunction endclass
         module top; if (1) begin : g {BLOCK_F}
           class C extends B; function int m(); return f(); endfunction endclass
         end endmodule"
    );
    assert_eq!(at_outcome(&src, "f").outcome, Outcome::None(Hide::Member));
}

#[test]
fn a_type_parameter_base_leaves_only_a_name_some_class_declares_unbound() {
    // §8.25: `T` may declare anything some class declares.
    let src = format!(
        "class B; function int f(); return 1; endfunction endclass
         module top; if (1) begin : g {BLOCK_F}
           function automatic int h(); return 2; endfunction
           class C #(type T = B) extends T;
             function int m(); return f() + h(); endfunction
           endclass
         end endmodule"
    );
    let l = audit(&src);
    assert_eq!(at(&l, "f", 0).outcome, Outcome::None(Hide::Member));
    check(at(&l, "h", 0), "Decl(top.g, Function)", Some("g.h"), None);
}

#[test]
fn an_out_of_block_method_sees_its_class_before_the_block() {
    // §8.24.
    let src = format!(
        "module top; {BLOCK_F}
           class C; int f; extern function int m(); endclass
           function int C::m(); return f; endfunction
         endmodule"
    );
    let l = audit(&src);
    let m = l
        .iter()
        .find(|m| m.name == "f" && m.pos == "class")
        .expect("the read");
    assert_eq!(m.outcome, Outcome::None(Hide::Member));
}

#[test]
fn a_constraint_binds_class_members_first_and_then_the_block() {
    // §18.5.
    let src = format!(
        "module top; if (1) begin : g {BLOCK_F} int lim;
           class C; rand int x; constraint c {{ x < lim; x > f(); }} endclass
         end endmodule"
    );
    let l = audit(&src);
    assert_eq!(at(&l, "x", 0).outcome, Outcome::None(Hide::Member));
    check(
        at(&l, "lim", 0),
        "Decl(top.g, Data)",
        None,
        Some(Disagree::Unvisited),
    );
    check(at(&l, "f", 0), "Decl(top.g, Function)", Some("g.f"), None);
}

// §23.9: positions the rename reaches for subroutine names only.

fn expect_renamed(body: &str, pos: &str) {
    let src = format!(
        "module top; wire a, b; logic clk; if (1) begin : g {BLOCK_F} {body} end endmodule"
    );
    let l = audit(&src);
    let m = l
        .iter()
        .find(|m| m.name == "f" && m.pos == pos)
        .unwrap_or_else(|| panic!("no {pos} mention in {l:#?}"));
    check(m, "Decl(top.g, Function)", Some("g.f"), None);
}

#[test]
fn a_call_in_a_class_body_is_renamed_to_the_block_function() {
    expect_renamed(
        "class C; function int m(); return f(); endfunction endclass",
        "class",
    );
}

#[test]
fn a_call_in_a_final_block_is_renamed_to_the_block_function() {
    expect_renamed("final $display(f());", "final");
}

#[test]
fn a_gate_terminal_is_renamed_to_the_block_function() {
    expect_renamed("buf u(a, f());", "gate");
}

#[test]
fn a_named_property_is_renamed_to_the_block_function() {
    expect_renamed(
        "property p; @(posedge clk) f() == 5; endproperty",
        "property",
    );
}

#[test]
fn a_named_sequence_is_renamed_to_the_block_function() {
    expect_renamed(
        "sequence s; @(posedge clk) f() == 5; endsequence",
        "sequence",
    );
}

#[test]
fn a_let_body_is_renamed_to_the_block_function() {
    expect_renamed("let l(x) = f() + x;", "let");
}

#[test]
fn a_covergroup_is_renamed_to_the_block_function() {
    expect_renamed(
        "covergroup cg @(posedge clk); coverpoint f(); endgroup",
        "covergroup",
    );
}

#[test]
fn a_clocking_signal_expression_is_renamed_to_the_block_function() {
    expect_renamed(
        "clocking cb @(posedge clk); input i = f(); endclocking",
        "clocking",
    );
}

#[test]
fn a_method_default_a_property_initializer_and_a_nested_class_are_renamed() {
    // §8.8, §8.23, §13.5.3.
    let src = format!(
        "module top; if (1) begin : g {BLOCK_F}
           class C; int v = f(); task t(int a = f()); endtask
             class I; function int m(); return f(); endfunction endclass
           endclass
         end endmodule"
    );
    let l = audit(&src);
    for n in 0..3 {
        check(at(&l, "f", n), "Decl(top.g, Function)", Some("g.f"), None);
    }
}

#[test]
fn a_class_in_a_nested_block_is_renamed_to_the_nearest_function() {
    // §23.9.
    let src = format!(
        "module top; if (1) begin : g {BLOCK_F}
           if (1) begin : h {BLOCK_F}
             class C; function int m(); return f(); endfunction endclass
           end
         end endmodule"
    );
    check(
        at(&audit(&src), "f", 0),
        "Decl(top.g.h, Function)",
        Some("g.h.f"),
        None,
    );
}

#[test]
fn a_member_a_local_and_a_formal_of_a_class_keep_the_name_of_a_block_function() {
    // §8.3, §13.5, §6.21.
    let src = format!(
        "module top; if (1) begin : g {BLOCK_F}
           class M; int f; function int m(); return f; endfunction endclass
           class L; function int m(); int f = 1; return f; endfunction endclass
           class P; function int m(int f); return f; endfunction endclass
         end endmodule"
    );
    let l = audit(&src);
    for n in 0..3 {
        let m = at(&l, "f", n);
        assert_eq!(m.renamed, None, "{m:?}");
        assert_eq!(m.disagree, None, "{m:?}");
    }
}

#[test]
fn a_formal_of_a_property_a_sequence_and_a_let_keeps_the_name_of_a_block_function() {
    // §16.8, §16.12, §11.13.
    let src = format!(
        "module top; logic clk; if (1) begin : g {BLOCK_F}
           property p(f); @(posedge clk) f; endproperty
           sequence s(f); @(posedge clk) f; endsequence
           let l(f) = f + 1;
         end endmodule"
    );
    let l = audit(&src);
    for n in 0..3 {
        let m = at(&l, "f", n);
        assert_eq!(m.renamed, None, "{m:?}");
        assert_eq!(m.disagree, None, "{m:?}");
    }
}

#[test]
fn block_data_read_from_a_final_block_or_a_class_stays_in_group_b() {
    // §23.9: the bare name is what the rename leaves at these positions.
    let src = "module top; if (1) begin : g int v;
        function automatic int f(); return v; endfunction
        final $display(v);
        class C; function int m(); return v; endfunction endclass
      end endmodule";
    let l = audit(src);
    for (n, pos) in [(1, "final"), (2, "class")] {
        let m = at(&l, "v", n);
        assert_eq!(m.pos, pos);
        check(m, "Decl(top.g, Data)", None, Some(Disagree::Unvisited));
    }
}

#[test]
fn a_clocking_event_binds_to_the_block_data_the_rename_misses() {
    let src = "module top; logic k; if (1) begin : g logic c; int v;
        clocking cb @(posedge c); input v; endclocking
      end endmodule";
    let l = audit(src);
    let m = l.iter().find(|m| m.name == "c").expect("the clock");
    assert_eq!(m.pos, "clocking");
    check(m, "Decl(top.g, Data)", None, Some(Disagree::Unvisited));
}

#[test]
fn a_dpi_export_binds_to_the_block_function_the_rename_misses() {
    let src = format!(
        "module top; if (1) begin : g {BLOCK_F} export \"DPI-C\" function f; end endmodule"
    );
    let l = at_outcome(&src, "f");
    check(&l, "Decl(top.g, Function)", None, Some(Disagree::Unvisited));
}

// `disable`.

#[test]
fn a_disable_inside_the_block_binds_to_its_task() {
    let src = "module top; if (1) begin : g
        task automatic t(); endtask
        initial disable t;
      end endmodule";
    check(
        at(&audit(src), "t", 0),
        "Decl(top.g, Task)",
        Some("g.t"),
        None,
    );
}

#[test]
fn a_disable_by_path_names_the_block_task_by_its_key() {
    // §9.6.2, §23.9.
    let src = "module top; if (1) begin : g task automatic t(); endtask end
      initial disable g.t; endmodule";
    check(at(&audit(src), "g.t", 0), "Decl(top.g, Task)", None, None);
}

#[test]
fn a_disable_by_path_from_inside_a_block_names_the_key_from_the_definition() {
    // §9.6.2, §23.9: `h.t` from `g` is `g.h.t`.
    let src = "module top; if (1) begin : g
        if (1) begin : h task automatic t(); endtask end
        initial disable h.t;
      end endmodule";
    check(at(&audit(src), "g.h.t", 0), "Decl(top.g.h, Task)", None, None);
}

#[test]
fn a_disable_by_path_into_a_loop_block_takes_the_literal_index() {
    // §9.6.2, §27.4.
    let src = "module top; for (genvar i = 0; i < 2; i++) begin : g
        task automatic t(); endtask
      end
      initial disable g[1].t; endmodule";
    check(at(&audit(src), "g[1].t", 0), "Decl(top.g[@], Task)", None, None);
}

#[test]
fn a_disable_of_a_block_by_path_keeps_its_path() {
    // §9.6.2: a named block, not a task.
    let src = "module top; initial begin : b #1; end
      if (1) begin : g initial begin : c #1; end end
      initial begin disable b; disable g.c; disable u.t; end endmodule";
    let parsed = xezim_core::parse(src);
    let mut descs = parsed.source.descriptions;
    build_design(&mut descs);
    let Description::Module(m) = &descs[0] else {
        panic!("a module")
    };
    let ModuleItem::InitialConstruct(ic) = &m.items[2] else {
        panic!("the process")
    };
    let StatementKind::SeqBlock { stmts, .. } = &ic.stmt.kind else {
        panic!("the block")
    };
    let paths: Vec<(Vec<&str>, Bound)> = stmts
        .iter()
        .map(|s| match &s.kind {
            StatementKind::Disable(h) => (
                h.path.iter().map(|p| p.name.name.as_str()).collect(),
                h.bound,
            ),
            k => panic!("{k:?}"),
        })
        .collect();
    assert_eq!(
        paths,
        [
            (vec!["b"], Bound::NO_TARGET),
            (vec!["g", "c"], Bound::NO_TARGET),
            (vec!["u", "t"], Bound::NO_TARGET),
        ]
    );
}

// The field.

#[test]
fn the_binding_is_written_on_the_identifier_of_the_ast() {
    let src = format!(
        "module top; if (1) begin : g {BLOCK_F} initial f(); end initial begin int f; f = 1; end endmodule"
    );
    let parsed = xezim_core::parse(&src);
    let mut descs = parsed.source.descriptions;
    build_design(&mut descs);
    let Description::Module(m) = &descs[0] else {
        panic!("a module")
    };
    let ModuleItem::GenerateIf(gi) = &m.items[0] else {
        panic!("the generate block")
    };
    let ModuleItem::InitialConstruct(ic) = &gi.branches[0].1[1] else {
        panic!("the process")
    };
    let StatementKind::Expr(e) = &ic.stmt.kind else {
        panic!("the enable: {:?}", ic.stmt.kind)
    };
    let h = match &e.kind {
        ExprKind::Ident(h) => h,
        ExprKind::Call { func, .. } => match &func.kind {
            ExprKind::Ident(h) => h,
            k => panic!("{k:?}"),
        },
        k => panic!("{k:?}"),
    };
    let t = tree_of("top").expect("the tree of top");
    let d = h.bound.as_decl().expect("a declaration");
    let decl = &t.decls[d.0 as usize];
    assert_eq!(decl.kind, DeclKind::Function);
    assert_eq!(t.path(decl.scope), "g");
}

#[test]
fn the_encoding_separates_not_analysed_no_target_upward_and_a_declaration() {
    assert_eq!(Bound::default(), Bound::UNSET);
    assert!(Bound::UNSET.is_unset() && Bound::UNSET.as_decl().is_none());
    assert!(!Bound::NO_TARGET.is_unset() && Bound::NO_TARGET.as_decl().is_none());
    assert!(Bound::UPWARD.is_upward() && Bound::UPWARD.as_decl().is_none());
    let d = Bound::decl(xezim_core::ast::binding::DeclId(0));
    assert_eq!(d.as_decl().map(|d| d.0), Some(0));
    assert!(!d.is_unset() && !d.is_upward());
}

#[test]
fn a_hidden_name_is_analysed_and_has_no_target() {
    let src = "module top; int x; initial begin int x; x = 1; end endmodule";
    let parsed = xezim_core::parse(src);
    let mut descs = parsed.source.descriptions;
    build_design(&mut descs);
    let Description::Module(m) = &descs[0] else {
        panic!("a module")
    };
    let ModuleItem::InitialConstruct(ic) = &m.items[1] else {
        panic!("the process")
    };
    let StatementKind::SeqBlock { stmts, .. } = &ic.stmt.kind else {
        panic!("the block")
    };
    let StatementKind::BlockingAssign { lvalue, .. } = &stmts[1].kind else {
        panic!("the assignment")
    };
    let ExprKind::Ident(h) = &lvalue.kind else {
        panic!("the name")
    };
    assert_eq!(h.bound, Bound::NO_TARGET);
}

#[test]
fn a_named_block_under_an_unnamed_fork_is_a_name_of_the_enclosing_block() {
    // §9.3.4.
    let src = "module top; if (1) begin : g
        task automatic t(); endtask
        initial begin : outer
          fork begin : t #5 $display(1); end join_none
          #1 disable t;
        end
      end endmodule";
    let l = at_outcome(src, "t");
    assert_eq!(l.outcome, Outcome::None(Hide::Label));
    check(&l, "none", None, None);
}

#[test]
fn a_named_block_under_an_unnamed_begin_is_a_name_of_the_enclosing_block() {
    // §9.3.4.
    let src = "module top; if (1) begin : g
        task automatic t(); endtask
        initial begin : outer
          begin begin : t #5 $display(1); end end
          disable t;
        end
      end endmodule";
    let l = at_outcome(src, "t");
    assert_eq!(l.outcome, Outcome::None(Hide::Label));
    check(&l, "none", None, None);
}

#[test]
fn an_unnamed_block_with_a_declaration_keeps_its_labels_to_itself() {
    // §9.3.4: this unnamed block opens a scope.
    let src = "module top; if (1) begin : g
        task automatic t(); endtask
        initial begin : outer
          begin int v; begin : t #5 v = 1; end end
          disable t;
        end
      end endmodule";
    check(
        at(&audit(src), "t", 0),
        "Decl(top.g, Task)",
        Some("g.t"),
        None,
    );
}

#[test]
fn a_named_block_under_a_process_level_unnamed_begin_is_a_path_head_of_the_module() {
    // §9.3.4.
    let src = "module top;
        initial begin begin : b int x; end end
        initial $display(b.x);
      endmodule";
    check(at(&audit(src), "b", 0), "Decl(top, Label)", None, None);
}

#[test]
fn a_built_in_type_as_a_class_type_argument_is_not_a_name() {
    let src = "class K #(type T = int); T v; endclass
      module top; K #(int) k; endmodule";
    let l = audit(src);
    assert!(l.iter().all(|m| m.binding != "Upward"), "{l:#?}");
}

#[test]
fn a_definition_adopted_from_a_library_is_bound_with_its_own_tree() {
    let dir = std::env::temp_dir().join(format!("xezim_bind_lib_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("a temp dir");
    let lib = dir.join("c.sv");
    std::fs::write(
        &lib,
        "module c; if (1) begin : g int x; initial x = 1; end endmodule\n",
    )
    .expect("the library file");
    xezim_core::set_library_cli(xezim_core::LibraryCli {
        lib_files: vec![lib.display().to_string()],
        ..Default::default()
    });
    let result = xezim_core::parse_and_elaborate_multi(
        &["module top; c u(); endmodule".to_string()],
        Some("top"),
        &[],
        &["t.sv".to_string()],
        &[],
    );
    xezim_core::set_library_cli(Default::default());
    std::fs::remove_dir_all(&dir).expect("removing the temp dir");
    let (defs, _) = result.unwrap_or_else(|e| panic!("{e}"));
    let t = tree_of("c").expect("the tree of the adopted definition");
    let Some(xezim_core::SourceDefinition::Module(m)) = defs.get("c") else {
        panic!("the adopted definition")
    };
    let ModuleItem::GenerateIf(gi) = &m.items[0] else {
        panic!("the generate block")
    };
    let ModuleItem::InitialConstruct(ic) = &gi.branches[0].1[1] else {
        panic!("the process")
    };
    let StatementKind::BlockingAssign { lvalue, .. } = &ic.stmt.kind else {
        panic!("the assignment")
    };
    let ExprKind::Ident(h) = &lvalue.kind else {
        panic!("the name")
    };
    let d = h.bound.as_decl().expect("a declaration");
    assert_eq!(t.decls[d.0 as usize].name, "x");
    assert_eq!(t.path(t.decls[d.0 as usize].scope), "g");
}

#[test]
fn a_hidden_mention_reports_the_subroutine_it_hides_as_its_target() {
    let src = format!(
        "module top; if (1) begin : g {BLOCK_F}
           initial begin int f = 7; $display(f); end end endmodule"
    );
    assert_eq!(at_outcome(&src, "f").target, Some(DeclKind::Function));
}

#[test]
fn a_mention_reports_the_innermost_declaration_as_its_target() {
    let src = format!(
        "module top; if (1) begin : g {BLOCK_F}
           if (1) begin : h typedef enum {{f = 9}} e_t; initial $display(f); end
         end endmodule"
    );
    assert_eq!(at_outcome(&src, "f").target, Some(DeclKind::EnumMember));
}

#[test]
fn a_name_the_tree_does_not_declare_has_no_target() {
    let src = "module top; initial begin int x = 7; $display(x); end endmodule";
    assert_eq!(at_outcome(src, "x").target, None);
}

#[test]
fn a_local_hides_the_innermost_of_two_block_functions_and_keeps_its_spelling() {
    // §23.9, §6.21.
    let src = format!(
        "module top; if (1) begin : g {BLOCK_F}
           if (1) begin : h {BLOCK_F}
             initial begin int f = 7; $display(f); end
             initial $display(f());
           end
         end endmodule"
    );
    let l = audit(&src);
    let f: Vec<_> = l.iter().filter(|m| m.name == "f").collect();
    check(f[0], "none", None, None);
    check(f[1], "Decl(top.g.h, Function)", Some("g.h.f"), None);
}

#[test]
fn nested_block_data_named_like_an_outer_block_function_is_renamed() {
    // §23.9: `f` in `h` binds to `h`'s data.
    let src = format!(
        "module top; if (1) begin : g {BLOCK_F}
           if (1) begin : h int f = 3; initial $display(f); end
         end endmodule"
    );
    check(
        at(&audit(&src), "f", 0),
        "Decl(top.g.h, Data)",
        Some("g.h.f"),
        None,
    );
}

#[test]
fn a_unit_scoped_call_in_a_block_that_declares_the_name_is_not_renamed() {
    // §3.12.1.
    let src = format!(
        "function automatic int f(); return 42; endfunction
         module top; if (1) begin : g {BLOCK_F}
           initial $display($unit::f());
         end endmodule"
    );
    let l = audit(&src);
    let m = l.iter().find(|m| m.name.ends_with("f")).expect("the call");
    check(m, "none", None, None);
}

#[test]
fn a_subroutine_declaration_carries_the_id_its_references_bind_to() {
    let parsed = xezim_core::parse(
        "module top; if (1) begin : g
           function automatic int f(); return 5; endfunction
           task automatic t(); endtask
           initial f();
         end endmodule",
    );
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
    let mut descs = parsed.source.descriptions;
    build_design(&mut descs);
    let Description::Module(m) = &descs[0] else {
        panic!("a module")
    };
    let ModuleItem::GenerateIf(gi) = &m.items[0] else {
        panic!("the generate block")
    };
    let items = &gi.branches[0].1;
    let ModuleItem::FunctionDeclaration(f) = &items[0] else {
        panic!("the function")
    };
    let ModuleItem::TaskDeclaration(t) = &items[1] else {
        panic!("the task")
    };
    let ModuleItem::InitialConstruct(ic) = &items[2] else {
        panic!("the process")
    };
    let StatementKind::Expr(e) = &ic.stmt.kind else {
        panic!("the enable: {:?}", ic.stmt.kind)
    };
    let ExprKind::Call { func, .. } = &e.kind else {
        panic!("the call: {:?}", e.kind)
    };
    let ExprKind::Ident(h) = &func.kind else {
        panic!("the callee: {:?}", func.kind)
    };
    assert_eq!(h.bound, f.decl);
    let tree = tree_of("top").expect("the tree of top");
    let kind = |b: Bound| tree.decls[b.as_decl().expect("a stamp").0 as usize].kind;
    assert_eq!(kind(f.decl), DeclKind::Function);
    assert_eq!(kind(t.decl), DeclKind::Task);
}

const OTHER_F: &str = "class Other; function int f(); return 1; endfunction endclass";

#[test]
fn a_known_receiver_without_the_name_leaves_it_to_the_block() {
    // §18.7.
    let src = format!(
        "{OTHER_F} class R; rand int x; endclass
         module top; if (1) begin : g {BLOCK_F}
           initial begin R r = new; void'(r.randomize() with {{ x == f(); }}); end
         end endmodule"
    );
    check(
        at(&audit(&src), "f", 0),
        "Decl(top.g, Function)",
        Some("g.f"),
        None,
    );
}

#[test]
fn a_block_level_handle_declared_after_its_use_is_a_known_receiver() {
    // §18.7, §23.9.
    let src = format!(
        "{OTHER_F} class R; rand int x; endclass
         module top; if (1) begin : g {BLOCK_F}
           initial void'(r.randomize() with {{ x == f(); }});
           R r = new;
         end endmodule"
    );
    check(
        at(&audit(&src), "f", 0),
        "Decl(top.g, Function)",
        Some("g.f"),
        None,
    );
}

#[test]
fn a_formal_handle_is_a_known_receiver() {
    // §18.7, §13.5.
    let src = format!(
        "{OTHER_F} class R; rand int x; endclass
         module top; if (1) begin : g {BLOCK_F}
           task automatic t(R r); void'(r.randomize() with {{ x == f(); }}); endtask
         end endmodule"
    );
    check(
        at(&audit(&src), "f", 0),
        "Decl(top.g, Function)",
        Some("g.f"),
        None,
    );
}

#[test]
fn a_member_of_a_known_receivers_class_wins_over_the_block() {
    // §18.7.
    let src = format!(
        "class R; rand int x; function int f(); return 9; endfunction endclass
         module top; if (1) begin : g {BLOCK_F}
           initial begin R r = new; void'(r.randomize() with {{ x == f(); }}); end
         end endmodule"
    );
    let l = at_outcome(&src, "f");
    assert_eq!(l.outcome, Outcome::None(Hide::Member));
    check(&l, "none", None, None);
}

#[test]
fn a_member_inherited_through_a_package_qualified_base_wins_over_the_block() {
    // §18.7, §8.13.
    let src = format!(
        "package pk; class B; function int f(); return 9; endfunction endclass endpackage
         class R extends pk::B; rand int x; endclass
         module top; if (1) begin : g {BLOCK_F}
           initial begin R r = new; void'(r.randomize() with {{ x == f(); }}); end
         end endmodule"
    );
    let l = at_outcome(&src, "f");
    assert_eq!(l.outcome, Outcome::None(Hide::Member));
    check(&l, "none", None, None);
}

#[test]
fn a_known_receiver_with_an_unknown_base_leaves_the_name_to_a_member() {
    // §18.7, §8.13: the base may declare it.
    let src = format!(
        "{OTHER_F} class R extends Missing; rand int x; endclass
         module top; if (1) begin : g {BLOCK_F}
           initial begin R r = new; void'(r.randomize() with {{ x == f(); }}); end
         end endmodule"
    );
    let l = at_outcome(&src, "f");
    assert_eq!(l.outcome, Outcome::None(Hide::Member));
    check(&l, "none", None, None);
}

#[test]
fn a_member_handle_receiver_stays_unknown() {
    // §18.7: the handle's class is not looked up.
    let src = format!(
        "{OTHER_F} class R; rand int x; endclass class H; R r; endclass
         module top; if (1) begin : g {BLOCK_F}
           initial begin H h = new; void'(h.r.randomize() with {{ x == f(); }}); end
         end endmodule"
    );
    assert_eq!(at_outcome(&src, "f").outcome, Outcome::None(Hide::Member));
}

#[test]
fn std_randomize_searches_no_class() {
    // §18.12.
    let src = format!(
        "{OTHER_F}
         module top; if (1) begin : g {BLOCK_F}
           int x;
           initial void'(std::randomize(x) with {{ x == f(); }});
         end endmodule"
    );
    check(
        at(&audit(&src), "f", 0),
        "Decl(top.g, Function)",
        Some("g.f"),
        None,
    );
}

#[test]
fn nested_data_named_like_a_subroutine_of_an_unlabelled_block_follows_its_name() {
    // §23.9, §27.6.
    let src = format!(
        "module top; if (1) begin {BLOCK_F}
           if (1) begin : h int f = 3; initial $display(f); end
         end endmodule"
    );
    assert_eq!(
        at(&audit(&src), "f", 0).renamed.as_deref(),
        Some("genblk1.h.f")
    );
}
