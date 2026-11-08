//! Lexical binding: §23.9 innermost scope first, §26.3 imports, §8 and §13 hiding,
//! §23.8.1 upward. Each test asserts what a name binds to and the key the
//! generate rename gives it.

use xezim_core::ast::Description;
use xezim_core::ast::binding::{Bound, DeclKind};
use xezim_core::ast::decl::ModuleItem;
use xezim_core::ast::expr::ExprKind;
use xezim_core::ast::stmt::StatementKind;
use xezim_core::elaborate::bind::{AuditLine, Hide, Outcome, audit_design};
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

fn check(l: &AuditLine, binding: &str, renamed: Option<&str>) {
    assert_eq!(l.binding, binding, "{l:?}");
    assert_eq!(l.renamed.as_deref(), renamed, "{l:?}");
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
    check(at(&l, "f", 0), "Decl(top.g.h, Function)", Some("g.h.f"));
    check(at(&l, "f", 1), "Decl(top.g, Function)", Some("g.f"));
    check(at(&l, "f", 2), "Decl(top, Function)", None);
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
    );
}

#[test]
fn a_subroutine_of_an_unlabelled_block_is_named_by_its_implicit_scope() {
    let src = format!("module top; if (1) begin {BLOCK_F} initial $display(f()); end endmodule");
    check(
        at(&audit(&src), "f", 0),
        "Decl(top.genblk1, Function)",
        Some("genblk1.f"),
    );
}

#[test]
fn data_of_an_unlabelled_block_is_named_by_its_implicit_scope() {
    let src = "module top; if (1) begin int x; initial x = 1; end endmodule";
    check(
        at(&audit(src), "x", 0),
        "Decl(top.genblk1, Data)",
        Some("genblk1.x"),
    );
}

#[test]
fn data_of_a_labelled_block_inside_an_unlabelled_one_takes_both_scopes() {
    let src = "module top; if (1) begin if (1) begin : h int x; initial x = 1; end end endmodule";
    check(
        at(&audit(src), "x", 0),
        "Decl(top.genblk1.h, Data)",
        Some("genblk1.h.x"),
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
    );
}

#[test]
fn a_generate_loop_scope_is_indexed_and_its_variable_is_not_bound() {
    let src = "module top; for (genvar i = 0; i < 2; i++) begin : g
        int x; function int f(); return i; endfunction
        initial x = f();
      end endmodule";
    let l = audit(src);
    check(at(&l, "x", 0), "Decl(top.g[@], Data)", Some("g[@].x"));
    check(at(&l, "f", 0), "Decl(top.g[@], Function)", Some("g[@].f"));
    assert_eq!(at(&l, "i", 0).outcome, Outcome::None(Hide::Genvar));
}

#[test]
fn an_unlabelled_loop_renames_data_under_its_implicit_name() {
    let src =
        "module top; for (genvar i = 0; i < 2; i++) begin int x; initial x = 1; end endmodule";
    check(
        at(&audit(src), "x", 0),
        "Decl(top.genblk1[@], Data)",
        Some("genblk1[@].x"),
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
    check(at(&l, "x", 0), "Decl(top.a, Data)", Some("a.x"));
    check(at(&l, "x", 1), "Decl(top.b, Data)", Some("b.x"));
    check(at(&l, "P", 0), "Decl(top, Param)", None);
}

#[test]
fn a_block_label_binds_in_the_enclosing_scope_as_a_path_head() {
    let src =
        format!("module top; if (1) begin : g {BLOCK_F} end initial $display(g.f()); endmodule");
    check(at(&audit(&src), "g", 0), "Decl(top, Label)", None);
}

#[test]
fn an_instance_in_a_block_binds_as_a_path_head() {
    let src = "module c; int n; endmodule
      module top; if (1) begin : g c u(); initial u.n = 1; end endmodule";
    check(
        at(&audit(src), "u", 0),
        "Decl(top.g, Instance)",
        Some("g.u"),
    );
}

#[test]
fn a_gate_instance_is_a_name_the_rename_leaves_alone_and_a_type_takes_the_blocks_key() {
    // §6.18, §23.9.
    let src = "module top; wire a, b;
      if (1) begin : g
        typedef int t_t; t_t v;
        buf u(a, b);
        initial $display(u.n);
      end endmodule";
    let l = audit(src);
    check(at(&l, "t_t", 0), "Decl(top.g, Typedef)", Some("g.t_t"));
    check(at(&l, "u", 0), "Decl(top.g, Gate)", None);
}

#[test]
fn a_typedefs_dimension_takes_the_blocks_parameter() {
    // §6.18, §23.9.
    let src = "module top; if (1) begin : g localparam W = 4;
        typedef logic [W-1:0] t; t v;
      end endmodule";
    let l = audit(src);
    let w = at(&l, "W", 0);
    assert_eq!(w.pos, "typedef");
    check(w, "Decl(top.g, Param)", Some("g.W"));
    check(at(&l, "t", 0), "Decl(top.g, Typedef)", Some("g.t"));
}

#[test]
fn a_loop_variable_a_constraint_cast_and_a_local_typedef_name_the_blocks_type() {
    // §12.7.1, §18.5, §6.18: a local typedef hides the block's after it.
    let src = "module top; if (1) begin : g typedef int t;
        class C; rand int x; constraint k { x == t'(1); } endclass
        initial begin for (t i = 0; i < 2; i++) ; end
        initial begin typedef logic [1:0] t; t v; end
      end endmodule";
    let l = audit(src);
    let k = at(&l, "t", 0);
    assert_eq!(k.pos, "constraint");
    check(k, "Decl(top.g, Typedef)", Some("g.t"));
    let f = at(&l, "t", 1);
    assert_eq!(f.pos, "local-dim");
    check(f, "Decl(top.g, Typedef)", Some("g.t"));
    let v = at(&l, "t", 2);
    assert_eq!(v.outcome, Outcome::None(Hide::Type));
    check(v, "none", None);
}

#[test]
fn a_forward_class_typedef_and_its_class_keep_their_name() {
    // §6.18, §8.3: classes keep their name; so does the forward declaration.
    let src = "module top; if (1) begin : g typedef class C;
        class D; C c; endclass
        class C; endclass
      end endmodule";
    let l = audit(src);
    check(at(&l, "C", 0), "Decl(top.g, Class)", None);
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
    check(at(&l, "f", 0), "Decl(top.g, Function)", Some("g.f"));
    check(at(&l, "h", 0), "Decl(top.g, Function)", Some("g.h"));
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
    check(&l, "none", None);
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
    check(at(&l, "b", 0), "Decl(top.g, Data)", Some("g.b"));
    assert_eq!(at(&l, "b", 1).outcome, Outcome::None(Hide::Formal));
    check(at(&l, "b", 1), "none", None);
}

#[test]
fn a_subroutine_local_hides_a_block_function_with_the_rename_agreeing() {
    let src = format!(
        "module top; if (1) begin : g {BLOCK_F}
           function automatic int h(); int f = 1; return f; endfunction end endmodule"
    );
    let l = at_outcome(&src, "f");
    assert_eq!(l.outcome, Outcome::None(Hide::Local));
    check(&l, "none", None);
}

#[test]
fn a_for_variable_hides_a_block_declaration_in_the_loop() {
    let src = "module top; if (1) begin : g int i;
        initial for (int i = 0; i < 2; i++) $display(i);
      end endmodule";
    let l = audit(src);
    for nth in 0..3 {
        assert_eq!(at(&l, "i", nth).outcome, Outcome::None(Hide::Loop));
        check(at(&l, "i", nth), "none", None);
    }
}

#[test]
fn a_class_member_and_a_property_formal_hide_the_generate_loops_genvar() {
    // §8.3, §16.8, §27.4.
    let src = "module top; for (genvar i = 0; i < 2; i++) begin : g
        class C; int i; function int f(); return i; endfunction endclass
        property p(int i); i; endproperty
        initial $display(i);
      end endmodule";
    let l = audit(src);
    let why = |nth| at(&l, "i", nth).outcome;
    let n = l.iter().filter(|m| m.name == "i").count();
    assert_eq!(why(n - 3), Outcome::None(Hide::Member));
    assert_eq!(why(n - 2), Outcome::None(Hide::Formal));
    assert_eq!(why(n - 1), Outcome::None(Hide::Genvar));
}

#[test]
fn a_foreach_variable_hides_a_block_declaration_in_the_loop() {
    let src = "module top; if (1) begin : g int i; int a[2];
        initial foreach (a[i]) $display(i);
      end endmodule";
    let l = audit(src);
    assert_eq!(at(&l, "i", 0).outcome, Outcome::None(Hide::Loop));
    check(at(&l, "i", 0), "none", None);
    check(at(&l, "a", 0), "Decl(top.g, Data)", Some("g.a"));
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
    );
}

#[test]
fn a_wildcard_import_answers_only_for_a_name_its_package_declares() {
    let src = "package p; function automatic int f(); return 100; endfunction endpackage
      module top; import p::*; initial begin $display(f()); $display(q()); end endmodule";
    let l = audit(src);
    assert_eq!(at(&l, "f", 0).outcome, Outcome::None(Hide::Import));
    check(at(&l, "f", 0), "none", None);
    check(at(&l, "q", 0), "Upward", None);
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
    check(at(&audit(src), "f", 0), "Upward", None);
}

#[test]
fn a_nested_module_reads_the_outer_modules_names() {
    // §23.4: the outer name space is visible to the inner module. A call
    // still finds its subroutine upward (§23.8.1).
    let src = "module top; int x; if (1) begin : g int y; end
        function automatic int f(); return 1; endfunction
        module inner; initial x = g.y + f(); endmodule
        inner u();
      endmodule";
    let l = audit(src);
    for name in ["x", "g"] {
        assert_eq!(
            at(&l, name, 0).outcome,
            Outcome::None(Hide::Outer),
            "{name}"
        );
        check(at(&l, name, 0), "none", None);
    }
    check(at(&l, "f", 0), "Upward", None);
}

#[test]
fn same_named_nested_modules_in_two_parents_keep_their_own_trees() {
    // §23.4.
    let src = "module a; module inner; int x; initial x = 1; endmodule inner u(); endmodule
      module b; module inner; int y; initial y = 1; endmodule inner u(); endmodule";
    let l = audit(src);
    check(at(&l, "x", 0), "Decl(a.inner, Data)", None);
    check(at(&l, "y", 0), "Decl(b.inner, Data)", None);

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
    check(at(&l, "x", 0), "Decl(top.g.ck, Data)", None);
    check(at(&l, "y", 0), "Decl(top.h.ck, Data)", None);
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
    );
}

#[test]
fn a_path_through_the_outer_block_binds_at_its_head_and_keeps_its_spelling() {
    // §23.6: `g.f` names the outer function from the inner block; its head
    // is the label `g`, which the rename does not rename.
    let src = "module top; if (1) begin : g
        function automatic int f(); return 1; endfunction
        if (1) begin : h
          function automatic int f(); return g.f(); endfunction
        end
      end endmodule";
    check(at(&audit(src), "g", 0), "Decl(top, Label)", None);
}

#[test]
fn a_local_data_type_takes_the_blocks_parameter_and_a_shallow_copy_is_missed() {
    // §6.21, §23.9.
    let src = "module top; if (1) begin : g
        localparam W = 2; class C; endclass C o;
        initial begin logic [W:0] v; C n; n = new o; end
      end endmodule";
    let l = audit(src);
    check(at(&l, "W", 0), "Decl(top.g, Param)", Some("g.W"));
    assert_eq!(at(&l, "W", 0).pos, "local-dim");
    check(at(&l, "o", 0), "Decl(top.g, Data)", None);
    assert_eq!(at(&l, "o", 0).pos, "shallow-copy");
}

#[test]
fn block_data_in_a_local_data_type_keeps_its_bare_name() {
    // The instance resolves `mem` in the block's scope; only parameters are
    // renamed in a local's type.
    let src = "module top; if (1) begin : g int mem [3];
        initial begin logic [$size(mem):0] v; end
      end endmodule";
    let l = audit(src);
    let m = at(&l, "mem", 0);
    assert_eq!(m.pos, "local-dim");
    check(m, "Decl(top.g, Data)", None);
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
        check(m, "Decl(top, Param)", None);
    }
    check(at(&l, "M", 0), "Decl(top, Param)", None);
    check(at(&l, "L", 0), "Decl(top.g, Param)", Some("g.L"));
}

#[test]
fn header_parameters_and_ports_bind_in_the_definition() {
    let src = "module top #(parameter A = 1, parameter B = A) (input logic [A:0] p); endmodule";
    let l = audit(src);
    check(at(&l, "A", 0), "Decl(top, Param)", None);
    check(at(&l, "A", 1), "Decl(top, Param)", None);
}

// Hiding: a name an inner scope hides keeps its spelling (§23.9, §6.21).

#[test]
fn a_block_local_hides_a_block_function_of_the_same_name() {
    let src = format!(
        "module top; if (1) begin : g {BLOCK_F}
           initial begin int f = 7; $display(f); end end endmodule"
    );
    let l = at_outcome(&src, "f");
    assert_eq!(l.outcome, Outcome::None(Hide::Local));
    check(&l, "none", None);
}

#[test]
fn a_local_hides_only_from_its_declaration() {
    // §6.5: the initializer of `a` sees the block's function.
    let src = format!(
        "module top; if (1) begin : g {BLOCK_F}
           initial begin int a = f(); int f = 7; $display(a, f); end end endmodule"
    );
    let l = audit(&src);
    check(at(&l, "f", 0), "Decl(top.g, Function)", Some("g.f"));
    assert_eq!(at(&l, "f", 1).outcome, Outcome::None(Hide::Local));
    assert_eq!(at(&l, "f", 1).renamed, None);
}

#[test]
fn a_block_local_hides_block_data_of_the_same_name() {
    let src = "module top; if (1) begin : g int x = 5;
        initial begin int x = 7; $display(x); end end endmodule";
    let l = at_outcome(src, "x");
    assert_eq!(l.outcome, Outcome::None(Hide::Local));
    check(&l, "none", None);
}

#[test]
fn a_local_enum_label_hides_a_block_function() {
    let src = format!(
        "module top; if (1) begin : g {BLOCK_F}
           initial begin enum {{f = 9}} e; $display(f); end end endmodule"
    );
    let l = at_outcome(&src, "f");
    assert_eq!(l.outcome, Outcome::None(Hide::Type));
    check(&l, "none", None);
}

#[test]
fn an_enum_label_of_an_inner_block_hides_a_block_function() {
    let src = format!(
        "module top; if (1) begin : g {BLOCK_F}
           if (1) begin : h typedef enum {{f = 9}} e_t; initial $display(f); end
         end endmodule"
    );
    check(at(&audit(&src), "f", 0), "Decl(top.g.h, EnumMember)", None);
}

#[test]
fn an_enum_label_inside_a_struct_is_a_name_of_the_block() {
    // §6.19.
    let src = "module top; if (1) begin : g
        struct { enum { A, B } e; } s;
        initial $display(A);
      end endmodule";
    check(at(&audit(src), "A", 0), "Decl(top.g, EnumMember)", None);
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
    check(&l, "none", None);
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
    check(&l, "none", None);
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
    check(m, "Decl(top.g.h, Clocking)", None);
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
    check(&l, "none", None);
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
    check(&l, "none", None);
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
    check(at(&l, "f", 0), "Decl(top.g, Function)", Some("g.f"));
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
    check(at(&l, "v", 1), "Decl(top.g, Data)", Some("g.v"));
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
    check(&l, "none", None);
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
    check(at(&l, "h", 0), "Decl(top.g, Function)", Some("g.h"));
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
    // The solver resolves block data by its bare name.
    check(at(&l, "lim", 0), "Decl(top.g, Data)", None);
    assert_eq!(at(&l, "lim", 0).pos, "constraint");
    check(at(&l, "f", 0), "Decl(top.g, Function)", Some("g.f"));
}

// §23.9: positions outside processes and subroutines.

fn expect_renamed(body: &str, pos: &str) {
    let src = format!(
        "module top; wire a, b; logic clk; if (1) begin : g {BLOCK_F} {body} end endmodule"
    );
    let l = audit(&src);
    let m = l
        .iter()
        .find(|m| m.name == "f" && m.pos == pos)
        .unwrap_or_else(|| panic!("no {pos} mention in {l:#?}"));
    check(m, "Decl(top.g, Function)", Some("g.f"));
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
        check(at(&l, "f", n), "Decl(top.g, Function)", Some("g.f"));
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
    }
}

#[test]
fn block_data_read_from_a_final_block_or_a_class_takes_the_blocks_key() {
    // §9.2.3, §8.3, §23.9.
    let src = "module top; if (1) begin : g int v;
        function automatic int f(); return v; endfunction
        final $display(v);
        class C; function int m(); return v; endfunction endclass
      end endmodule";
    let l = audit(src);
    for (n, pos) in [(1, "final"), (2, "class")] {
        let m = at(&l, "v", n);
        assert_eq!(m.pos, pos);
        check(m, "Decl(top.g, Data)", Some("g.v"));
    }
}

#[test]
fn a_clocking_event_names_the_block_data_by_its_key() {
    // §14.3, §23.9.
    let src = "module top; logic k; if (1) begin : g logic c; int v;
        clocking cb @(posedge c); input v; endclocking
      end endmodule";
    let l = audit(src);
    let m = l.iter().find(|m| m.name == "c").expect("the clock");
    assert_eq!(m.pos, "clocking");
    check(m, "Decl(top.g, Data)", Some("g.c"));
}

#[test]
fn a_dpi_export_binds_to_the_block_function_the_rename_misses() {
    let src = format!(
        "module top; if (1) begin : g {BLOCK_F} export \"DPI-C\" function f; end endmodule"
    );
    let l = at_outcome(&src, "f");
    check(&l, "Decl(top.g, Function)", None);
}

// `disable`.

#[test]
fn a_disable_inside_the_block_binds_to_its_task() {
    let src = "module top; if (1) begin : g
        task automatic t(); endtask
        initial disable t;
      end endmodule";
    check(at(&audit(src), "t", 0), "Decl(top.g, Task)", Some("g.t"));
}

#[test]
fn a_disable_by_path_names_the_block_task_by_its_key() {
    // §9.6.2, §23.9.
    let src = "module top; if (1) begin : g task automatic t(); endtask end
      initial disable g.t; endmodule";
    check(at(&audit(src), "g.t", 0), "Decl(top.g, Task)", None);
}

#[test]
fn a_disable_by_path_from_inside_a_block_names_the_key_from_the_definition() {
    // §9.6.2, §23.9: `h.t` from `g` is `g.h.t`.
    let src = "module top; if (1) begin : g
        if (1) begin : h task automatic t(); endtask end
        initial disable h.t;
      end endmodule";
    check(at(&audit(src), "g.h.t", 0), "Decl(top.g.h, Task)", None);
}

#[test]
fn a_disable_by_path_into_a_loop_block_takes_the_literal_index() {
    // §9.6.2, §27.4.
    let src = "module top; for (genvar i = 0; i < 2; i++) begin : g
        task automatic t(); endtask
      end
      initial disable g[1].t; endmodule";
    check(at(&audit(src), "g[1].t", 0), "Decl(top.g[@], Task)", None);
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
    check(&l, "none", None);
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
    check(&l, "none", None);
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
    check(at(&audit(src), "t", 0), "Decl(top.g, Task)", Some("g.t"));
}

#[test]
fn a_named_block_under_a_process_level_unnamed_begin_is_a_path_head_of_the_module() {
    // §9.3.4.
    let src = "module top;
        initial begin begin : b int x; end end
        initial $display(b.x);
      endmodule";
    check(at(&audit(src), "b", 0), "Decl(top, Label)", None);
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
    check(f[0], "none", None);
    check(f[1], "Decl(top.g.h, Function)", Some("g.h.f"));
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
    check(m, "none", None);
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
    check(&l, "none", None);
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
    check(&l, "none", None);
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
    check(&l, "none", None);
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

// Every legal bare name binds: what is left `Upward` in a value position is
// declared nowhere.

fn why(l: &AuditLine) -> Hide {
    match l.outcome {
        Outcome::None(w) => w,
        o => panic!("{o:?} in {l:?}"),
    }
}

#[test]
fn the_std_classes_bind_as_imports() {
    // §26.7: `std` is wildcard imported into every compilation unit.
    let src = "module top;
        initial begin process p = process::self(); mailbox #(int) m = new; semaphore s = new(1); end
      endmodule";
    let l = audit(src);
    for name in ["process", "mailbox", "semaphore"] {
        assert_eq!(why(at(&l, name, 0)), Hide::Import, "{name}");
        check(at(&l, name, 0), "none", None);
    }
}

#[test]
fn a_user_class_named_like_a_std_class_is_found_first() {
    // §26.7: user code can redefine the names of `std`.
    let src = "class mailbox; int n; endclass
      module top; class semaphore; endclass initial begin mailbox m; semaphore s; end endmodule";
    let l = audit(src);
    assert_eq!(why(at(&l, "mailbox", 0)), Hide::Import);
    check(at(&l, "semaphore", 0), "Decl(top, Class)", None);
}

#[test]
fn a_design_unit_name_is_a_qualified_head() {
    // §23.9: a path can start with a module name; a port names an interface.
    let src = "interface bus_if; logic v; endinterface
      module p(bus_if b); endmodule
      module top; bus_if i(); p u(.b(i)); initial $dumpvars(0, top); endmodule";
    let l = audit(src);
    for name in ["bus_if", "top"] {
        assert_eq!(why(at(&l, name, 0)), Hide::Qualified, "{name}");
    }
}

#[test]
fn a_call_named_like_a_design_unit_is_still_found_upward() {
    // §23.8.1.
    let src = "module f; endmodule
      module c; initial $display(f()); endmodule
      module top; function automatic int f(); return 1; endfunction c u(); endmodule";
    check(at(&audit(src), "f", 0), "Upward", None);
}

#[test]
fn an_implicit_net_is_declared_in_the_scope_of_its_first_reference() {
    // §6.10: a port connection, a gate terminal and the left-hand side of a
    // continuous assignment; §31.9: a delayed signal of a timing check.
    let src = "module w(output logic o); assign o = 1; endmodule
      module top(input logic ck, input logic d);
        w u(.o(p_net));
        buf b(g_net, p_net);
        assign a_net = g_net;
        specify $setuphold(posedge ck, d, 1, 1, , , , d_ck, d_d); endspecify
        if (1) begin : g w v(.o(b_net)); initial $display(b_net); end
        initial $display(p_net, g_net, a_net, d_ck, d_d);
      endmodule";
    let l = audit(src);
    for name in ["p_net", "g_net", "a_net", "d_ck", "d_d"] {
        let last = l.iter().filter(|m| m.name == name).count() - 1;
        for n in [0, last] {
            check(at(&l, name, n), "Decl(top, ImplicitNet)", None);
        }
    }
    check(at(&l, "b_net", 0), "Decl(top.g, ImplicitNet)", None);
    check(at(&l, "b_net", 1), "Decl(top.g, ImplicitNet)", None);
}

#[test]
fn an_implicit_net_of_a_block_is_not_a_name_of_the_module() {
    // §6.10: the net belongs to the block that references it.
    let src = "module w(output logic o); assign o = 1; endmodule
      module top; if (1) begin : g w v(.o(n)); end initial $display(n); endmodule";
    let l = audit(src);
    check(at(&l, "n", 0), "Decl(top.g, ImplicitNet)", None);
    check(at(&l, "n", 1), "Upward", None);
}

#[test]
fn a_name_found_another_way_is_not_an_implicit_net() {
    // §6.10: only an identifier not declared in a visible scope; §26.3 and
    // §27.4: an import and a loop variable are.
    let src = "package q; parameter int K = 3; endpackage
      module m(input logic [1:0] i); endmodule
      module top; import q::*; m u(.i(K));
        for (genvar j = 0; j < 2; j++) begin : l m v(.i(j)); end
      endmodule";
    let l = audit(src);
    assert_eq!(why(at(&l, "K", 0)), Hide::Import);
    assert_eq!(why(at(&l, "j", 2)), Hide::Genvar);
    assert_eq!(at(&l, "j", 2).target, None);
}

#[test]
fn a_property_local_variable_is_visible_in_its_body() {
    // §16.10.
    let src = "module top; logic clk, a, b; int d;
        property p_lv; int x; @(posedge clk) (a, x = d) |-> ##1 (b && d == x + 1); endproperty
        sequence s_lv; int v = 0; (a, v = d) ##1 (d == v); endsequence
      endmodule";
    let l = audit(src);
    for (name, uses) in [("x", 3), ("v", 3)] {
        for n in 0..uses {
            assert_eq!(why(at(&l, name, n)), Hide::Local, "{name} {n}");
        }
    }
}

#[test]
fn randomize_arguments_name_members_of_the_receiver() {
    // §18.11, also on an indexed receiver (§18.7).
    let src = "module top; class c; rand int a, b; endclass c one; c many[2];
        initial begin
          void'(one.randomize(a, b));
          void'(many[0].randomize(a));
          void'(many[1].randomize with { b == 2; });
        end
      endmodule";
    let l = audit(src);
    for (name, n) in [("a", 0), ("b", 0), ("a", 1), ("b", 1)] {
        assert_eq!(why(at(&l, name, n)), Hide::Member, "{name} {n}");
    }
}

#[test]
fn a_formal_default_sees_the_formals_before_it() {
    // §13.5.3: a default binds in the declaring scope; a name found nowhere
    // there names an earlier formal.
    let src = "module top; int c = 4;
        function automatic int f(int a = 1, int b = a + 1, int c = 2, int d = c);
          return a + b + c + d;
        endfunction
      endmodule";
    let l = audit(src);
    assert_eq!(why(at(&l, "a", 0)), Hide::Formal);
    check(at(&l, "c", 0), "Decl(top, Data)", None);
}

#[test]
fn a_ranged_enum_declares_each_member() {
    // §6.19.2, Table 6-10.
    let src = "module top; typedef enum {A[3], B[2:4], C[1:0]} e_t;
        initial $display(A0, A2, B2, B4, C0, C1);
      endmodule";
    let l = audit(src);
    for name in ["A0", "A2", "B2", "B4", "C0", "C1"] {
        check(at(&l, name, 0), "Decl(top, EnumMember)", None);
    }
}

#[test]
fn an_implicit_generate_name_is_a_label_of_its_scope() {
    // §27.6: `genblk1` names the unnamed block; no construct is numbered 7.
    let src = "module top; if (1) begin int x; end if (1) begin : g int y; end
        initial $display(genblk1.x, genblk7.x);
      endmodule";
    let l = audit(src);
    check(at(&l, "genblk1", 0), "Decl(top, Label)", None);
    check(at(&l, "genblk7", 0), "Upward", None);
}

#[test]
fn an_implicit_name_with_only_labelled_arms_names_no_block() {
    // §27.6: only an unnamed block takes the construct's name.
    let src = "module top; if (1) begin : a int x; end else begin : b int x; end
        initial $display(genblk1.x);
      endmodule";
    check(at(&audit(src), "genblk1", 0), "Upward", None);
}

#[test]
fn a_1step_delay_is_not_a_name() {
    // §14.4, A.2.2.3.
    let src = "module top; logic clk, d, w;
        clocking cb @(posedge clk); default input #1step output #0; input d; endclocking
        assign #1step w = d;
        initial #1step $display(d);
      endmodule";
    let l = audit(src);
    let steps: Vec<_> = l.iter().filter(|m| m.name == "1step").collect();
    assert_eq!(steps.len(), 3, "{l:#?}");
    for m in steps {
        assert_eq!(why(m), Hide::Qualified);
    }
}

#[test]
fn the_audit_marks_callees_and_the_assign_and_port_positions() {
    let src = "module w(input logic i); endmodule
      module top; logic a, b;
        function automatic logic f(); return 1; endfunction
        assign a = f();
        w u(.i(b));
        initial $display(f());
      endmodule";
    let l = audit(src);
    let a = at(&l, "a", 0);
    assert_eq!((a.pos, a.call), ("assign-lhs", false));
    let b = at(&l, "b", 0);
    assert_eq!((b.pos, b.call), ("port", false));
    for (n, pos) in [(0, "process"), (1, "process")] {
        let f = at(&l, "f", n);
        assert_eq!((f.pos, f.call), (pos, true), "{f:?}");
    }
}

#[test]
fn a_randsequence_production_value_has_no_target() {
    // §18.17.7: a code block reads each production of its rule as a
    // variable. A production of another rule is not one.
    let src = "module top; int n, k;
        initial randsequence (vr)
          void vr : r1 r2 { n = r1 + r2 + r3; k = n; };
          int r1 : { return 5; };
          int r2 : { return 6; };
          int r3 : { return 7; };
        endsequence
      endmodule";
    let l = audit(src);
    assert_eq!(why(at(&l, "r1", 0)), Hide::Qualified);
    assert_eq!(why(at(&l, "r2", 0)), Hide::Qualified);
    assert_eq!(at(&l, "r3", 0).outcome, Outcome::Upward);
    assert_eq!(at(&l, "k", 0).binding, "Decl(top, Data)");
}

#[test]
fn each_name_of_a_concatenation_at_an_implicit_net_position_is_declared() {
    // §6.10, §11.4.12: the members of a concatenation on the left-hand side
    // or as a port actual.
    let src = "module m(output logic [1:0] z); assign z = 2'b01; endmodule
      module top; logic [3:0] a, b;
        assign {cout, sum} = a + b;
        m u(.z({z1, z0}));
        initial $display(cout, sum, z1, z0);
      endmodule";
    let l = audit(src);
    for name in ["cout", "sum", "z1", "z0"] {
        for n in [0, 1] {
            check(at(&l, name, n), "Decl(top, ImplicitNet)", None);
        }
    }
}

#[test]
fn a_bare_built_in_randomization_method_is_not_a_name() {
    // §18.8 rand_mode, §18.9 constraint_mode, §18.13 srandom, get_randstate,
    // set_randstate, called bare in a method of the class.
    let src = "module top; class C; rand int x; string st;
        function void go();
          rand_mode(0); constraint_mode(1); srandom(3);
          st = get_randstate(); set_randstate(st);
        endfunction
      endclass endmodule";
    let l = audit(src);
    for name in [
        "rand_mode",
        "constraint_mode",
        "srandom",
        "get_randstate",
        "set_randstate",
    ] {
        assert_eq!(why(at(&l, name, 0)), Hide::Qualified, "{name}");
    }
}

#[test]
fn export_star_star_re_exports_each_imported_package() {
    // §26.6: `export *::*` exports from all packages from which imports occur.
    let src = "package p1; localparam int A = 1; endpackage
      package p2; localparam int B = 2; endpackage
      package q; localparam int Z = 9; endpackage
      package both; import p1::*; import p2::*; export *::*; localparam int C = A + B; endpackage
      package none; import q::*; localparam int D = Z; endpackage
      module top; import both::*; import none::*; initial $display(A, B, C, Z); endmodule";
    let l = audit(src);
    for name in ["A", "B"] {
        assert_eq!(why(at(&l, name, 0)), Hide::Import, "{name}");
    }
    assert_eq!(at(&l, "Z", 0).outcome, Outcome::Upward);
}

// The stamps the generate rename reads.

/// Where `top`'s tree declares the declaration `b` names, and its kind.
fn stamped(b: Bound) -> (String, DeclKind) {
    let tree = tree_of("top").expect("the tree of top");
    let d = b
        .as_decl()
        .unwrap_or_else(|| panic!("not a declaration: {b:?}"));
    let decl = &tree.decls[d.0 as usize];
    (tree.path(decl.scope), decl.kind)
}

#[test]
fn block_typedefs_properties_sequences_type_names_bases_and_clocks_are_stamped() {
    // §6.18, §8.13, §14.3, §16.8, §16.12, §23.9: each names a declaration of
    // the nested block `g.h`.
    let src = "module top;
      if (1) begin : g if (1) begin : h
        logic c;
        typedef logic [7:0] t;
        t v;
        property p; @(posedge c) 1; endproperty
        sequence s; 1; endsequence
        class B; endclass
        typedef B base_t;
        class D extends base_t; endclass
        clocking cb @(posedge c); endclocking
      end end endmodule";
    let parsed = xezim_core::parse(src);
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
    let mut descs = parsed.source.descriptions;
    build_design(&mut descs);
    let Description::Module(m) = &descs[0] else {
        panic!("a module")
    };
    let block = |i: &ModuleItem| match i {
        ModuleItem::GenerateIf(gi) => gi.branches[0].1.clone(),
        k => panic!("{k:?}"),
    };
    let h = block(&block(&m.items[0])[0]);
    let mut got = Vec::new();
    for item in &h {
        match item {
            ModuleItem::TypedefDeclaration(t) => got.push((t.name.name.clone(), stamped(t.decl))),
            ModuleItem::PropertyDeclaration(p) => got.push((p.name.name.clone(), stamped(p.decl))),
            ModuleItem::SequenceDeclaration(s) => got.push((s.name.name.clone(), stamped(s.decl))),
            ModuleItem::DataDeclaration(d) => {
                if let xezim_core::ast::types::DataType::TypeReference { name, .. } = &d.data_type {
                    got.push(("type of v".to_string(), stamped(name.bound)));
                }
            }
            ModuleItem::ClassDeclaration(c) => {
                if let Some(e) = &c.extends {
                    got.push(("base of D".to_string(), stamped(e.bound)));
                }
            }
            ModuleItem::ClockingDeclaration(c) => {
                got.push(("clock of cb".to_string(), stamped(c.clock_bound)))
            }
            _ => {}
        }
    }
    let at = |k| ("g.h".to_string(), k);
    assert_eq!(
        got,
        [
            ("t".to_string(), at(DeclKind::Typedef)),
            ("type of v".to_string(), at(DeclKind::Typedef)),
            ("p".to_string(), at(DeclKind::Property)),
            ("s".to_string(), at(DeclKind::Sequence)),
            ("base_t".to_string(), at(DeclKind::Typedef)),
            ("base of D".to_string(), at(DeclKind::Typedef)),
            ("clock of cb".to_string(), at(DeclKind::Data)),
        ]
    );
}
