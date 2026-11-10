//! The scope tree of a definition: §27.5 direct nesting, §27.6 implicit names,
//! §23.9 lookup. Run-time names are pinned in xezim's
//! `tests/hierarchy/generate_scope_tree.rs`.

use xezim_core::ast::Description;
use xezim_core::ast::binding::{DeclKind, ScopeId};
use xezim_core::ast::decl::ModuleItem;
use xezim_core::scope_tree::{ScopeKind, ScopeTree, build_all, tree_of};

fn trees(src: &str) -> (Vec<ScopeTree>, Vec<Description>) {
    let parsed = xezim_core::parse(src);
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
    let mut descs = parsed.source.descriptions;
    (build_all(&mut descs), descs)
}

fn tree(src: &str) -> ScopeTree {
    trees(src).0.pop().expect("a definition")
}

/// Every scope path of the tree, in build order, the root left out.
fn paths(t: &ScopeTree) -> Vec<String> {
    (1..t.scopes.len())
        .map(|i| t.path(ScopeId(i as u32)))
        .collect()
}

/// The scope with this path.
fn at(t: &ScopeTree, path: &str) -> ScopeId {
    (0..t.scopes.len())
        .map(|i| ScopeId(i as u32))
        .find(|s| t.path(*s) == path)
        .unwrap_or_else(|| panic!("{path} not in {:?}", paths(t)))
}

const LRM_27_6: &str = "module top;
  parameter genblk2 = 0;
  genvar i;
  if (genblk2) logic a;
  else         logic b;
  if (genblk2) logic a;
  else         logic b;
  for (i = 0; i < 1; i = i + 1) begin : g1
    if (1) logic a;
  end
  for (i = 0; i < 1; i = i + 1)
    if (1) logic a;
  if (1) logic a;
endmodule";

#[test]
fn the_tree_of_the_lrm_example_has_the_names_the_lrm_gives() {
    let t = tree(LRM_27_6);
    assert_eq!(
        paths(&t),
        [
            "genblk1",
            "genblk1",
            "genblk02",
            "genblk02",
            "g1[@]",
            "g1[@].genblk1",
            "genblk4[@]",
            "genblk4[@].genblk1",
            "genblk5",
        ]
    );
}

#[test]
fn the_lrm_example_keys_its_declarations_by_those_names() {
    let t = tree(LRM_27_6);
    assert_eq!(t.key(at(&t, "genblk02"), "b", &[]), "genblk02.b");
    assert_eq!(t.key(at(&t, "g1[@].genblk1"), "a", &[0]), "g1[0].genblk1.a");
    assert_eq!(
        t.key(at(&t, "genblk4[@].genblk1"), "a", &[0]),
        "genblk4[0].genblk1.a"
    );
    assert_eq!(t.key(at(&t, "genblk5"), "a", &[]), "genblk5.a");
    assert_eq!(t.key(t.root, "genblk2", &[]), "genblk2");
}

#[test]
fn numbers_count_every_construct_named_or_not() {
    let t = tree(LRM_27_6);
    let ordinal = |p: &str| match &t.scopes[at(&t, p).0 as usize].kind {
        ScopeKind::Generate { ordinal, .. } => *ordinal,
        ScopeKind::Definition => panic!("{p} is the root"),
    };
    assert_eq!(ordinal("genblk02"), 2);
    assert_eq!(ordinal("g1[@]"), 3);
    assert_eq!(ordinal("genblk4[@]"), 4);
    assert_eq!(ordinal("genblk5"), 5);
    assert_eq!(ordinal("g1[@].genblk1"), 1);
}

#[test]
fn a_directly_nested_construct_opens_no_scope_of_its_own() {
    let t = tree(
        "module test; parameter p = 0, q = 0;
           if (p == 1)
             if (q == 0) begin : u1 int a; end
             else if (q == 2) begin : u1 int b; end
             else ;
           else if (p == 2)
             case (q)
               0, 1, 2: begin : u1 int c; end
               default: begin : u1 int d; end
             endcase
         endmodule",
    );
    // The null arm of the inner `if` is a block of its own, unnamed.
    assert_eq!(paths(&t), ["u1", "u1", "genblk1", "u1", "u1"]);
    assert_eq!(t.scopes[t.root.0 as usize].children.len(), 5);
    for s in &t.scopes[1..] {
        assert_eq!(s.parent, Some(t.root));
    }
}

#[test]
fn a_begin_wrapped_nest_opens_a_scope() {
    let t = tree("module m; if (1) begin if (1) int x; end endmodule");
    assert_eq!(paths(&t), ["genblk1", "genblk1.genblk1"]);
}

#[test]
fn a_loop_under_a_conditional_is_not_directly_nested() {
    let t = tree("module m; if (1) for (genvar i = 0; i < 1; i++) int x; endmodule");
    assert_eq!(paths(&t), ["genblk1", "genblk1.genblk1[@]"]);
}

#[test]
fn the_construct_after_a_direct_nest_takes_the_next_number() {
    let t = tree("module m; if (1) if (1) int x; if (1) int y; endmodule");
    assert_eq!(paths(&t), ["genblk1", "genblk2"]);
}

#[test]
fn a_generate_region_is_not_a_scope_and_shares_the_numbers() {
    let t = tree(
        "module m; if (1) int a; generate if (1) int b; for (genvar i = 0; i < 1; i++) int c; endgenerate if (1) int d; endmodule",
    );
    assert_eq!(paths(&t), ["genblk1", "genblk2", "genblk3[@]", "genblk4"]);
}

#[test]
fn zeros_go_on_until_the_name_is_free() {
    let t = tree("module m; parameter genblk1 = 0, genblk01 = 0; if (1) int a; endmodule");
    assert_eq!(paths(&t), ["genblk001"]);
}

#[test]
fn header_names_and_later_names_conflict() {
    let t = tree(
        "module m #(parameter genblk1 = 0) (input genblk2); if (1) int a; if (1) int b; if (1) int c; int genblk3; endmodule",
    );
    assert_eq!(paths(&t), ["genblk01", "genblk02", "genblk03"]);
}

#[test]
fn a_nested_label_conflicts_only_where_it_is_declared() {
    let t =
        tree("module m; if (1) begin : a if (1) begin : genblk2 end end if (1) int x; endmodule");
    assert_eq!(paths(&t), ["a", "a.genblk2", "genblk2"]);
}

#[test]
fn a_directly_nested_label_is_declared_in_the_enclosing_scope() {
    let t = tree("module m; if (1) if (0) begin : genblk2 end if (1) int x; endmodule");
    assert_eq!(paths(&t), ["genblk2", "genblk02"]);
    let label = t.lookup(t.root, "genblk2").expect("declared");
    assert_eq!(t.decls[label.0 as usize].kind, DeclKind::Label);
}

#[test]
fn lookup_finds_the_innermost_declaration_through_nested_arms() {
    let t = tree(
        "module m; int x; int y;
           if (1) begin : a int x; if (1) if (1) begin : b int z; end end
         endmodule",
    );
    let b = at(&t, "a.b");
    let decl = |n: &str| t.lookup(b, n).map(|d| t.decls[d.0 as usize].clone());
    assert_eq!(decl("z").unwrap().scope, b);
    assert_eq!(decl("x").unwrap().scope, at(&t, "a"));
    assert_eq!(decl("y").unwrap().scope, t.root);
    assert_eq!(decl("nope").map(|d| d.name), None);
}

#[test]
fn arms_exclude_each_other() {
    let t = tree(
        "module m;
           if (1) begin : a int p; end else begin : b int q; end
           if (1) begin : c int r; end
         endmodule",
    );
    let (a, b, c) = (at(&t, "a"), at(&t, "b"), at(&t, "c"));
    assert_eq!(t.lookup(a, "q"), None);
    assert_eq!(t.lookup(b, "p"), None);
    let group = |s: ScopeId| t.scopes[s.0 as usize].arm_group;
    assert!(group(a).is_some());
    assert_eq!(group(a), group(b));
    assert_ne!(group(a), group(c));
}

#[test]
fn directly_nested_arms_are_in_the_outer_constructs_group() {
    let t = tree(
        "module m;
           if (0) begin : a end
           else case (1) 1: begin : b end default: begin : c end endcase
         endmodule",
    );
    let group = |p: &str| t.scopes[at(&t, p).0 as usize].arm_group;
    assert_eq!(group("a"), group("b"));
    assert_eq!(group("a"), group("c"));
}

#[test]
fn a_loop_body_is_in_no_group() {
    let t = tree("module m; for (genvar i = 0; i < 1; i++) begin : l end endmodule");
    assert_eq!(t.scopes[at(&t, "l[@]").0 as usize].arm_group, None);
}

#[test]
fn imports_are_recorded_on_the_scope_they_are_written_in() {
    let t = tree("module m; import p::*; if (1) begin : a import q::x; end endmodule");
    let root = &t.scopes[t.root.0 as usize];
    assert_eq!(root.wildcard_imports, ["p"]);
    assert!(root.explicit_imports.is_empty());
    let a = &t.scopes[at(&t, "a").0 as usize];
    assert_eq!(a.explicit_imports.get("x").map(String::as_str), Some("q"));
}

#[test]
fn building_stamps_the_implicit_name_on_every_construct_of_a_chain() {
    let (_, descs) = trees(
        "module m; parameter genblk1 = 0;
           if (0) ; else case (1) 1: if (1) int x; endcase
           for (genvar i = 0; i < 1; i++) int y;
         endmodule",
    );
    let Description::Module(m) = &descs[0] else {
        panic!("a module")
    };
    let gi = m
        .items
        .iter()
        .find_map(|i| match i {
            ModuleItem::GenerateIf(g) => Some(g),
            _ => None,
        })
        .expect("the if");
    assert_eq!(gi.implicit_name, "genblk01");
    assert_eq!(gi.branch_direct, [false, true]);
    let ModuleItem::GenerateCase(gc) = &gi.branches[1].1[0] else {
        panic!("the case")
    };
    assert_eq!(gc.implicit_name, "genblk01");
    assert!(gc.arms[0].direct);
    let ModuleItem::GenerateIf(inner) = &gc.arms[0].items[0] else {
        panic!("the inner if")
    };
    assert_eq!(inner.implicit_name, "genblk01");
    assert_eq!(inner.branch_direct, [false]);
    let gf = m
        .items
        .iter()
        .find_map(|i| match i {
            ModuleItem::GenerateFor(g) => Some(g),
            _ => None,
        })
        .expect("the for");
    assert_eq!(gf.implicit_name, "genblk2");
}

#[test]
fn nested_modules_and_checkers_have_trees_of_their_own() {
    let (ts, _) = trees(
        "module outer; parameter genblk1 = 0;
           module inner; if (1) int a; endmodule
           checker ck; if (1) int b; endchecker
           if (1) int c;
         endmodule",
    );
    let of = |n: &str| ts.iter().find(|t| t.def == n).expect(n);
    assert_eq!(paths(of("outer.inner")), ["genblk1"]);
    assert_eq!(paths(of("outer.ck")), ["genblk1"]);
    assert_eq!(paths(of("outer")), ["genblk01"]);
}

#[test]
fn a_compilation_unit_checker_has_a_tree_and_names_its_blocks() {
    let (ts, _) = trees(
        "checker ck(input logic c);
           if (1) int a;
           if (1) if (1) begin : d int b; end
           if (1) int e;
         endchecker",
    );
    let t = ts.iter().find(|t| t.def == "ck").expect("the tree of ck");
    assert_eq!(paths(t), ["genblk1", "d", "genblk3"]);
}

#[test]
fn interfaces_and_programs_have_trees() {
    let (ts, _) = trees(
        "interface i; if (1) int a; endinterface
         program p; int genblk1; if (1) int b; endprogram",
    );
    let of = |n: &str| ts.iter().find(|t| t.def == n).expect(n);
    assert_eq!(paths(of("i")), ["genblk1"]);
    assert_eq!(paths(of("p")), ["genblk01"]);
}

#[test]
fn elaboration_keeps_a_tree_per_definition() {
    xezim_core::parse_and_elaborate_multi(
        &[
            "module c; if (1) if (1) begin : d end endmodule module top; c u(); endmodule"
                .to_string(),
        ],
        Some("top"),
        &[],
        &["t.sv".to_string()],
        &[],
    )
    .unwrap_or_else(|e| panic!("{e}"));
    let c = tree_of("c").expect("the tree of c");
    assert_eq!(paths(&c), ["d"]);
    assert!(tree_of("top").is_some());
    assert!(tree_of("nope").is_none());
}
