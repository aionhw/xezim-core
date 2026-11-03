//! IEEE 1800-2023 §3.12.1 / §8.24 / §6.21: shared unit declarations and diagnostics.

use xezim_core::{SourceDefinition, ast::decl::ModuleItem};

fn elaborate(
    source: &str,
    top: Option<&str>,
) -> Result<
    (
        xezim_core::hasher::HashMap<String, SourceDefinition>,
        xezim_core::ElaboratedModule,
    ),
    String,
> {
    xezim_core::parse_and_elaborate_multi(
        &[source.to_string()],
        top,
        &[],
        &["top.sv".to_string()],
        &[],
    )
}

fn subs(def: &SourceDefinition) -> Vec<String> {
    def.items()
        .iter()
        .filter_map(|it| match it {
            ModuleItem::FunctionDeclaration(f) => Some(f.name.qualified()),
            ModuleItem::TaskDeclaration(t) => Some(t.name.qualified()),
            _ => None,
        })
        .collect()
}

#[test]
fn unused_bodies_are_not_copied_to_definitions_or_instances() {
    let (defs, design) = elaborate(
        r#"
function automatic int unused(int x); return x+1; endfunction
module leaf; endmodule
module other; endmodule
module top; leaf a(), b(); other c(); endmodule
"#,
        Some("top"),
    )
    .expect("elaborate");
    assert_eq!(subs(&defs["top"]), ["unused"]);
    assert!(subs(&defs["leaf"]).is_empty());
    assert!(subs(&defs["other"]).is_empty());
    assert!(design.functions.contains_key("unused"));
    assert!(!design.functions.contains_key("a.unused"));
    assert!(!design.functions.contains_key("b.unused"));
    assert!(!design.functions.contains_key("c.unused"));
}

#[test]
fn calls_retain_transitive_function_and_task_dependencies() {
    let (defs, design) = elaborate(
        r#"
function automatic int last(int n); return n+1; endfunction
function automatic int middle(int n); return last(n)+1; endfunction
function automatic int first(int n); return middle(n)+1; endfunction
function automatic int unused(int n); return n; endfunction
task automatic work(output int n); n=first(3); endtask
module leaf; int n; initial work(n); endmodule
module top; leaf a(), b(); endmodule
"#,
        Some("top"),
    )
    .expect("elaborate");
    let names = subs(&defs["leaf"]);
    for name in ["last", "middle", "first", "work"] {
        assert!(names.iter().any(|n| n == name), "{names:?}");
    }
    assert!(!names.iter().any(|n| n == "unused"));
    for instance in ["a", "b"] {
        for name in ["last", "middle", "first"] {
            assert!(design.functions.contains_key(&format!("{instance}.{name}")));
        }
        assert!(design.tasks.contains_key(&format!("{instance}.work")));
    }
}

#[test]
fn type_dimensions_and_unit_initializers_retain_dependencies() {
    let (defs, design) = elaborate(
        r#"
function automatic int width(); return 9; endfunction
function automatic int initial_value(); return 17; endfunction
int unit_value=initial_value();
module leaf #(parameter int W=width()) (input logic [width()-1:0] p);
  localparam int CHECK=W;
endmodule
module top; leaf a(); endmodule
"#,
        Some("top"),
    )
    .expect("elaborate");
    let names = subs(&defs["leaf"]);
    assert!(names.iter().any(|n| n == "width"));
    assert!(names.iter().any(|n| n == "initial_value"));
    assert_eq!(design.parameters["a.CHECK"].to_u64(), Some(9));
}

#[test]
fn unused_static_initializer_diagnostic_is_preserved() {
    let error = elaborate(
        r#"
function int unused(); int value=3; return value; endfunction
module leaf; endmodule
module top; leaf a(); endmodule
"#,
        Some("top"),
    )
    .expect_err("unit declaration must still be checked");
    assert!(error.contains("implicitly static"), "{error}");
}

#[test]
fn out_of_block_body_is_retained_once_for_linking() {
    let (defs, design) = elaborate(
        r#"
class lookup; extern function int get(int x); endclass
function int lookup::get(int x); return x+3; endfunction
module leaf; lookup value; initial begin value=new; $display("%0d", value.get(4)); end endmodule
module top; leaf a(), b(); endmodule
"#,
        Some("top"),
    )
    .expect("elaborate");
    assert_eq!(subs(&defs["top"]), ["lookup::get"]);
    assert!(subs(&defs["leaf"]).is_empty());
    let method = &design.classes["lookup"].methods["get"];
    match &method.kind {
        xezim_core::ast::decl::ClassMethodKind::Function(f) => assert!(!f.items.is_empty()),
        _ => panic!("expected function body"),
    }
}

#[test]
fn single_automatic_root_uses_pruning_but_multiple_roots_stay_conservative() {
    let single = r#"
function automatic int unused(); return 1; endfunction
module leaf; endmodule
module top; leaf a(); endmodule
"#;
    let (defs, _) = elaborate(single, None).expect("single root");
    assert!(subs(&defs["leaf"]).is_empty());
    let multiple = format!("{single}\nmodule second; endmodule\n");
    let (defs, _) = elaborate(&multiple, None).expect("multiple roots");
    for name in ["top", "leaf", "second"] {
        assert_eq!(subs(&defs[name]), ["unused"]);
    }
}

#[test]
fn program_and_interface_retain_called_unit_functions() {
    let (defs, _) = elaborate(
        r#"
function automatic int value(); return 7; endfunction
function automatic int unused(); return 9; endfunction
program p; int n; initial n=value(); endprogram
interface i; localparam int N=value(); endinterface
module top; p a(); i b(); endmodule
"#,
        Some("top"),
    )
    .expect("elaborate");
    assert_eq!(subs(&defs["p"]), ["value"]);
    assert_eq!(subs(&defs["i"]), ["value"]);
}

#[test]
fn unused_function_fork_diagnostic_is_preserved() {
    let error = elaborate(
        r#"
function automatic void unused(); fork begin end join endfunction
module leaf; endmodule
module top; leaf a(); endmodule
"#,
        Some("top"),
    )
    .expect_err("unit declaration must still be checked");
    assert!(error.contains("only fork-join_none"), "{error}");
}

#[test]
fn mutual_dependencies_reach_a_fixed_point() {
    let (defs, _) = elaborate(
        r#"
function automatic int first(int n); return n>0?second(n-1):0; endfunction
function automatic int second(int n); return n>0?first(n-1):0; endfunction
function automatic int unused(); return 99; endfunction
module leaf; initial $display("%0d", first(2)); endmodule
module top; leaf a(); endmodule
"#,
        Some("top"),
    )
    .expect("elaborate");
    assert_eq!(subs(&defs["leaf"]), ["first", "second"]);
}

/// IEEE 1800-2023 §23.3.1: a package or a class is never instantiated, so it
/// is no hierarchy root; with no top named, one uninstantiated module beside
/// them is still the unit-body carrier (#834).
#[test]
fn a_package_or_class_does_not_make_the_root_ambiguous() {
    let with_package = r#"
function automatic int unused(); return 1; endfunction
package unrelated_pkg; int v; endpackage
module leaf; endmodule
module top; leaf a(); endmodule
"#;
    let (defs, _) = elaborate(with_package, None).expect("package beside the root");
    assert_eq!(subs(&defs["top"]), ["unused"]);
    assert!(subs(&defs["leaf"]).is_empty());

    let with_class = r#"
function automatic int unused(); return 1; endfunction
class lookup; extern function int get(int x); endclass
function int lookup::get(int x); return x+3; endfunction
module leaf; endmodule
module top; leaf a(); lookup value; initial begin value=new; $display("%0d", value.get(4)); end endmodule
"#;
    let (defs, design) = elaborate(with_class, None).expect("class beside the root");
    assert_eq!(subs(&defs["top"]), ["unused", "lookup::get"]);
    assert!(subs(&defs["leaf"]).is_empty());
    match &design.classes["lookup"].methods["get"].kind {
        xezim_core::ast::decl::ClassMethodKind::Function(f) => assert!(!f.items.is_empty()),
        _ => panic!("expected function body"),
    }
}
