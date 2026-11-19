//! §23.8 (aionhw/xezim#721): the scope tree upward names are resolved
//! against holds each instance path and each definition name once, however
//! many of its tables name them.

use super::*;

fn scopes_of(src: &str) -> Rc<std::cell::RefCell<UpwardScopes>> {
    let (_, m) = crate::parse_and_elaborate_multi(
        &[src.to_string()],
        Some("top"),
        &[],
        &["t.sv".to_string()],
        &[],
    )
    .expect("elaborates");
    Rc::clone(&m.upward_scopes)
}

const SRC: &str = "
module leaf_unit; function automatic int id(); return 1; endfunction endmodule
module branch_unit;
  function automatic int width(); return 4; endfunction
  leaf_unit child_0();
  leaf_unit child_1();
  for (genvar i = 0; i < 2; i++) begin : g
    leaf_unit u();
  end
endmodule
module top;
  branch_unit cluster_0();
  branch_unit cluster_1();
  leaf_unit lone();
endmodule
";

#[test]
fn an_instance_path_is_one_string_in_every_table() {
    let scopes = scopes_of(SRC);
    let scopes = scopes.borrow();
    let mut paths = 0;
    for (parent, kids) in &scopes.children {
        for kid in kids {
            paths += 1;
            let (in_defs, _) = scopes.defs.get_key_value(&**kid).expect("defs");
            assert!(Rc::ptr_eq(kid, in_defs), "{kid}");
            let (in_parents, up) = scopes.parents.get_key_value(&**kid).expect("parents");
            assert!(Rc::ptr_eq(kid, in_parents), "{kid}");
            assert!(Rc::ptr_eq(&up.path, parent), "{kid}");
            let (parent_in_defs, _) = scopes.defs.get_key_value(&**parent).expect("parent");
            assert!(Rc::ptr_eq(parent, parent_in_defs), "{kid}");
        }
    }
    // 2 clusters x (2 children + 2 generated) + 2 clusters + 1.
    assert_eq!(paths, 11);
    assert_eq!(scopes.defs.len(), 12);
}

#[test]
fn a_definition_name_is_one_string_for_all_its_instances() {
    let scopes = scopes_of(SRC);
    let scopes = scopes.borrow();
    let leaf = &scopes.defs["lone"];
    let mut leaves = 0;
    for (path, def) in &scopes.defs {
        if &**def == "leaf_unit" {
            leaves += 1;
            assert!(Rc::ptr_eq(def, leaf), "{path}");
        }
        if let Some(up) = scopes.parents.get(&**path) {
            // The record of the instantiation names the same definition.
            assert!(Rc::ptr_eq(&up.def, def), "{path}");
        }
    }
    assert_eq!(leaves, 9);
    let mut names: Vec<&str> = scopes.def_names.iter().map(|n| &**n).collect();
    names.sort_unstable();
    assert_eq!(names, ["branch_unit", "leaf_unit", "top"]);
}

#[test]
fn a_child_is_found_by_its_name_below_the_parent() {
    let scopes = scopes_of(SRC);
    let scopes = scopes.borrow();
    assert_eq!(scopes.child_named("", "cluster_1"), Some("cluster_1"));
    assert_eq!(scopes.child_named("", "child_0"), None);
    assert_eq!(scopes.child_named("cluster_1", "child_0"), Some("child_0"));
    assert_eq!(scopes.child_named("cluster_1", "g[1].u"), Some("g[1].u"));
    assert_eq!(scopes.child_named("cluster_1", "cluster_1"), None);
    assert_eq!(scopes.child_named("cluster_1.child_0", "child_0"), None);
    assert_eq!(UpwardScopes::child_leaf("a.b", "a.b.c"), "c");
    assert_eq!(UpwardScopes::child_leaf("", "a.b"), "a.b");
}
