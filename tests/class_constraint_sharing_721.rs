//! aionhw/xezim#721: a class declared in a module is elaborated once per
//! instance of the module (§8.3, §23.6). The copies name the class's own
//! members in their constraint blocks, so every copy holds the block of the
//! declaration instead of a copy of its own.

use std::sync::Arc;
use xezim_core::ElaboratedModule;

fn elaborate(src: &str) -> ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[src.to_string()],
        Some("top"),
        &[],
        &["t.sv".to_string()],
        &[],
    )
    .map(|(_, m)| m)
    .expect("elaborates")
}

fn block<'a>(
    m: &'a ElaboratedModule,
    class: &str,
    name: &str,
) -> &'a Arc<xezim_core::ast::decl::ClassConstraint> {
    m.classes
        .get(class)
        .unwrap_or_else(|| panic!("class {class}"))
        .constraints
        .get(name)
        .unwrap_or_else(|| panic!("constraint {name} of {class}"))
}

/// §18.5: the block of every instance's copy is the same allocation.
#[test]
fn instances_of_a_module_share_the_constraint_blocks_of_its_class() {
    let mut src = String::from(
        "module worker #(parameter int LIMIT = 3);
           class packet;
             rand bit [7:0] value;
             rand bit [7:0] other;
             constraint permitted { value inside {[LIMIT-2:LIMIT]}; }
             constraint ordered { value < other; other != 8'd200; }
           endclass
         endmodule
         module top;\n",
    );
    for i in 0..16 {
        src.push_str(&format!("worker #(.LIMIT({})) u{i}();\n", i + 3));
    }
    src.push_str("endmodule\n");
    let m = elaborate(&src);
    for name in ["permitted", "ordered"] {
        let first = block(&m, "u0.packet", name);
        assert!(!first.items.is_empty());
        for i in 1..16 {
            assert!(
                Arc::ptr_eq(first, block(&m, &format!("u{i}.packet"), name)),
                "u{i}.packet holds its own copy of {name}"
            );
        }
        // One per class entry (two entries name the first copy: the scoped
        // key and the bare class name) plus the declaration's.
        assert!(Arc::strong_count(first) >= 16);
    }
    assert!(!Arc::ptr_eq(
        block(&m, "u0.packet", "permitted"),
        block(&m, "u0.packet", "ordered")
    ));
}

/// §8.3: nested instances and a class with a base share per declaration.
#[test]
fn nested_instances_and_derived_classes_share_per_declaration() {
    let m = elaborate(
        "module leaf;
           class base; rand int lo; constraint low { lo > 4; } endclass
           class derived extends base; rand int hi; constraint high { hi > lo; } endclass
         endmodule
         module mid; leaf a(); leaf b(); endmodule
         module top; mid m0(); mid m1(); endmodule",
    );
    let paths = ["m0.a", "m0.b", "m1.a", "m1.b"];
    for (class, name) in [("base", "low"), ("derived", "high")] {
        let first = block(&m, &format!("{}.{class}", paths[0]), name);
        for p in &paths[1..] {
            assert!(Arc::ptr_eq(first, block(&m, &format!("{p}.{class}"), name)));
        }
    }
    assert!(!Arc::ptr_eq(
        block(&m, "m0.a.base", "low"),
        block(&m, "m0.a.derived", "high")
    ));
}

/// §18.5.1: an out-of-block body is installed in the class it names; the
/// block of another class with the same constraint name keeps its own.
#[test]
fn an_external_constraint_body_is_installed_in_its_own_class() {
    let m = elaborate(
        "package p;
           class pa; rand int x; extern constraint c; endclass
           constraint pa::c { x > 7; }
           class pb; rand int x; constraint c { x < 3; x > -3; } endclass
         endpackage
         module top; import p::*; pa ha; pb hb; endmodule",
    );
    let class = |n: &str| {
        m.classes
            .values()
            .find(|c| c.name == n || c.name.ends_with(&format!("::{n}")))
            .unwrap_or_else(|| panic!("class {n}"))
    };
    let ca = &class("pa").constraints["c"];
    assert!(ca.has_body);
    assert_eq!(ca.items.len(), 1);
    assert_eq!(class("pb").constraints["c"].items.len(), 2);
}
