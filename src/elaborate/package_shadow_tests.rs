//! IEEE 1800-2023 §26.2/§26.3: package shadow checks need local-name
//! intersections only when a relevant package or wildcard import exists.

use super::*;

fn shadows(
    source: &str,
) -> (
    std::collections::HashSet<String>,
    std::collections::HashSet<String>,
) {
    let parsed = crate::parse(source);
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
    let mut defs = HashMap::default();
    let mut module = None;
    for description in &parsed.source.descriptions {
        match description {
            crate::ast::Description::Package(package) => {
                defs.insert(package.name.name.clone(), Definition::Package(package));
            }
            crate::ast::Description::Module(m) => {
                defs.insert(m.name.name.clone(), Definition::Module(m));
                module = Some(m);
            }
            _ => {}
        }
    }
    let module = module.expect("module expected");
    (
        compute_wildcard_shadowed(&module.items, &module.params, &defs),
        compute_foreign_package_names(&module.items, &defs),
    )
}

#[test]
fn definitions_without_packages_have_no_package_collisions() {
    let (wildcard, foreign) =
        shadows("module top; int value; function int f(); return value; endfunction endmodule");
    assert!(wildcard.is_empty() && foreign.is_empty());
}

#[test]
fn explicit_imports_do_not_enter_the_wildcard_shadow_set() {
    let (wildcard, foreign) = shadows(
        "package p; int value; endpackage module top; import p::value; int value; endmodule",
    );
    assert!(wildcard.is_empty() && foreign.is_empty());
}

#[test]
fn importing_every_package_leaves_no_foreign_package_names() {
    let (wildcard, foreign) = shadows(
        "package p; int value; endpackage package q; int other; endpackage module top; import p::value; import q::*; int value; int other; endmodule",
    );
    assert_eq!(wildcard, ["other".to_string()].into_iter().collect());
    assert!(foreign.is_empty());
}

#[test]
fn unimported_package_members_still_intersect_with_local_names() {
    let (wildcard, foreign) = shadows(
        "package p; int value; int absent; endpackage module top; int value; int different; endmodule",
    );
    assert!(wildcard.is_empty());
    assert_eq!(foreign, ["value".to_string()].into_iter().collect());
}

#[test]
fn an_imported_package_does_not_hide_an_unimported_package_collision() {
    let (_, foreign) = shadows(
        "package p; int value; endpackage package q; int value; endpackage module top; import p::*; int value; endmodule",
    );
    assert_eq!(foreign, ["value".to_string()].into_iter().collect());
}

#[test]
fn wildcard_shadowing_keeps_the_existing_declaration_order_rule() {
    let (wildcard, foreign) = shadows(
        "package p; int value; int later; parameter int SIZE = 1; endpackage module top #(parameter int SIZE = 2); import p::*; int value; initial value = 1; int later; endmodule",
    );
    assert_eq!(
        wildcard,
        ["value".to_string(), "SIZE".to_string()]
            .into_iter()
            .collect()
    );
    assert!(foreign.is_empty());
}
