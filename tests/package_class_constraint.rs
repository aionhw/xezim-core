//! IEEE 1800-2017 §8.23 / §18.3 / §26.3: a package class can be the
//! root of a scoped constraint reference; unknown roots remain errors.
#[test]
fn package_classes_are_known_constraint_roots() {
    for import in [
        "import protocol_pkg::*;",
        "import protocol_pkg::message_codes;",
    ] {
        let source = format!(
            "package protocol_pkg; class message_codes; localparam int REQUEST = 7; endclass endpackage\n\
             module top; {import}\n\
             class request; rand int code; constraint legal_code {{ code == message_codes::REQUEST; }} endclass\n\
             request r; endmodule"
        );
        xezim_core::parse_and_elaborate_multi(&[source], Some("top"), &[], &[], &[])
            .expect("imported class names a scoped constant");
    }
}

#[test]
fn unknown_constraint_roots_are_still_rejected() {
    let source = "module top; class request; rand int code; constraint c { code == missing_codes::REQUEST; } endclass endmodule";
    let err =
        match xezim_core::parse_and_elaborate_multi(&[source.into()], Some("top"), &[], &[], &[]) {
            Ok(_) => panic!("accepted an undeclared constraint root"),
            Err(err) => err,
        };
    assert!(
        err.contains("Undeclared identifier 'missing_codes' in class constraint"),
        "{err}"
    );
}
