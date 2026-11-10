//! IEEE 1800-2023 §26.3: an import names a package the design declares. An
//! instantiated module's import of an undeclared package is an error at that
//! import, as it is for the top module's; the inlining path skipped such an
//! import, so the error surfaced later as an undeclared name, or not at all
//! when nothing from the package was used (#937). The built-in `std` package
//! (§9.7, §18.13) may be imported anywhere. Expected outcomes are the
//! reference simulator's.

fn elaborate(source: &str) -> Result<(), String> {
    xezim_core::parse_and_elaborate_multi(
        &[source.to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .map(|_| ())
}

#[test]
fn a_submodule_import_of_an_undeclared_package_is_an_error_at_the_import() {
    let err = elaborate(
        r#"
module sub;
  import NOPE_PKG::*;
  initial $display("sub");
endmodule
module top;
  sub u();
endmodule
"#,
    )
    .expect_err("an import of an undeclared package must not elaborate");
    assert!(err.contains("Package 'NOPE_PKG' not found"), "{err}");
    assert!(
        err.contains("top.sv:3:"),
        "the error names the import: {err}"
    );
}

#[test]
fn the_import_error_comes_before_a_use_of_the_missing_package() {
    let err = elaborate(
        r#"
module sub;
  import NOPE_PKG::P;
  int x;
  initial x = P;
endmodule
module top;
  sub u();
endmodule
"#,
    )
    .expect_err("an import of an undeclared package must not elaborate");
    assert!(err.contains("Package 'NOPE_PKG' not found"), "{err}");
    assert!(!err.contains("Undeclared identifier"), "{err}");
}

#[test]
fn a_header_import_of_an_undeclared_package_is_an_error() {
    let err = elaborate(
        r#"
module sub import NOPE_PKG::*; (input logic a);
endmodule
module top;
  logic a;
  sub u(.a(a));
endmodule
"#,
    )
    .expect_err("an import of an undeclared package must not elaborate");
    assert!(err.contains("Package 'NOPE_PKG' not found"), "{err}");
}

#[test]
fn the_std_package_may_be_imported_by_the_top_and_by_a_submodule() {
    elaborate(
        r#"
module sub;
  import std::*;
  initial $display("sub");
endmodule
module top;
  import std::*;
  sub u();
endmodule
"#,
    )
    .unwrap_or_else(|e| panic!("{e}"));
}

#[test]
fn a_submodule_import_of_a_declared_package_still_elaborates() {
    elaborate(
        r#"
package p; localparam int P = 4; endpackage
module sub;
  import p::*;
  int x;
  initial x = P;
endmodule
module top;
  sub u();
endmodule
"#,
    )
    .unwrap_or_else(|e| panic!("{e}"));
}
