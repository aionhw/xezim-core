//! §3.13, §26.2: the package name space holds one declaration per name across
//! all compilation units, so a second `package P` in one file or across files
//! is an error, located at the second definition and naming the first.

fn elaborate(sources: &[&str], files: &[&str]) -> Result<(), String> {
    let sources: Vec<String> = sources.iter().map(|s| s.to_string()).collect();
    let files: Vec<String> = files.iter().map(|s| s.to_string()).collect();
    xezim_core::parse_and_elaborate_multi(&sources, Some("top"), &[], &files, &[]).map(|_| ())
}

fn error_of(src: &str) -> String {
    elaborate(&[src], &["dup.sv"]).expect_err("a duplicate package definition is an error")
}

#[test]
fn duplicate_package_in_one_file() {
    let e = error_of(
        "package p; localparam int K = 1; endpackage
package p; localparam int K = 2; endpackage
module top; initial $display(\"K=%0d\", p::K); endmodule
",
    );
    assert!(
        e.contains("dup.sv:2:9: error: duplicate definition of package 'p': it is already defined at dup.sv:1:9"),
        "{e}"
    );
    assert!(e.contains("IEEE 1800-2017 §3.13, §26.2"), "{e}");
}

#[test]
fn duplicate_package_across_files() {
    let e = elaborate(
        &[
            "package p; localparam int K = 1; endpackage\n",
            "package p; localparam int K = 2; endpackage\nmodule top; initial $display(\"K=%0d\", p::K); endmodule\n",
        ],
        &["first.sv", "second.sv"],
    )
    .expect_err("package names share one global name space across files");
    assert!(e.contains("second.sv:1:9: error: duplicate definition of package 'p': it is already defined at first.sv:1:9"), "{e}");
}

#[test]
fn package_with_same_named_other_kinds_and_same_inner_names_is_legal() {
    elaborate(
        &["package pm; localparam int K = 1; endpackage
module pm; endmodule
package pi; localparam int K = 2; endpackage
interface pi; logic a; endinterface
package pc; localparam int K = 3; endpackage
class pc; int v; endclass
package pt; localparam int K = 4; endpackage
typedef int pt;
package p1; localparam int K = 10; class c; int v; endclass endpackage
package p2; localparam int K = 20; class c; int v; endclass endpackage
module top; pi u_i(); pm u_m(); endmodule
"],
        &["legal.sv"],
    )
    .expect("separate name spaces and separate package scopes must pass");
}
