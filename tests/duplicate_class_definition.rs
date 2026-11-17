//! §3.13, §8.3: a scope's name space holds one declaration per name, so a
//! second class of the same name in the compilation unit, a package, a
//! module or a class is an error, located at the second definition and
//! naming the first. All source files share one compilation unit. The same
//! name in different scopes stays legal.

fn elaborate(sources: &[&str], files: &[&str]) -> Result<(), String> {
    let sources: Vec<String> = sources.iter().map(|s| s.to_string()).collect();
    let files: Vec<String> = files.iter().map(|s| s.to_string()).collect();
    xezim_core::parse_and_elaborate_multi(&sources, Some("top"), &[], &files, &[]).map(|_| ())
}

fn error_of(src: &str) -> String {
    elaborate(&[src], &["dup.sv"]).expect_err("a duplicate class definition is an error")
}

#[test]
fn compilation_unit() {
    let e = error_of(
        "class c; int a; endclass
class c; int b; endclass
module top; c h; endmodule
",
    );
    assert!(
        e.contains(
            "dup.sv:2:7: error: duplicate definition of class 'c' in the compilation unit: \
             it is already defined at dup.sv:1:7"
        ),
        "{e}"
    );
}

#[test]
fn compilation_unit_across_files() {
    let e = elaborate(
        &[
            "class c; int a; endclass\n",
            "class c; int b; endclass\nmodule top; c h; endmodule\n",
        ],
        &["first.sv", "second.sv"],
    )
    .expect_err("the files share one compilation unit");
    assert!(e.contains("second.sv:1:7: error:"), "{e}");
    assert!(e.contains("already defined at first.sv:1:7"), "{e}");
}

#[test]
fn package_module_and_class_scopes() {
    let e = error_of(
        "package p;
  class c; int a; endclass
  class c; int b; endclass
endpackage
module top; endmodule
",
    );
    assert!(e.contains("class 'c' in package 'p'"), "{e}");

    let e = error_of(
        "module top;
  class c; int a; endclass
  class c; int b; endclass
endmodule
",
    );
    assert!(e.contains("class 'c' in module 'top'"), "{e}");

    let e = error_of(
        "class outer;
  class c; int a; endclass
  class c; int b; endclass
endclass
module top; endmodule
",
    );
    assert!(e.contains("class 'c' in class 'outer'"), "{e}");
}

#[test]
fn same_name_in_different_scopes_is_legal() {
    elaborate(
        &["typedef class c;
class c; int a; endclass
module c; endmodule
package p1; class c; int v; endclass endpackage
package p2; class c; int v; endclass endpackage
class outer;
  class c; int a; endclass
endclass
module other;
  class loc; int v; endclass
endmodule
module top;
  class loc; int v; endclass
  if (1) begin : g
    class gc; int v; endclass
  end else begin : g
    class gc; int w; endclass
  end
endmodule
"],
        &["legal.sv"],
    )
    .expect("no scope declares a class twice");
}
