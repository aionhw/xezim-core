//! §3.13, §6.18: a scope's type-name space holds one typedef or class per name.
//! Forward typedefs never count, and identical typedefs in different
//! command-line files emit a warning and keep the first; different text or
//! definitions in the same file are errors.

fn elaborate(sources: &[&str], files: &[&str]) -> Result<(), String> {
    let sources: Vec<String> = sources.iter().map(|s| s.to_string()).collect();
    let files: Vec<String> = files.iter().map(|s| s.to_string()).collect();
    xezim_core::parse_and_elaborate_multi(&sources, Some("top"), &[], &files, &[]).map(|_| ())
}

fn error_of(src: &str) -> String {
    elaborate(&[src], &["dup.sv"]).expect_err("a duplicate typedef is an error")
}

#[test]
fn duplicate_typedef_in_unit_module_package_and_class_collision() {
    let e = error_of(
        "typedef logic [7:0] t;
typedef logic [15:0] t;
module top; t v; endmodule
",
    );
    assert!(
        e.contains("dup.sv:2:22: error: duplicate definition of typedef 't' in the compilation unit: it is already defined at dup.sv:1:21"),
        "{e}"
    );

    let e = error_of(
        "typedef logic [7:0] t;
typedef logic [7:0] t;
module top; t v; endmodule
",
    );
    assert!(
        e.contains(
            "dup.sv:2:21: error: duplicate definition of typedef 't' in the compilation unit"
        ),
        "{e}"
    );

    let e = error_of(
        "module top;
  typedef logic [7:0] t;
  typedef logic [15:0] t;
  t v;
endmodule
",
    );
    assert!(e.contains("typedef 't' in module 'top'"), "{e}");

    let e = error_of(
        "package p;
  typedef logic [7:0] t;
  typedef logic [15:0] t;
endpackage
module top; endmodule
",
    );
    assert!(e.contains("typedef 't' in package 'p'"), "{e}");

    let e = error_of(
        "typedef int c;
class c; int x; endclass
module top; endmodule
",
    );
    assert!(
        e.contains("duplicate definition of class 'c' in the compilation unit"),
        "{e}"
    );
}

#[test]
fn differing_cross_file_typedefs_error_and_identical_cross_file_warn() {
    let e = elaborate(
        &[
            "typedef logic [7:0] t;\nmodule a; t v; endmodule\n",
            "typedef logic [15:0] t;\nmodule top; t v; a ua(); endmodule\n",
        ],
        &["a.sv", "b.sv"],
    )
    .expect_err("differing cross-file typedefs must fail");
    assert!(
        e.contains("b.sv:1:22: error: duplicate definition of typedef 't'"),
        "{e}"
    );
    assert!(e.contains("already defined at a.sv:1:21"), "{e}");

    let e = elaborate(
        &[
            "typedef int c;\n",
            "class c; int x; endclass\nmodule top; endmodule\n",
        ],
        &["a.sv", "b.sv"],
    )
    .expect_err("typedef and class of the same name across files must fail");
    assert!(
        e.contains("b.sv:1:7: error: duplicate definition of class 'c'"),
        "{e}"
    );

    elaborate(
        &[
            "typedef enum {RED, GREEN} color_t;\ntypedef struct packed { logic [3:0] a; } s_t;\nmodule a; color_t c; s_t s; endmodule\n",
            "typedef enum { RED, GREEN } color_t;\ntypedef struct packed {\n  logic [3:0] a;\n} s_t;\nmodule top; color_t c; s_t s; a ua(); endmodule\n",
        ],
        &["same_a.sv", "same_b.sv"],
    )
    .expect("identical cross-file typedefs warn and pass");
}

#[test]
fn forward_typedefs_and_distinct_scopes_stay_legal() {
    elaborate(
        &["typedef class c;
typedef class c;
typedef c;
class c; int x = 3; endclass
typedef struct s_t;
typedef struct { int a; } s_t;
typedef s_t;
typedef int tt;
package p1; typedef logic [3:0] tt; endpackage
package p2; typedef logic [5:0] tt; endpackage
module top;
  import p1::*;
  typedef logic [8:0] tt;
  tt v;
  c o = new;
  s_t s;
  if (1) begin : g1 typedef logic [1:0] tt; tt w; end
  else begin : g2 typedef logic [2:0] tt; tt w; end
  for (genvar i = 0; i < 2; i++) begin : g typedef logic [i:0] tt; tt w; end
endmodule
"],
        &["legal.sv"],
    )
    .expect("forward typedefs and separate scopes must pass");
}
