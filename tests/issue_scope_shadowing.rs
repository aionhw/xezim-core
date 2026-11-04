//! IEEE 1800-2023 §23.9, §6.19.3, §26.3, §35.5.4: scope-local declarations.

fn elaborate(source: &str) -> Result<xezim_core::ElaboratedModule, String> {
    xezim_core::parse_and_elaborate_multi(
        &[source.to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .map(|(_, design)| design)
}

#[test]
fn integer_function_formal_shadows_enum_member_677() {
    elaborate(
        r#"
module top;
  typedef enum {low, high} range_t;
  range_t high_value;
  function automatic void set_limit(int high); high = 1024; endfunction
  initial set_limit(0);
endmodule
"#,
    )
    .expect("integer formal is not an enum");
}

#[test]
fn package_dpi_local_names_do_not_collide_676() {
    elaborate(
        r#"
package first_pkg;
  import "DPI-C" context c_first = function void callback();
endpackage
package second_pkg;
  import "DPI-C" context c_second = function void callback();
endpackage
module top; initial $finish; endmodule
"#,
    )
    .expect("separate package declarations");
}

#[test]
fn integer_task_and_block_locals_shadow_enum_members_677() {
    elaborate(
        r#"
module top;
  typedef enum {low, high} range_t;
  task automatic set_limit(int high); high = 1024; endtask
  initial begin
    begin int high; high = 1024; end
    for (int high = 0; high < 1; high++) begin high = 1024; end
    set_limit(0);
  end
endmodule
"#,
    )
    .expect("local integers shadow enum members");
}

#[test]
fn enum_checks_resume_after_leaving_shadowing_block_677() {
    let error = elaborate(
        r#"
module top;
  typedef enum {low, high} range_t;
  range_t value;
  initial begin
    begin int value; value = 1024; end
    value = 1024;
  end
endmodule
"#,
    )
    .unwrap_err();
    assert!(error.contains("not a declared member"), "{error}");
}

#[test]
fn enum_formal_still_rejects_nonmember_assignment_677() {
    let error = elaborate(
        r#"
module top;
  typedef enum {low, high} range_t;
  function void f(range_t arg); arg = 1024; endfunction
endmodule
"#,
    )
    .unwrap_err();
    assert!(error.contains("not a declared member"), "{error}");
}

#[test]
fn dpi_default_c_linkage_survives_package_scoping_676() {
    let design = elaborate(
        r#"
package p; import "DPI-C" function int callback(); endpackage
package q; import "DPI-C" function int callback(); endpackage
module top; endmodule
"#,
    )
    .expect("same foreign function may be imported in two packages");
    for key in ["p::callback", "q::callback"] {
        assert_eq!(design.dpi_imports[key].c_name, "callback");
    }
}

#[test]
fn conflicting_dpi_declarations_in_one_scope_still_fail_676() {
    let error = elaborate(
        r#"
package p;
  import "DPI-C" c_first = function int callback();
  import "DPI-C" c_second = function int callback();
endpackage
module top; endmodule
"#,
    )
    .unwrap_err();
    assert!(error.contains("Conflicting DPI import"), "{error}");
}
