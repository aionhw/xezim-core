//! IEEE 1800-2017 §13.5.2 / §26.3: ref-actual validation uses the
//! declaration the call names, including the caller's package scope.
fn elaborate(src: &str) -> Result<(), String> {
    xezim_core::parse_and_elaborate_multi(&[src.into()], Some("top"), &[], &[], &[]).map(|_| ())
}

#[test]
fn package_input_calls_ignore_another_packages_ref_signature() {
    elaborate(
        r#"package a;
  function automatic void route(ref int value); value++; endfunction
  task automatic send(ref int value); value++; endtask
endpackage
package b;
  function automatic void route(input int value); endfunction
  task automatic send(input int value); endtask
  function automatic void run(); route(7); endfunction
  task automatic run_task(); send(.value(7)); endtask
endpackage
module top;
  initial begin b::run(); b::run_task(); b::route(7); b::send(7); end
endmodule"#,
    )
    .expect("the callee has an input formal");
}

#[test]
fn package_ref_calls_still_reject_literals() {
    for (declaration, call) in [
        (
            "function automatic void route(ref int value); endfunction",
            "route(7);",
        ),
        (
            "function automatic void route(ref int value); endfunction",
            "route(.value(7));",
        ),
        ("task automatic route(ref int value); endtask", "route(7);"),
    ] {
        for qualified in [false, true] {
            let caller = if qualified {
                format!("module top; initial b::{call} endmodule")
            } else if declaration.starts_with("task") {
                format!("task automatic run(); {call} endtask endpackage\nmodule top; initial b::run(); endmodule")
            } else {
                format!("function automatic void run(); {call} endfunction endpackage\nmodule top; initial b::run(); endmodule")
            };
            let close = if qualified { "endpackage" } else { "" };
            let source = format!(
                "package a; function automatic void route(input int value); endfunction endpackage\npackage b; {declaration} {close}\n{caller}"
            );
            let err = elaborate(&source).expect_err("a ref actual must remain a variable");
            assert!(err.contains("Argument to `ref` formal 'value'"), "{err}");
        }
    }
}

#[test]
fn hierarchical_call_does_not_use_an_unrelated_bare_signature() {
    elaborate(
        r#"package a;
  function automatic void route(ref int value); value++; endfunction
endpackage
module child;
  function automatic void route(input int value); endfunction
endmodule
module top;
  child u();
  initial u.route(7);
endmodule"#,
    )
    .expect("a hierarchical callee is not the bare package function");
}

#[test]
fn object_variables_shadow_package_names_for_method_calls() {
    for body in [
        "C p; initial p.route(7);",
        "initial begin C p; p.route(7); end",
        "function automatic void run(C p); p.route(7); endfunction",
    ] {
        let source = format!(
            "package p; function automatic void route(ref int value); endfunction endpackage\n\
             class C; function void route(input int value); endfunction endclass\n\
             module top; {body} endmodule"
        );
        elaborate(&source).expect("an object receiver does not name the package");
    }
}
