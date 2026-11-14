//! §23.11, §23.8: a bound instance is instantiated in its target, so the
//! target can name it in a hierarchical reference, `a.y`, even though the
//! target's own source does not declare `a`. The undeclared-name checks run
//! before compilation-unit binds are applied, so they must know those names.

fn elaborate(src: &str, top: &str) -> Result<xezim_core::ElaboratedModule, String> {
    xezim_core::parse_and_elaborate_multi(
        &[src.to_string()],
        Some(top),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .map(|r| r.1)
}

const CHILD: &str = "module c #(parameter int A = 0) (output int y); assign y = A; endmodule\n";

#[test]
fn target_is_the_top() {
    let src =
        format!("{CHILD}module t; int r; initial #1 r = a.y; endmodule\nbind t c #(3) a();\n");
    let m = elaborate(&src, "t").expect("bound instance name must resolve");
    assert!(m.signals.contains_key("a.y"), "no bound instance a");
}

#[test]
fn target_is_an_instance() {
    let src = format!(
        "{CHILD}module t; int r; initial #1 r = a.y; endmodule\n\
         module top; t u (); endmodule\nbind t c #(3) a();\n"
    );
    let m = elaborate(&src, "top").expect("bound instance name must resolve");
    assert!(m.signals.contains_key("u.a.y"), "no bound instance u.a");
}

#[test]
fn in_a_continuous_assign() {
    let src = format!("{CHILD}module t; int r; assign r = a.y; endmodule\nbind t c #(3) a();\n");
    elaborate(&src, "t").expect("bound instance name must resolve");
}

#[test]
fn a_name_no_bind_declares_is_still_undeclared() {
    let src =
        format!("{CHILD}module t; int r; initial #1 r = zz.y; endmodule\nbind t c #(3) a();\n");
    let e = elaborate(&src, "t").err().expect("zz must be rejected");
    assert!(e.contains("Undeclared identifier 'zz'"), "{e}");
}

/// §23.8: a top that is not the bind's target cannot name the bound instance;
/// the target's own processes can.
#[test]
fn another_top_cannot_name_the_bound_instance() {
    let src = format!(
        "{CHILD}module t; endmodule\nmodule other; int r; initial #1 r = a.y; endmodule\n\
         bind t c #(3) a();\n"
    );
    let e = elaborate(&src, "other")
        .err()
        .expect("other must not see a");
    assert!(e.contains("Undeclared identifier 'a'"), "{e}");
}
