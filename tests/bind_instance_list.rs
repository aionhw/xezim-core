//! §23.11: a bind instantiation can list several instances, and each one is
//! bound into the target, with the directive's parameter values.

fn elaborate(src: &str, top: &str) -> xezim_core::ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[src.to_string()],
        Some(top),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .expect("elaborate")
    .1
}

const CHILD: &str = "module c #(parameter int A = 0) (output int y); assign y = A; endmodule\n";

fn a_of(m: &xezim_core::ElaboratedModule, inst: &str) -> Option<i64> {
    m.parameters
        .get(&format!("{inst}.A"))
        .and_then(|v| v.to_i64())
}

#[test]
fn unit_scope_instance_list_binds_every_instance() {
    let src = format!("{CHILD}module t; endmodule\nbind t c #(3) a(), b();\n");
    let m = elaborate(&src, "t");
    assert_eq!(a_of(&m, "a"), Some(3));
    assert_eq!(a_of(&m, "b"), Some(3));
}

#[test]
fn instance_list_into_an_instance_path() {
    let src = format!(
        "{CHILD}module t; endmodule\nmodule top; t u1 (); t u2 (); endmodule\nbind top.u1 c #(4) a(), b();\n"
    );
    let m = elaborate(&src, "top");
    assert_eq!(a_of(&m, "u1.a"), Some(4));
    assert_eq!(a_of(&m, "u1.b"), Some(4));
    assert_eq!(a_of(&m, "u2.a"), None);
}

#[test]
fn module_scope_instance_list() {
    let src = format!(
        "{CHILD}module t; endmodule\nmodule top; t u (); bind t c #(5) a(), b(); endmodule\n"
    );
    let m = elaborate(&src, "top");
    assert_eq!(a_of(&m, "u.a"), Some(5));
    assert_eq!(a_of(&m, "u.b"), Some(5));
}

#[test]
fn single_instance_guard() {
    let src = format!("{CHILD}module t; endmodule\nbind t c #(3) a();\n");
    assert_eq!(a_of(&elaborate(&src, "t"), "a"), Some(3));
}
