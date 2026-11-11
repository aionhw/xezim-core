//! §23.10.1: a `defparam` can change only an overridable parameter. A
//! `localparam`, a body `parameter` of a module with a parameter port list
//! (local by §6.20.1) and a type parameter are not, wherever the `defparam`
//! and the definition are written. The per-file strict pass sees only a child
//! defined in the same file, so these cases check the elaboration-time rule.

fn elaborate(sources: &[&str]) -> Result<xezim_core::ElaboratedModule, String> {
    let names: Vec<String> = (0..sources.len()).map(|i| format!("f{i}.sv")).collect();
    let sources: Vec<String> = sources.iter().map(|s| s.to_string()).collect();
    xezim_core::parse_and_elaborate_multi(&sources, Some("t"), &[], &names, &[]).map(|r| r.1)
}

#[track_caller]
fn rejected(sources: &[&str], needle: &str) {
    let e = elaborate(sources).err().expect("must be rejected");
    assert!(e.contains(needle), "no '{needle}' in: {e}");
}

#[track_caller]
fn param(sources: &[&str], key: &str) -> Option<i64> {
    let m = elaborate(sources).expect("must elaborate");
    m.parameters.get(key).and_then(|v| v.to_i64())
}

const LOCALPARAM: &str =
    "module c (output int y); parameter int A = 0; localparam int L = 1; assign y = L; endmodule\n";
const BODY_UNDER_HEADER: &str = "module c #(parameter int A = 0) (output int y); parameter int L = 1; assign y = L; endmodule\n";
const PARENT: &str = "module t; int y; c u (y); defparam u.L = 9; endmodule\n";

#[test]
fn localparam_in_another_file() {
    rejected(
        &[LOCALPARAM, PARENT],
        "defparam cannot override 'L' of module 'c'",
    );
}

#[test]
fn local_body_parameter_in_another_file_says_why() {
    rejected(&[BODY_UNDER_HEADER, PARENT], "is local (§6.20.1)");
}

#[test]
fn rejection_names_the_defparam_location() {
    rejected(&[BODY_UNDER_HEADER, PARENT], "f1.sv:1:");
}

#[test]
fn deeper_path_from_another_module() {
    let mid = "module m; int y; c u (y); endmodule\n";
    let top = "module t; m k (); defparam k.u.L = 9; endmodule\n";
    rejected(
        &[BODY_UNDER_HEADER, mid, top],
        "defparam cannot override 'L'",
    );
}

#[test]
fn type_parameter_in_another_file() {
    let child =
        "module c #(parameter type T = int) (output int y); assign y = $bits(T); endmodule\n";
    rejected(
        &[
            child,
            "module t; int y; c u (y); defparam u.T = 8; endmodule\n",
        ],
        "defparam cannot override type parameter 'T'",
    );
}

#[test]
fn header_parameter_in_another_file_is_applied() {
    let parent = "module t; int y; c u (y); defparam u.A = 7; endmodule\n";
    assert_eq!(param(&[BODY_UNDER_HEADER, parent], "u.A"), Some(7));
}

#[test]
fn body_parameter_without_header_is_applied() {
    let parent = "module t; int y; c u (y); defparam u.A = 7; endmodule\n";
    assert_eq!(param(&[LOCALPARAM, parent], "u.A"), Some(7));
}
