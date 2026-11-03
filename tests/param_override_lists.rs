//! A parameter override list must fit the definition it instantiates
//! (§23.10.2), wherever the instance and its definition are written. The
//! fuller behaviour, with exit status and `--no-strict`, is pinned in xezim's
//! `tests/hierarchy/param_override_lists.rs`.

fn elaborate(sources: &[&str]) -> Result<xezim_core::ElaboratedModule, String> {
    let names: Vec<String> = (0..sources.len()).map(|i| format!("f{i}.sv")).collect();
    let sources: Vec<String> = sources.iter().map(|s| s.to_string()).collect();
    xezim_core::parse_and_elaborate_multi(&sources, Some("t"), &[], &names, &[]).map(|r| r.1)
}

const CHILD: &str = "module c #(parameter int A = 0) (output int y); assign y = A; endmodule\n";

#[track_caller]
fn rejected(sources: &[&str], needle: &str) {
    let e = elaborate(sources).err().expect("must be rejected");
    assert!(e.contains(needle), "no '{needle}' in: {e}");
}

#[test]
fn excess_ordered_value_in_another_file() {
    rejected(
        &[CHILD, "module t; int y; c #(1, 2) u (.y(y)); endmodule\n"],
        "has 2 ordered parameter values, but 'c' accepts 1",
    );
}

#[test]
fn name_given_twice_in_another_file() {
    rejected(
        &[
            CHILD,
            "module t; int y; c #(.A(1), .A(2)) u (.y(y)); endmodule\n",
        ],
        "sets parameter 'A' more than once",
    );
}

#[test]
fn name_that_is_not_a_parameter_in_another_file() {
    rejected(
        &[CHILD, "module t; int y; c #(.Z(1)) u (.y(y)); endmodule\n"],
        "names 'Z'",
    );
}

#[test]
fn local_body_parameter_by_name_says_why() {
    let child = "module c #(parameter int A = 0) (output int y); parameter int B = 3; assign y = A + B; endmodule\n";
    rejected(
        &[child, "module t; int y; c #(.B(1)) u (.y(y)); endmodule\n"],
        "is local (§6.20.1)",
    );
}

#[test]
fn inside_a_taken_generate_branch_only() {
    let bad = "module t; int y; if (1) begin : g c #(1, 2) u (.y(y)); end endmodule\n";
    rejected(&[CHILD, bad], "accepts 1");
    let untaken = "module t; int y; if (0) begin : g c #(1, 2) u (.y(y)); end endmodule\n";
    elaborate(&[CHILD, untaken]).expect("an untaken branch is not built");
}

#[test]
fn ordered_values_bind_to_body_parameters_without_a_header() {
    let child = "module c (output int y); parameter A = 0, B = 0; assign y = A + B; endmodule\n";
    elaborate(&[child, "module t; int y; c #(1, 2) u (.y(y)); endmodule\n"]).expect("legal");
}

/// §27.3: a `generate ... endgenerate` region adds no scope, so a parameter
/// in one is a body parameter with an ordered slot.
#[test]
fn ordered_values_bind_to_body_parameters_in_a_generate_region() {
    let child =
        "module c (output int y); generate parameter A = 0; endgenerate assign y = A; endmodule\n";
    elaborate(&[child, "module t; int y; c #(7) u (.y(y)); endmodule\n"]).expect("legal");
    rejected(
        &[child, "module t; int y; c #(7, 8) u (.y(y)); endmodule\n"],
        "accepts 1",
    );
}

#[test]
fn excess_ordered_value_counts_a_type_parameter_as_a_slot() {
    let child = "module c #(parameter type T = int, parameter int A = 0) (output int y); T v = A; assign y = v; endmodule\n";
    rejected(
        &[
            child,
            "module t; int y; c #(byte, 1, 2) u (.y(y)); endmodule\n",
        ],
        "accepts 2",
    );
    elaborate(&[
        child,
        "module t; int y; c #(byte, 1) u (.y(y)); endmodule\n",
    ])
    .expect("legal");
}

/// Only one of two same-named definitions survives (§3.3), so a list written
/// for the other cannot be judged, whichever kinds they are.
#[test]
fn a_redefined_name_is_not_judged() {
    let first = "interface i #(parameter int A = 0); int v = A; endinterface\n";
    let second = "interface i; int v; endinterface\n";
    let top = "module t; i #(5) u (); endmodule\n";
    elaborate(&[first, second, top]).expect("interface over interface");
    let module = "module i; int v; endmodule\n";
    elaborate(&[first, module, top]).expect("module over interface");
}

/// The record of redefined names lasts one elaboration: a later design on the
/// same thread is checked in full.
#[test]
fn a_redefinition_does_not_reach_a_later_elaboration() {
    let again = "module c (output int y); assign y = 1; endmodule\n";
    let top = "module t; int y; c #(1, 2) u (.y(y)); endmodule\n";
    elaborate(&[CHILD, again, top]).expect("not judged");
    rejected(&[CHILD, top], "accepts 1");
}
