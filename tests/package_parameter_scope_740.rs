//! IEEE 1800-2023 §23.10, §26.3: an inlined instance sees the package,
//! `$unit` and top-module parameters it names, with its own parameters and
//! those of the instances above it hiding them (#740). Each design here is
//! padded with package parameters no module names, so a scope built from
//! only what its definition spells must still find every name it reads.

use xezim_core::ElaboratedModule;

/// `count` filler parameters no module names.
fn filler(count: usize) -> String {
    (0..count)
        .map(|i| format!("  localparam int FILL_{i} = {i};\n"))
        .collect()
}

fn elaborate(source: &str) -> ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[source.to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .unwrap_or_else(|e| panic!("{e}\n{source}"))
    .1
}

fn param(design: &ElaboratedModule, name: &str) -> i64 {
    design
        .parameters
        .get(name)
        .unwrap_or_else(|| panic!("no parameter {name}"))
        .to_i64()
        .unwrap_or_else(|| panic!("{name} is not an integer"))
}

fn width(design: &ElaboratedModule, name: &str) -> u32 {
    design
        .signals
        .get(name)
        .unwrap_or_else(|| panic!("no signal {name}"))
        .width
}

/// A module parameter hides the package parameter of the same name for its
/// bare spelling, the scoped spelling still reads the package's, and an
/// override from the parent hides the default.
#[test]
fn own_parameter_hides_the_package_parameter_of_its_name() {
    let source = format!(
        "package pk;\n  localparam int A = 3;\n{}endpackage\n\
         module leaf import pk::*; #(parameter int A = 2) ();\n\
         \x20 logic [A-1:0] own;\n\
         \x20 logic [pk::A-1:0] pkg;\n\
         \x20 localparam int SUM = A + pk::A;\n\
         endmodule\n\
         module mid #(parameter int A = 9) ();\n\
         \x20 leaf d();\n\
         \x20 leaf #(.A(A + 1)) o();\n\
         endmodule\n\
         module top;\n  mid m();\n  mid #(.A(5)) n();\nendmodule\n",
        filler(64)
    );
    let d = elaborate(&source);
    assert_eq!(width(&d, "m.d.own"), 2);
    assert_eq!(width(&d, "m.d.pkg"), 3);
    assert_eq!(param(&d, "m.d.SUM"), 5);
    assert_eq!(width(&d, "m.o.own"), 10);
    assert_eq!(param(&d, "m.o.SUM"), 13);
    assert_eq!(width(&d, "n.o.own"), 6);
    assert_eq!(width(&d, "n.o.pkg"), 3);
    assert_eq!(param(&d, "n.o.SUM"), 9);
}

/// A parameter read through a wildcard import and one read by its scoped
/// name, in a header localparam, a port, a variable and a body localparam,
/// two levels down.
#[test]
fn wildcard_import_and_scoped_name() {
    let source = format!(
        "package pk;\n{}  localparam int A = 3;\n  localparam int B = 5;\n{}endpackage\n\
         module leaf import pk::*; #(parameter int W = 1, localparam int S = A + pk::B + W)\n\
         \x20 (output logic [A+W-1:0] y);\n\
         \x20 logic [pk::B-1:0] v;\n\
         \x20 localparam int T = S * A;\n\
         \x20 assign y = '0;\n\
         endmodule\n\
         module wrap #(parameter int W = 1) (output logic [15:0] y);\n\
         \x20 leaf #(.W(W)) u(.y());\n\
         endmodule\n\
         module top;\n\
         \x20 for (genvar i = 0; i < 4; i++) begin : g\n    wrap #(.W(i + 1)) u(.y());\n  end\n\
         endmodule\n",
        filler(40),
        filler(40).replace("FILL_", "MORE_")
    );
    let d = elaborate(&source);
    for i in 0..4i64 {
        let w = i + 1;
        let p = format!("g[{i}].u.u");
        assert_eq!(param(&d, &format!("{p}.S")), 8 + w, "{p}.S");
        assert_eq!(param(&d, &format!("{p}.T")), 3 * (8 + w), "{p}.T");
        assert_eq!(width(&d, &format!("{p}.y")), (3 + w) as u32, "{p}.y");
        assert_eq!(width(&d, &format!("{p}.v")), 5, "{p}.v");
    }
}

/// A `$unit` parameter, next to a package parameter of another name and a
/// package typedef sized by a package parameter the module never spells.
#[test]
fn unit_parameter_and_package_typedef() {
    let source = format!(
        "localparam int U = 6;\n\
         package pk;\n{}  localparam int HIDDEN_W = 11;\n\
         \x20 typedef logic [HIDDEN_W-1:0] word_t;\nendpackage\n\
         module leaf;\n\
         \x20 logic [U-1:0] v;\n\
         \x20 pk::word_t w;\n\
         \x20 localparam int UW = U + $bits(pk::word_t);\n\
         endmodule\n\
         module top;\n  leaf a();\n  leaf b();\nendmodule\n",
        filler(64)
    );
    let d = elaborate(&source);
    for p in ["a", "b"] {
        assert_eq!(width(&d, &format!("{p}.v")), 6);
        assert_eq!(width(&d, &format!("{p}.w")), 11);
        assert_eq!(param(&d, &format!("{p}.UW")), 17);
    }
}

/// §23.11: a bound instance's override is evaluated in the target's scope,
/// and names a package parameter the target's definition never spells.
#[test]
fn bind_override_names_a_package_parameter_its_target_does_not() {
    let source = format!(
        "package pk;\n{}  localparam int C = 7;\nendpackage\n\
         module probe #(parameter int K = 1) ();\n  logic [K-1:0] s;\nendmodule\n\
         module leaf #(parameter int W = 1) ();\n  logic [W-1:0] q;\nendmodule\n\
         module top;\n  leaf #(.W(2)) a();\n  leaf #(.W(3)) b();\nendmodule\n\
         bind leaf probe #(.K(pk::C + W)) p();\n",
        filler(64)
    );
    let d = elaborate(&source);
    assert_eq!(width(&d, "a.p.s"), 9);
    assert_eq!(width(&d, "b.p.s"), 10);
}

/// A package parameter named only inside a constant function: one declared
/// in the module, and one of the package that reads its own parameter.
#[test]
fn name_spelled_only_inside_a_constant_function() {
    let source = format!(
        "package pk;\n{}  localparam int D = 4;\n  localparam int E = 9;\n\
         \x20 function automatic int depth();\n    return E + 1;\n  endfunction\nendpackage\n\
         module leaf #(parameter int W = 1) ();\n\
         \x20 function automatic int twice();\n    return pk::D * 2 + W;\n  endfunction\n\
         \x20 localparam int L = twice();\n\
         \x20 localparam int M = pk::depth();\n\
         \x20 logic [L-1:0] a;\n\
         \x20 logic [M-1:0] b;\n\
         endmodule\n\
         module top;\n  leaf #(.W(1)) x();\n  leaf #(.W(2)) y();\nendmodule\n",
        filler(64)
    );
    let d = elaborate(&source);
    assert_eq!(param(&d, "x.L"), 9);
    assert_eq!(param(&d, "y.L"), 10);
    assert_eq!(param(&d, "x.M"), 10);
    assert_eq!(width(&d, "x.a"), 9);
    assert_eq!(width(&d, "y.a"), 10);
    assert_eq!(width(&d, "y.b"), 10);
}

/// Package parameters named in a generate scope: a condition, a loop bound
/// and declarations inside the blocks.
#[test]
fn generate_scope_names() {
    let source = format!(
        "package pk;\n{}  localparam int G = 5;\n  localparam int H = 3;\n  localparam bit ON = 1;\nendpackage\n\
         module leaf #(parameter int W = 1) ();\n\
         \x20 if (pk::ON) begin : gb\n    logic [pk::G+W-1:0] z;\n  end\n\
         \x20 for (genvar i = 0; i < pk::H; i++) begin : lp\n    logic [pk::G+i-1:0] q;\n  end\n\
         endmodule\n\
         module top;\n  leaf #(.W(1)) a();\n  leaf #(.W(4)) b();\nendmodule\n",
        filler(64)
    );
    let d = elaborate(&source);
    assert_eq!(width(&d, "a.gb.z"), 6);
    assert_eq!(width(&d, "b.gb.z"), 9);
    for i in 0..3u32 {
        assert_eq!(width(&d, &format!("a.lp[{i}].q")), 5 + i);
    }
    assert!(!d.signals.contains_key("a.lp[3].q"));
}

/// A type parameter written in the parent with a package parameter the
/// child never spells, passed down one more level.
#[test]
fn type_parameter_from_the_parent() {
    let source = format!(
        "package pk;\n{}  localparam int F = 13;\nendpackage\n\
         module leaf #(parameter type T = logic) ();\n  T t;\n  localparam int B = $bits(T);\nendmodule\n\
         module mid #(parameter type T = logic) ();\n  leaf #(.T(T)) l();\nendmodule\n\
         module top;\n  mid #(.T(logic [pk::F-1:0])) m();\nendmodule\n",
        filler(64)
    );
    let d = elaborate(&source);
    assert_eq!(width(&d, "m.l.t"), 13);
    assert_eq!(param(&d, "m.l.B"), 13);
}
