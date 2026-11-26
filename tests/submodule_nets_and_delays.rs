//! Elaboration facts about inlined sub-module instances that the simulator
//! and VPI read back: gate / net-declaration delays, which ports are nets,
//! and no implicit net for an array that a continuous assignment reads.

use xezim_core::elaborate::{ContinuousAssignment, ElaboratedModule};

fn elab(src: &str) -> ElaboratedModule {
    let (_, mut m) = xezim_core::parse_and_elaborate_multi(
        &[src.to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .expect("elaborate");
    m.materialize_pending();
    m
}

fn lhs_name(ca: &ContinuousAssignment) -> String {
    use xezim_core::ast::expr::ExprKind;
    match &ca.lhs.kind {
        ExprKind::Ident(h) => h
            .path
            .iter()
            .map(|s| s.name.name.as_str())
            .collect::<Vec<_>>()
            .join("."),
        _ => String::new(),
    }
}

fn assign_to<'a>(m: &'a ElaboratedModule, name: &str) -> &'a ContinuousAssignment {
    m.continuous_assigns
        .iter()
        .find(|ca| lhs_name(ca) == name)
        .unwrap_or_else(|| {
            panic!(
                "no continuous assign drives {name}; have {:?}",
                m.continuous_assigns
                    .iter()
                    .map(lhs_name)
                    .collect::<Vec<_>>()
            )
        })
}

/// §28.9 / §10.3.1: an inlined instance's gates and net-declaration
/// assignments keep their delays, with the parameters they name resolved per
/// instance. They used to reach the simulator with delay 0.
#[test]
fn inlined_gate_and_net_decl_delays_resolve_per_instance() {
    let m = elab(
        r#"
`timescale 1ns/1ns
module sub #(parameter D = 3, parameter W = 2) (input a, input b);
  wire g, n, w;
  and #D g1 (g, a, b);
  nand #(1, D) g2 (n, a, b);
  wire #W w2 = a & b;
endmodule
module top;
  reg a, b;
  sub u1 (.a(a), .b(b));
  sub #(.D(5), .W(4)) u2 (.a(a), .b(b));
endmodule
"#,
    );
    assert_eq!(assign_to(&m, "u1.g").delay, 3);
    assert_eq!(assign_to(&m, "u2.g").delay, 5);
    assert_eq!(assign_to(&m, "u1.w2").delay, 2);
    assert_eq!(assign_to(&m, "u2.w2").delay, 4);
    let n1 = assign_to(&m, "u1.n");
    assert_eq!((n1.delay, n1.delay_fall), (1, Some(3)));
    let n2 = assign_to(&m, "u2.n");
    assert_eq!((n2.delay, n2.delay_fall), (1, Some(5)));
    // §28.4: the gate outputs are gate-driven, as at the top level.
    for n in ["u1.g", "u1.n", "u2.g", "u2.n"] {
        assert!(m.gate_driven_nets.contains(n), "{n} not gate-driven");
    }
}

/// §23.2.2.3: a port with no net type is still a net when it has no data
/// type, or is an ANSI input/inout of type `logic`; a non-ANSI port that a
/// `reg` declaration completes is a variable.
#[test]
fn implicit_net_ports_are_nets() {
    let m = elab(
        r#"
module s1 (a, y, d, e);
  input a;
  output y;
  output d;
  reg d;
  input logic e;
endmodule
module s2 (input a, input logic [3:0] c, output y, output logic z, output var v,
           input int i);
endmodule
module top (input tin, output tout, output logic tl);
  s1 u1 (.a(tin), .y(), .d(), .e(tin));
  s2 u2 (.a(tin), .c(4'h1), .y(), .z(), .v(), .i(1));
endmodule
"#,
    );
    for n in ["tin", "tout", "u1.a", "u1.y", "u2.a", "u2.c", "u2.y"] {
        assert!(m.nets.contains(n), "{n} should be a net");
    }
    for n in ["tl", "u1.d", "u1.e", "u2.z", "u2.v", "u2.i"] {
        assert!(!m.nets.contains(n), "{n} should be a variable");
    }
}

/// A continuous assignment that READS an unpacked-array element must not
/// declare an implicit net named after the array (§6.10 applies to
/// undeclared identifiers only).
#[test]
fn array_element_read_in_cont_assign_adds_no_implicit_net() {
    let m = elab(
        r#"
module top;
  logic [7:0] m1 [3:0];
  wire [7:0] w2;
  assign w2 = m1[2];
endmodule
"#,
    );
    assert!(!m.nets.contains("m1"), "phantom net m1");
    assert!(!m.implicit_nets.contains("m1"), "phantom implicit net m1");
    assert!(!m.signals.contains_key("m1"), "phantom signal m1");
}

#[test]
fn variable_delays_survive_port_rewriting_and_net_staging() {
    let m = elab(
        r#"
`timescale 1ns/1ps
module child #(parameter int PD = 1) (input a, input [3:0] dv);
  wire c, g;
  assign #(dv + PD, 2, dv) c = a;
  wire #(dv) init_net = a;
  buf #(dv) drive(g, a);
endmodule
module top;
  logic a;
  int d;
  wire out;
  assign #(d) out = a;
  child u(a, d[3:0]);
endmodule
"#,
    );
    for (target, arity) in [("out", 1), ("u.c", 3), ("u.init_net", 1), ("u.g", 1)] {
        let ca = assign_to(&m, target);
        assert_ne!(ca.delay, 0, "{target} must use the delayed driver path");
        let args = ca.delay_exprs.as_ref().expect("runtime operands");
        assert_eq!(args.iter().flatten().count(), arity, "{target}");
    }
}

#[test]
fn variable_net_delay_retains_its_own_scope_for_an_external_driver() {
    let m = elab(
        r#"
module sub;
  timeunit 1ns;
  timeprecision 100ps;
  real d = 0.16;
  wire #(d) y;
endmodule
module top;
  timeunit 1ns;
  timeprecision 1ps;
  logic a;
  sub u();
  assign u.y = a;
endmodule
"#,
    );
    let stage = assign_to(&m, "u.y");
    assert!(stage.delay_exprs.is_some());
    assert!(stage.origin.is_none(), "the stage derives its scope from u.y");
    let driver = assign_to(&m, "u.y$netdrv");
    assert!(driver.delay_exprs.is_none());
    assert_eq!(driver.origin.as_ref().unwrap().1.as_ref(), "");
}
