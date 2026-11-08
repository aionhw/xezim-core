//! §6.10: a continuous assignment that names a member through a scope select
//! (`assign g[0].u.a = s;`, `assign y = g[1].u.c;`) does not declare an
//! implicit net named after the generate block or instance array. The root
//! of such a path is a scope, never a scalar net; it was collected as an
//! undeclared identifier, so every such assignment declared a 1-bit net `g`
//! and warned about it. A name used inside the selects is read, not
//! assigned, so it is not an implicit net either.

fn elaborate(src: &str) -> xezim_core::ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[src.to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .expect("elaborate")
    .1
}

#[test]
fn scope_select_root_is_not_an_implicit_net() {
    let m = elaborate(
        r#"
module leaf (input logic [3:0] a, output logic [3:0] c);
  assign c = a;
endmodule
module top;
  logic [3:0] s, y, z;
  for (genvar i = 0; i < 2; i++) begin : g
    leaf u (.c());
  end
  for (genvar j = 0; j < 2; j++) begin : h
    for (genvar k = 0; k < 2; k++) begin : q
      leaf u (.c());
    end
  end
  leaf ua [1:0] (.c());
  assign g[0].u.a = s;
  assign y = g[1].u.c;
  assign h[1].q[0].u.a = s;
  assign ua[1].a = s;
  assign z = ua[1].c;
endmodule
"#,
    );
    for n in ["g", "h", "ua"] {
        assert!(!m.implicit_nets.contains(n), "phantom implicit net {n}");
        assert!(!m.nets.contains(n), "phantom net {n}");
    }
}

#[test]
fn an_undeclared_select_operand_on_the_left_hand_side_is_undeclared() {
    // §6.10: the implicit net is the assigned name; `w` is only read.
    let err = xezim_core::parse_and_elaborate_multi(
        &[r#"
module leaf (input logic [3:0] a, output logic [3:0] c);
  assign c = a;
endmodule
module top;
  for (genvar i = 0; i < 2; i++) begin : g
    leaf u (.c());
  end
  assign g[1].u.a[w] = 1'b1;
endmodule
"#
        .to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .err()
    .expect("w is undeclared");
    assert!(err.contains("Undeclared identifier 'w'"), "{err}");
}
