//! IEEE 1800-2023 §7.2 / §23.3.3: an inlined instance's unpacked-struct output
//! port is stored member-wise, like the root module's ports, and a child's
//! whole-struct continuous assign to it expands to one assign per member.

const SRC: &str = r#"typedef struct { int a; int b; } s_t;
typedef struct packed { logic [3:0] hi; logic [3:0] lo; } p_t;
module ch(input int x, output s_t o, output p_t q);
  assign o = '{a: x, b: 7};
  assign q = '{hi: 4'd1, lo: 4'd2};
endmodule
module tp #(type T = s_t) (input int x, output T o);
  assign o = '{x, 9};
endmodule
module top;
  int x;
  s_t s, t;
  p_t p;
  ch u(.x(x), .o(s), .q(p));
  tp v(.x(x), .o(t));
endmodule"#;

fn design() -> xezim_core::elaborate::ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[SRC.to_string()],
        Some("top"),
        &[],
        &["ports.sv".to_string()],
        &[],
    )
    .expect("elaborate")
    .1
}

/// The written name of an assign target: `u.o.a` for a leaf, None otherwise.
fn target(e: &xezim_core::ast::expr::Expression) -> Option<String> {
    match &e.kind {
        xezim_core::ast::expr::ExprKind::Ident(h) => Some(
            h.path
                .iter()
                .map(|s| s.name.name.as_str())
                .collect::<Vec<_>>()
                .join("."),
        ),
        _ => None,
    }
}

#[test]
fn unpacked_struct_port_is_member_wise() {
    let model = design();
    // No packed field layout for the unpacked port; the packed one keeps it.
    assert!(!model.packed_struct_fields.contains_key("u.o"));
    assert!(model.packed_struct_fields.contains_key("u.q"));
    // The declared type is recorded, as for a root-module port.
    assert!(model.var_decl_types.contains_key("u.o"));
    // The child's whole-struct assign now writes the member leaves.
    let targets: Vec<String> = model
        .continuous_assigns
        .iter()
        .filter_map(|ca| target(&ca.lhs))
        .collect();
    for leaf in ["u.o.a", "u.o.b"] {
        assert!(
            targets.iter().any(|t| t == leaf),
            "{leaf} not written: {targets:?}"
        );
    }
    assert!(
        !targets.iter().any(|t| t == "u.o"),
        "whole-struct write kept: {targets:?}"
    );
}

#[test]
fn type_parameter_port_keeps_its_layout() {
    // A port typed by a type parameter keeps the previous handling: the
    // binding exists only while the instance is inlined. This pins that known
    // limitation; a fix that resolves type-parameter struct ports should
    // replace it.
    let model = design();
    assert!(model.packed_struct_fields.contains_key("v.o"));
    assert!(!model.var_decl_types.contains_key("v.o"));
}
