//! Regression guards for #721 compact object layouts, shared instance/signal
//! metadata, and selective VPI driver staging.

use std::mem::size_of;
use xezim_core::{
    ElaboratedModule,
    ast::{
        expr::{ExprKind, Expression, HierRoot, HierarchicalIdentifier},
        stmt::Statement,
    },
    elaborate::{ContinuousAssignment, ElabInstance, Signal, set_vpi_net_drivers, vpi_net_drivers},
};

fn elaborate(src: &str) -> ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[src.to_string()],
        Some("top"),
        &[],
        &["t.sv".to_string()],
        &[],
    )
    .expect("elaborate")
    .1
}

#[test]
fn core_ast_and_elaboration_object_sizes_stay_compact() {
    assert!(
        size_of::<HierarchicalIdentifier>() <= 80,
        "HierarchicalIdentifier grew to {} B",
        size_of::<HierarchicalIdentifier>()
    );
    assert!(
        size_of::<ExprKind>() <= 80,
        "ExprKind grew to {} B",
        size_of::<ExprKind>()
    );
    assert!(
        size_of::<Expression>() <= 104,
        "Expression grew to {} B",
        size_of::<Expression>()
    );
    assert!(
        size_of::<Statement>() <= 240,
        "Statement grew to {} B",
        size_of::<Statement>()
    );
    assert!(
        size_of::<ContinuousAssignment>() <= 232,
        "ContinuousAssignment grew to {} B",
        size_of::<ContinuousAssignment>()
    );
    assert!(
        size_of::<Signal>() <= 56,
        "Signal grew to {} B",
        size_of::<Signal>()
    );
    assert!(
        size_of::<ElabInstance>() <= 32,
        "ElabInstance grew to {} B",
        size_of::<ElabInstance>()
    );
}

#[test]
fn instance_and_signal_metadata_share_allocations_across_instances() {
    let src = r#"
typedef logic [7:0] byte_t;
module leaf(input byte_t a, output byte_t y);
  byte_t mem [0:3];
  assign y = a;
endmodule
module top;
  byte_t d0, d1, q0, q1;
  leaf u0(.a(d0), .y(q0));
  leaf u1(.a(d1), .y(q1));
endmodule
"#;
    let m = elaborate(src);

    // Sibling ElabInstance entries share def_name and parent SharedNames.
    assert_eq!(m.instances.len(), 2);
    assert!(m.instances[0].def_name.ptr_eq(&m.instances[1].def_name));
    assert!(m.instances[0].parent.ptr_eq(&m.instances[1].parent));

    // Signals typed with the same typedef share their type_name SharedName.
    let t0 = m.signals["u0.y"]
        .type_name
        .as_ref()
        .expect("u0.y type_name");
    let t1 = m.signals["u1.y"]
        .type_name
        .as_ref()
        .expect("u1.y type_name");
    assert_eq!(t0.as_str(), "byte_t");
    assert!(t0.ptr_eq(t1));

    // Unpacked declared dimension slices are shared across sibling instances.
    let d0 = m
        .unpacked_decl_dims
        .get_shared("u0.mem")
        .expect("u0.mem unpacked_decl_dims");
    let d1 = m
        .unpacked_decl_dims
        .get_shared("u1.mem")
        .expect("u1.mem unpacked_decl_dims");
    assert_eq!(d0.as_slice(), &[(0, 3)]);
    assert!(d0.ptr_eq(d1));

    // Synthesized port-connection continuous assigns carry no boxed extras.
    assert!(!m.continuous_assigns.is_empty());
    assert!(
        m.continuous_assigns
            .iter()
            .all(|ca| ca.origin().is_none() && ca.extras.is_none()),
        "synthesized port connections must not allocate ContinuousAssignExtras"
    );
}

#[test]
fn continuous_assign_extras_and_hier_root_round_trip_bincode() {
    let src = r#"
`timescale 1ns/1ns
module top;
  wire a, b, c;
  assign #(2, 5, 7) c = a & b;
  assign b = a;
endmodule
"#;
    let mut m = elaborate(src);
    m.materialize_pending();

    let cfg = bincode::config::standard();
    let bytes = bincode::serde::encode_to_vec(&m.continuous_assigns, cfg).expect("encode");
    let (decoded, _): (Vec<ContinuousAssignment>, _) =
        bincode::serde::decode_from_slice(&bytes, cfg).expect("decode");
    assert_eq!(decoded.len(), m.continuous_assigns.len());

    let delayed = decoded
        .iter()
        .find(|ca| ca.delay == 2)
        .expect("delayed assign");
    assert_eq!(delayed.delay_fall(), Some(5));
    assert_eq!(delayed.delay_off(), Some(7));
    assert!(delayed.origin().is_some());

    let plain = decoded
        .iter()
        .find(|ca| ca.delay == 0)
        .expect("undelayed source assign");
    assert!(plain.origin().is_some());
    assert!(
        plain.extras.as_deref().is_some_and(|e| e.delays.is_none()),
        "undelayed source assign must not allocate ContinuousAssignDelays"
    );

    for root in [HierRoot::Root, HierRoot::Unit, HierRoot::Local] {
        let encoded = bincode::serde::encode_to_vec(root, cfg).expect("encode HierRoot");
        let (back, _): (HierRoot, _) =
            bincode::serde::decode_from_slice(&encoded, cfg).expect("decode HierRoot slice");
        assert_eq!(back, root);
        // Streaming reader passes owned strings (visit_string -> visit_str),
        // matching `.xez` compiled-artifact loading.
        let mut reader = std::io::Cursor::new(&encoded);
        let streamed: HierRoot =
            bincode::serde::decode_from_std_read(&mut reader, cfg).expect("decode HierRoot reader");
        assert_eq!(streamed, root);
    }
}

#[test]
fn vpi_driver_staging_keeps_non_net_pending_assigns_lazy_and_stages_complex_net_drivers() {
    struct Guard(bool);
    impl Drop for Guard {
        fn drop(&mut self) {
            set_vpi_net_drivers(self.0);
        }
    }
    let _guard = Guard(vpi_net_drivers());
    set_vpi_net_drivers(true);

    let src = r#"
module leaf(input logic [7:0] a, input logic [7:0] b, output logic [7:0] var_out, output wire [7:0] net_out);
  assign var_out = a;
  assign net_out = a ^ b;
endmodule
module top;
  logic [7:0] a, b, vo;
  wire [7:0] no;
  leaf u(.a(a), .b(b), .var_out(vo), .net_out(no));
endmodule
"#;
    let m = elaborate(src);

    // Non-net variable continuous assignment stays deferred in pending_cont_assign.
    assert_eq!(
        m.pending_cont_assign.len(),
        1,
        "non-net pending assign should remain lazy"
    );
    // Complex net driver (`a ^ b` driving `u.net_out`) was materialized and staged for VPI deposits.
    assert!(
        m.signals.keys().any(|k| k.contains("$vpidrv")),
        "expected a $vpidrv stage signal for complex net driver"
    );
}
