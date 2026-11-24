//! Regression guards for #721 compact object layouts, shared instance/signal
//! metadata, and selective VPI driver staging.

use std::mem::size_of;
use xezim_core::{
    ElaboratedModule,
    ast::{
        Identifier, Span,
        cache::{LiteralCache, NameCache, SignalCache, WidthCache},
        expr::{
            ExprKind, Expression, HierPathSegment, HierRoot, HierarchicalIdentifier, NumberLiteral,
        },
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
        size_of::<Span>() <= 8,
        "Span grew to {} B",
        size_of::<Span>()
    );
    assert!(
        size_of::<WidthCache>() <= 4,
        "WidthCache grew to {} B",
        size_of::<WidthCache>()
    );
    assert!(
        size_of::<SignalCache>() <= 4,
        "SignalCache grew to {} B",
        size_of::<SignalCache>()
    );
    assert!(
        size_of::<NameCache>() <= 16,
        "NameCache grew to {} B",
        size_of::<NameCache>()
    );
    assert!(
        size_of::<LiteralCache>() <= 16,
        "LiteralCache grew to {} B",
        size_of::<LiteralCache>()
    );
    assert!(
        size_of::<Identifier>() <= 32,
        "Identifier grew to {} B",
        size_of::<Identifier>()
    );
    assert!(
        size_of::<HierPathSegment>() <= 56,
        "HierPathSegment grew to {} B",
        size_of::<HierPathSegment>()
    );
    assert!(
        size_of::<NumberLiteral>() <= 56,
        "NumberLiteral grew to {} B",
        size_of::<NumberLiteral>()
    );
    assert!(
        size_of::<HierarchicalIdentifier>() <= 64,
        "HierarchicalIdentifier grew to {} B",
        size_of::<HierarchicalIdentifier>()
    );
    assert!(
        size_of::<ExprKind>() <= 64,
        "ExprKind grew to {} B",
        size_of::<ExprKind>()
    );
    assert!(
        size_of::<Expression>() <= 80,
        "Expression grew to {} B",
        size_of::<Expression>()
    );
    assert!(
        size_of::<Statement>() <= 192,
        "Statement grew to {} B",
        size_of::<Statement>()
    );
    assert!(
        size_of::<ContinuousAssignment>() <= 184,
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

#[test]
fn streaming_serialize_matches_materialized_bincode_byte_for_byte() {
    let src = r#"
module leaf(input logic [7:0] a, output logic [7:0] y);
  logic [7:0] r;
  logic [7:0] src_arr [0:1];
  logic [7:0] dst_arr [0:1];
  function automatic logic [7:0] bump(input logic [7:0] x);
    return x + r;
  endfunction
  task automatic poke(input logic [7:0] v);
    r = v;
  endtask
  assign y = bump(a);
  assign dst_arr = src_arr;
  always @* r = a;
  initial poke(8'h5a);
endmodule
module top;
  logic [7:0] a0, a1, y0, y1;
  leaf u0(.a(a0), .y(y0));
  leaf u1(.a(a1), .y(y1));
endmodule
"#;
    let mut m = elaborate(src);
    assert!(!m.pending_always.is_empty(), "expected lazy pending_always");
    assert!(
        !m.pending_initial.is_empty(),
        "expected lazy pending_initial"
    );
    assert!(
        !m.pending_cont_assign.is_empty(),
        "expected lazy pending_cont_assign"
    );
    assert!(
        !m.deferred_function_bodies.is_empty(),
        "expected lazy deferred_function_bodies"
    );
    assert!(
        !m.deferred_task_bodies.is_empty(),
        "expected lazy deferred_task_bodies"
    );

    let cfg = xezim_core::xez_bincode_config();
    let streamed = bincode::serde::encode_to_vec(&m, cfg).expect("stream serialize lazy elab");
    // Streaming serialization must not mutate or eagerly materialize `m`.
    assert!(!m.pending_always.is_empty());
    assert!(!m.pending_cont_assign.is_empty());

    m.materialize_pending();
    assert!(m.pending_always.is_empty());
    assert!(m.pending_initial.is_empty());
    assert!(m.pending_cont_assign.is_empty());
    assert!(m.deferred_function_bodies.is_empty());
    assert!(m.deferred_task_bodies.is_empty());

    let eager = bincode::serde::encode_to_vec(&m, cfg).expect("serialize materialized elab");
    assert_eq!(
        streamed, eager,
        "streaming ElaboratedModule serialization must match materialized output byte-for-byte"
    );

    let mut cursor = std::io::Cursor::new(&streamed);
    let decoded: ElaboratedModule =
        bincode::serde::decode_from_std_read(&mut cursor, cfg).expect("decode streamed elab");
    assert_eq!(decoded.always_blocks.len(), m.always_blocks.len());
    assert_eq!(decoded.initial_blocks.len(), m.initial_blocks.len());
    assert_eq!(decoded.continuous_assigns.len(), m.continuous_assigns.len());
    assert_eq!(decoded.functions.len(), m.functions.len());
    assert_eq!(decoded.tasks.len(), m.tasks.len());
}
