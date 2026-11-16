//! §7.2 / §7.4.1 / §23.6: generated member storage retains its type and shape.
#[test]
fn generated_members_keep_scope_and_packed_dimensions() {
    let src = r#"
      typedef struct packed {logic [3:0] n;} [1:0][1:0] P;
      typedef enum logic [3:0] {ZERO=0} [1:0][1:0] E;
      typedef struct {P p; E e; string text; event ready; int aa[string];} S;
      module top; if(1) begin:g S value; end endmodule
    "#;
    let (_, mut m) = xezim_core::parse_and_elaborate_multi(
        &[src.to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .expect("elaborate");
    m.materialize_pending();
    assert_eq!(m.typedefs["E"], 16);
    for member in ["g.value.p", "g.value.e"] {
        assert_eq!(m.signals[member].width, 16);
        assert_eq!(m.packed_full_dims[member], vec![(1, 0), (1, 0), (3, 0)]);
    }
    assert!(m.struct_members.contains_key("g.value"));
    assert!(m.string_signals.contains("g.value.text"));
    assert!(m.events.contains("g.value.ready"));
    assert_eq!(m.associative_arrays.get("g.value.aa"), Some(&true));
}
