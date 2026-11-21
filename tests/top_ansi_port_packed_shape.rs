//! IEEE 1800-2023 §7.4.1 / §7.2 / §23.2.2.2: an ANSI port of the top module
//! keeps the packed shape a variable of its type has: the dimensions and
//! element width of a packed multi-D array, of a packed array of a typedef'd
//! element, and the field layout of a packed structure. Without them `o[1]`
//! of `output logic [5:0][7:0] o` on the top module was a one-bit select, and
//! a member of a packed-structure port read x.

const SRC: &str = r#"package P;
  typedef logic [7:0] byte_t;
  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } s_t;
endpackage
module top import P::*; (output logic [5:0][7:0] w2, output byte_t [5:0] w,
    output s_t s, output s_t [1:0] sa, output logic [0:3][3:0] asc, input logic [3:0][5:0][7:0] w3);
endmodule"#;

fn design() -> xezim_core::elaborate::ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[SRC.to_string()],
        Some("top"),
        &[],
        &["top_ansi_ports.sv".to_string()],
        &[],
    )
    .expect("elaborate")
    .1
}

#[test]
fn packed_array_ports_keep_dims_and_element_width() {
    let m = design();
    for (name, dims, elem) in [
        ("w2", vec![(5, 0), (7, 0)], 8),
        ("w", vec![(5, 0), (7, 0)], 8),
        ("asc", vec![(0, 3), (3, 0)], 4),
        ("w3", vec![(3, 0), (5, 0), (7, 0)], 48),
    ] {
        assert_eq!(m.packed_full_dims.get(name), Some(&dims), "{name}");
        assert_eq!(m.packed_signal_elem_widths.get(name), Some(&elem), "{name}");
    }
}

#[test]
fn packed_struct_ports_keep_their_fields() {
    let m = design();
    let fields = |name: &str| -> Vec<(String, u32, u32)> {
        m.packed_struct_fields
            .get(name)
            .unwrap_or_else(|| panic!("no fields for {name}"))
            .clone()
    };
    let want = vec![("hi".to_string(), 4, 4), ("lo".to_string(), 0, 4)];
    let mut got = fields("s");
    got.sort();
    assert_eq!(got, want);
    let mut got = fields("sa");
    got.sort();
    assert_eq!(got, want);
    assert_eq!(m.packed_full_dims.get("sa"), Some(&vec![(1, 0), (7, 0)]));
}
