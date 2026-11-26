//! §6.8 and §7.2.1: a packed structure has one state domain across its packed width.

#[test]
fn aliased_array_members_preserve_wide_two_and_four_state_defaults() {
    let src = r#"
module top;
  typedef struct packed { bit   [31:0] word; } two_cell_t;
  typedef struct packed { logic [31:0] word; } four_cell_t;
  typedef two_cell_t two_alias_t;
  typedef four_cell_t four_alias_t;
  typedef struct packed { two_alias_t [2:0] cells; } two_row_t;
  typedef struct packed { four_alias_t [2:0] cells; } four_row_t;
  two_row_t known_row;
  four_row_t unknown_row;
endmodule
"#;
    let (_, design) = xezim_core::parse_and_elaborate_multi(
        &[src.to_owned()],
        Some("top"),
        &[],
        &["top.sv".to_owned()],
        &[],
    )
    .expect("elaborate packed rows");
    for (name, bit) in [("known_row", "0"), ("unknown_row", "x")] {
        let signal = design.signals.get(name).expect(name);
        assert_eq!(signal.width, 96, "{name}");
        assert_eq!(signal.value.to_bin_string(), bit.repeat(96), "{name}");
    }
}
