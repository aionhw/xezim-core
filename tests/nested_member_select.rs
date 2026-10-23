//! §7.2.2 / §6.20.2: `array[i].field.subfield` on a localparam array of
//! packed structs is that member, not a 32-bit 0.

fn elaborate(source: &str) -> xezim_core::ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[source.to_string()],
        Some("t"),
        &[],
        &["t.sv".to_string()],
        &[],
    )
    .expect("elaborate")
    .1
}

#[test]
fn nested_member_of_array_param_is_not_zero() {
    let model = elaborate(
        r#"
typedef struct packed {
  logic       accept;
  logic [1:0] gpr;
} inner_t;
typedef struct packed {
  logic [31:0] instr;
  inner_t      rsp;
} outer_t;
module t;
  localparam inner_t INNERS[1] = '{'{accept: 1'b1, gpr: 2'b01}};
  localparam outer_t OUTERS[1] = '{'{instr: 32'h0400702b, rsp: '{accept: 1'b1, gpr: 2'b01}}};
  localparam int inner_arr = INNERS[0].accept;
  localparam int inner_bits = $bits(INNERS[0].accept);
  localparam int chain = OUTERS[0].rsp.accept;
  localparam int chain_bits = $bits(OUTERS[0].rsp.accept);
  localparam int whole = OUTERS[0].rsp;
endmodule
"#,
    );
    let val = |name: &str| {
        model
            .parameters
            .get(name)
            .unwrap_or_else(|| panic!("{name} missing"))
            .to_i64()
            .unwrap_or_else(|| panic!("{name} not a number"))
    };
    assert_eq!(val("inner_arr"), 1, "one-level select");
    assert_eq!(val("inner_bits"), 1);
    assert_eq!(val("chain"), 1, "nested select");
    assert_eq!(val("chain_bits"), 1);
    assert_eq!(val("whole"), 5);
}
