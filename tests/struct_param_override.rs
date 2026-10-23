//! A packed-struct parameter passed as another module's parameter override
//! keeps its fields (§6.20, §23.10).
//!
//! `child #(.Features(FPU_FEATURES))` bound the override value but never
//! registered the struct's field layout before the child's body localparams
//! were folded, so `localparam WIDTH = Features.Width` read a 32-bit 0 and a
//! port `[WIDTH-1:0]` elaborated to 2 bits. The parent's own select of the
//! same value was fine.
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

const STRUCT_PARAM: &str = r#"
package p;
  typedef struct packed {
    int unsigned Width;
    logic        Flag;
  } features_t;
  parameter features_t F = '{Width: 32, Flag: 1'b1};
endpackage

module child #(
  parameter p::features_t Features = p::F,
  localparam int unsigned WIDTH = Features.Width
) (
  output logic [WIDTH-1:0] result_o
);
endmodule

module parent #(
  parameter p::features_t FPU_FEATURES = p::F
);
  logic [31:0] result;
  child #(.Features(FPU_FEATURES)) u (.result_o(result));
endmodule

module t;
  parent u ();
endmodule
"#;

#[test]
fn overridden_struct_param_keeps_its_fields() {
    let design = elaborate(STRUCT_PARAM);
    // {Width: 32, Flag: 1} packs to 33 bits, Flag at bit 0.
    let parent = &design.parameters["u.FPU_FEATURES"];
    assert_eq!(parent.width, 33);
    assert_eq!(parent.to_u64(), Some(65));
    assert_eq!(design.parameters["u.u.WIDTH"].to_i64(), Some(32));
    assert_eq!(design.signals["u.u.result_o"].width, 32);
}
