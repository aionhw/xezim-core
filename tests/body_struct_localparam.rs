//! A localparam typed by a body struct typedef is packed in every instance (§6.20.2 / §7.2.1).
fn elaborate(source: &str) -> xezim_core::ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[source.to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .expect("elaborate")
    .1
}

#[test]
fn body_struct_localparam_is_packed_in_the_first_instance() {
    let design = elaborate(
        r#"
module m;
  typedef logic [1:0] field_t;
  typedef struct packed { logic a; logic b; field_t c; } s_t;
  localparam s_t R = '{a: 1'b0, b: 1'b1, c: 2'b10};
endmodule
module top; m u0(); m u1(); endmodule
"#,
    );
    let param = |name: &str| design.parameters.get(name).and_then(|v| v.to_u64());
    assert_eq!(param("u0.R"), Some(0b0110));
    assert_eq!(param("u1.R"), Some(0b0110));
}

/// §7.4.5 / §10.9.1 / §10.9.2: a packed ARRAY of body structs packs its
/// pattern element by element — nested, positional, `parameter`, and a header
/// override — with the first item as the left (most significant) element.
#[test]
fn body_struct_array_param_pattern_packs_by_element_in_an_instance() {
    let design = elaborate(
        r#"
typedef struct packed { logic [7:0] a; logic [7:0] b; } h_t;
module m #(parameter h_t [1:0] H = '{16'h0001, 16'h0002});
  typedef struct packed { logic [7:0] a; logic [7:0] b; } s_t;
  localparam s_t [1:0] PAT     = '{'{a: 8'h33, b: 8'h44}, '{a: 8'h11, b: 8'h22}};
  localparam s_t [1:0] PAT_POS = '{16'h3344, 16'h1122};
  parameter  s_t [1:0] PRM     = '{16'h3344, 16'h1122};
  localparam s_t [1:0] CAT     = {16'h3344, 16'h1122};
endmodule
module top;
  m u0();
  m #(.H('{'{a: 8'h55, b: 8'h66}, '{a: 8'h77, b: 8'h88}})) u1();
  m #('{16'h5566, 16'h7788}) u2();
endmodule
"#,
    );
    let param = |name: &str| design.parameters.get(name).map(|v| (v.to_u64(), v.width));
    for name in ["PAT", "PAT_POS", "PRM", "CAT"] {
        assert_eq!(
            param(&format!("u0.{name}")),
            Some((Some(0x3344_1122), 32)),
            "{name}"
        );
    }
    assert_eq!(param("u0.H"), Some((Some(0x0001_0002), 32)));
    assert_eq!(param("u1.H"), Some((Some(0x5566_7788), 32)));
    assert_eq!(param("u2.H"), Some((Some(0x5566_7788), 32)));
}
