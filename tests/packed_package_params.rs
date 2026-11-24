//! Indexing a packed multi-dimensional package parameter selects an element (IEEE 1800-2017 §7.4.5 / §26.3).
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
fn package_constant_uses_its_own_struct_member_before_a_module_sizes_a_net() {
    let design = elaborate(
        r#"
package types;
  typedef struct packed { logic [1:0] hi; logic [11:0] irq; logic [1:0] lo; } config_t;
endpackage
package a;
  import types::config_t;
  parameter config_t pt = 16'h03fc;
  parameter int unsigned count = pt.irq - 43;
endpackage
package other_types;
  typedef struct packed { logic [3:0] hi; logic [11:0] irq; } config_t;
endpackage
package b;
  import other_types::config_t;
  parameter config_t pt = 16'h0040;
  parameter int unsigned count = pt.irq - 43;
endpackage
module top;
  wire [a::count-1:0] bus_a;
  wire [b::count-1:0] bus_b;
  localparam int width_a = $bits(bus_a);
  localparam int width_b = $bits(bus_b);
endmodule
"#,
    );
    let param = |name: &str| design.parameters.get(name).and_then(|v| v.to_u64());
    assert_eq!(param("a::count"), Some(212));
    assert_eq!(param("b::count"), Some(21));
    assert_eq!(param("width_a"), Some(212));
    assert_eq!(param("width_b"), Some(21));
}

#[test]
fn unqualified_wide_parameter_member_sizes_a_consuming_net() {
    let design = elaborate(
        r#"
package types;
  typedef struct packed { logic [1140:0] hi; logic [11:0] irq; logic [1140:0] lo; } config_t;
endpackage
package opts;
  import types::config_t;
  parameter config_t pt = {1141'b0, 12'd255, 1141'b0};
  parameter int unsigned count = pt.irq - 43;
endpackage
module top;
  wire [opts::count-1:0] bus;
  localparam int bus_width = $bits(bus);
endmodule
"#,
    );
    assert_eq!(design.parameters["bus_width"].to_u64(), Some(212));
}

#[test]
fn packed_package_parameter_index_selects_an_element() {
    let design = elaborate(
        r#"
package p; parameter logic [3:0][3:0] Q = {4'h4, 4'h3, 4'h2, 4'h1}; endpackage
package r; parameter logic [1:0][3:0] R = 8'h12; endpackage
module m import p::*; ; localparam logic [3:0] E = Q[2]; localparam logic [7:0] R = 8'hA5; localparam logic [3:0] B = R[1]; endmodule
module top; import p::*; localparam logic [3:0] S = p::Q[1]; localparam logic [3:0] I = Q[3]; m u(); endmodule
"#,
    );
    let param = |name: &str| design.parameters.get(name).and_then(|v| v.to_u64());
    assert_eq!(param("S"), Some(2));
    assert_eq!(param("I"), Some(4));
    assert_eq!(param("u.E"), Some(3));
    assert_eq!(param("u.B"), Some(0));
}
