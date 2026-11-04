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
