//! IEEE 1800-2023 §26.3: header parameters and package parameters have
//! independent lexical bindings, including constant subroutine evaluation.

#[test]
fn module_header_does_not_replace_package_function_parameters() {
    let src = r#"
package cfg;
 parameter int W=8;
 function automatic int width(); return W; endfunction
 function automatic logic [W-1:0] mask(input logic [W-1:0] v); return v; endfunction
endpackage
module top #(parameter int W=3);
 import cfg::*;
 localparam int PACKAGE_W=width();
 localparam int MASK=mask(8'hf3);
 logic [W-1:0] data;
endmodule
"#;
    let (_, d) = xezim_core::parse_and_elaborate_multi(
        &[src.into()],
        Some("top"),
        &[],
        &["top.sv".into()],
        &[],
    )
    .expect("elaborate");
    assert_eq!(d.parameters["W"].to_i64(), Some(3));
    assert_eq!(d.parameters["cfg::W"].to_i64(), Some(8));
    assert_eq!(d.parameters["PACKAGE_W"].to_i64(), Some(8));
    assert_eq!(d.parameters["MASK"].to_i64(), Some(0xf3));
    assert_eq!(d.signals["data"].width, 3);
}

#[test]
fn explicit_import_cannot_replace_a_header_parameter() {
    let src = "package cfg; parameter int W=8; endpackage\n\
        module top #(parameter int W=3); import cfg::W; endmodule";
    let result = xezim_core::parse_and_elaborate_multi(
        &[src.into()],
        Some("top"),
        &[],
        &["top.sv".into()],
        &[],
    );
    let error = match result {
        Ok(_) => panic!("expected conflict"),
        Err(e) => e,
    };
    assert!(
        error.contains("W") && error.contains("already declared"),
        "{error}"
    );
}
