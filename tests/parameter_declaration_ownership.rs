//! §26.3 / §21.7.2.3: lookup aliases do not declare module parameters.
#[test]
fn parameter_declarations_keep_their_instance_scope() {
    let (_, elab) = xezim_core::parse_and_elaborate_multi(
        &[r#"
 package p; parameter W=4; endpackage
 module child #(parameter W=5);
  import p::*; localparam L=W+1;
  if(1) begin:g localparam P=7; end
 endmodule
 module top;
  import p::*; localparam L=W+1; child u();
 endmodule
 "#
        .to_string()],
        Some("top"),
        &[],
        &[],
        &[],
    )
    .unwrap();
    for n in ["L", "u.W", "u.L", "u.g.P"] {
        assert!(
            elab.declared_parameters.contains(n),
            "{n}: {:?}",
            elab.declared_parameters
        );
    }
    assert!(!elab.declared_parameters.contains("W"));
    assert!(!elab.declared_parameters.contains("p::W"));
}
