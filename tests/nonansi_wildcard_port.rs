//! §23.3.2.4: `.*` fills every port a connection list does not name, including
//! a non-ANSI header. That header is only a name list; direction and type
//! come from later `input` / `output` declarations. Expanding `.*` for ANSI
//! ports alone left the unnamed inputs unconnected, so they read Z.

fn elab(src: &str) -> xezim_core::ElaboratedModule {
    let (_, mut m) = xezim_core::parse_and_elaborate_multi(
        &[src.to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .expect("elaborate");
    m.materialize_pending();
    m
}

#[test]
fn wildcard_connects_nonansi_ports() {
    let m = elab(
        r#"
module child(clk, rst, din, dout);
  input clk;
  input rst;
  input [7:0] din;
  output [7:0] dout;
  assign dout = din;
endmodule
module top;
  logic clk;
  logic rst;
  logic [7:0] din;
  logic [7:0] dout_tied;
  logic [7:0] dout_over;
  logic other_clk;
  child tied (.*, .dout(dout_tied));
  child over (.*, .clk(other_clk), .dout(dout_over));
endmodule
"#,
    );
    let alias = |formal: &str| m.port_aliases.get(formal).map(String::as_str);
    assert_eq!(alias("tied.clk"), Some("clk"));
    assert_eq!(alias("tied.rst"), Some("rst"));
    assert_eq!(alias("tied.din"), Some("din"));
    assert_eq!(alias("tied.dout"), Some("dout_tied"));
    // An explicit connection wins over `.*`.
    assert_eq!(alias("over.clk"), Some("other_clk"));
    assert_eq!(alias("over.rst"), Some("rst"));
    assert_eq!(alias("over.din"), Some("din"));
}
