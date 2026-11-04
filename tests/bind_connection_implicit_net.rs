//! §23.11 / §6.10: an actual in a bind instantiation names objects in the
//! bind target, so a name the target does not declare is an implicit net of
//! the target, even when the scope holding the bind declares that name.

fn elaborate(src: &str) -> xezim_core::ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[src.to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .expect("elaborate")
    .1
}

#[test]
fn bind_connection_names_an_implicit_net_of_the_target() {
    let m = elaborate(
        r#"
interface edges (input logic clk);
  int n = 0;
  always @(posedge clk) n++;
endinterface
module target();
endmodule
module binder;
  logic clk = 0;
  bind target edges far (.clk(clk));
endmodule
module top;
  logic clk = 0;
  target dut();
  binder b();
  bind target edges mon (.clk(clk));
endmodule
"#,
    );
    assert!(m.signals.contains_key("dut.clk"), "no implicit net dut.clk");
    assert_eq!(m.port_aliases.get("dut.far.clk").map(|s| s.as_str()), Some("dut.clk"));
    assert_eq!(m.port_aliases.get("dut.mon.clk").map(|s| s.as_str()), Some("dut.clk"));
}
