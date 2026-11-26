//! §23.3.3, §6.8: each input port renamed to its actual records its formal's
//! path and whether the formal is 2-state, which sets the value the port's
//! time-0 update starts from (0 for `bit`, unknown for `logic` or `wire`).
//! The simulator needs it for elided ports, whose own net and type entries
//! are gone. A 2-state formal is renamed only to a 2-state actual: one that
//! can carry X or Z keeps the formal (§6.11.2), so `ub` and `un` connect `b`.

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
fn input_port_actuals_record_the_formal_state() {
    let m = elaborate(
        r#"
module kl (input logic c);
  always @(negedge c) ;
endmodule
module kb (input bit c);
  always @(negedge c) ;
endmodule
module kw (input wire c);
  always @(negedge c) ;
endmodule
module kn (c);
  input bit c;
  always @(negedge c) ;
endmodule
module top;
  logic s = 0;
  bit b = 0;
  kl ul (.c(s));
  kb ub (.c(b));
  kw uw (.c(s));
  kn un (.c(b));
endmodule
"#,
    );
    let state = |inst: &str| {
        m.input_port_actuals
            .iter()
            .find(|port| {
                let f = port.formal();
                f.rsplit('.').nth(1) == Some(inst) && f.ends_with(".c")
            })
            .map(|port| port.two_state())
    };
    assert_eq!(state("ul"), Some(false));
    assert_eq!(state("ub"), Some(true));
    assert_eq!(state("uw"), Some(false));
    assert_eq!(state("un"), Some(true));
}

/// §16.5.1, §16.9.3: a sampled input has a prehistory of its own. The
/// clock, which supplies timing alone, can still use its parent's signal.
#[test]
fn sampled_operand_keeps_its_formal() {
    let m = elaborate(
        r#"
module leaf(input clk, input [3:0] data);
  always @(posedge clk) $display("%b", $past(data ^ 4'h2));
endmodule
module top;
  reg clk = 0;
  reg [3:0] data = 0;
  leaf u(clk, data);
endmodule"#,
    );
    assert!(m.sampled_input_ports.contains("u.data"));
    assert!(!m.sampled_input_ports.contains("u.clk"));
    assert!(m.input_port_actuals.iter().all(|port| port.formal() != "u.data"));
    assert!(m.input_port_actuals.iter().any(|port| port.formal() == "u.clk"));
}
