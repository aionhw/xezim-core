//! §23.3.3, §6.8: each input port renamed to its actual records whether its
//! formal is 2-state, which sets the value the port's time-0 update starts
//! from (0 for `bit`, unknown for `logic` or `wire`). The simulator needs it
//! for elided ports, whose own net and type entries are gone; a scalar ANSI
//! port is not in `two_state_signals` either.

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
  kl ul (.c(s));
  kb ub (.c(s));
  kw uw (.c(s));
  kn un (.c(s));
endmodule
"#,
    );
    let state = |inst: &str| {
        m.input_port_actuals
            .iter()
            .find(|(i, ..)| i.rsplit('.').next() == Some(inst))
            .map(|(_, _, two_state)| *two_state)
    };
    assert_eq!(state("ul"), Some(false));
    assert_eq!(state("ub"), Some(true));
    assert_eq!(state("uw"), Some(false));
    assert_eq!(state("un"), Some(true));
}
