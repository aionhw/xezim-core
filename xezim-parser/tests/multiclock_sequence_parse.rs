//! IEEE 1800-2023 §16.13.1, A.2.10: a multiclocked sequence joins singly
//! clocked subsequences with `##1` or `##0`, and `clocking_event
//! sequence_expr` is itself a sequence_expr, so the operand of a cycle delay
//! may open with a clocking event: `##1 @(posedge clk) c`. The parser only
//! took that operand after an infix delay (`b ##1 @(posedge clk2) c`). After
//! a delay with no left operand, the `@` was not among the tokens that may
//! start the operand, so `##1 ##1 @(posedge clk) c` stopped at the `@`, and
//! the enclosing parentheses failed with "expected RParen, found At".

use sv_parser::parse;
use sv_parser::strict_check::strict_diagnostics;

fn check(src: &str) {
    let r = parse(src);
    assert!(r.errors.is_empty(), "{:?}", r.errors);
    let strict = strict_diagnostics(&r.source.descriptions);
    assert!(strict.is_empty(), "{strict:?}");
    // The operand after the clocking event is kept, not dropped.
    assert!(
        format!("{:?}", r.source).contains("$fell"),
        "{:?}",
        r.source
    );
}

/// The shape of a cover in an open-source I3C target FSM: the clock moves to
/// `clk2` and back, each time after a delay with no left operand.
#[test]
fn delay_then_clocking_event_in_a_property() {
    check(
        r#"
module m(input logic clk, clk2, a, b);
  property p_mc;
    @(posedge clk)
    ( $rose(a) |=> ##1 b ##1 @(posedge clk2) ##1 ##1 @(posedge clk) ##1 $fell(b) );
  endproperty
  c_mc: cover property (p_mc);
endmodule
"#,
    );
}

#[test]
fn clocking_event_right_after_a_leading_delay() {
    check(
        r#"
module m(input logic clk, clk2, a, b);
  a_mc: assert property (@(posedge clk) a |=> ##1 @(posedge clk2) $fell(b));
  c_mc: cover property (@(posedge clk) (##1 @(posedge clk2) ##0 $fell(b)));
endmodule
"#,
    );
}

#[test]
fn delay_then_clocking_event_in_a_sequence_declaration() {
    check(
        r#"
module m(input logic clk, clk2, a, b);
  sequence s_mc;
    @(posedge clk) a ##1 (##1 @(posedge clk2) $fell(b));
  endsequence
  c_mc: cover property (s_mc);
endmodule
"#,
    );
}
