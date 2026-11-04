//! §16.12.11: the `always` property operator must parse inside a concurrent
//! assertion. `assert property (@(posedge clk) always (|a) == (&a))` failed
//! with "expected expression, found KwAlways 'always'".

use sv_parser::parse;

fn errors(src: &str) -> Vec<String> {
    parse(src)
        .errors
        .iter()
        .map(|e| format!("{:?}", e))
        .collect()
}

#[test]
fn always_property_operator_parses() {
    let src = r#"
module m(input logic clk, logic [1:0] a);
  assert property (@(posedge clk) always (|a) == (&a));
  assert property (@(posedge clk) always ((|a) == (&a)));
endmodule
"#;
    let e = errors(src);
    assert!(e.is_empty(), "`always` property must parse, got: {:?}", e);
}

/// Always blocks next to it keep parsing as always blocks.
#[test]
fn always_blocks_still_parse() {
    let src = r#"
module m(input logic clk, logic [1:0] a);
  logic q;
  always @(posedge clk) q <= |a;
  always_comb begin end
  assert property (@(posedge clk) always q);
  always @(negedge clk) q <= &a;
endmodule
"#;
    let e = errors(src);
    assert!(e.is_empty(), "got: {:?}", e);
}
