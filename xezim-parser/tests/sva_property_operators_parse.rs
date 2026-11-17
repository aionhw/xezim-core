//! §16.12 property operators that failed to parse inside a concurrent
//! assertion:
//!
//!   * §16.12.8 `p implies q` — "expected RParen, found KwImplies".
//!   * §16.12.10 `nexttime [n] p` / `s_nexttime [n] p` — the bracketed count
//!     after the keyword: "expected expression, found LBracket".
//!   * §16.12.11 `always [m:n] p` / `s_always [m:n] p` and §16.12.13
//!     `eventually [m:n] p` / `s_eventually [m:n] p` — the bracketed range.
//!   * §16.12.16 the property `case` — "expected expression, found KwCase".

use sv_parser::parse;

fn errors(src: &str) -> Vec<String> {
    parse(src)
        .errors
        .iter()
        .map(|e| format!("{:?}", e))
        .collect()
}

/// A property body in a minimal module, both inline and in a declaration.
fn prop(body: &str) -> String {
    format!(
        r#"
module m(input logic clk, a, b, c, logic [1:0] s);
  property p; @(posedge clk) {body}; endproperty
  ap: assert property (p);
  aq: assert property (@(posedge clk) {body});
endmodule
"#
    )
}

fn assert_parses(bodies: &[&str]) {
    for body in bodies {
        let e = errors(&prop(body));
        assert!(e.is_empty(), "`{}` must parse, got: {:?}", body, e);
    }
}

fn assert_rejected(body: &str, needle: &str) {
    let e = errors(&prop(body));
    assert!(
        e.iter().any(|m| m.contains(needle)),
        "`{}` must be rejected with `{}`, got: {:?}",
        body,
        needle,
        e
    );
}

#[test]
fn implies_parses() {
    assert_parses(&[
        "a implies b",
        "(a implies b)",
        "(a ##1 b) implies (b ##1 c)",
        "a |-> (b implies c)",
        "a implies b implies c",
    ]);
}

#[test]
fn nexttime_with_a_count_parses() {
    assert_parses(&[
        "nexttime [2] b",
        "s_nexttime [2] b",
        "a |-> nexttime [0] b",
        "a |-> nexttime [1 + 1] (b ##1 c)",
    ]);
}

#[test]
fn ranged_always_and_eventually_parse() {
    assert_parses(&[
        "a |-> always [1:2] b",
        "a |-> s_always [1:2] b",
        "a |-> always [2:$] b",
        "a |-> always [0:0] (b && c)",
        "a |-> eventually [1:2] b",
        "a |-> s_eventually [1:2] b",
        "a |-> s_eventually [1:$] b",
        "a |-> s_eventually [0:2] (b ##1 c)",
    ]);
}

#[test]
fn property_case_parses() {
    assert_parses(&[
        "case (s) 2'd0: a; default: b; endcase",
        "case (s) 2'd0, 2'd1: a; 2'd2: b |-> c; endcase",
        "case (s) default: a && b; endcase",
        "a |-> case (s) 2'd0: b; default: c; endcase",
    ]);
}

/// The unranged forms and procedural `case` statements keep parsing.
#[test]
fn existing_forms_still_parse() {
    assert_parses(&[
        "nexttime b",
        "s_nexttime b",
        "always b",
        "s_eventually b",
        "a |-> b",
        "if (a) b else c",
    ]);
    let src = r#"
module m(input logic clk, logic [1:0] s, output logic q);
  always @(posedge clk) case (s) 2'd0: q <= 1'b0; default: q <= 1'b1; endcase
  assert property (@(posedge clk) always q);
endmodule
"#;
    let e = errors(src);
    assert!(e.is_empty(), "got: {:?}", e);
}

/// Shapes the LRM forbids, and ranged forms over operands the lowering does
/// not cover, are reported instead of being run with other semantics.
#[test]
fn unsupported_ranges_are_reported() {
    // §16.12.13: `eventually` takes a bounded range.
    assert_rejected("a |-> eventually b", "eventually");
    assert_rejected("a |-> eventually [1:$] b", "eventually");
    // §16.12.11: `s_always` takes a bounded range.
    assert_rejected("a |-> s_always [1:$] b", "s_always");
    // Not supported: a ranged `always` of a sequence, a ranged eventually of
    // a property.
    assert_rejected("a |-> always [1:2] (b ##1 c)", "always");
    assert_rejected("s_eventually [1:2] (b |-> c)", "s_eventually");
}
