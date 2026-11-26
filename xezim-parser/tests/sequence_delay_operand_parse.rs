//! IEEE 1800-2023 A.2.10: the operand of a cycle delay with no left operand
//! (`##N sequence_expr`) is any sequence_expr. A prefix delay took its operand
//! only when the next token was on a short list, so an operand opening with
//! an escaped name, a real, unbased or string literal, a concatenation or
//! `first_match` left a bare delay, and the enclosing parentheses reported
//! "unexpected". §16.13.1, §9.4.2: a clocking event inside a sequence may
//! also be `@ identifier`, whose name is the event, not the operand.

use sv_parser::parse;
use sv_parser::strict_check::strict_diagnostics;

/// Parses `body` as the property of a `cover property` and checks that it
/// parses cleanly and keeps the operand that names `opnd`.
fn check(body: &str) {
    let module = |prop: &str| {
        format!(
            "module m(input logic clk, clk2, a, opnd);\n  event e;\n  wire \\esc = opnd;\n  c: cover property ({prop});\nendmodule\n"
        )
    };
    let r = parse(&module(body));
    assert!(r.errors.is_empty(), "{body}: {:?}", r.errors);
    let strict = strict_diagnostics(&r.source.descriptions);
    assert!(strict.is_empty(), "{body}: {strict:?}");
    // The operand naming `opnd` is in the tree, not dropped: `opnd` occurs
    // more often than in the same module with a property that omits it.
    let count = |src: &str| {
        format!("{:?}", parse(src).source.descriptions)
            .matches("opnd")
            .count()
    };
    let base = count(&module("@(posedge clk) a"));
    assert!(count(&module(body)) > base, "{body}: operand dropped");
}

#[test]
fn concatenation_operand() {
    check("@(posedge clk) a ##1 (##1 {a, opnd} == 2'b11)");
    check("@(posedge clk) a ##1 (##1 {2{opnd}} == 2'b11)");
}

#[test]
fn literal_operands() {
    check("@(posedge clk) a ##1 (##1 '1 ##1 opnd)");
    check("@(posedge clk) a ##1 (##1 1.0 ##1 opnd)");
    check("@(posedge clk) a ##1 (##1 \"x\" == \"x\" ##1 opnd)");
}

#[test]
fn escaped_name_operand() {
    check("@(posedge clk) a ##1 (##1 \\esc  ##1 opnd)");
}

#[test]
fn first_match_operand() {
    check("@(posedge clk) a ##1 (##1 first_match(a ##1 opnd))");
    check("@(posedge clk) a ##1 (##[1:2] first_match(a ##1 opnd))");
}

#[test]
fn named_event_clocking_event() {
    check("@(posedge clk) a ##1 (##1 @e opnd)");
    check("@(posedge clk) a ##1 @e opnd");
    check("@(posedge clk) a ##1 (##1 @clk2 opnd)");
}
