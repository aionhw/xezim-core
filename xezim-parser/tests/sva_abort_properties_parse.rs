//! §16.12.14 abort properties, `accept_on`, `reject_on`, `sync_accept_on`
//! and `sync_reject_on`, failed to parse inside a concurrent assertion
//! ("expected expression, found KwAccept_on"). Each now parses to a marker
//! the assertion engine evaluates, `$sva_<operator>(condition, property)`,
//! whose property operand extends as far right as it can (Table 16-3: the
//! abort operators have the lowest precedence).

use sv_parser::parse;

fn parsed(src: &str) -> (Vec<String>, String) {
    let r = parse(src);
    let errors = r.errors.iter().map(|e| format!("{:?}", e)).collect();
    (errors, format!("{:?}", r.source))
}

/// A property body in a minimal module, both inline and in a declaration.
fn prop(body: &str) -> String {
    format!(
        r#"
module m(input logic clk, a, b, c, r);
  property p; @(posedge clk) {body}; endproperty
  ap: assert property (p);
  aq: assert property (@(posedge clk) {body});
endmodule
"#
    )
}

/// The text after the first occurrence of `marker` in the AST dump.
fn after<'a>(ast: &'a str, marker: &str) -> &'a str {
    let at = ast
        .find(marker)
        .unwrap_or_else(|| panic!("no `{}` in the AST", marker));
    &ast[at + marker.len()..]
}

#[test]
fn each_abort_operator_parses_to_its_marker() {
    for (word, marker) in [
        ("accept_on", "\"$sva_accept_on\""),
        ("reject_on", "\"$sva_reject_on\""),
        ("sync_accept_on", "\"$sva_sync_accept_on\""),
        ("sync_reject_on", "\"$sva_sync_reject_on\""),
    ] {
        let body = format!("{word} (r) a ##1 b");
        let (e, ast) = parsed(&prop(&body));
        assert!(e.is_empty(), "`{}` must parse, got: {:?}", body, e);
        // Both the declared and the inline assertion carry the marker.
        assert_eq!(ast.matches(marker).count(), 2, "`{}`: {}", body, ast);
    }
}

/// The property operand takes the whole implication, and an abort nests
/// inside a consequent and inside another abort.
#[test]
fn the_property_operand_extends_to_the_right() {
    let (e, ast) = parsed(&prop("accept_on (r) a |-> b"));
    assert!(e.is_empty(), "got: {:?}", e);
    assert!(
        after(&ast, "\"$sva_accept_on\"").contains("OrMinusArrow"),
        "the implication must be the operand: {}",
        ast
    );
    let (e, ast) = parsed(&prop("a |=> reject_on (r || c) b ##1 c"));
    assert!(e.is_empty(), "got: {:?}", e);
    assert!(
        after(&ast, "OrFatArrow").contains("\"$sva_reject_on\""),
        "the abort must be the consequent: {}",
        ast
    );
    let (e, ast) = parsed(&prop("accept_on (r) sync_reject_on (c) a until b"));
    assert!(e.is_empty(), "got: {:?}", e);
    assert!(
        after(&ast, "\"$sva_accept_on\"").contains("\"$sva_sync_reject_on\""),
        "got: {}",
        ast
    );
}

#[test]
fn a_missing_condition_is_reported() {
    let (e, _) = parsed(&prop("accept_on r a"));
    assert!(
        e.iter().any(|m| m.contains("condition in parentheses")),
        "got: {:?}",
        e
    );
}
