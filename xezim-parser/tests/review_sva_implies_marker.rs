//! §16.12.8, §16.14.8 (z): `p implies q` is kept as `$sva_implies(p, q)`.
//! Lowered to `(not p) or q`, an attempt whose `p` fails was a nonvacuous
//! success, so its pass action ran, and an `x` antecedent failed it; §16.14.8
//! makes the attempt vacuous unless `p` holds nonvacuously.
//! §16.12.13, §16.12.14: a ranged `eventually` of an abort property is a
//! ranged eventually of a property, which the `##[m:n]` lowering cannot
//! express, so it is reported like the other properties.

use sv_parser::parse;

fn parsed(body: &str) -> (Vec<String>, String) {
    let src = format!(
        r#"
module m(input logic clk, a, b, c, r);
  property p; @(posedge clk) {body}; endproperty
  ap: assert property (p);
  aq: assert property (@(posedge clk) {body});
endmodule
"#
    );
    let r = parse(&src);
    let errors = r.errors.iter().map(|e| format!("{:?}", e)).collect();
    (errors, format!("{:?}", r.source))
}

#[test]
fn implies_is_kept_as_its_marker() {
    for body in [
        "a implies b",
        "(a ##1 b) implies (b ##1 c)",
        "a |-> (b implies c)",
    ] {
        let (e, ast) = parsed(body);
        assert!(e.is_empty(), "`{}` must parse, got: {:?}", body, e);
        assert_eq!(
            ast.matches("\"$sva_implies\"").count(),
            2,
            "`{}`: {}",
            body,
            ast
        );
        assert!(
            !ast.contains("SeqOr"),
            "`{}` lowered to an `or`: {}",
            body,
            ast
        );
    }
    // Right associative: `a implies (b implies c)`.
    let (e, ast) = parsed("a implies b implies c");
    assert!(e.is_empty(), "got: {:?}", e);
    assert_eq!(ast.matches("\"$sva_implies\"").count(), 4, "{}", ast);
}

#[test]
fn a_ranged_eventually_of_an_abort_or_implies_is_reported() {
    for body in [
        "a |-> s_eventually [1:2] (accept_on (r) b)",
        "a |-> eventually [1:2] (reject_on (r) b)",
        "a |-> s_eventually [1:2] (b implies c)",
    ] {
        let (e, _) = parsed(body);
        assert!(
            e.iter()
                .any(|m| m.contains("of a property is not supported")),
            "`{}` must be rejected, got: {:?}",
            body,
            e
        );
    }
}
