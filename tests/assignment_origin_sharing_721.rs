//! aionhw/xezim#721: a continuous assignment the source spells out records
//! the span of its statement and the instance scope it was elaborated in
//! (`ContinuousAssignment::origin`). The assignments of one instance hold
//! one scope string between them; each keeps its own span.

use std::collections::BTreeMap;
use std::sync::Arc;
use xezim_core::ElaboratedModule;

fn elaborate(src: &str) -> ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[src.to_string()],
        Some("top"),
        &[],
        &["t.sv".to_string()],
        &[],
    )
    .map(|(_, mut m)| {
        // The assignments of instances are deferred until the design is
        // published (an artifact, the design cache).
        m.materialize_pending();
        m
    })
    .expect("elaborates")
}

const SRC: &str = "
module unit #(parameter int D = 1) (input wire pulse, output wire echo);
  wire mirrored = ~pulse;
  wire tap0, tap1, tap2;
  assign tap0 = pulse;
  assign tap1 = tap0, tap2 = tap1;
  assign #D echo = tap2 ^ mirrored;
endmodule
module mid (input wire pulse, output wire [1:0] echo);
  wire local_tap;
  assign local_tap = pulse;
  unit #(.D(2)) a (.pulse(local_tap), .echo(echo[0]));
  unit #(.D(4)) b (.pulse(local_tap), .echo(echo[1]));
endmodule
module top;
  reg pulse = 0;
  wire [1:0] e0, e1;
  wire both;
  wire seen = pulse;
  assign both = &e0 & &e1;
  mid m0 (.pulse(pulse), .echo(e0));
  mid m1 (.pulse(pulse), .echo(e1));
endmodule
";

/// Every scope with spelled-out assignments, with the origins recorded there.
fn by_scope(m: &ElaboratedModule) -> BTreeMap<String, Vec<(xezim_core::ast::Span, Arc<str>)>> {
    let mut out: BTreeMap<String, Vec<_>> = BTreeMap::new();
    for ca in &m.continuous_assigns {
        if let Some((span, scope)) = ca.origin() {
            out.entry(scope.to_string())
                .or_default()
                .push((*span, Arc::clone(scope)));
        }
    }
    out
}

#[test]
fn the_assignments_of_an_instance_share_one_scope_string() {
    let m = elaborate(SRC);
    let scopes = by_scope(&m);
    let names: Vec<&str> = scopes.keys().map(String::as_str).collect();
    assert_eq!(
        names,
        ["", "m0", "m0.a", "m0.b", "m1", "m1.a", "m1.b"],
        "every instance with an assign, and the top"
    );
    for (scope, origins) in &scopes {
        let first = &origins[0].1;
        for (_, held) in origins {
            assert!(Arc::ptr_eq(first, held), "scope {scope:?}");
        }
    }
    // The five assignments of `unit` (one a net declaration assignment).
    assert_eq!(scopes["m0.a"].len(), 5);
    assert_eq!(scopes["m1.b"].len(), 5);
    assert_eq!(scopes[""].len(), 2);
    // Two instances never share: the scope is the instance's.
    assert!(!Arc::ptr_eq(&scopes["m0.a"][0].1, &scopes["m0.b"][0].1));
}

#[test]
fn each_assignment_keeps_the_span_of_its_statement() {
    let m = elaborate(SRC);
    let scopes = by_scope(&m);
    let spans = |scope: &str| {
        let mut spans: Vec<_> = scopes[scope]
            .iter()
            .map(|(s, _)| (s.start, s.end))
            .collect();
        spans.sort_unstable();
        spans
    };
    // `assign tap1 = tap0, tap2 = tap1;` is one statement with two
    // assignments; the others have a span each.
    let mut distinct = spans("m0.a");
    distinct.dedup();
    assert_eq!(distinct.len(), 4);
    // A net declaration assignment records its initializer.
    let texts: Vec<&str> = distinct
        .iter()
        .map(|(s, e)| &SRC[*s as usize..*e as usize])
        .collect();
    assert!(texts.contains(&"~pulse"), "{texts:?}");
    for text in texts.iter().filter(|t| **t != "~pulse") {
        assert!(text.starts_with("assign ") && text.contains('='), "{text}");
    }
    // Instances of one module record the same statements.
    assert_eq!(spans("m0.a"), spans("m1.b"));
    assert_ne!(spans("m0"), spans("m0.a"));
}

/// A design restored from its serialized form reads the same origins.
#[test]
fn origins_survive_serialization() {
    let m = elaborate(SRC);
    let bytes = bincode::serde::encode_to_vec(&m.continuous_assigns, bincode::config::standard())
        .expect("encode");
    let (back, _): (Vec<xezim_core::elaborate::ContinuousAssignment>, _) =
        bincode::serde::decode_from_slice(&bytes, bincode::config::standard()).expect("decode");
    assert_eq!(back.len(), m.continuous_assigns.len());
    for (a, b) in m.continuous_assigns.iter().zip(&back) {
        assert_eq!(
            a.origin()
                .map(|(s, scope)| (s.start, s.end, &**scope)),
            b.origin()
                .map(|(s, scope)| (s.start, s.end, &**scope))
        );
    }
}
