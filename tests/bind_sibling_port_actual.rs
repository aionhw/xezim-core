//! IEEE 1800-2023 §23.11, §23.8: a port connection actual whose HEAD names a
//! SIBLING instance created by `bind` must resolve exactly as the same
//! connection written out in the target's body.
//!
//! A `bind` adds its instances after the target's items were prepared, so two
//! registrations that written instances get for free were missing:
//!
//! * the bound instance names were not LOCAL names of the target scope, which
//!   is what the inlining rewrite uses to decide that a bare head is a child of
//!   the current instance (`expr_rewrite`'s `local_names` arm), and
//! * the bound instances were not recorded as children of the target scope in
//!   `UpwardScopes` until each one was inlined, so a bound instance inlined
//!   before its sibling could not find it at all.
//!
//! Both left the actual un-prefixed; once rooted it named a phantom top-level
//! instance (`$root.u_mon.arr[0]` where the written design says
//! `$root.h.u_mon.arr[0]`), the formal was driven by a signal nothing writes,
//! and the port kept its x. A whole-net actual hides this, because
//! `port_aliases` folds the leftover leaf name away — only a SELECTED actual
//! (unpacked-array element, associative-array element) shows it.
//!
//! Every case is asserted on the elaborated design: the connection has to land
//! on the target's own scope, and the bound design has to elaborate like the
//! design that writes the same instances out.

use xezim_core::ElaboratedModule;
use xezim_core::ast::expr::{ExprKind, Expression, NumberLiteral};

fn elaborate(src: &str) -> ElaboratedModule {
    let (_, mut m) = xezim_core::parse_and_elaborate_multi(
        &[src.to_string()],
        Some("tb"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .unwrap_or_else(|e| panic!("elaboration failed: {e}"));
    m.materialize_pending();
    m
}

/// The shared definitions of every case: a monitor with one of each actual
/// shape, and a DUT that samples its ports.
const DEFS: &str = "\
module mon;
  logic arr [0:0];
  logic aa [int];
  logic s;
  initial begin #5 arr[0] = 1'b1; aa[0] = 1'b1; s = 1'b1; end
endmodule
module dut (input logic vld);
  logic seen;
  initial #10 seen = vld;
endmodule
";

/// The top of every case: `tb` instantiating one host, so the expected actual
/// is always `$root.h.…`.
fn tail() -> &'static str {
    "
module tb;
  host h();
endmodule
"
}

/// The actual that drives the port whose path ends with `port`: the continuous
/// assignment's RHS, or the alias the whole-net connection folded to. A
/// whole-net connection is recorded BOTH ways — as an assignment and as the
/// alias it folds to — so the two spellings are deduplicated rather than
/// counted twice.
fn actual_for(m: &ElaboratedModule, port: &str) -> String {
    let mut hits: Vec<String> = m
        .continuous_assigns
        .iter()
        .filter(|ca| path_of(&ca.lhs).ends_with(port))
        .map(|ca| text(&ca.rhs))
        .collect();
    if let Some(alias) = m
        .port_aliases
        .iter()
        .find(|(k, _)| k.ends_with(port))
        .map(|(_, v)| v.clone())
    {
        hits.push(alias);
    }
    hits.sort();
    // The same connection spelled with and without its explicit root is one
    // answer, not two; keep the rooted spelling, which is the fuller one.
    hits.dedup_by(|a, b| unroot(a) == unroot(b));
    assert_eq!(hits.len(), 1, "expected one connection for {port}");
    let rooted = hits.iter().find(|h| h.starts_with("$root.")).cloned();
    rooted.or_else(|| hits.into_iter().next()).unwrap()
}

/// A connection spelling without its leading explicit root.
fn unroot(actual: &str) -> &str {
    actual.strip_prefix("$root.").unwrap_or(actual)
}

fn instance_paths(m: &ElaboratedModule) -> Vec<String> {
    m.instances.iter().map(|i| i.path.clone()).collect()
}

fn path_of(e: &Expression) -> String {
    match &e.kind {
        ExprKind::Ident(h) => h
            .path
            .iter()
            .map(|s| s.name.name.as_str())
            .collect::<Vec<_>>()
            .join("."),
        other => panic!("unexpected connection target {other:?}"),
    }
}

/// A readable spelling of an actual: `root.a.b[0]`, selects included.
fn text(e: &Expression) -> String {
    match &e.kind {
        ExprKind::Ident(h) => {
            let p = h
                .path
                .iter()
                .map(|s| {
                    let mut seg = s.name.name.clone();
                    for sel in &s.selects {
                        seg.push_str(&format!("[{}]", text(sel)));
                    }
                    seg
                })
                .collect::<Vec<_>>()
                .join(".");
            match &h.root {
                Some(r) => format!("{r}.{p}"),
                None => p,
            }
        }
        ExprKind::Index { expr, index } => format!("{}[{}]", text(expr), text(index)),
        ExprKind::MemberAccess { expr, member } => format!("{}.{}", text(expr), member.name),
        ExprKind::Paren(inner) => text(inner),
        ExprKind::Number(NumberLiteral::Integer { value, .. }) => value.clone(),
        other => panic!("unexpected actual {other:?}"),
    }
}

/// A bound sibling instance's UNPACKED ARRAY ELEMENT, as a port actual.
#[test]
fn bound_sibling_array_element() {
    let written = elaborate(&format!(
        "{DEFS}module host; mon u_mon(); dut u_dut(.vld(u_mon.arr[0])); endmodule{tail}",
        tail = tail()
    ));
    let bound = elaborate(&format!(
        "{DEFS}module host; endmodule
         bind tb.h mon u_mon();
         bind tb.h dut u_dut(.vld(u_mon.arr[0]));{tail}",
        tail = tail()
    ));
    assert_eq!(
        actual_for(&bound, "u_dut.vld"),
        "$root.h.u_mon.arr[0]",
        "the actual must stay inside the target scope"
    );
    assert_eq!(
        actual_for(&bound, "u_dut.vld"),
        actual_for(&written, "u_dut.vld"),
        "bound must connect like the written instance"
    );
    assert_eq!(instance_paths(&bound), instance_paths(&written));
    assert!(
        !bound.signals.keys().any(|s| s.starts_with("u_mon.")),
        "a phantom top-level u_mon appeared: {:?}",
        bound
            .signals
            .keys()
            .filter(|s| s.contains("u_mon"))
            .collect::<Vec<_>>()
    );
}

/// A bound sibling instance's ASSOCIATIVE ARRAY ELEMENT, as a port actual.
#[test]
fn bound_sibling_associative_array_element() {
    let written = elaborate(&format!(
        "{DEFS}module host; mon u_mon(); dut u_dut(.vld(u_mon.aa[0])); endmodule{tail}",
        tail = tail()
    ));
    let bound = elaborate(&format!(
        "{DEFS}module host; endmodule
         bind tb.h mon u_mon();
         bind tb.h dut u_dut(.vld(u_mon.aa[0]));{tail}",
        tail = tail()
    ));
    assert_eq!(
        actual_for(&bound, "u_dut.vld"),
        "$root.h.u_mon.aa[0]",
        "the actual must stay inside the target scope"
    );
    assert_eq!(
        actual_for(&bound, "u_dut.vld"),
        actual_for(&written, "u_dut.vld"),
        "bound must connect like the written instance"
    );
    assert_eq!(instance_paths(&bound), instance_paths(&written));
}

/// A PLAIN DOTTED actual under a bound head — the shape that already worked,
/// kept covered because `port_aliases` rescues it rather than resolving it.
#[test]
fn bound_sibling_plain_dotted_actual() {
    let bound = elaborate(&format!(
        "{DEFS}module host; endmodule
         bind tb.h mon u_mon();
         bind tb.h dut u_dut(.vld(u_mon.s));{tail}",
        tail = tail()
    ));
    // The whole-net connection folds to an alias, which carries no explicit
    // root; what matters is that it names the monitor INSIDE the target.
    assert_eq!(unroot(&actual_for(&bound, "u_dut.vld")), "h.u_mon.s");
}

/// The CHILD of a bound module, connected to a SIBLING bound instance's array
/// element: the reference is resolved while inlining `mon_b`'s body, where the
/// sibling `u_a` exists only as a bound instance of the target.
#[test]
fn child_of_a_bound_module_reaches_its_bound_sibling() {
    let written = elaborate(&format!(
        "{DEFS}module mon_b; dut u_child(.vld(u_a.arr[0])); endmodule
         module host; mon u_a(); mon_b u_b(); endmodule{tail}",
        tail = tail()
    ));
    let bound = elaborate(&format!(
        "{DEFS}module mon_b; dut u_child(.vld(u_a.arr[0])); endmodule
         module host; endmodule
         bind tb.h mon u_a();
         bind tb.h mon_b u_b();{tail}",
        tail = tail()
    ));
    assert_eq!(
        actual_for(&bound, "u_b.u_child.vld"),
        "$root.h.u_a.arr[0]",
        "the child's actual must name the sibling bound instance"
    );
    assert_eq!(
        actual_for(&bound, "u_b.u_child.vld"),
        actual_for(&written, "u_b.u_child.vld"),
        "bound must connect like the written instance"
    );
    assert_eq!(instance_paths(&bound), instance_paths(&written));
}

/// The target is a CHILD, an INSTANCE-ARRAY element, a GENERATE-BLOCK scope and
/// a GRANDCHILD: the monitor is bound to the host, so the sibling reference has
/// to climb out of the deeper target scope and land back on the host.
#[test]
fn bound_sibling_from_a_deeper_target_scope() {
    for (host, scope) in [
        ("leaf u_in();", "u_in"),
        ("leaf u_in [0:0] ();", "u_in[0]"),
        (
            "for (genvar gi = 0; gi < 1; gi++) begin : gb leaf hb (); end",
            "gb[0].hb",
        ),
        ("leaf_a u_a ();", "u_a.u_b"),
    ] {
        let bound = elaborate(&format!(
            "{DEFS}module leaf; endmodule
             module leaf_b; endmodule
             module leaf_a; leaf_b u_b (); endmodule
             module host; {host} endmodule
             bind tb.h             mon    u_mon();
             bind tb.h.{scope} dut u_dut(.vld(u_mon.arr[0]));{tail}",
            host = host,
            scope = scope,
            tail = tail()
        ));
        assert_eq!(
            actual_for(&bound, "u_dut.vld"),
            "$root.h.u_mon.arr[0]",
            "target h.{scope}"
        );
    }
}

/// §23.11: bound instances are elaborated in the order the directives are
/// written, so a design whose binds reference each other behaves like the same
/// design written out in that order — including which direction a reference
/// between two bound instances goes.
#[test]
fn bound_instances_are_ordered_as_the_directives_are_written() {
    let written = elaborate(&format!(
        "{DEFS}module host; mon u_mon(); dut u_dut(.vld(u_mon.arr[0])); endmodule{tail}",
        tail = tail()
    ));
    let bound = elaborate(&format!(
        "{DEFS}module host; endmodule
         bind tb.h mon u_mon();
         bind tb.h dut u_dut(.vld(u_mon.arr[0]));{tail}",
        tail = tail()
    ));
    let paths = instance_paths(&bound);
    let at = |p: &str| {
        paths
            .iter()
            .position(|q| q == p)
            .unwrap_or_else(|| panic!("{p} missing from {paths:?}"))
    };
    assert!(
        at("h.u_mon") < at("h.u_dut"),
        "bound instances were elaborated in reverse directive order: {paths:?}"
    );
    assert_eq!(paths, instance_paths(&written));
}
