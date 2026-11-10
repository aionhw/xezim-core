//! §23.8 (upward name referencing): a hierarchical name in an inlined body
//! whose first segment is not one of the body's own declarations is resolved
//! scope by scope upward — as the INSTANCE name of a child of an enclosing
//! scope, or as the DEFINITION name of one (`node1.req1` from a module bound
//! into `u_node1`, an instance of `node1`) — and rewritten to the matched
//! scope's absolute, rooted path. The runtime used to search for it with a
//! scope hint and bound it to a same-named signal of the top module instead
//! (aionhw/xezim#890).

use xezim_core::ast::expr::{ExprKind, Expression};
use xezim_core::elaborate::ElaboratedModule;

fn elab(src: &str) -> ElaboratedModule {
    let (_, mut m) = xezim_core::parse_and_elaborate_multi(
        &[src.to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .expect("elaborate");
    m.materialize_pending();
    m
}

/// `(rooted, dotted path)` of an identifier expression.
fn ident(e: &Expression) -> (bool, String) {
    match &e.kind {
        ExprKind::Ident(h) => (
            h.root.is_some(),
            h.path
                .iter()
                .map(|s| s.name.name.as_str())
                .collect::<Vec<_>>()
                .join("."),
        ),
        other => panic!("not an identifier: {other:?}"),
    }
}

/// The right-hand side of the continuous assignment driving `lhs`.
fn rhs_of(m: &ElaboratedModule, lhs: &str) -> (bool, String) {
    let ca = m
        .continuous_assigns
        .iter()
        .find(|ca| ident(&ca.lhs).1 == lhs)
        .unwrap_or_else(|| {
            panic!(
                "no continuous assign drives {lhs}; have {:?}",
                m.continuous_assigns
                    .iter()
                    .map(|ca| ident(&ca.lhs).1)
                    .collect::<Vec<_>>()
            )
        });
    ident(&ca.rhs)
}

const WATCH: &str = r#"
module node (input logic clk, input logic req);
  logic [7:0] tag;
endmodule
module watch (input logic clk);
  logic [7:0] seen;
  logic r;
  assign seen = node.tag;
  assign r = node.req;
endmodule
bind node watch u_watch (.clk(clk));
"#;

/// Each bound watcher names ITS target by module name: the nearest enclosing
/// instance of that module, not the top module's same-named bait signal.
#[test]
fn module_name_head_resolves_to_the_enclosing_instance_of_that_module() {
    let m = elab(&format!(
        "{WATCH}{}",
        r#"
module top;
  logic clk = 0, req = 1;
  logic [7:0] tag = 8'hEE;
  node a (.clk(clk), .req(1'b0));
  node b (.clk(clk), .req(1'b0));
endmodule
"#
    ));
    assert_eq!(rhs_of(&m, "a.u_watch.seen"), (true, "a.tag".to_string()));
    assert_eq!(rhs_of(&m, "b.u_watch.seen"), (true, "b.tag".to_string()));
    // An unconnected port of the target is still the target's own net.
    assert_eq!(rhs_of(&m, "a.u_watch.r"), (true, "a.req".to_string()));
}

/// A target inside a generate loop and one two levels down a wrapper: the
/// walk crosses generate scopes and finds the nearest enclosing instance.
#[test]
fn module_name_head_crosses_generate_and_wrapper_scopes() {
    let m = elab(&format!(
        "{WATCH}{}",
        r#"
module wrap (input logic clk);
  node u_node (.clk(clk), .req(1'b1));
endmodule
module top;
  logic clk = 0;
  logic [7:0] tag = 8'hEE;
  for (genvar i = 0; i < 2; i++) begin : g
    node u_node (.clk(clk), .req(1'b0));
  end
  wrap u_wrap (.clk(clk));
endmodule
"#
    ));
    assert_eq!(
        rhs_of(&m, "g[0].u_node.u_watch.seen"),
        (true, "g[0].u_node.tag".to_string())
    );
    assert_eq!(
        rhs_of(&m, "g[1].u_node.u_watch.seen"),
        (true, "g[1].u_node.tag".to_string())
    );
    assert_eq!(
        rhs_of(&m, "u_wrap.u_node.u_watch.seen"),
        (true, "u_wrap.u_node.tag".to_string())
    );
}

/// §23.8 step b: in an enclosing scope the first segment matches that
/// scope's own module name (an ancestor two levels up), a child of it by
/// INSTANCE name (a sibling of the parent, the grandparent's child, an
/// interface instance of the bind target) or a generate label it declares.
/// A module name that is not an ancestor's (a sibling's) matches nothing —
/// the reference simulator rejects such a name — and is left alone.
#[test]
fn instance_and_definition_heads_in_enclosing_scopes() {
    let m = elab(
        r#"
interface tic_if;
  logic member = 1'b1;
endinterface
module sib;
  logic s = 1'b1;
endmodule
module leaf;
  int z, v, q, g, w;
  assign z = u_sib.s;    // instance name of a sibling of the parent
  assign v = outer.o;    // module name of an ancestor two levels up
  assign q = u_mid.m;    // instance name of the parent, a child of the grandparent
  assign g = gb.x;       // generate label of the grandparent
  assign w = sib.s;      // module name of a sibling: no match
  logic t;
  assign t = tic.member; // interface instance of the parent
endmodule
module mid;
  int m = 5;
  tic_if tic ();
  sib u_sib ();
  leaf u_leaf ();
endmodule
module outer;
  int o = 100;
  if (1) begin : gb
    int x = 42;
  end
  mid u_mid ();
endmodule
module top;
  int o = 2000, m = 1000, x = 99;
  logic s = 1'b0, member = 1'b0;
  outer u_outer ();
endmodule
"#,
    );
    let leaf = "u_outer.u_mid.u_leaf";
    assert_eq!(
        rhs_of(&m, &format!("{leaf}.z")),
        (true, "u_outer.u_mid.u_sib.s".to_string())
    );
    assert_eq!(
        rhs_of(&m, &format!("{leaf}.v")),
        (true, "u_outer.o".to_string())
    );
    assert_eq!(
        rhs_of(&m, &format!("{leaf}.q")),
        (true, "u_outer.u_mid.m".to_string())
    );
    assert_eq!(
        rhs_of(&m, &format!("{leaf}.g")),
        (true, "u_outer.gb.x".to_string())
    );
    assert_eq!(
        rhs_of(&m, &format!("{leaf}.w")),
        (false, "sib.s".to_string())
    );
    assert_eq!(
        rhs_of(&m, &format!("{leaf}.t")),
        (true, "u_outer.u_mid.tic.member".to_string())
    );
}

/// §23.8 step a: a name headed by a scope the current module declares itself
/// — a child instance (even one declared later), a generate label — is a
/// downward reference and keeps its scope-relative form; and a head that is
/// the module name of the enclosing instance AND an instance name further up
/// is the nearest enclosing instance of that module (as in the reference
/// simulator).
#[test]
fn own_scopes_stay_downward_and_instance_names_win() {
    let m = elab(
        r#"
module k;
  int x = 1;
endmodule
module m;
  int x = 2;
  leaf u_leaf ();
endmodule
module leaf;
  int y, d, g;
  assign y = m.x;          // `m`: instance of k at top, and module of the parent
  assign d = u_later.x;    // child declared after this reference
  assign g = gb.x;         // own generate label
  k u_later ();
  if (1) begin : gb
    int x = 3;
  end
endmodule
module top;
  k m ();
  m u_m ();
endmodule
"#,
    );
    assert_eq!(rhs_of(&m, "u_m.u_leaf.y"), (true, "u_m.x".to_string()));
    let (rooted, d) = rhs_of(&m, "u_m.u_leaf.d");
    assert!(
        !rooted && d.ends_with("u_later.x"),
        "downward child reference: {d}"
    );
    let (rooted, g) = rhs_of(&m, "u_m.u_leaf.g");
    assert!(!rooted && g.ends_with("gb.x"), "own generate label: {g}");
}
