//! §23.3.2.4: `.*` fills every port a connection list does not name, including
//! a non-ANSI header. That header is only a name list; direction and type
//! come from later `input` / `output` declarations. Expanding `.*` for ANSI
//! ports alone left the unnamed inputs unconnected, so they read Z.

fn elab(src: &str) -> xezim_core::ElaboratedModule {
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

#[test]
fn wildcard_connects_nonansi_ports() {
    let m = elab(
        r#"
module child(clk, rst, din, dout);
  input clk;
  input rst;
  input [7:0] din;
  output [7:0] dout;
  assign dout = din;
endmodule
module top;
  logic clk;
  logic rst;
  logic [7:0] din;
  logic [7:0] dout_tied;
  logic [7:0] dout_over;
  logic other_clk;
  child tied (.*, .dout(dout_tied));
  child over (.*, .clk(other_clk), .dout(dout_over));
endmodule
"#,
    );
    let alias = |formal: &str| m.port_aliases.get(formal).map(String::as_str);
    assert_eq!(alias("tied.clk"), Some("clk"));
    assert_eq!(alias("tied.rst"), Some("rst"));
    assert_eq!(alias("tied.din"), Some("din"));
    assert_eq!(alias("tied.dout"), Some("dout_tied"));
    // An explicit connection wins over `.*`.
    assert_eq!(alias("over.clk"), Some("other_clk"));
    assert_eq!(alias("over.rst"), Some("rst"));
    assert_eq!(alias("over.din"), Some("din"));
}

// §23.3.2.4 (core #163): `.*` connects only the ports that have a name, in a
// nested parent as in the top, outputs as inputs. A null port and an unnamed
// port expression carry the parser's placeholder names and stay unconnected;
// the placeholders used to be connected like named ports, so a non-ANSI
// parent's own port expression was wired to the child's.

/// The net a port formal is finally aliased to, through every enclosing
/// instance's own port aliases.
fn resolved<'m>(m: &'m xezim_core::ElaboratedModule, formal: &'m str) -> &'m str {
    let mut n = formal;
    while let Some(next) = m.port_aliases.get(n) {
        n = next;
    }
    n
}

/// The port aliases of the child instance `child` (its path with a trailing
/// dot) that involve a placeholder name on either side.
fn placeholder_aliases<'m>(m: &'m xezim_core::ElaboratedModule, child: &str) -> Vec<&'m String> {
    let mut v: Vec<&String> = m
        .port_aliases
        .iter()
        .filter(|(k, v)| k.starts_with(child) && (k.contains("__xz_") || v.contains("__xz_")))
        .map(|(k, _)| k)
        .collect();
    v.sort();
    v
}

#[test]
fn wildcard_connects_an_output_in_a_nested_parent() {
    let m = elab(
        r#"
module leaf(clk, d, q);
  input clk;
  input d;
  output q;
  assign q = d;
endmodule
module mid(clk, d, q);
  input clk;
  input d;
  output q;
  leaf u(.*);
endmodule
module top;
  logic clk;
  logic d;
  logic q;
  mid m(.clk(clk), .d(d), .q(q));
endmodule
"#,
    );
    // Each `.*` port binds to the nested parent's own port net, which is the
    // top's net.
    assert_eq!(resolved(&m, "m.u.clk"), "clk");
    assert_eq!(resolved(&m, "m.u.d"), "d");
    assert_eq!(resolved(&m, "m.u.q"), "q");
}

#[test]
fn wildcard_skips_a_null_port_and_a_port_expression() {
    let m = elab(
        r#"
module leaf(a[1:0], , q);
  input [3:0] a;
  output q;
  assign q = ^a;
endmodule
module mid(b[1:0], q);
  input [3:0] b;
  output q;
  logic [3:0] a;
  assign a = b;
  leaf u(.*);
endmodule
module top;
  logic [1:0] x;
  logic q;
  mid m(x, q);
endmodule
"#,
    );
    assert_eq!(placeholder_aliases(&m, "m.u."), Vec::<&String>::new());
    assert_eq!(resolved(&m, "m.u.q"), "q");
}

#[test]
fn wildcard_skips_a_trailing_null_port_of_a_top_level_child() {
    let m = elab(
        r#"
module leaf(a, , );
  input a;
endmodule
module top;
  logic a;
  leaf u(.*);
endmodule
"#,
    );
    assert_eq!(placeholder_aliases(&m, "u."), Vec::<&String>::new());
    assert_eq!(m.port_aliases.get("u.a").map(String::as_str), Some("a"));
}
