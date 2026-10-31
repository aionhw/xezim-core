//! §23.11: the instances a `bind` directive selects — by module name, by
//! instance name or path, and by a path whose generate and array indices are
//! constant expressions evaluated in the directive's scope (its own
//! parameters, an enclosing scope's, the top's, or the compilation unit's).
//! Pins the targets while their selection is indexed instead of scanned
//! (aionhw/xezim#679).

fn elaborate(src: &str) -> xezim_core::ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[src.to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .expect("elaborate")
    .1
}

/// Paths of the instances of `def`, sorted.
fn instances_of(m: &xezim_core::ElaboratedModule, def: &str) -> Vec<String> {
    let mut paths: Vec<String> = m
        .instances
        .iter()
        .filter(|i| i.def_name == def)
        .map(|i| i.path.clone())
        .collect();
    paths.sort();
    paths
}

const CHK: &str = r#"
module chk (input logic a);
endmodule
module sub (input logic clk);
endmodule
"#;

#[test]
fn bind_by_module_name_selects_every_instance_of_the_module() {
    let m = elaborate(&format!(
        "{CHK}{}",
        r#"
module leaf (input logic clk);
endmodule
module top;
  logic clk = 0;
  for (genvar i = 0; i < 3; i++) begin : g
    leaf u (.clk(clk));
  end
  leaf v (.clk(clk));
endmodule
bind leaf chk m (.a(clk));
"#
    ));
    assert_eq!(
        instances_of(&m, "chk"),
        ["g[0].u.m", "g[1].u.m", "g[2].u.m", "v.m"]
    );
}

#[test]
fn bind_by_instance_path_and_by_instance_name() {
    let m = elaborate(&format!(
        "{CHK}{}",
        r#"
module leaf (input logic clk);
  sub u (.clk(clk));
  bind u chk inner (.a(clk));
endmodule
module top;
  logic clk = 0;
  leaf u0 (.clk(clk));
  leaf u1 (.clk(clk));
  // An instance named like a module: the instance wins (§23.11).
  sub leaf (.clk(clk));
  bind leaf chk by_name (.a(clk));
endmodule
bind top.u1 chk p (.a(clk));
bind $root.top.u0.u chk q (.a(clk));
"#
    ));
    assert_eq!(
        instances_of(&m, "chk"),
        ["leaf.by_name", "u0.u.inner", "u0.u.q", "u1.p", "u1.u.inner"]
    );
}

#[test]
fn indexed_target_in_a_replicated_module_uses_each_instance_parameter() {
    let m = elaborate(&format!(
        "{CHK}{}",
        r#"
module leaf #(parameter int W = 2) (input logic clk);
  for (genvar i = 0; i < 3; i++) begin : g
    sub l (.clk(clk));
  end
  bind g[W-1].l chk c (.a(clk));
endmodule
module top;
  logic clk = 0;
  for (genvar i = 0; i < 2; i++) begin : g
    for (genvar j = 0; j < 2; j++) begin : h
      leaf #(.W(1 + (i + 2 * j) % 3)) w (.clk(clk));
    end
  end
endmodule
"#
    ));
    assert_eq!(
        instances_of(&m, "chk"),
        [
            "g[0].h[0].w.g[0].l.c",
            "g[0].h[1].w.g[2].l.c",
            "g[1].h[0].w.g[1].l.c",
            "g[1].h[1].w.g[0].l.c"
        ]
    );
}

#[test]
fn a_scope_without_the_name_does_not_see_another_directive_scope() {
    // `a` declares P and binds first; `b` does not, so its P is the top's.
    let m = elaborate(&format!(
        "{CHK}{}",
        r#"
module la #(parameter int P = 1) (input logic clk);
  for (genvar i = 0; i < 2; i++) begin : g
    sub l (.clk(clk));
  end
  bind g[P].l chk ca (.a(clk));
endmodule
module lb (input logic clk);
  for (genvar i = 0; i < 2; i++) begin : g
    sub l (.clk(clk));
  end
  bind g[P].l chk cb (.a(clk));
endmodule
module top;
  localparam int P = 0;
  logic clk = 0;
  la a (.clk(clk));
  lb b (.clk(clk));
  la #(.P(0)) c (.clk(clk));
endmodule
"#
    ));
    assert_eq!(
        instances_of(&m, "chk"),
        ["a.g[1].l.ca", "b.g[0].l.cb", "c.g[0].l.ca"]
    );
}

#[test]
fn unit_and_top_scope_indices_use_their_own_constants() {
    // §3.12.1: the `$unit` directive's K is the compilation unit's, not the
    // top's same-named localparam; the top's own directive sees the top's,
    // and a qualified name reaches an instance's parameter.
    let m = elaborate(&format!(
        "{CHK}{}",
        r#"
localparam int K = 2;
module leaf #(parameter int S = 1) (input logic clk);
endmodule
module top;
  localparam int K = 0;
  logic clk = 0;
  for (genvar i = 0; i < 3; i++) begin : g
    sub l (.clk(clk));
  end
  leaf #(.S(1)) cfg (.clk(clk));
  bind g[K].l chk in_top (.a(clk));
  bind g[cfg.S].l chk by_qualified (.a(clk));
endmodule
bind top.g[K].l chk in_unit (.a(clk));
bind top.g[top.K + 1].l chk top_qualified (.a(clk));
"#
    ));
    assert_eq!(
        instances_of(&m, "chk"),
        [
            "g[0].l.in_top",
            "g[1].l.by_qualified",
            "g[1].l.top_qualified",
            "g[2].l.in_unit"
        ]
    );
}
