//! §23.3.2, §23.3.3: an instance is elaborated from its module's body, and
//! its ports connect as continuous assignments (§10.3). xezim-core replaces an
//! instance of a module named `gated_clk_cell` by a direct assignment of its
//! clock, an optimization that is only equivalent when the module's body is
//! the OpenC910 pass-through (`assign clk_out = clk_in;` plus dead enable
//! logic). Another design's `gated_clk_cell` that really gates its clock
//! (Wujian100 latches the enable) is elaborated as written, with its signals
//! and sub-instances, reachable by hierarchical name (§23.6). So is a
//! pass-through whose clock net has a delay (§6.7.1, §28.16), a strength or a
//! resolving net type (§6.6), since the direct assignment would drop it.

fn elaborate(src: &str, top: &str) -> xezim_core::ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[src.to_string()],
        Some(top),
        &[],
        &[format!("{top}.sv")],
        &[],
    )
    .expect("elaborate")
    .1
}

#[test]
fn passthrough_cell_is_a_direct_assignment() {
    let m = elaborate(
        r#"
module gated_clk_cell(clk_in, global_en, module_en, local_en, external_en,
                      pad_yy_icg_scan_en, clk_out);
  input  clk_in;
  input  global_en;
  input  module_en;
  input  local_en;
  input  external_en;
  input  pad_yy_icg_scan_en;
  output clk_out;
  wire   clk_en_bf_latch;
  wire   SE;
  assign clk_en_bf_latch = (global_en && (module_en || local_en)) || external_en;
  assign SE = pad_yy_icg_scan_en;
  assign clk_out = clk_in;
endmodule
module top;
  reg clk = 0, en = 0;
  wire gclk;
  gated_clk_cell u (.clk_in(clk), .global_en(en), .module_en(en), .local_en(en),
                    .external_en(en), .pad_yy_icg_scan_en(1'b0), .clk_out(gclk));
endmodule
"#,
        "top",
    );
    assert!(
        !m.signals.contains_key("u.clk_en_bf_latch"),
        "the pass-through cell is not inlined"
    );
}

#[test]
fn real_clock_gate_named_gated_clk_cell_is_elaborated() {
    let m = elaborate(
        r#"
module latch_cell(input clk, input d, output reg q);
  always @(*) if (!clk) q = d;
endmodule
module gated_clk_cell(input clk_in, input en, output clk_out);
  wire en_l;
  latch_cell x_lat (.clk(clk_in), .d(en), .q(en_l));
  assign clk_out = clk_in & en_l;
endmodule
module top;
  reg clk = 0;
  wire gclk;
  gated_clk_cell u (.clk_in(clk), .en(1'b0), .clk_out(gclk));
endmodule
"#,
        "top",
    );
    assert!(
        m.signals.contains_key("u.en_l"),
        "the gate's body is elaborated"
    );
    assert!(
        m.signals.contains_key("u.x_lat.q"),
        "its sub-instance exists for hierarchical references"
    );
}

/// The body is `assign clk_out = clk_in;`, but the clock net shapes what the
/// connection sees: a net delay holds each edge back (§6.7.1, §28.16), and a
/// `tri0`/`tri1` net pulls a floating clock to a value (§6.6.5). These cells
/// are elaborated as written, so their delay or net type stays in effect.
#[test]
fn passthrough_with_a_shaped_clock_net_is_elaborated() {
    let cells = [
        ("net delay", "output clk_out; wire #5 clk_out;"),
        ("rise and fall delays", "output clk_out; wire #(2, 3) clk_out;"),
        ("pulled net", "output clk_out; tri1 clk_out;"),
        ("pulled port", "output tri0 clk_out;"),
        ("delayed input", "output clk_out; wire #1 clk_in;"),
    ];
    for (what, decl) in cells {
        let m = elaborate(
            &format!(
                r#"
module gated_clk_cell(clk_in, en, clk_out);
  input clk_in;
  input en;
  {decl}
  wire en_q;
  assign en_q = en;
  assign clk_out = clk_in;
endmodule
module top;
  reg clk = 0;
  wire gclk;
  gated_clk_cell u (.clk_in(clk), .en(1'b1), .clk_out(gclk));
endmodule
"#
            ),
            "top",
        );
        assert!(
            m.signals.contains_key("u.en_q"),
            "{what}: the cell is elaborated as written"
        );
    }
}
