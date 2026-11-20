//! §6.19 / §6.10: an enum label used in a port actual of an instance inside
//! a module (`.din(st == STREAM)`, the enum typedef declared in that module)
//! names a declared constant, so it is not an implicit net of the instance.

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

#[test]
fn enum_label_in_a_port_actual_is_no_implicit_net() {
    let m = elaborate(
        r#"
module ff (input logic clk, input logic din, output logic dout);
  always_ff @(posedge clk) dout <= din;
endmodule
module thr #(parameter enum logic [1:0] {HP0, HP1} HP = HP1) (input logic clk,
    input enum logic [1:0] {PA, PB} pin);
  typedef enum logic [3:0] {IDLE = 4'd0, STREAM = 4'd6, RUN[2]} st_t;
  st_t miss_state = STREAM;
  struct packed { enum logic {SA, SB} k; } s;
  enum logic [1:0] {DA, DB, DC} d = DC;
  logic p0, p1, p2, p3, p4, p5, p6;
  ff u0 (.clk(clk), .din(miss_state == STREAM), .dout(p0));
  ff u1 (.clk(clk), .din(miss_state != IDLE && d == DC), .dout(p1));
  ff u2 (clk, (miss_state == RUN1), p2);
  ff u3 (.clk(clk), .din(s.k == SB), .dout(p3));
  ff u4 (.clk(clk), .din(pin == PB), .dout(p4));
  ff u5 (.clk(clk), .din(HP == HP1), .dout(p5));
  if (1) begin : g
    ff u6 (.clk(clk), .din(miss_state == RUN0), .dout(p6));
  end
endmodule
module top;
  logic clk = 0;
  thr inst (.clk(clk), .pin(2'd1));
endmodule
"#,
    );
    for label in [
        "STREAM", "IDLE", "RUN0", "RUN1", "SB", "DC", "PB", "HP1",
    ] {
        let key = format!("inst.{label}");
        assert!(
            !m.implicit_nets.contains(&key),
            "enum label {label} became the implicit net {key}"
        );
    }
}

/// §6.10, §27.5: a label declared in a generate block is the block's, so a
/// port actual of the same name in the module scope is still an implicit
/// net of the module, the one net connecting the two instances. Taken for a
/// declared constant, it was not created, and with procedural children (no
/// continuous assignment for the later scan to find) the connection had no
/// signal.
#[test]
fn generate_block_label_leaves_the_module_implicit_net() {
    let m = elaborate(
        r#"
module drv (output logic o);
  initial o = 1'b1;
endmodule
module rcv (input logic i, output logic seen);
  always @(i) seen = i;
endmodule
module wrap (output logic seen);
  if (0) begin : g
    typedef enum logic {LINK, IDLE} t;
  end
  drv d (.o(LINK));
  rcv r (.i(LINK), .seen(seen));
endmodule
module top;
  logic seen;
  wrap w (.seen(seen));
endmodule
"#,
    );
    assert!(
        m.implicit_nets.contains("w.LINK"),
        "no implicit net w.LINK: {:?}",
        m.implicit_nets
    );
}

/// §3.13, §6.10: definitions have a name space of their own, so a module
/// named `LINK` in the design leaves a bare port actual `LINK` the implicit
/// net of the scope it is used in, below the top and at it.
#[test]
fn module_name_leaves_the_implicit_net() {
    let m = elaborate(
        r#"
module LINK;
endmodule
module drv (output logic o);
  initial o = 1'b1;
endmodule
module rcv (input logic i, output logic seen);
  always @(i) seen = i;
endmodule
module wrap (output logic seen);
  drv d (.o(LINK));
  rcv r (.i(LINK), .seen(seen));
endmodule
module top;
  logic seen, seen_top;
  wrap w (.seen(seen));
  drv d (.o(LINK));
  rcv r (.i(LINK), .seen(seen_top));
endmodule
"#,
    );
    for net in ["w.LINK", "LINK"] {
        assert!(
            m.implicit_nets.contains(net),
            "no implicit net {net}: {:?}",
            m.implicit_nets
        );
    }
}

/// §6.10, §26.3: a label a module imports from a package (or `$unit`) and
/// uses in a port actual is the package's constant, not a local name of the
/// module: the inlined module's uses of it keep the bare name instead of
/// taking the instance path (`m.l.SYS_CSR`, which names nothing).
#[test]
fn imported_enum_label_in_a_port_actual_keeps_its_name() {
    let src = |top: &str| {
        format!(
            r#"
package pk;
  typedef enum logic [2:0] {{SYS_CSR, SYS_ERET}} sys_op_e;
endpackage
typedef enum logic [1:0] {{U_A, U_B}} u_e;
module probe (input i);
endmodule
module leaf;
  import pk::*;
  logic [2:0] op = 3'd0;
  logic y, z;
  probe p (.i(op == SYS_CSR));
  probe q (.i(op == U_B));
  assign y = op == SYS_CSR;
  assign z = op == U_B;
endmodule
module mid; leaf l(); endmodule
module top; {top} endmodule
"#
        )
    };
    for (top, path) in [("leaf l();", "l."), ("mid m();", "m.l.")] {
        let m = xezim_core::parse_and_elaborate_multi(
            &[src(top)],
            Some("top"),
            &[],
            &["top.sv".to_string()],
            &[],
        )
        .expect("elaborate")
        .1;
        let assigns = format!("{:?}", m.continuous_assigns);
        for label in ["SYS_CSR", "U_B"] {
            assert!(assigns.contains(&format!("\"{label}\"")), "{top}: {label} missing");
            assert!(
                !assigns.contains(&format!("\"{path}{label}\"")),
                "{top}: {label} took the instance path {path}"
            );
        }
    }
}
