//! §25.10, §23.3.3: a module sees the parameters of the interface instance
//! bound to its interface port through the port formal (`c.W` in a constant
//! context). Pins which entries each instance gets while they are found by a
//! range scan of the bound instance's keys instead of a pass over the
//! design-wide parameter table (aionhw/xezim#736).

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

fn param(m: &xezim_core::ElaboratedModule, key: &str) -> Option<i64> {
    m.parameters.get(key).and_then(|v| v.to_i64())
}

/// The entries of `parameters` under `prefix`, sorted.
fn under(m: &xezim_core::ElaboratedModule, prefix: &str) -> Vec<(String, i64)> {
    let mut found: Vec<_> = m
        .parameters
        .iter()
        .filter(|(k, _)| k.starts_with(prefix))
        .map(|(k, v)| (k[prefix.len()..].to_string(), v.to_i64().unwrap_or(-1)))
        .collect();
    found.sort();
    found
}

#[test]
fn each_instance_sees_its_own_interface_instance_parameters() {
    // `g[1]` next to `g[10]`, `b` next to `bb`: a key prefix of another.
    let m = elaborate(
        r#"
interface cfg_if #(parameter int W = 4) ();
endinterface
module user(cfg_if c, output logic [7:0] y);
  localparam int WW = c.W;
  assign y = WW;
endmodule
module top;
  logic [7:0] y [12];
  for (genvar i = 0; i < 12; i++) begin : g
    cfg_if #(.W(i + 1)) c();
    user u(.c(c), .y(y[i]));
  end
  logic [7:0] yb, ybb;
  cfg_if #(.W(20)) b();
  cfg_if #(.W(30)) bb();
  user ub(.c(b), .y(yb));
  user ubb(.c(bb), .y(ybb));
endmodule
"#,
    );
    for i in 0..12 {
        assert_eq!(param(&m, &format!("g[{i}].u.WW")), Some(i + 1), "g[{i}]");
        assert_eq!(
            under(&m, &format!("g[{i}].u.c.")),
            [("W".to_string(), i + 1)],
            "g[{i}]"
        );
    }
    assert_eq!(param(&m, "ub.WW"), Some(20));
    assert_eq!(param(&m, "ubb.WW"), Some(30));
    assert_eq!(under(&m, "ub.c."), [("W".to_string(), 20)]);
    assert_eq!(under(&m, "ubb.c."), [("W".to_string(), 30)]);
}

#[test]
fn the_bound_instance_sub_instances_come_along_under_the_formal() {
    let m = elaborate(
        r#"
interface core_if #(parameter int V = 2) ();
endinterface
interface cfg_if #(parameter int W = 4) ();
  core_if #(.V(W * 2)) k();
endinterface
module user(cfg_if c, output logic [7:0] y);
  localparam int WW = c.W;
  assign y = WW;
endmodule
module top;
  logic [7:0] y0, y1;
  cfg_if #(.W(3)) c0();
  cfg_if #(.W(5)) c1();
  user u0(.c(c0), .y(y0));
  user u1(.c(c1), .y(y1));
endmodule
"#,
    );
    assert_eq!(param(&m, "u0.WW"), Some(3));
    assert_eq!(param(&m, "u1.WW"), Some(5));
    assert_eq!(
        under(&m, "u1.c."),
        [("W".to_string(), 5), ("k.V".to_string(), 10)]
    );
}

#[test]
fn an_interface_port_passed_through_a_wrapper_and_a_struct_parameter() {
    // The struct parameter writes `<param>.<member>` entries into the table
    // while the instance is elaborated.
    let m = elaborate(
        r#"
typedef struct packed {logic [3:0] a; logic [3:0] b;} cfg_t;
interface cfg_if #(parameter int W = 4) ();
endinterface
module user(cfg_if c, output logic [7:0] y);
  localparam cfg_t K = '{a: 4'd1, b: 4'd2};
  localparam int WW = c.W;
  assign y = WW + K.a - 1;
endmodule
module wrap(cfg_if cc, output logic [7:0] y);
  localparam int OUTER = cc.W;
  user u(.c(cc), .y(y));
endmodule
module top;
  logic [7:0] y [3];
  for (genvar i = 0; i < 3; i++) begin : g
    cfg_if #(.W(7 + i)) c();
    wrap w(.cc(c), .y(y[i]));
  end
endmodule
"#,
    );
    for i in 0..3 {
        assert_eq!(param(&m, &format!("g[{i}].w.OUTER")), Some(7 + i));
        assert_eq!(param(&m, &format!("g[{i}].w.u.WW")), Some(7 + i));
        assert_eq!(param(&m, &format!("g[{i}].w.u.K.a")), Some(1));
    }
}
