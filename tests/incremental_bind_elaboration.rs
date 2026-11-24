//! §23.11: incremental worklist bind elaboration and nested bind parity.

fn elaborate_res(src: &str, top: &str) -> Result<xezim_core::ElaboratedModule, String> {
    xezim_core::parse_and_elaborate_multi(
        &[src.to_string()],
        Some(top),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .map(|(_, m)| m)
}

fn elaborate(src: &str) -> xezim_core::ElaboratedModule {
    elaborate_res(src, "top").expect("elaborate")
}

fn instances_of(m: &xezim_core::ElaboratedModule, def: &str) -> Vec<String> {
    let mut paths: Vec<String> = m
        .instances
        .iter()
        .filter(|i| i.def_name == def)
        .map(|i| i.path.to_string())
        .collect();
    paths.sort();
    paths
}

fn all_instance_paths(m: &xezim_core::ElaboratedModule) -> Vec<String> {
    let mut paths: Vec<String> = m.instances.iter().map(|i| i.path.to_string()).collect();
    paths.sort();
    paths
}

fn staged_source(staged: bool) -> String {
    let mut src = String::new();
    for k in 0..4 {
        let child = if !staged && k < 3 {
            format!("watch{} w();", k + 1)
        } else {
            String::new()
        };
        src.push_str(&format!("module watch{k}(); wire flag=1; {child} endmodule\n"));
    }
    src.push_str("module element();\n");
    for k in 0..256 {
        src.push_str(&format!("wire [31:0] x{k}=32'd{k};\n"));
    }
    if !staged {
        src.push_str("watch0 w();\n");
    }
    src.push_str("endmodule\n");
    if staged {
        src.push_str("bind element watch0 w();\n");
        for k in 0..3 {
            src.push_str(&format!("bind watch{k} watch{} w();\n", k + 1));
        }
    }
    src.push_str("module top; for(genvar i=0;i<128;i++) begin:g element u(); end endmodule\n");
    src
}

#[test]
fn four_level_nested_bind_matches_direct_hierarchy() {
    let direct = elaborate(&staged_source(false));
    let staged = elaborate(&staged_source(true));

    assert_eq!(direct.signals.len(), 33_282);
    assert_eq!(staged.signals.len(), 33_282);
    assert_eq!(all_instance_paths(&staged), all_instance_paths(&direct));
    assert!(staged.signals.contains_key("g[0].u.w.w.w.w.flag"));
    assert!(staged.signals.contains_key("g[127].u.w.w.w.w.flag"));
}

#[test]
fn portless_unit_bind_prefers_a_same_named_instance() {
    let model = elaborate(
        r#"
module watched; endmodule
module different; endmodule
module observer; wire flag = 1; endmodule
module top;
  watched actual();
  different watched();
endmodule
bind watched observer o();
"#,
    );
    assert!(model.signals.contains_key("watched.o.flag"));
    assert!(!model.signals.contains_key("actual.o.flag"));
}

#[test]
fn nested_bind_target_instance_selection_and_bind_created_path() {
    let model = elaborate(
        r#"
module watch1 #(parameter int W = 1);
  logic [W-1:0] obs;
endmodule
module watch0;
  logic flag;
endmodule
module fake_w0;
  logic wrong;
endmodule
module sub;
  fake_w0 watch0 ();
  // By-name bind to `watch0` inside `sub` sees instance `watch0` (of `fake_w0`),
  // whereas an external unit bind to `leaf` creates `leaf.w0` (of `watch0`).
  bind watch0 watch1 #(.W(5)) by_inst ();
endmodule
module leaf;
  logic data;
endmodule
module top;
  sub s ();
  leaf a ();
  leaf b ();
endmodule
bind leaf watch0 w0 ();
bind top.a.w0 watch1 #(.W(7)) w1_a ();
bind watch0 : top.a.w0, top.b.w0 watch1 #(.W(9)) w1_both ();
"#,
    );

    assert_eq!(model.signals["s.watch0.by_inst.obs"].width, 5);
    assert!(!model.signals.contains_key("a.w0.by_inst.obs"));
    assert_eq!(model.signals["a.w0.w1_a.obs"].width, 7);
    assert!(!model.signals.contains_key("b.w0.w1_a.obs"));
    assert_eq!(model.signals["a.w0.w1_both.obs"].width, 9);
    assert_eq!(model.signals["b.w0.w1_both.obs"].width, 9);
}

#[test]
fn module_scoped_and_generate_scoped_binds_inside_bound_modules() {
    let model = elaborate(
        r#"
module watch2 #(parameter int N = 1);
  logic [N-1:0] s2;
endmodule
module inner;
  logic leaf_sig;
endmodule
module watch1 #(parameter int N = 1);
  logic [N-1:0] s1;
  inner sub_i ();
  bind sub_i watch2 #(.N(4)) leaf_obs ();
endmodule
module watch0 #(parameter int EN = 0);
  if (EN) begin : gb
    bind watch0 watch1 #(.N(6)) from_gen ();
  end
  bind watch0 watch1 #(.N(3)) direct_m ();
endmodule
module elem;
  logic v;
endmodule
module top;
  elem e_on ();
endmodule
bind top.e_on watch0 #(.EN(1)) w0 ();
"#,
    );

    assert_eq!(model.signals["e_on.w0.direct_m.s1"].width, 3);
    assert_eq!(model.signals["e_on.w0.from_gen.s1"].width, 6);
    assert_eq!(
        model.signals["e_on.w0.direct_m.sub_i.leaf_obs.s2"].width,
        4
    );
    assert_eq!(
        model.signals["e_on.w0.from_gen.sub_i.leaf_obs.s2"].width,
        4
    );
}

#[test]
fn nested_bind_package_target_and_type_parameters() {
    let model = elaborate(
        r#"
package pk;
  localparam int C = 7;
endpackage
module probe #(parameter type P = logic, parameter int K = 1);
  P s;
  logic [K-1:0] kvec;
endmodule
module watch0 #(parameter int W = 2);
  localparam int LW = W + 1;
endmodule
module leaf #(parameter type T = logic, parameter int W = 2);
  T q;
endmodule
module top;
  leaf #(.T(logic [15:0]), .W(2)) a ();
  leaf #(.T(logic [7:0]), .W(4)) b ();
endmodule
bind leaf watch0 #(.W(W)) w ();
bind watch0 probe #(.P(logic [3:0]), .K(pk::C + LW)) kw ();
bind leaf probe #(.P(T), .K(W)) pt ();
"#,
    );

    assert_eq!(model.signals["a.pt.s"].width, 16);
    assert_eq!(model.signals["b.pt.s"].width, 8);
    assert_eq!(model.signals["a.pt.kvec"].width, 2);
    assert_eq!(model.signals["b.pt.kvec"].width, 4);
    assert_eq!(model.signals["a.w.kw.kvec"].width, 10); // 7 + (2 + 1)
    assert_eq!(model.signals["b.w.kw.kvec"].width, 12); // 7 + (4 + 1)
}

#[test]
fn bound_child_port_forwarding_and_implicit_nets() {
    let mut model = elaborate(
        r#"
module obs (input logic in_s, output logic out_s, input logic imp_net);
  assign out_s = in_s;
endmodule
module mid (input logic a_in, output logic a_out);
  logic mid_tmp;
  assign mid_tmp = a_in;
endmodule
module top;
  logic src = 1'b1;
  logic dst;
  mid u (.a_in(src), .a_out(dst));
endmodule
bind mid obs u_obs (.in_s(a_in), .out_s(a_out), .imp_net(undeclared_wire));
"#,
    );
    model.materialize_pending();

    // Undeclared wire becomes an implicit net in the target scope (`u`).
    assert!(model.signals.contains_key("u.undeclared_wire"));
    assert_eq!(
        model
            .port_aliases
            .get("u.u_obs.imp_net")
            .map(|s| s.as_str()),
        Some("u.undeclared_wire")
    );
    // Input port `a_in` on `u` forwards parent net `src`.
    assert_eq!(
        model.port_aliases.get("u.u_obs.in_s").map(|s| s.as_str()),
        Some("src")
    );
    // Output port `a_out` on `u` maps to `u.a_out`.
    assert_eq!(
        model.port_aliases.get("u.u_obs.out_s").map(|s| s.as_str()),
        Some("u.a_out")
    );
}

#[test]
fn nested_bind_instance_array_and_list() {
    let model = elaborate(
        r#"
module chk #(parameter int K = 3) (input logic x, output logic y);
  logic [K-1:0] v;
  assign y = x;
endmodule
module watch0;
  logic [1:0] r;
  logic [1:0] out_v;
endmodule
module t;
  logic dummy;
endmodule
module top;
  t u ();
endmodule
bind t watch0 w ();
bind watch0 chk #(.K(5)) arr[1:0] (.x(r), .y(out_v));
bind watch0 chk #(.K(6)) p (.x(r[0]), .y()), q (.x(r[1]), .y());
"#,
    );

    assert_eq!(
        instances_of(&model, "chk"),
        ["u.w.arr[0]", "u.w.arr[1]", "u.w.p", "u.w.q"]
    );
    assert_eq!(model.signals["u.w.arr[0].v"].width, 5);
    assert_eq!(model.signals["u.w.arr[1].v"].width, 5);
    assert_eq!(model.signals["u.w.p.v"].width, 6);
    assert_eq!(model.signals["u.w.q.v"].width, 6);
}

#[test]
fn defparam_targeting_bound_instance() {
    let model = elaborate(
        r#"
module watch1 #(parameter int K = 1);
  logic [K-1:0] q1;
endmodule
module watch0 #(parameter int K = 1);
  logic [K-1:0] q0;
endmodule
module target;
  logic x;
endmodule
module top;
  target u ();
  defparam u.w0.K = 11;
  defparam u.w0.w1.K = 13;
endmodule
bind target watch0 w0 ();
bind watch0 watch1 w1 ();
"#,
    );

    assert_eq!(model.signals["u.w0.q0"].width, 11);
    assert_eq!(model.signals["u.w0.w1.q1"].width, 13);
}

#[test]
fn bind_into_top_with_hierarchical_reference_and_nested_child() {
    let model = elaborate(
        r#"
module w1 #(parameter int A = 3) (output int v);
  assign v = A;
endmodule
module w0;
  int z;
endmodule
module top;
  int r;
  initial #1 r = a.b.v;
endmodule
bind top w0 a ();
bind w0 w1 #(9) b ();
"#,
    );

    assert!(model.signals.contains_key("a.b.v"));
    assert_eq!(model.parameters["a.b.A"].to_i64(), Some(9));
}

#[test]
fn nonconverging_recursive_bind_reports_diagnostic() {
    let err = elaborate_res(
        r#"
module m;
  logic x;
endmodule
module top;
  m u ();
endmodule
bind m m self_child ();
"#,
        "top",
    )
    .expect_err("self-recursive bind must fail");

    assert!(
        err.contains("bind hierarchy does not converge (§23.11)"),
        "unexpected error: {err}"
    );
}

#[test]
fn bound_interface_referenced_by_existing_child_fallback() {
    let model = elaborate(
        r#"
interface my_if;
  logic [7:0] data;
endinterface
module child (my_if bus);
  logic [7:0] captured;
  assign captured = bus.data;
endmodule
module mid;
  child u (.bus(bif));
endmodule
module top;
  mid m ();
endmodule
bind mid my_if bif ();
"#,
    );

    assert!(model.signals.contains_key("m.bif.data"));
    assert_eq!(
        model.interface_port_aliases.get("m.u.bus").map(String::as_str),
        Some("m.bif")
    );
}
