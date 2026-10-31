//! IEEE 1800-2017 §8.24 / §26.3: an out-of-block class method is not
//! a package function, including during the package parameter prepass.
#[test]
fn out_of_block_methods_do_not_supply_bare_function_signatures() {
    let source = r#"package mon_pkg;
  class ic_model;
    extern function void route(input int xact, ref int ports[$], ref int sync);
  endclass
  function void ic_model::route(input int xact, ref int ports[$], ref int sync);
    sync = xact;
  endfunction
  class monitor_model;
    extern function void route(input string mode, input int xact, input int addr, ref int ports[$]);
    extern function void run();
  endclass
  function void monitor_model::route(input string mode, input int xact, input int addr, ref int ports[$]);
    ports.push_back(addr);
  endfunction
  function void monitor_model::run();
    int ports[$];
    route("dvm", 1, 0, ports);
  endfunction
endpackage
module top; import mon_pkg::*; monitor_model m; initial begin m = new(); m.run(); end endmodule"#;
    let unit_source = source
        .replace("package mon_pkg;", "")
        .replace("endpackage", "")
        .replace("import mon_pkg::*;", "");
    let child_source =
        unit_source.replace("module top;", "module child;") + "\nmodule top; child u(); endmodule";
    let qualified_source = source.replace("import mon_pkg::*;", "").replace(
        "monitor_model m; initial",
        "mon_pkg::monitor_model m; initial",
    );
    for source in [
        source.to_string(),
        qualified_source,
        unit_source,
        child_source,
    ] {
        let (_, model) =
            xezim_core::parse_and_elaborate_multi(&[source], Some("top"), &[], &[], &[])
                .expect("the input argument must not borrow another class's ref signature");
        assert!(!model.functions.contains_key("route"));
        assert!(!model.functions.contains_key("run"));
    }
}

#[test]
fn package_constant_function_is_not_hidden_by_a_class_method() {
    let source = r#"package p;
  class c;
    extern function int width();
  endclass
  function int c::width(); return 99; endfunction
  function automatic int width(); return 7; endfunction
  localparam int W = width();
endpackage
module top; import p::*; logic [W-1:0] value; endmodule"#;
    let (_, model) =
        xezim_core::parse_and_elaborate_multi(&[source.into()], Some("top"), &[], &[], &[])
            .expect("package constant function");
    assert_eq!(model.signals["value"].width, 7);
}
