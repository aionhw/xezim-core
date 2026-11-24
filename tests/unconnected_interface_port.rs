//! IEEE 1800-2023 §25.3/§23.3.3 (#1541).

fn elaborate(body: &str) -> Result<(), String> {
    let source = format!(
        "interface bus_if; logic data; modport snk(input data); endinterface
        module sink(input logic clk, bus_if.snk bus, output logic out);
            assign out = bus.data;
        endmodule
        module top; logic clk, out; {body} endmodule"
    );
    xezim_core::parse_and_elaborate_multi(&[source], Some("top"), &[], &[], &[]).map(|_| ())
}

#[test]
fn interface_ports_require_an_actual() {
    for body in [
        "sink dut(.clk(clk), .out(out));",
        "sink dut(.clk(clk), .bus(), .out(out));",
        "sink dut(clk, , out);",
        "sink dut(clk);",
        "sink dut(.*);",
        "bus_if bus(); sink dut(.bus(), .*);",
        "if (1) begin : g sink dut(.*); end",
    ] {
        let err = elaborate(body).expect_err(body);
        assert!(
            err.contains("interface port 'bus'")
                && err.contains("dut")
                && err.contains("not connected"),
            "{body}: {err}"
        );
    }
}

#[test]
fn interface_ports_accept_actuals_in_scope() {
    for body in [
        "sink dut(.clk(clk), .bus(bus), .out(out)); bus_if bus();",
        "bus_if bus(); sink dut(clk, bus.snk, out);",
        "sink dut(.*); bus_if bus();",
        "if (1) begin : g bus_if bus(); sink dut(.*); end",
    ] {
        elaborate(body).unwrap_or_else(|err| panic!("{body}: {err}"));
    }
}
