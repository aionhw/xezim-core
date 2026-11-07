//! IEEE 1800-2023 §6.6.7: "A nettype may be declared without a resolution
//! function, in which case it shall be an error for a net of that nettype to
//! have multiple drivers", counted over the whole net a port connection
//! merges (§23.3.3.7). An unpacked-struct net's port connection arrives member
//! by member, so two children driving one net, or a child and the parent, were
//! counted as one driver each. The reference simulator rejects all three
//! multi-driver shapes and runs the one-driver net with a reader.

const TYPES: &str = r#"
typedef struct { real V; int code; } e_t;
nettype e_t enet;
module drv(input real v, output enet p); assign p = '{v, 1}; endmodule
module rd(input enet p, output real o); assign o = p.V; endmodule
module mid(input real v, output enet p); drv d(.v(v), .p(p)); endmodule
"#;

fn elaborate(top: &str) -> Result<(), String> {
    xezim_core::parse_and_elaborate_multi(
        &[format!(
            "{TYPES}
module top{top}"
        )],
        Some("top"),
        &[],
        &["t.sv".to_string()],
        &[],
    )
    .map(|_| ())
}

#[test]
fn two_drivers_through_ports_are_an_error() {
    for (name, top) in [
        (
            "two_children",
            r#"; real v = 1.0; enet n; drv a(.v(v), .p(n)); drv b(.v(v), .p(n)); initial #1 $display("R %.1f", n.V); endmodule"#,
        ),
        (
            "child_and_parent",
            r#"; real v = 1.0; enet n; drv a(.v(v), .p(n)); assign n = '{2.0, 3}; initial #1 $display("R %.1f", n.V); endmodule"#,
        ),
        (
            "two_levels",
            r#"; real v = 1.0; enet n; mid a(.v(v), .p(n)); drv b(.v(v), .p(n)); initial #1 $display("R %.1f", n.V); endmodule"#,
        ),
    ] {
        let err = elaborate(top).expect_err(name);
        assert!(
            err.contains("of an unresolved nettype has 2 continuous drivers"),
            "{name}: {err}"
        );
    }
}

#[test]
fn one_driver_and_a_reader_through_ports_elaborate() {
    elaborate(r#"; real v = 1.0, o; enet n; drv a(.v(v), .p(n)); rd r(.p(n), .o(o)); initial #1 $display("R %.1f %.1f", n.V, o); endmodule"#).expect("one driver");
}
