//! IEEE 1800-2023 §6.20, §23.10, §27: prepared bodies may share immutable
//! package context, but every complete instance parameter still selects its
//! own generate branch (#721).

fn elaborate(source: &str) -> xezim_core::ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[source.to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .unwrap_or_else(|error| panic!("{error}\n{source}"))
    .1
}

#[test]
fn prepared_body_key_distinguishes_parameter_bits_above_63() {
    let design = elaborate(
        "module leaf #(parameter logic[127:0] P=0) ();\n\
         if (P[90]) begin:g logic[6:0] a; end\n\
         else begin:g logic[2:0] a; end\n\
         endmodule\n\
         module top;\n\
         leaf #(.P(128'h40000000000000000000000)) high();\n\
         leaf #(.P(128'd0)) low();\n\
         leaf #(.P(128'h40000000000000000000000)) high_again();\n\
         endmodule",
    );
    for (name, expected) in [("high.g.a", 7), ("low.g.a", 3), ("high_again.g.a", 7)] {
        assert_eq!(design.signals[name].width, expected, "{name}");
    }
}

#[test]
fn prepared_body_key_distinguishes_long_string_parameter_prefixes() {
    let design = elaborate(
        "module leaf #(parameter string P=\"first___same_low\") ();\n\
         if (P == \"first___same_low\") begin:g logic[6:0] a; end\n\
         else begin:g logic[2:0] a; end\n\
         endmodule\n\
         module top;\n\
         leaf first();\n\
         leaf #(.P(\"other___same_low\")) other();\n\
         leaf #(.P(\"first___same_low\")) first_again();\n\
         endmodule",
    );
    for (name, expected) in [("first.g.a", 7), ("other.g.a", 3), ("first_again.g.a", 7)] {
        assert_eq!(design.signals[name].width, expected, "{name}");
    }
}
