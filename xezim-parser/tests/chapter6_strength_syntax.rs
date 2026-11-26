//! IEEE 1800-2023 §6.7, §10.3.4 and Annex A.2.2.2.

#[test]
fn invalid_net_and_continuous_assignment_strengths_are_rejected() {
    for (declaration, expected) in [
        ("wire (small) w;", "charge strength requires a trireg"),
        (
            "wire (strong0, strong1) w;",
            "requires a net declaration assignment",
        ),
        (
            "wire w; assign (strong0 strong1) w = 1;",
            "invalid drive or charge strength",
        ),
        (
            "wire w; assign (weak1, strong1) w = 1;",
            "invalid drive or charge strength",
        ),
        (
            "wire w; assign (highz0, highz1) w = 1;",
            "invalid drive or charge strength",
        ),
        (
            "wire w; assign (large) w = 1;",
            "expected a drive strength pair",
        ),
    ] {
        let result = sv_parser::parse(&format!("module top; {declaration} endmodule"));
        assert!(
            result.errors.iter().any(|d| d.message.contains(expected)),
            "{declaration}: {:?}",
            result.errors
        );
    }
}

#[test]
fn valid_drive_charge_and_pull_strengths_are_accepted() {
    let result = sv_parser::parse(
        r#"
module top;
    trireg (small) charge_net;
    wire (weak1, strong0) driven = 1'b1;
    wire a, b, c, d;
    assign (highz0, strong1) a = 1'b1;
    buf (highz1, strong0) g(b, 1'b1);
    pullup (strong1) p(c);
    pulldown (weak0, supply1) n(d);
endmodule
"#,
    );
    assert!(result.errors.is_empty(), "{:?}", result.errors);
}
