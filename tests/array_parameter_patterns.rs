//! Replication, keyed and `default:` patterns in unpacked array parameters (§10.9.1 / §23.10).
fn elaborate(source: &str) -> xezim_core::ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[source.to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .expect("elaborate")
    .1
}

fn ints(design: &xezim_core::ElaboratedModule, keys: &[&str]) -> Vec<i64> {
    keys.iter()
        .map(|k| design.parameters[*k].to_i64().unwrap_or(i64::MIN))
        .collect()
}

#[test]
fn replication_keyed_and_default_initializers() {
    let design = elaborate(
        r#"
module top;
 localparam int K = 1;
 localparam int R[4] = '{2{5, 6}};
 localparam int D[3] = '{default: 5};
 localparam int I[3] = '{K: 9, default: 5};
 localparam int S[2:0] = '{0: 7, default: 1};
 localparam int M[2][3] = '{1: '{default: 9}, default: '{3{2}}};
 localparam int L = D[2] + I[1];
endmodule
"#,
    );
    assert_eq!(
        ints(&design, &["R[0]", "R[1]", "R[2]", "R[3]"]),
        [5, 6, 5, 6]
    );
    assert_eq!(ints(&design, &["D[0]", "D[1]", "D[2]"]), [5, 5, 5]);
    assert_eq!(ints(&design, &["I[0]", "I[1]", "I[2]"]), [5, 9, 5]);
    assert_eq!(ints(&design, &["S[2]", "S[1]", "S[0]"]), [1, 1, 7]);
    assert_eq!(
        ints(&design, &["M[0][0]", "M[0][2]", "M[1][0]", "M[1][2]"]),
        [2, 2, 9, 9]
    );
    assert_eq!(design.parameters["L"].to_i64(), Some(14));
}

#[test]
fn default_reaches_every_leaf_of_a_nested_array() {
    let design = elaborate(
        r#"
module top; localparam int A[2][2][2] = '{default: 3}; endmodule
"#,
    );
    assert_eq!(ints(&design, &["A[0][0][0]", "A[1][1][1]"]), [3, 3]);
}

#[test]
fn instance_overrides_with_patterns() {
    let design = elaborate(
        r#"
module leaf;
 parameter int P[3] = '{0, 0, 0};
 parameter int M[2][2] = '{'{0, 0}, '{0, 0}};
endmodule
module top;
 localparam int K = 2;
 leaf #(.P('{3{6}})) u_rep();
 leaf #(.P('{K: 5, default: 3})) u_key();
 leaf #(.M('{default: 4})) u_dfl();
endmodule
"#,
    );
    assert_eq!(ints(&design, &["u_rep.P[0]", "u_rep.P[2]"]), [6, 6]);
    assert_eq!(
        ints(&design, &["u_key.P[0]", "u_key.P[1]", "u_key.P[2]"]),
        [3, 3, 5]
    );
    assert_eq!(ints(&design, &["u_dfl.M[0][0]", "u_dfl.M[1][1]"]), [4, 4]);
}
