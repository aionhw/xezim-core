//! IEEE 1800-2023 §7.4.5, §7.6, §26.3: preserve bounds and declaration order.

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

#[test]
fn packed_package_parameter_ascending_constant_select() {
    let design = elaborate(
        r#"
package p;
  parameter logic [0:3][3:0] A = {4'h1, 4'h2, 4'h3, 4'h4};
endpackage
module top;
  import p::*;
  localparam int FIRST = p::A[0];
  localparam int LAST = A[3];
endmodule
"#,
    );
    assert_eq!(design.parameters["FIRST"].to_u64(), Some(1));
    assert_eq!(design.parameters["LAST"].to_u64(), Some(4));
}

#[test]
fn unpacked_parameter_copy_maps_declared_positions() {
    let design = elaborate(
        r#"
package p;
  parameter logic [33:0] A [3:2] = '{34'h100000009, 34'h20000000a};
endpackage
module leaf #(parameter logic [33:0] A [1:2] = p::A); endmodule
module mid #(parameter logic [33:0] A [4:3] = p::A);
  leaf #(.A(A)) u();
endmodule
module top; mid u(); leaf v(); endmodule
"#,
    );
    for name in ["u.u.A", "v.A"] {
        assert_eq!(
            design.parameters[&format!("{name}[1]")].to_u64(),
            Some(0x100000009)
        );
        assert_eq!(
            design.parameters[&format!("{name}[2]")].to_u64(),
            Some(0x20000000a)
        );
    }
}

/// §6.20.2: a named array copy retains the real type of its elements.
#[test]
fn referenced_real_array_parameter_keeps_element_type() {
    let design = elaborate(
        r#"
package reals; parameter real A[2] = '{1.5, 2.5}; endpackage
module leaf #(parameter real A[2] = reals::A); endmodule
module mid #(parameter real A[2] = reals::A);
  leaf #(.A(A)) v();
endmodule
module top; leaf u(); mid w(); endmodule
"#,
    );
    for name in ["u.A", "w.v.A"] {
        for (i, expected) in [1.5, 2.5].into_iter().enumerate() {
            let a = &design.parameters[&format!("{name}[{i}]")];
            assert!(a.is_real, "real element became integral: {a:?}");
            assert_eq!(a.to_f64(), expected);
        }
    }
}
