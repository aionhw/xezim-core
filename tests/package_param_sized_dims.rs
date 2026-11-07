//! §7.4.2, §26.2: a package array whose first unpacked dimension is sized by a
//! parameter, `d [N][2]`, has the same shape as one sized by a literal. The
//! parser reads `[N]` as an associative dimension keyed by "type" `N`, and the
//! package arm decided "multi-dimensional" from those parsed dimensions, so
//! `d` was registered one-dimensional and `p::d[3][1]` read 0. Package arrays
//! are registered under their bare names.

fn elaborate(source: &str) -> xezim_core::ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[source.to_string()],
        Some("t"),
        &[],
        &["t.sv".to_string()],
        &[],
    )
    .expect("elaborate")
    .1
}

#[test]
fn two_dimensional_array_sized_by_a_package_parameter() {
    let design = elaborate(
        "package p;
          localparam int N = 4;
          logic [31:0] a [4][2];
          logic [31:0] d [N][2];
        endpackage
        module t; endmodule",
    );
    assert!(design.arrays_2d.contains_key("a"));
    assert_eq!(design.arrays_2d.get("d"), design.arrays_2d.get("a"));
    assert!(!design.associative_arrays.contains_key("d"));
}

#[test]
fn three_dimensional_array_sized_by_a_package_parameter() {
    let design = elaborate(
        "package p;
          localparam int N = 4;
          logic [31:0] a [4][2][3];
          logic [31:0] d [N][2][3];
        endpackage
        module t; endmodule",
    );
    assert!(design.arrays_nd.contains_key("a"));
    assert_eq!(design.arrays_nd.get("d"), design.arrays_nd.get("a"));
    assert!(!design.associative_arrays.contains_key("d"));
}

#[test]
fn two_dimensional_array_sized_by_another_package_parameter() {
    let design = elaborate(
        "package q; localparam int N = 4; endpackage
        package p;
          logic [31:0] a [4][2];
          logic [31:0] d [q::N][2];
        endpackage
        module t; endmodule",
    );
    assert!(design.arrays_2d.contains_key("a"));
    assert_eq!(design.arrays_2d.get("d"), design.arrays_2d.get("a"));
    assert!(!design.associative_arrays.contains_key("d"));
}

/// A dimension keyed by a type stays associative in a package.
#[test]
fn string_keyed_package_array_stays_associative() {
    let design = elaborate(
        "package p; logic [31:0] s [string]; endpackage
        module t; endmodule",
    );
    assert_eq!(design.associative_arrays.get("s"), Some(&true));
    assert!(!design.arrays_2d.contains_key("s"));
}
