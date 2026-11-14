//! IEEE 1800-2023 §26.3, §6.18: a package typedef's range names its own
//! package's constants (aionhw/xezim#1148). A negative one, or one whose
//! declared type changes its value (§6.20.2), is read in the package's scope
//! wherever the type is used, so `pk::A` keeps `[LO:1]` even when another
//! top-level module declares a parameter `LO`.

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
fn negative_and_typed_package_constants_in_typedef_ranges() {
    let design = elaborate(
        "package pk;
          localparam int LO = -1;
          localparam byte B = 2147483646;
          typedef int A[LO:1];
          typedef int AB[B:B+1];
        endpackage
        module t;
          pk::A v;
          pk::AB b;
        endmodule
        module other #(parameter int LO = -1)(); endmodule",
    );
    let bounds = |n: &str| {
        design
            .arrays
            .get(n)
            .map(|&(lo, hi, _)| (lo, hi))
            .unwrap_or_else(|| panic!("array {n}: {:?}", design.arrays.keys().collect::<Vec<_>>()))
    };
    assert_eq!(bounds("v"), (-1, 1));
    assert_eq!(bounds("b"), (-2, -1));
}
