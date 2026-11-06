//! IEEE 1800-2023 §26.3, §7.4.2: when two packages declare the constant `N`,
//! a module's own import of it (`import q::N;` or `import q::*;`) is found
//! before the compilation unit's wildcard import `import r::*;` — for the
//! size `a[N]` of an unpacked array as for every other reference (#895).
//! `[N]` parses as an associative dimension keyed by the type `N`, which the
//! package-scope pass did not resolve as a value, so the elaborator read the
//! bare name from the flat table, where the compilation unit's wildcard import
//! had put `r::N`. Expected values are the reference simulator's.

use xezim_core::ElaboratedModule;

fn elaborate(source: &str) -> ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[source.to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .unwrap_or_else(|e| panic!("{e}\n{source}"))
    .1
}

fn width(design: &ElaboratedModule, name: &str) -> u32 {
    design
        .signals
        .get(name)
        .unwrap_or_else(|| panic!("no signal {name}"))
        .width
}

fn bounds(design: &ElaboratedModule, name: &str) -> (i64, i64) {
    let (lo, hi, _) = design
        .arrays
        .get(name)
        .unwrap_or_else(|| panic!("no array {name}"));
    (*lo, *hi)
}

#[test]
fn a_module_import_sizes_its_arrays_over_the_unit_wildcard() {
    let d = elaborate(
        r#"
package r; localparam int N = 3; localparam int K = 30; endpackage
package q; localparam int N = 5; localparam int K = 50; endpackage
import r::*;
module leaf;
  import q::N;
  int c [N];
endmodule
module child;
  import q::N;
  int a [N];
  logic [N-1:0] v;
  localparam int L = N * 2;
  int b [L];
  leaf u_leaf();
endmodule
module wild;
  import q::*;
  int a [K];
  logic [K-1:0] v;
endmodule
module top;
  child u();
  wild w();
endmodule
"#,
    );
    assert_eq!(bounds(&d, "u.a"), (0, 4));
    assert_eq!(width(&d, "u.v"), 5);
    assert_eq!(bounds(&d, "u.b"), (0, 9));
    assert_eq!(bounds(&d, "u.u_leaf.c"), (0, 4));
    assert_eq!(bounds(&d, "w.a"), (0, 49));
    assert_eq!(width(&d, "w.v"), 50);
}

/// The compilation unit's candidate does not size the array even when it is
/// 0 (the issue's second shape, where the array came out 32 elements wide).
#[test]
fn a_zero_unit_candidate_does_not_size_the_array() {
    let d = elaborate(
        r#"
package r; localparam int N = 0; endpackage
package q; localparam int N = 5; endpackage
import r::*;
module child;
  import q::N;
  int a [N];
endmodule
module top;
  child u();
endmodule
"#,
    );
    assert_eq!(bounds(&d, "u.a"), (0, 4));
}
