//! §7.4.5, §26.3: a class property whose element type is a package typedef
//! of an unpacked array, `p::q_t qq[$];`, has the declarator's dimensions
//! and then the typedef's. Only a typedef named without a scope was looked
//! up, so the property recorded no shape and its rows held one scalar each.
use xezim_core::elaborate::{CollShape, Dim};

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

fn dims<H: std::hash::BuildHasher>(
    shapes: &std::collections::HashMap<String, CollShape, H>,
    name: &str,
) -> Option<Vec<Dim>> {
    shapes.get(name).map(|s| s.dims.clone())
}

#[test]
fn class_property_of_package_typedef_rows_records_both_levels() {
    let d = elaborate(
        r#"
package p;
  typedef int q_t[$];
  typedef int d_t[];
endpackage
class C;
  typedef int q_t[3];
  p::q_t pq[$];
  p::d_t pd[2];
  q_t own[$];
endclass
module top;
  C h;
endmodule
"#,
    );
    let c = &d.classes["C"].prop_coll_shapes;
    assert_eq!(dims(c, "pq"), Some(vec![Dim::Queue, Dim::Queue]));
    assert_eq!(
        dims(c, "pd"),
        Some(vec![Dim::Fixed(Some((0, 1))), Dim::Dyn])
    );
    // The class's own `q_t` is a fixed array, not the package's queue.
    assert_eq!(
        dims(c, "own"),
        Some(vec![Dim::Queue, Dim::Fixed(Some((0, 2)))])
    );
}
