//! §7.4.5, §6.18: a class property whose element type is an unpacked-array
//! typedef and which declares its own unpacked dimensions
//! (`typedef int q_t[$]; q_t qq[$];`) is a collection of collections: the
//! declarator's dimensions come first, then the typedef's, as at module
//! scope. The typedef's dimensions were dropped whenever the declarator had
//! any, so the property recorded no shape and its rows held one scalar each.
use xezim_core::elaborate::{CollShape, Dim, KeyKind};

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

const SRC: &str = r#"
module top;
  typedef int mq_t[$];
  mq_t mqq[$];
  class C;
    typedef int q_t[$];
    typedef int d_t[];
    typedef int s_t[string];
    q_t qq[$];
    d_t qd[$];
    q_t aq[int];
    s_t fs[2];
    mq_t mq[$];
    q_t one;
    int anon[$][$];
  endclass
  C h;
endmodule
"#;

#[test]
fn class_property_of_typedef_rows_records_both_levels() {
    let d = elaborate(SRC);
    let c = &d.classes["C"].prop_coll_shapes;
    let int32 = Dim::Assoc(KeyKind::Integral {
        width: 32,
        signed: true,
    });
    assert_eq!(dims(c, "qq"), Some(vec![Dim::Queue, Dim::Queue]));
    assert_eq!(dims(c, "qd"), Some(vec![Dim::Queue, Dim::Dyn]));
    assert_eq!(dims(c, "aq"), Some(vec![int32, Dim::Queue]));
    assert_eq!(
        dims(c, "fs"),
        Some(vec![Dim::Fixed(Some((0, 1))), Dim::Assoc(KeyKind::String)])
    );
    // A typedef of the enclosing module.
    assert_eq!(dims(c, "mq"), Some(vec![Dim::Queue, Dim::Queue]));
}

/// Guards: the anonymous form, a typedef'd property without its own
/// dimensions (one level, no rows), and the module-scope form were already
/// right.
#[test]
fn anonymous_single_level_and_module_scope_guard() {
    let d = elaborate(SRC);
    let c = &d.classes["C"].prop_coll_shapes;
    assert_eq!(dims(c, "anon"), Some(vec![Dim::Queue, Dim::Queue]));
    assert_eq!(dims(c, "one"), None);
    assert_eq!(
        dims(&d.coll_shapes, "mqq"),
        Some(vec![Dim::Queue, Dim::Queue])
    );
}
