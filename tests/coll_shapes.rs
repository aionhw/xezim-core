//! §7.4.5: every unpacked collection records its declared shape — each
//! dimension's kind, outermost first, with the key type of each associative
//! dimension — at every declaration scope.
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

const SRC: &str = r#"
package p;
  localparam int N = 3;
  int pq [string][$];
  int pn [N][$];
endpackage
module child;
  int cm [int][$];
endmodule
module top;
  typedef bit [3:0] k_t;
  typedef struct { int a [string][$]; } st;
  int m [int][$];
  int x [string][int][$];
  int d [][string][$];
  int v [2][string][$];
  int vr [3:1][$];
  byte w [*];
  byte wq [*][$];
  int q [$];
  int f [4];
  int f2 [2][3];
  int t [k_t][$];
  int s [shortint];
  int sq [shortint][$];
  st sv;
  class C;
    typedef bit [11:0] k12_t;
    int pk [k12_t][$];
    int pm [int][$];
    static int ps [string][];
    int pf [4];
    int pv [2][$];
  endclass
  class D #(int K = 2);
    int pk [K-1:0][$];
  endclass
  D #(4) dh;
  C h;
  child c();
endmodule
"#;

fn int32() -> Dim {
    Dim::Assoc(KeyKind::Integral {
        width: 32,
        signed: true,
    })
}

fn dims<H: std::hash::BuildHasher>(
    shapes: &std::collections::HashMap<String, CollShape, H>,
    name: &str,
) -> Option<Vec<Dim>> {
    shapes.get(name).map(|s| s.dims.clone())
}

#[test]
fn every_scope_records_each_dimension() {
    let d = elaborate(SRC);
    let s = &d.coll_shapes;
    let string = || Dim::Assoc(KeyKind::String);
    assert_eq!(dims(s, "m"), Some(vec![int32(), Dim::Queue]));
    assert_eq!(dims(s, "x"), Some(vec![string(), int32(), Dim::Queue]));
    assert_eq!(dims(s, "d"), Some(vec![Dim::Dyn, string(), Dim::Queue]));
    // §7.4.2: a fixed dimension carries its index bounds, ascending.
    let fixed = |lo, hi| Dim::Fixed(Some((lo, hi)));
    assert_eq!(dims(s, "v"), Some(vec![fixed(0, 1), string(), Dim::Queue]));
    assert_eq!(dims(s, "vr"), Some(vec![fixed(1, 3), Dim::Queue]));
    // A one-dimensional collection has no rows, and an all-fixed array is
    // laid out by its bounds: neither is a collection of collections.
    for name in ["w", "q", "f", "f2", "s"] {
        assert_eq!(dims(s, name), None, "{name}");
    }
    let wild = Dim::Assoc(KeyKind::Wildcard);
    assert_eq!(dims(s, "wq"), Some(vec![wild, Dim::Queue]));
    let short = Dim::Assoc(KeyKind::Integral {
        width: 16,
        signed: true,
    });
    assert_eq!(dims(s, "sq"), Some(vec![short, Dim::Queue]));
    // §7.8.4: each key keeps its declared width and signedness.
    let t = vec![
        Dim::Assoc(KeyKind::Integral {
            width: 4,
            signed: false,
        }),
        Dim::Queue,
    ];
    assert_eq!(dims(s, "t"), Some(t));
    // Package, struct-member and child-instance collections, under the
    // storage names the other declaration tables use.
    for name in ["pq", "sv.a", "c.cm"] {
        assert!(d.associative_arrays.contains_key(name), "{name}");
    }
    assert_eq!(dims(s, "pq"), Some(vec![string(), Dim::Queue]));
    assert_eq!(dims(s, "sv.a"), Some(vec![string(), Dim::Queue]));
    assert_eq!(dims(s, "c.cm"), Some(vec![int32(), Dim::Queue]));
    // Class properties, instance and static.
    let c = &d.classes["C"].prop_coll_shapes;
    assert_eq!(dims(c, "pm"), Some(vec![int32(), Dim::Queue]));
    assert_eq!(dims(c, "ps"), Some(vec![string(), Dim::Dyn]));
    assert_eq!(dims(c, "pf"), None);
    assert_eq!(dims(c, "pv"), Some(vec![fixed(0, 1), Dim::Queue]));
    // §8.25: a bound set by a class parameter is left unchecked, since each
    // specialization sizes it with its own value.
    let dk = &d.classes["D"].prop_coll_shapes;
    assert_eq!(dims(dk, "pk"), Some(vec![Dim::Fixed(None), Dim::Queue]));
    // A class typedef'd key resolves to its width.
    let k12 = Dim::Assoc(KeyKind::Integral {
        width: 12,
        signed: false,
    });
    assert_eq!(dims(c, "pk"), Some(vec![k12, Dim::Queue]));
    // `[N]` with `N` a parameter is a fixed dimension at package scope too.
    assert_eq!(dims(s, "pn"), Some(vec![fixed(0, 2), Dim::Queue]));
}
