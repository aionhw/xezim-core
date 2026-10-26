//! §7.4.2 / §7.6: a fixed unpacked variable of an inlined child module keeps
//! its declared direction, as a top-level one does. A descending child array
//! (`int a [3:0];`) was registered as ascending, so a whole-array assignment
//! between it and a procedural local paired the elements in reverse.

fn elab(src: &str) -> xezim_core::elaborate::ElaboratedModule {
    let (_, mut m) = xezim_core::parse_and_elaborate_multi(
        &[src.to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .expect("elaborate");
    m.materialize_pending();
    m
}

#[test]
fn child_arrays_record_descending_ranges() {
    let m = elab(
        r#"
module sub #(parameter int HI = 3);
  typedef int fat [3:0];
  int d [HI:0];
  int a [0:HI];
  int b [5:2];
  logic [7:0] l [3:0];
  fat t;
  int n [4];
endmodule
module top;
  sub u();
  sub #(.HI(1)) v();
endmodule
"#,
    );
    for inst in ["u", "v"] {
        for name in ["d", "b", "l", "t"] {
            let key = format!("{inst}.{name}");
            assert!(m.descending_arrays.contains(&key), "{key} is descending");
        }
        for name in ["a", "n"] {
            let key = format!("{inst}.{name}");
            assert!(m.arrays.contains_key(&key), "{key} is an array");
            assert!(!m.descending_arrays.contains(&key), "{key} is ascending");
        }
    }
}
