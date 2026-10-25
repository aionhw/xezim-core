//! §6.18 / §7.4: an unpacked-array typedef declared inside a child module
//! (`typedef logic [7:0] arr_t [N];`) keeps its dimensions through inlining,
//! per instance, for module variables and for statement-local declarations.
//! Only its element width and type were recorded, so every `arr_t v;` in an
//! instance became a scalar of the element width.

use xezim_core::ast::stmt::StatementKind;
use xezim_core::ast::types::DataType;
use xezim_core::elaborate::ElaboratedModule;

fn elab(src: &str) -> ElaboratedModule {
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

const SRC: &str = r#"
typedef int arr_t [0:1];
module sub #(parameter int N = 3);
  typedef logic [7:0] arr_t [N];
  typedef arr_t alias_t;
  arr_t m;
  alias_t al;
  initial begin
    arr_t a;
    a[0] = 8'd1;
  end
endmodule
module other;
  arr_t x;
endmodule
module top;
  sub u3();
  sub #(.N(5)) u5();
  other o();
endmodule
"#;

#[test]
fn child_typedef_arrays_keep_their_dimensions_per_instance() {
    let m = elab(SRC);
    assert_eq!(m.arrays.get("u3.m").map(|a| (a.0, a.1)), Some((0, 2)));
    assert_eq!(m.arrays.get("u5.m").map(|a| (a.0, a.1)), Some((0, 4)));
    assert_eq!(m.arrays.get("u3.al").map(|a| (a.0, a.1)), Some((0, 2)));
    assert_eq!(m.arrays.get("u5.al").map(|a| (a.0, a.1)), Some((0, 4)));
    for key in ["u3.arr_t", "u5.arr_t", "u3.alias_t", "u5.alias_t"] {
        assert_eq!(
            m.typedef_unpacked_dims.get(key).map(Vec::len),
            Some(1),
            "{key}"
        );
    }
    // The $unit typedef the child shadowed is back once the child is done.
    assert_eq!(m.arrays.get("o.x").map(|a| (a.0, a.1)), Some((0, 1)));
}

#[test]
fn statement_local_typedef_array_keeps_its_name() {
    let m = elab(SRC);
    let mut found = 0;
    for b in &m.initial_blocks {
        let StatementKind::SeqBlock { stmts, .. } = &b.stmt.kind else {
            continue;
        };
        for s in stmts {
            if let StatementKind::VarDecl { data_type, .. } = &s.kind {
                assert!(
                    matches!(data_type, DataType::TypeReference { .. }),
                    "an unpacked typedef was replaced by its element type: {data_type:?}"
                );
                found += 1;
            }
        }
    }
    assert_eq!(found, 2, "one `arr_t a;` per instance");
}
