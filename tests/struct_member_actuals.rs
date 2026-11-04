//! IEEE 1800-2023 §23.3.3 / §7.2: connections to struct members must
//! reach the selected member's leaf storage, including §7.4 array elements.

use xezim_core::ast::expr::{ExprKind, Expression};

fn design(src: &str) -> xezim_core::elaborate::ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[src.to_string()],
        Some("top"),
        &[],
        &["ports.sv".to_string()],
        &[],
    )
    .expect("elaborate")
    .1
}

fn name(expr: &Expression) -> Option<String> {
    match &expr.kind {
        ExprKind::Ident(h) if h.path.iter().all(|s| s.selects.is_empty()) => Some(
            h.path
                .iter()
                .map(|s| s.name.name.as_str())
                .collect::<Vec<_>>()
                .join("."),
        ),
        _ => None,
    }
}

#[test]
fn output_connections_write_selected_member_leaves() {
    let src = r#"
typedef struct { real r; int n; } leaf_t;
typedef struct { leaf_t deep; } in_t;
typedef struct { in_t in; int c; } w_t;
module ch(input int x, output leaf_t o); assign o = '{x, 7}; endmodule
module wrapper;
  int x; w_t w, arr[2];
  ch a(.x(x), .o(w.in.deep));
  ch b(.x(x), .o(arr[1].in.deep));
endmodule
module top; wrapper w(); endmodule
"#;
    let model = design(src);
    let connections: Vec<_> = model
        .continuous_assigns
        .iter()
        .filter_map(|ca| Some((name(&ca.lhs)?, name(&ca.rhs)?)))
        .collect();
    for (actual, formal) in [("w.w.in.deep", "w.a.o"), ("w.arr[1].in.deep", "w.b.o")] {
        for member in ["r", "n"] {
            let pair = (format!("{actual}.{member}"), format!("{formal}.{member}"));
            assert!(
                connections.contains(&pair),
                "missing {pair:?}: {connections:?}"
            );
        }
        assert!(!connections.iter().any(|(lhs, _)| lhs == actual));
        assert!(model.signals[&format!("{actual}.r")].is_real);
    }
}

/// §11.5 / §23.3.3: a runtime selector must stay on one connection, not
/// be copied to each member or folded away by the constant-path expansion.
#[test]
fn runtime_output_selector_is_not_duplicated() {
    let src = r#"
typedef struct { int a; int b; } in_t;
typedef struct { in_t in; int c; } w_t;
module ch(input int x, output in_t o); assign o = '{x, 7}; endmodule
module top;
  int x, calls; w_t arr[2];
  function automatic int next_index(); calls++; return 1; endfunction
  ch u(.x(x), .o(arr[next_index()].in));
endmodule
"#;
    let model = design(src);
    let connections: Vec<_> = model
        .continuous_assigns
        .iter()
        .filter(|ca| name(&ca.rhs).as_deref() == Some("u.o"))
        .collect();
    assert_eq!(connections.len(), 1);
    let ExprKind::MemberAccess { expr, member } = &connections[0].lhs.kind else {
        panic!("runtime member select was lost: {:?}", connections[0].lhs);
    };
    assert_eq!(member.name, "in");
    let ExprKind::Index { expr: base, index } = &expr.kind else {
        panic!("runtime array select was lost: {expr:?}");
    };
    assert_eq!(name(base).as_deref(), Some("arr"));
    let ExprKind::Call { func, args } = &index.kind else {
        panic!("selector call was lost: {index:?}");
    };
    assert_eq!(name(func).as_deref(), Some("next_index"));
    assert!(args.is_empty());
    assert!(
        !model
            .continuous_assigns
            .iter()
            .any(|ca| { matches!(name(&ca.rhs).as_deref(), Some("u.o.a" | "u.o.b")) })
    );
}
