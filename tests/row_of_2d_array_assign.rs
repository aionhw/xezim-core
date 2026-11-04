//! `assign dst = src[row];` expands to one assign per element of the row (§7.6 / §10.3).
use xezim_core::ast::expr::{ExprKind, Expression, NumberLiteral};

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

/// `name[i][j]...` with literal indices, as text.
fn element(e: &Expression) -> Option<String> {
    match &e.kind {
        ExprKind::Ident(h) => Some(h.path.iter().map(|s| s.name.name.as_str()).collect()),
        ExprKind::Index { expr, index } => match &index.kind {
            ExprKind::Number(NumberLiteral::Integer { value, .. }) => {
                Some(format!("{}[{value}]", element(expr)?))
            }
            _ => None,
        },
        _ => None,
    }
}

#[test]
fn row_of_2d_array_assign_expands_per_element() {
    let design = elaborate(
        r#"
module top;
  localparam int ST = 2;
  logic [7:0] src [ST][3];
  logic [7:0] dst [2:0];
  logic [7:0] unk [3];
  localparam logic R = 1'bx;
  assign dst = src[ST-1];
  assign unk = src[R];
endmodule
"#,
    );
    let [assign, unknown] = design.continuous_assigns.as_slice() else {
        panic!("expected two continuous assigns");
    };
    let parts = |a: &xezim_core::elaborate::ContinuousAssignment| {
        xezim_core::elaborate::whole_array_row_assign_parts(
            &a.lhs,
            &a.rhs,
            a.delay,
            &design.arrays,
            &design.arrays_2d,
            &design.parameters,
            Some(&design.descending_arrays),
            Some(&design.unpacked_decl_dims),
        )
    };
    assert!(parts(unknown).is_none(), "an x row index selects no row");
    let pairs: Vec<_> = parts(assign)
        .expect("expanded per element")
        .iter()
        .map(|a| (element(&a.lhs).unwrap(), element(&a.rhs).unwrap()))
        .collect();
    assert_eq!(
        pairs,
        [
            ("dst[2]".to_string(), "src[1][0]".to_string()),
            ("dst[1]".to_string(), "src[1][1]".to_string()),
            ("dst[0]".to_string(), "src[1][2]".to_string()),
        ],
    );
}

/// §7.4.5: a synthesized negative row index remains a signed expression.
#[test]
fn negative_row_index_is_preserved() {
    let design = elaborate(
        r#"
module top;
  logic [7:0] src [-1:0][4:2];
  wire [7:0] dst [10:12];
  assign dst = src[-1];
endmodule
"#,
    );
    let assign = &design.continuous_assigns[0];
    let parts = xezim_core::elaborate::whole_array_row_assign_parts(
        &assign.lhs,
        &assign.rhs,
        assign.delay,
        &design.arrays,
        &design.arrays_2d,
        &design.parameters,
        Some(&design.descending_arrays),
        Some(&design.unpacked_decl_dims),
    )
    .expect("row expands");
    for part in parts {
        let ExprKind::Index { expr, .. } = &part.rhs.kind else {
            panic!("column select")
        };
        let ExprKind::Index { index, .. } = &expr.kind else {
            panic!("row select")
        };
        assert_eq!(
            xezim_core::elaborate::const_eval_i64_with_params(index, Some(&design.parameters)),
            Some(-1)
        );
        assert!(matches!(index.kind, ExprKind::Unary { .. }));
    }
}
