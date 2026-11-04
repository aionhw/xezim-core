//! A whole-array continuous assign with a hierarchical side drives each element (§7.6 / §10.3).
use xezim_core::ast::expr::{ExprKind, NumberLiteral};

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

#[test]
fn hierarchical_whole_array_assign_expands_per_element() {
    let design = elaborate(
        r#"
interface ifc; logic [7:0] arr [0:1]; endinterface
module dut; logic [7:0] src [1:0]; endmodule
module top; ifc i(); dut d(); assign i.arr = d.src; endmodule
"#,
    );
    let element = |e: &xezim_core::ast::expr::Expression| match &e.kind {
        ExprKind::Index { expr, index } => match (&expr.kind, &index.kind) {
            (ExprKind::Ident(h), ExprKind::Number(NumberLiteral::Integer { value, .. })) => {
                Some(format!(
                    "{}[{}]",
                    h.path
                        .iter()
                        .map(|s| s.name.name.as_str())
                        .collect::<Vec<_>>()
                        .join("."),
                    value
                ))
            }
            _ => None,
        },
        _ => None,
    };
    let [assign] = design.continuous_assigns.as_slice() else {
        panic!("expected one continuous assign");
    };
    let parts = xezim_core::elaborate::whole_array_assign_parts_dir(
        &assign.lhs,
        &assign.rhs,
        assign.delay,
        &design.arrays,
        Some(&design.descending_arrays),
        Some(&design.unpacked_decl_dims),
    )
    .expect("expanded per element");
    let pairs: Vec<_> = parts
        .iter()
        .map(|a| (element(&a.lhs), element(&a.rhs)))
        .collect();
    assert_eq!(
        pairs,
        [
            (Some("i.arr[0]".into()), Some("d.src[1]".into())),
            (Some("i.arr[1]".into()), Some("d.src[0]".into())),
        ],
    );
}
