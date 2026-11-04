//! IEEE 1800-2023 §7.2 / §23.3.3.5: an instance-array output connection
//! targets the selected struct element's member storage, in declared order.

use xezim_core::ast::expr::{ExprKind, Expression};

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
fn split_output_connections_write_member_leaves() {
    for (range, first, second) in [("1:0", 1, 0), ("0:1", 0, 1)] {
        let src = format!(
            "typedef struct {{ real a; int b; }} s_t;
             module ch(input int x, output s_t o); assign o = '{{x, 7}}; endmodule
             module top;
               int x; s_t w[4:5];
               ch u[{range}] (.x(x), .o(w));
             endmodule"
        );
        let model = xezim_core::parse_and_elaborate_multi(
            &[src],
            Some("top"),
            &[],
            &["ports.sv".to_string()],
            &[],
        )
        .expect("elaborate")
        .1;
        let connections: Vec<_> = model
            .continuous_assigns
            .iter()
            .filter_map(|ca| Some((name(&ca.lhs)?, name(&ca.rhs)?)))
            .collect();
        for (element, instance) in [(4, first), (5, second)] {
            for member in ["a", "b"] {
                let pair = (
                    format!("w[{element}].{member}"),
                    format!("u[{instance}].o.{member}"),
                );
                assert!(
                    connections.contains(&pair),
                    "missing {pair:?}: {connections:?}"
                );
            }
        }
        for instance in [0, 1] {
            let port = format!("u[{instance}].o");
            assert!(!model.packed_struct_fields.contains_key(&port));
            assert!(model.var_decl_types.contains_key(&port));
        }
        assert!(model.signals["w[4].a"].is_real);
    }
}
