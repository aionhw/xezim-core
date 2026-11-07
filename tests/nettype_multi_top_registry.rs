//! IEEE 1800-2023 §6.6.7, §3.12.1, §23.3.1: a `$unit` nettype applies in a
//! design with more than one top-level module too. The synthetic root that
//! elaborates several tops registered no `$unit` nettype, so a net's
//! resolution function never ran (two drivers summed by `rsum` read the
//! parent's driver alone: 2.0 instead of the reference simulator's 5.0) and
//! two drivers of a resolver-less net were not an error.

use xezim_core::ast::expr::{ExprKind, Expression};

const RESOLVED: &str = r#"
function automatic real rsum(input real d[]); real s = 0; foreach (d[i]) s += d[i]; return s; endfunction
nettype real rnet with rsum;
module drv(input real v, output rnet p); assign p = v; endmodule
module spare; endmodule
module top; real v = 1.5; rnet n; drv a(.v(v), .p(n)); drv b(.v(v), .p(n)); assign n = 2.0; endmodule
"#;

const UNRESOLVED: &str = r#"
typedef struct { real V; int code; } e_t;
nettype e_t enet;
module drv(input real v, output enet p); assign p = '{v, 1}; endmodule
module spare; endmodule
module top; real v = 1.0; enet n; drv a(.v(v), .p(n)); drv b(.v(v), .p(n)); endmodule
"#;

fn elaborate(src: &str) -> Result<xezim_core::ElaboratedModule, String> {
    xezim_core::parse_and_elaborate_multi(&[src.to_string()], None, &[], &["t.sv".into()], &[])
        .map(|(_, m)| m)
}

fn calls(e: &Expression, name: &str) -> bool {
    match &e.kind {
        ExprKind::Call { func, .. } => {
            matches!(&func.kind, ExprKind::Ident(h) if h.path.last().is_some_and(|s| s.name.name == name))
        }
        _ => false,
    }
}

#[test]
fn a_unit_resolver_runs_in_a_multi_top_design() {
    let m = elaborate(RESOLVED).expect("elaborate");
    assert!(
        m.nettype_resolvers.values().any(|r| r == "rsum"),
        "{:?}",
        m.nettype_resolvers
    );
    assert!(
        m.continuous_assigns.iter().any(|ca| calls(&ca.rhs, "rsum")),
        "no call of the resolution function"
    );
}

#[test]
fn two_drivers_of_a_unit_unresolved_nettype_are_an_error_in_a_multi_top_design() {
    let err = elaborate(UNRESOLVED).expect_err("two drivers");
    assert!(
        err.contains("of an unresolved nettype has 2 continuous drivers"),
        "{err}"
    );
}
