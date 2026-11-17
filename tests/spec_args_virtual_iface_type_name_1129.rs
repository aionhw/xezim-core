//! §8.25 / §25.9: `virtual clk_rst_if` in a class specialization names the
//! interface type, not an interface instance declared with the same spelling.
use xezim_core::ast::expr::{ExprKind, Expression};

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

fn spec_texts(e: &Expression, out: &mut Vec<String>) {
    match &e.kind {
        ExprKind::Specialization { type_args_text, base, .. } => {
            out.push(type_args_text.clone());
            spec_texts(base, out);
        }
        ExprKind::Call { func, args } => {
            spec_texts(func, out);
            args.iter().for_each(|a| spec_texts(a, out));
        }
        ExprKind::MemberAccess { expr, .. } => spec_texts(expr, out),
        _ => {}
    }
}

#[test]
fn virtual_interface_type_arg_keeps_type_spelling() {
    let mut d = elaborate(
        r#"
package p;
  class db #(type T = int);
    static bit found[string];
  endclass
endpackage
interface clk_rst_if; logic clk; endinterface
module u_tb(output bit a, output bit b, output bit ok);
  import p::*;
  clk_rst_if clk_rst_if();
  assign a = db#(virtual clk_rst_if)::found.exists("k");
  assign b = db#(.T(virtual clk_rst_if))::found.exists("k");
  assign ok = db#(virtual \clk_rst_if )::found.exists("k");
endmodule
module top;
  bit a, b, ok;
  u_tb u(a, b, ok);
endmodule
"#,
    );
    d.materialize_pending();
    let mut texts = Vec::new();
    for ca in &d.continuous_assigns {
        spec_texts(&ca.rhs, &mut texts);
    }
    assert!(texts.iter().any(|t| t.contains("virtual clk_rst_if")));
    assert!(!texts.iter().any(|t| t.contains("u.clk_rst_if") || t.contains("u_tb.clk_rst_if")));
    assert!(texts.iter().any(|t| t.contains(r"\clk_rst_if")));
}