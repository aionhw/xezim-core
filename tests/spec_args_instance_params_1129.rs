//! §8.25, §23.10: the argument text of a class specialization written in a
//! module instance (`g#(PW)::id()`) names the instance's own parameter, as an
//! expression reference to it does, so two instances with different values
//! name different specializations (aionhw/xezim#1129). Named-argument labels,
//! scoped names and literals keep their spelling (the text is the parser's
//! token spelling).
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
        ExprKind::Specialization {
            base,
            type_args_text,
        } => {
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
fn specialization_arguments_name_the_instance_parameters() {
    let mut d = elaborate(
        r#"
package gp;
  virtual class g #(parameter int W = 8);
    static function int id(); return W; endfunction
  endclass
  localparam int K = 3;
endpackage
module leaf #(parameter PW = 6) (output int a, output int b, output int c);
  import gp::*;
  assign a = g#(PW * 2)::id();
  assign b = g#(.W(PW))::id();
  assign c = g#(gp::K + 'h1)::id();
endmodule
module top;
  int a6, b6, c6, a9, b9, c9;
  leaf #(6) u6(a6, b6, c6);
  leaf #(9) u9(a9, b9, c9);
endmodule
"#,
    );
    // Inlined instances' assigns are rewritten when they are materialized.
    d.materialize_pending();
    let mut texts = Vec::new();
    for ca in &d.continuous_assigns {
        spec_texts(&ca.rhs, &mut texts);
    }
    texts.sort();
    assert_eq!(
        texts,
        [
            ". W ( u6.PW )",
            ". W ( u9.PW )",
            "gp :: K + 'h1",
            "gp :: K + 'h1",
            "u6.PW * 2",
            "u9.PW * 2",
        ]
    );
}

#[test]
fn virtual_interface_types_do_not_qualify_homonymous_instances() {
    let mut d = elaborate(r#"
interface bus #(parameter W=4); logic [W-1:0] data; endinterface
package p;
  class db #(type T=int); static function int id(); return 1; endfunction endclass
endpackage
module leaf #(parameter W=4)(output int a, b);
  import p::*;
  bus #(W) bus();
  assign a = db#(virtual bus#(W))::id();
  assign b = db#(virtual interface bus#(W))::id();
endmodule
module top;
  int a,b;
  leaf u(a,b);
endmodule
"#);
    d.materialize_pending();
    let mut texts = Vec::new();
    for ca in &d.continuous_assigns { spec_texts(&ca.rhs, &mut texts); }
    assert_eq!(texts.len(), 2, "{texts:?}");
    for text in texts {
        assert!(!text.contains("u.bus"), "{text}");
        assert!(text.contains("u.W"), "{text}");
    }
}
