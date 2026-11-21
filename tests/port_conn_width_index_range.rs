//! §23.3.3: a port connection is warned about when its width differs from
//! the port's. §7.4.3 and §11.5.1: a part-select after an index into a
//! multi-dimensional packed array selects elements of the next dimension, so
//! `.o(a[2][4:2])` on `logic [3:0][5:0][7:0] a` is three 8-bit elements,
//! 24 bits. The connection width counted 3 and every such connection drew a
//! bogus "port width mismatch … the connection is 3 bit(s)".

fn diagnostics(src: &str, top: &str) -> Vec<String> {
    xezim_core::elab_diag_capture_begin();
    let result = xezim_core::parse_and_elaborate_multi(
        &[src.to_string()],
        Some(top),
        &[],
        &[format!("{top}.sv")],
        &[],
    );
    let diags = xezim_core::elab_diag_capture_take();
    result.expect("elaborate");
    diags
}

#[test]
fn range_after_index_counts_element_widths() {
    let diags = diagnostics(
        r#"
module pcw_drv (output logic [2:0][7:0] o);
  assign o = 24'hc3c2c1;
endmodule
module pcw_snk (input logic [2:0][7:0] i, output logic [23:0] y);
  assign y = i;
endmodule
module pcw_top;
  logic [3:0][5:0][7:0] a;
  logic [5:0][7:0] u [2];
  logic [23:0] y0, y1;
  pcw_drv d0 (.o(a[2][4:2]));
  pcw_snk s0 (.i(a[1][3:1]), .y(y0));
  pcw_snk s1 (.i(u[1][5:3]), .y(y1));
endmodule
"#,
        "pcw_top",
    );
    assert!(
        !diags.iter().any(|d| d.contains("port width mismatch")),
        "no width mismatch expected: {diags:#?}"
    );
}

#[test]
fn a_real_mismatch_after_an_index_is_still_reported() {
    let diags = diagnostics(
        r#"
module pcw_short (output logic [2:0][7:0] o);
  assign o = 24'hc3c2c1;
endmodule
module pcw_top2;
  logic [3:0][5:0][7:0] a;
  pcw_short d0 (.o(a[2][4:3]));
endmodule
"#,
        "pcw_top2",
    );
    assert!(
        diags
            .iter()
            .any(|d| d.contains("port width mismatch") && d.contains("16 bit(s)")),
        "a 16-bit connection to a 24-bit port is reported: {diags:#?}"
    );
}

fn elaborate(src: &str, top: &str) -> xezim_core::ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[src.to_string()],
        Some(top),
        &[],
        &[format!("{top}.sv")],
        &[],
    )
    .expect("elaborate")
    .1
}

fn text(e: &xezim_core::ast::expr::Expression) -> String {
    use xezim_core::ast::expr::{ExprKind, NumberLiteral};
    match &e.kind {
        ExprKind::Ident(h) => h
            .path
            .iter()
            .map(|s| s.name.name.as_str())
            .collect::<Vec<_>>()
            .join("."),
        ExprKind::Index { expr, index } => format!("{}[{}]", text(expr), text(index)),
        ExprKind::RangeSelect {
            expr, left, right, ..
        } => format!("{}[{}:{}]", text(expr), text(left), text(right)),
        ExprKind::Number(NumberLiteral::Integer { size, value, .. }) => match size {
            Some(s) => format!("{s}'{value}"),
            None => value.clone(),
        },
        ExprKind::Concatenation(parts) => {
            format!(
                "{{{}}}",
                parts.iter().map(text).collect::<Vec<_>>().join(", ")
            )
        }
        ExprKind::Binary { op, left, right } => {
            format!("({} {op:?} {})", text(left), text(right))
        }
        ExprKind::Paren(inner) => text(inner),
        _ => "?".to_string(),
    }
}

/// §23.3.3: a connection whose width matches the port's is a plain rename of
/// an input, so the body reads the connection itself, and an inout's
/// connection is padded with z only up to the port's width. Both depend on
/// the connection's width: counted as 3 bits, the 24-bit `a[1][3:1]` kept the
/// input from being substituted (the body read a copy, `f.i`), and the
/// inout's connection got 21 bits of z in front of it.
#[test]
fn matching_width_after_index_substitutes_and_pads_nothing() {
    let mut m = elaborate(
        r#"
module pcw_flat (input logic [23:0] i, output logic [23:0] y);
  assign y = i ^ 24'h1;
endmodule
module pcw_io (inout wire [23:0] io);
endmodule
module pcw_top3;
  logic [3:0][5:0][7:0] a;
  wire [3:0][5:0][7:0] w;
  logic [23:0] y;
  pcw_flat f (.i(a[1][3:1]), .y(y));
  pcw_io b (.io(w[2][4:2]));
endmodule
"#,
        "pcw_top3",
    );
    // Instance bodies are kept unexpanded until the simulator asks for them.
    m.materialize_pending();
    let assigns: Vec<(String, String)> = m
        .continuous_assigns
        .iter()
        .map(|ca| (text(&ca.lhs), text(&ca.rhs)))
        .collect();
    let body: Vec<&String> = assigns
        .iter()
        .filter(|(l, _)| l == "f.y")
        .map(|(_, r)| r)
        .collect();
    assert!(
        body.len() == 1 && body[0].contains("a[1][3:1]") && !body[0].contains("f.i"),
        "the body reads the connection itself: {assigns:#?}"
    );
    assert!(
        assigns.contains(&("b.io".to_string(), "w[2][4:2]".to_string()))
            && !assigns.iter().any(|(_, r)| r.contains("'z")),
        "the inout's connection has no z padding: {assigns:#?}"
    );
}

/// The same range after the indices of an element of a two- or
/// three-dimensional unpacked array: `mm[1][0][3:1]` on
/// `logic [3:0][7:0] mm [0:1][0:1]` selects three 8-bit elements of the
/// element `mm[1][0]`, 24 bits. Only a one-dimensional unpacked base was
/// sized by elements, so these drew the 3-bit warning, and a real 16-bit
/// mismatch was reported as 2 bits.
#[test]
fn range_after_index_of_a_multi_dimensional_unpacked_element() {
    let diags = diagnostics(
        r#"
module pcw_snk2 (input logic [2:0][7:0] i, output logic [23:0] y);
  assign y = i;
endmodule
module pcw_snk3 (input logic [2:0][7:0] i, output logic [23:0] y);
  assign y = i;
endmodule
module pcw_snk4 (input logic [2:0][7:0] i, output logic [23:0] y);
  assign y = i;
endmodule
module pcw_top4;
  logic [3:0][7:0] mm [0:1][0:1];
  logic [3:0][7:0] m3 [0:1][0:1][0:1];
  logic [23:0] y0, y1, y2;
  pcw_snk2 s0 (.i(mm[1][0][3:1]), .y(y0));
  pcw_snk3 s1 (.i(m3[1][0][1][3:1]), .y(y1));
  pcw_snk4 s2 (.i(mm[0][1][3:2]), .y(y2));
endmodule
"#,
        "pcw_top4",
    );
    let mismatches: Vec<&String> = diags
        .iter()
        .filter(|d| d.contains("port width mismatch"))
        .collect();
    assert_eq!(mismatches.len(), 1, "{diags:#?}");
    assert!(
        mismatches[0].contains("'pcw_snk4'")
            && mismatches[0].contains("the connection is 16 bit(s)"),
        "{diags:#?}"
    );
}

#[test]
fn indexed_range_counts_elements_with_variable_start() {
    // The width warning is reported once per (module, port) pair, so each
    // select connects a sink of its own.
    for (k, select) in ["pos +: 2", "pos -: 2"].into_iter().enumerate() {
        let src = format!(
            "module sink{k}(input logic [23:0] a); endmodule
            module top(input int pos, input logic [3:0][5:0][7:0] words);
              sink{k} u(words[1][{select}]);
            endmodule"
        );
        let messages = diagnostics(&src, "top");
        assert!(
            messages
                .iter()
                .any(|d| d.contains("port width mismatch") && d.contains("16 bit(s)")),
            "{select}: {messages:?}"
        );
    }
}
