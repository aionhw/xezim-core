//! A name in a generate block whose head is the label of a block nested in
//! it (`h.V` in `g`, where `g` holds `begin : h`) names that nested block
//! (§23.6, §23.8, §27.6). The rename of `g` gives the head `g`'s path
//! (`g.h.V`), as it does for `g`'s own declarations; the head kept its
//! spelling, so a continuous assign, which carries no generate scope, read
//! whichever `h` the design had at the top or the first such block. Run-time
//! reads are pinned in xezim's tests.

use xezim_core::ast::expr::{ExprKind, Expression, NumberLiteral};

fn elaborate(source: &str) -> xezim_core::ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[source.to_string()],
        Some("t"),
        &[],
        &["t.sv".to_string()],
        &[],
    )
    .expect("elaborate")
    .1
}

/// Every name `e` reads, each segment with its constant selects.
fn names(e: &Expression, out: &mut Vec<String>) {
    match &e.kind {
        ExprKind::Ident(h) => out.push(
            h.path
                .iter()
                .map(|s| {
                    let mut n = s.name.name.clone();
                    for sel in &s.selects {
                        match &sel.kind {
                            ExprKind::Number(NumberLiteral::Integer { value, .. }) => {
                                n.push_str(&format!("[{value}]"))
                            }
                            _ => n.push_str("[?]"),
                        }
                    }
                    n
                })
                .collect::<Vec<_>>()
                .join("."),
        ),
        ExprKind::Unary { operand, .. } => names(operand, out),
        ExprKind::Binary { left, right, .. } => {
            names(left, out);
            names(right, out);
        }
        // `k[1].w` reads as a member of an indexed name.
        ExprKind::Index { expr, index } => {
            let mut base = Vec::new();
            names(expr, &mut base);
            match (base.as_slice(), &index.kind) {
                ([b], ExprKind::Number(NumberLiteral::Integer { value, .. })) => {
                    out.push(format!("{b}[{value}]"))
                }
                _ => out.extend(base),
            }
        }
        ExprKind::MemberAccess { expr, member } => {
            let mut base = Vec::new();
            names(expr, &mut base);
            match base.as_slice() {
                [b] => out.push(format!("{b}.{}", member.name)),
                _ => out.extend(base),
            }
        }
        ExprKind::RangeSelect { expr, .. } => names(expr, out),
        ExprKind::Paren(e) => names(e, out),
        ExprKind::Concatenation(parts) => parts.iter().for_each(|p| names(p, out)),
        _ => {}
    }
}

/// The names read by the continuous assign that drives `lhs`.
#[track_caller]
fn rhs_of(design: &xezim_core::ElaboratedModule, lhs: &str) -> Vec<String> {
    let mut seen = Vec::new();
    for ca in &design.continuous_assigns {
        let mut l = Vec::new();
        names(&ca.lhs, &mut l);
        if l.first().map(String::as_str) == Some(lhs) {
            let mut r = Vec::new();
            names(&ca.rhs, &mut r);
            return r;
        }
        seen.extend(l);
    }
    panic!("no continuous assign drives '{lhs}'; drivers: {seen:?}")
}

#[test]
fn each_block_reads_its_own_child_not_a_sibling_or_top_block() {
    let d = elaborate(
        "module t;
  logic [31:0] y1, y2, y3, y4, y5;
  if (1) begin : h localparam int V = 7; end
  if (1) begin : g1
    if (1) begin : h localparam int V = 2; logic [31:0] s = 32'h9; end
    assign y1 = h.V;
  end
  if (1) begin : g2
    if (1) begin : h localparam int V = 5; logic [31:0] s = 32'h6; end
    assign y2 = h.V;
    assign y3 = h.s;
  end
  if (1) begin : g3
    localparam int V = 11;
    if (1) begin : h localparam int V = 13; end
    assign y4 = h.V + V;
  end
  assign y5 = h.V;
endmodule",
    );
    assert_eq!(rhs_of(&d, "y1"), ["g1.h.V"]);
    assert_eq!(rhs_of(&d, "y2"), ["g2.h.V"]);
    assert_eq!(rhs_of(&d, "y3"), ["g2.h.s"]);
    assert_eq!(rhs_of(&d, "y4"), ["g3.h.V", "g3.V"]);
    assert_eq!(rhs_of(&d, "y5"), ["h.V"]);
}

#[test]
fn deeper_paths_loop_and_case_parents_and_selects() {
    let d = elaborate(
        "module t;
  logic [31:0] d1, c1, s1;
  if (1) begin : g
    if (1) begin : h
      if (1) begin : k localparam int V = 3; end
    end
    assign d1 = h.k.V;
  end
  for (genvar i = 0; i < 2; i++) begin : l
    if (1) begin : h localparam int V = 20 + i; end
    logic [31:0] q;
    assign q = h.V;
  end
  case (1)
    1: begin : cs
      if (1) begin : h localparam int V = 31; end
      assign c1 = h.V;
    end
  endcase
  if (1) begin : gl
    for (genvar j = 0; j < 2; j++) begin : k logic [31:0] w; end
    assign s1 = k[1].w[3:0];
  end
endmodule",
    );
    assert_eq!(rhs_of(&d, "d1"), ["g.h.k.V"]);
    assert_eq!(rhs_of(&d, "l[0].q"), ["l[0].h.V"]);
    assert_eq!(rhs_of(&d, "l[1].q"), ["l[1].h.V"]);
    assert_eq!(rhs_of(&d, "c1"), ["cs.h.V"]);
    assert_eq!(rhs_of(&d, "s1"), ["gl.k[1].w"]);
}

#[test]
fn an_instance_or_a_target_in_the_child_block() {
    let d = elaborate(
        "module c(output logic [7:0] p); assign p = 8'h5c; endmodule
module t;
  logic [7:0] i1;
  if (1) begin : g
    if (1) begin : h
      c u (.p());
      logic [31:0] s2;
    end
    assign i1 = h.u.p;
    assign h.s2 = 32'h77;
  end
endmodule",
    );
    assert_eq!(rhs_of(&d, "i1"), ["g.h.u.p"]);
    assert!(
        d.continuous_assigns.iter().any(|ca| {
            let mut l = Vec::new();
            names(&ca.lhs, &mut l);
            l == ["g.h.s2"]
        }),
        "no continuous assign drives 'g.h.s2'"
    );
}

#[test]
fn a_nested_block_that_declares_the_same_label_keeps_its_own() {
    let d = elaborate(
        "module t;
  logic [31:0] y, z;
  if (1) begin : g
    if (1) begin : h localparam int V = 2; end
    if (1) begin : k
      if (1) begin : h localparam int V = 4; end
      assign y = h.V;
    end
    assign z = k.h.V;
  end
endmodule",
    );
    assert_eq!(rhs_of(&d, "y"), ["g.k.h.V"]);
    assert_eq!(rhs_of(&d, "z"), ["g.k.h.V"]);
}

// Guard: names the rename already got right.

#[test]
fn a_top_level_reference_and_a_declared_name_keep_their_spelling() {
    let d = elaborate(
        "module t;
  logic [31:0] y, z;
  if (1) begin : g
    logic [31:0] h;
    assign h = 32'h3;
    assign y = h;
  end
  if (1) begin : p localparam int V = 9; end
  assign z = p.V;
endmodule",
    );
    assert_eq!(rhs_of(&d, "y"), ["g.h"]);
    assert_eq!(rhs_of(&d, "z"), ["p.V"]);
}
