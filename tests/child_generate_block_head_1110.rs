//! A name in a module body whose head is one of the module's own generate
//! blocks (`h.x`, `g[1].x`) names that block of the instance, as a head that
//! names a child instance does (§23.9, §27.5, aionhw/xezim#1110). When the
//! module was inlined as a child, the head kept its spelling, so the top
//! module's block of the same name won at run time. Run-time reads are pinned
//! in xezim's tests.

use xezim_core::ast::expr::{ExprKind, Expression, NumberLiteral};

/// The elaborated design with the instances' prefixed bodies materialized.
fn elaborate(source: &str) -> xezim_core::ElaboratedModule {
    let mut m = xezim_core::parse_and_elaborate_multi(
        &[source.to_string()],
        Some("top"),
        &[],
        &["t.sv".to_string()],
        &[],
    )
    .expect("elaborate")
    .1;
    m.materialize_pending();
    m
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
fn a_child_names_its_own_generate_block() {
    let d = elaborate(
        "module child;
  if (1) begin : h int x; int a [2]; end
  for (genvar i = 0; i < 2; i++) begin : g int x; end
  int y1, y2, y3;
  assign y1 = h.x;
  assign y2 = h.a[1];
  assign y3 = g[1].x;
endmodule
module top;
  child c ();
  if (1) begin : h int x; int a [2]; end
  for (genvar i = 0; i < 2; i++) begin : g int x; end
  int z;
  assign z = h.x;
endmodule",
    );
    assert_eq!(rhs_of(&d, "c.y1"), ["c.h.x"]);
    assert_eq!(rhs_of(&d, "c.y2"), ["c.h.a[1]"]);
    assert_eq!(rhs_of(&d, "c.y3"), ["c.g[1].x"]);
    assert_eq!(rhs_of(&d, "z"), ["h.x"]);
}

#[test]
fn an_upward_name_without_a_local_block_is_left_alone() {
    let d = elaborate(
        "module child;
  int y;
  assign y = h.x;
endmodule
module top;
  child c ();
  if (1) begin : h int x; end
endmodule",
    );
    assert_eq!(rhs_of(&d, "c.y"), ["h.x"]);
}
