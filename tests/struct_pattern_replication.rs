//! IEEE 1800-2023 §10.9.2: remove the inner braces of structure replication.
use xezim_core::ast::expr::{AssignmentPatternItem, ExprKind};

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
fn replicated_continuous_items_keep_member_context() {
    let design = elaborate(
        r#"
module top;
  typedef struct { logic [7:0] a; bit [15:0] b; } pair_t;
  typedef struct { pair_t left; pair_t right; } nested_t;
  nested_t n;
  assign n = '{2{'{2{'1}}}};
endmodule
"#,
    );
    assert_eq!(design.continuous_assigns.len(), 4);
    for ca in &design.continuous_assigns {
        assert!(matches!(ca.rhs.kind, ExprKind::Number(_)), "{:?}", ca.rhs);
    }
}

#[test]
fn constant_struct_replication_and_bounded_expansion() {
    let design = elaborate(
        r#"
module top;
  typedef struct packed { bit [7:0] a, b, c, d; } four_t;
  localparam four_t P = '{2{8'h12, 8'h34}};
  four_t p;
  assign p = '{2{8'h12, 8'h34}};
endmodule
"#,
    );
    assert_eq!(design.parameters["P"].to_u64(), Some(0x12341234));
    let ExprKind::AssignmentPattern(items) = &design.continuous_assigns[0].rhs.kind else {
        panic!("pattern retained");
    };
    assert!(matches!(items[0], AssignmentPatternItem::Ordered(_)));
    assert!(xezim_core::elaborate::struct_pattern_replication(items, 3).is_none());
}

/// Intentionally illegal §10.9.2 counts: check multiplication before allocation.
#[test]
fn huge_mismatching_counts_do_not_allocate_expansion() {
    for count in ["2000000000", "63'h7fffffffffffffff"] {
        let design = elaborate(&format!(
            r#"
module top;
  typedef struct packed {{ byte a, b, c, d; }} four_t;
  four_t s;
  assign s = '{{{count}{{8'h12, 8'h34, 8'h56}}}};
endmodule
"#
        ));
        let ExprKind::AssignmentPattern(items) = &design.continuous_assigns[0].rhs.kind else {
            panic!("pattern retained");
        };
        let AssignmentPatternItem::Ordered(e) = &items[0] else {
            panic!("ordered");
        };
        let ExprKind::Replication { count, .. } = &e.kind else {
            panic!("replication");
        };
        assert!(xezim_core::elaborate::struct_pattern_count(count).is_some());
        assert!(xezim_core::elaborate::struct_pattern_replication(items, 4).is_none());
    }
}

/// §7.2/§7.4.2: nested structures carry the array-member exclusion too.
#[test]
fn array_members_exclude_structure_replication() {
    let design = elaborate(
        r#"
module top;
  typedef struct { int a[2]; int b[2]; } arrays_t;
  typedef struct { arrays_t l; arrays_t r; } nested_t;
  typedef struct { int a, b; } pair_t;
  typedef int array_t[2];
  typedef struct { array_t a, b; } alias_t;
  arrays_t s;
  assign s = '{2{'{2{7}}}};
endmodule
"#,
    );
    for (name, excluded) in [
        ("arrays_t", true),
        ("nested_t", true),
        ("pair_t", false),
        ("alias_t", true),
    ] {
        let xezim_core::ast::types::DataType::Struct(su) = &design.typedef_types[name] else {
            panic!("structure type");
        };
        assert_eq!(
            xezim_core::elaborate::struct_pattern_has_array_member(
                su,
                &design.typedef_types,
                &design.typedef_unpacked_dims
            ),
            excluded
        );
    }
    // Main's §10.9.1 array binder now lowers this pattern to four leaves.
    // The structure helper still declines it, preserving that binding path.
    assert_eq!(design.continuous_assigns.len(), 4);
    for ca in &design.continuous_assigns {
        assert!(matches!(ca.rhs.kind, ExprKind::Number(_)), "{:?}", ca.rhs);
    }
}

/// §5.7.1 sizes integer literals before §10.9.2 member expansion.
#[test]
fn literal_counts_keep_self_determined_widths() {
    for count in ["2", "2'b10", "2'd6", "4'sd2", "66'd2", "'h2"] {
        let design = elaborate(&format!(
            r#"
module top;
  typedef struct {{ int a, b; }} pair_t;
  typedef struct packed {{ bit [7:0] a, b; }} packed_t;
  localparam packed_t P = '{{{count}{{8'd7}}}};
  pair_t p;
  assign p = '{{{count}{{7}}}};
endmodule
"#
        ));
        assert_eq!(design.parameters["P"].to_u64(), Some(0x0707));
        assert_eq!(design.continuous_assigns.len(), 2);
        for ca in &design.continuous_assigns {
            assert!(matches!(ca.rhs.kind, ExprKind::Number(_)), "{:?}", ca.rhs);
        }
    }
}

/// §11.6: neither raw integer arithmetic nor the selected conditional
/// arm's width determines the count. Mismatches retain the original pattern.
#[test]
fn truncated_counts_do_not_expand_to_unconverted_member_count() {
    // The count-2 six-member sources are illegal on purpose; only the helper
    // refusal is checked. The count-6 source is legal, but queried for two members.
    for (count, members) in [
        ("N", 6),
        ("2'd6", 6),
        ("(2'b11 + 2'b11)", 6),
        ("(1 ? (2'b11 + 2'b11) : 3'b0)", 2),
    ] {
        let design = elaborate(&format!(
            r#"
module top;
  localparam bit [1:0] N = 6;
  typedef struct packed {{ byte a, b, c, d, e, f; }} six_t;
  six_t s;
  assign s = '{{{count}{{7}}}};
endmodule
"#
        ));
        let ExprKind::AssignmentPattern(items) = &design.continuous_assigns[0].rhs.kind else {
            panic!("pattern retained");
        };
        assert!(xezim_core::elaborate::struct_pattern_replication(items, members).is_none());
    }
}

/// §10.9.2/§11.4.12.1: conversion must preserve every known count bit.
#[test]
fn count_conversion_is_lossless() {
    use xezim_core::elaborate::struct_pattern_count_value;
    use xezim_core::value::{LogicBit, Value};
    for width in [2, 32, 63, 64, 66, 128] {
        let mut value = Value::from_u64(2, width);
        assert_eq!(struct_pattern_count_value(&value), Some(2));
        value.set_bit(0, LogicBit::X);
        assert_eq!(struct_pattern_count_value(&value), None);
        value.set_bit(0, LogicBit::Z);
        assert_eq!(struct_pattern_count_value(&value), None);
    }
    for bit in [63, 64, 65, 127] {
        let mut value = Value::from_u64(2, 128);
        value.set_bit(bit, LogicBit::One);
        assert_eq!(struct_pattern_count_value(&value), None);
    }
    let mut negative = Value::from_u64(2, 2);
    negative.is_signed = true;
    assert_eq!(struct_pattern_count_value(&negative), None);
    assert_eq!(struct_pattern_count_value(&Value::from_f64(2.0)), None);
}

/// §11.6/§11.8.2: nonliteral expressions require evaluation.
/// These legal expressions all count 2; declining them is a helper limit,
/// not an assertion that the simulator's old structure values are correct.
#[test]
fn unproven_count_forms_are_declined() {
    for count in [
        "TYPED",
        "INFERRED",
        "LOCAL",
        "UNTYPED_LOCAL",
        "(2)",
        "+2",
        "1 + 1",
        "1 ? 2 : 3",
        "(2'b11 + 2'b11)",
        "((2'b11 + 2'b11) == 3'd6) ? 2 : 1",
        "1 + ((2'b11 + 2'b11) == 3'd6)",
        "((2'b11 + 2'b11) < 3'd7) ? 2 : 1",
        "2 << ((2'b11 + 2'b11) == 3'd2)",
        "2 ** ((2'b11 + 2'b11) == 3'd6)",
        "{2'b11 + 2'b11}",
        "N[1:0]",
        "two()",
        "two() + 0",
        "two() * 1",
        "64'hffffffffffffffff - 64'hfffffffffffffffd",
        "int'(2)",
    ] {
        let design = elaborate(&format!(
            r#"
module top;
  localparam int N = 6;
  parameter int TYPED = 2;
  parameter INFERRED = 2;
  localparam int LOCAL = 2;
  localparam UNTYPED_LOCAL = 2;
  function automatic int two(); return 2; endfunction
  typedef struct packed {{ byte a, b; }} pair_t;
  pair_t s;
  assign s = '{{{count}{{7}}}};
endmodule
"#
        ));
        let ExprKind::AssignmentPattern(items) = &design.continuous_assigns[0].rhs.kind else {
            panic!("pattern retained");
        };
        assert!(
            xezim_core::elaborate::struct_pattern_replication(items, 2).is_none(),
            "{count}"
        );
    }
}

/// Intentionally illegal §10.9.2 sources: assert refusal, not an SV value.
#[test]
fn unknown_oversized_and_comparison_mismatches_are_declined() {
    for (declaration, count) in [
        ("parameter logic [1:0] N = 2'b1x;", "N"),
        ("parameter logic [1:0] N = 2'b1z;", "N"),
        ("parameter bit [65:0] N = 66'h10000000000000002;", "N"),
        ("", "((2'b11 + 2'b11) == 3'd2) ? 2 : 1"),
        ("", "4294967298"),
        ("", "2'b1x"),
        ("", "2'b1z"),
        ("", "2'sb10"),
        ("", "66'h10000000000000002"),
        ("", "1 ? (3'sb011 * 3'sb110) : 4'sb0000"),
        ("", "1 ? (3'sd3 * 3'sd3 * 3'sd2) : 6'sd0"),
        ("parameter N = 1 ? (3'sd3 * 3'sd3 * 3'sd2) : 6'sd0;", "N"),
        ("localparam N = 1 ? (3'sd3 * 3'sd3 * 3'sd2) : 6'sd0;", "N"),
    ] {
        let design = elaborate(&format!(
            r#"
module top;
  {declaration}
  typedef struct packed {{ byte a, b; }} pair_t;
  pair_t s;
  assign s = '{{{count}{{7}}}};
endmodule
"#
        ));
        let ExprKind::AssignmentPattern(items) = &design.continuous_assigns[0].rhs.kind else {
            panic!("pattern retained");
        };
        assert!(
            xezim_core::elaborate::struct_pattern_replication(items, 2).is_none(),
            "{declaration} {count}"
        );
    }
}

/// §27.4 substitutes each genvar's implicit localparam before lowering.
/// Keep a nonliteral count outside the literal-only expansion, even after
/// substitution. This asserts helper refusal, not main's incorrect SV value.
#[test]
fn substituted_nonliteral_counts_are_declined() {
    let design = elaborate(
        r#"
module top;
  typedef struct packed { byte a, b; } pair_t;
  for (genvar g = 2; g < 3; g++) begin : G
    pair_t s;
    assign s = '{g{7}};
  end
endmodule
"#,
    );
    let ExprKind::AssignmentPattern(items) = &design.continuous_assigns[0].rhs.kind else {
        panic!("pattern retained");
    };
    assert!(xezim_core::elaborate::struct_pattern_replication(items, 2).is_none());
}
