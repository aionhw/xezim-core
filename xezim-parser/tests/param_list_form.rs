//! A.4.1.1: a parameter value list is all ordered or all named. The parser reads
//! these lists in several places, so each is pinned here. Issue #150.

use sv_parser::parse;

const MIX: &str = "cannot mix ordered and named";

#[track_caller]
fn rejected(src: &str) {
    let r = parse(src);
    assert!(
        r.errors.iter().any(|d| d.message.contains(MIX)),
        "must be rejected: {src}\ngot: {:?}",
        r.errors.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

#[track_caller]
fn accepted(src: &str) {
    let r = parse(src);
    assert!(
        !r.errors.iter().any(|d| d.message.contains(MIX)),
        "must be accepted: {src}\ngot: {:?}",
        r.errors.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

#[test]
fn instance_with_either_order() {
    rejected("module t; c #(1, .B(2)) u(); endmodule");
    rejected("module t; c #(.A(1), 2) u(); endmodule");
}

#[test]
fn mix_after_several_entries_of_one_form() {
    rejected("module t; c #(1, 2, .C(3)) u(); endmodule");
    rejected("module t; c #(.A(1), .B(2), 3) u(); endmodule");
}

#[test]
fn empty_named_entry_is_still_named() {
    rejected("module t; c #(1, .B()) u(); endmodule");
    rejected("module t; c #(.A(), 2) u(); endmodule");
}

#[test]
fn bind_directive() {
    rejected("bind t c #(1, .B(2)) u();");
}

#[test]
fn unused_module_is_still_rejected() {
    rejected("module never_built; c #(1, .B(2)) u(); endmodule");
}

#[test]
fn inside_an_untaken_generate_branch() {
    rejected("module t; if (0) begin c #(1, .B(2)) u(); end endmodule");
}

#[test]
fn class_scope_in_an_expression() {
    rejected("module t; initial $display(k#(1, .B(2))::v); endmodule");
    rejected("module t; initial $display(k#(.A(1), 2)::v); endmodule");
}

#[test]
fn class_type_of_a_variable() {
    rejected("module t; k#(1, .B(2)) h; endmodule");
    rejected("module t; initial begin k#(.A(1), 2) h; end endmodule");
}

#[test]
fn extends_clause() {
    rejected("class d extends b#(1, .B(2)); endclass");
}

#[test]
fn list_nested_in_a_named_entry() {
    rejected("module t; c #(.T(k#(1, .B(2)))) u(); endmodule");
}

#[test]
fn all_ordered_and_all_named_stay_legal() {
    accepted("module t; c #(1, 2) u(); endmodule");
    accepted("module t; c #(.A(1), .B(2)) u(); endmodule");
    accepted("module t; c #(.A(), .B(2)) u(); endmodule");
    accepted("module t; c #() u(); endmodule");
    accepted("module t; initial $display(k#(1, 2)::v, k#(.A(1), .B(2))::v); endmodule");
    accepted("class d extends b#(.A(1), .B(2)); endclass");
    accepted("module t; k#(int, 2) h; endmodule");
}

#[test]
fn dots_below_the_top_level_are_not_entries() {
    // A call's named argument, a member select and a nested list of the other
    // form belong to the entry that holds them.
    accepted("module t; c #(f(.x(1)), 2) u(); endmodule");
    accepted("module t; c #(.A(f(1, .x(2))), .B(2)) u(); endmodule");
    accepted("module t; c #(p.q, 2) u(); endmodule");
    accepted("module t; c #('{a: 1, b: 2}, x[f(.y(1))]) u(); endmodule");
    accepted("module t; c #(.A(k#(1, 2)::v), .B(k#(.A(1))::v)) u(); endmodule");
    accepted("module t; c #(k#(.A(1))::v, 2) u(); endmodule");
}

#[test]
fn a_constructor_call_may_mix() {
    accepted("class d extends b(1, .x(2)); endclass");
    accepted("class d extends b#(1, 2)(3, .x(4)); endclass");
    accepted("module t; initial h = new(1, .x(2)); endmodule");
    accepted("module t; initial f(1, .x(2)); endmodule");
}

#[test]
fn a_gate_delay_is_not_touched() {
    accepted("module t; wire o; reg a; buf #(1, 2) b(o, a); endmodule");
    accepted("module t; wire o; reg a; p #(1, 2) u(o, a); endmodule");
}
