//! A name in a generate block resolves from that block outward (§23.9, §27.5):
//! a declaration in a nested or sibling block is not visible by its bare name.
//! Renaming a block's declarations must not bind a reference to one of those,
//! or the reference names something that does not exist. Run-time reads are
//! pinned in xezim's `tests/hierarchy/generate_rename_scope.rs`.

const OUTER: &str = "localparam int W = 8;";
const NESTED_W: &str = "if (1) begin : h localparam int W = 2; end";
const P: &str = "localparam logic [W-1:0] P = 8'hA5;";

#[track_caller]
fn param(source: &str, key: &str) -> i64 {
    let design = xezim_core::parse_and_elaborate_multi(
        &[source.to_string()],
        Some("t"),
        &[],
        &["t.sv".to_string()],
        &[],
    )
    .expect("elaborate")
    .1;
    design
        .parameters
        .get(key)
        .unwrap_or_else(|| {
            let mut known: Vec<_> = design.parameters.keys().collect();
            known.sort();
            panic!("no parameter '{key}' in {known:?}")
        })
        .to_i64()
        .unwrap_or_else(|| panic!("parameter '{key}' has no integer value"))
}

// The forms that bound the outer `W` to the block's nested `W`.

#[test]
fn a_parameter_type_beside_a_nested_declaration() {
    let src = format!("module t; {OUTER} if (1) begin : g {P} {NESTED_W} end endmodule");
    assert_eq!(param(&src, "g.P"), 0xA5);
}

#[test]
fn an_unpacked_dimension_beside_a_nested_declaration() {
    let src = format!(
        "module t; {OUTER} if (1) begin : g
           localparam logic [7:0] A [W-1:W-2] = '{{8'h5, 8'h6}};
           {NESTED_W}
         end endmodule"
    );
    assert_eq!(param(&src, "g.A[7]"), 5);
    assert_eq!(param(&src, "g.A[6]"), 6);
}

#[test]
fn an_initializer_beside_a_nested_declaration() {
    let src = format!(
        "module t; {OUTER} if (1) begin : g localparam int Q = W; {NESTED_W} end endmodule"
    );
    assert_eq!(param(&src, "g.Q"), 8);
}

#[test]
fn a_data_declaration_beside_a_nested_declaration() {
    let src = format!(
        "module t; {OUTER} if (1) begin : g
           logic [W-1:0] x;
           localparam int B = $bits(x);
           {NESTED_W}
         end endmodule"
    );
    assert_eq!(param(&src, "g.B"), 8);
}

// Every way a block can hold the nested declaration.

#[test]
fn the_nested_block_is_unlabeled() {
    let src = format!(
        "module t; {OUTER} if (1) begin : g {P} if (1) begin localparam int W = 2; end end endmodule"
    );
    assert_eq!(param(&src, "g.P"), 0xA5);
}

#[test]
fn the_nested_block_is_a_case_arm() {
    let src = format!(
        "module t; {OUTER} if (1) begin : g {P}
           case (1) 1: begin : h localparam int W = 2; end endcase
         end endmodule"
    );
    assert_eq!(param(&src, "g.P"), 0xA5);
}

#[test]
fn the_nested_block_is_a_loop() {
    let src = format!(
        "module t; {OUTER} if (1) begin : g {P}
           for (genvar j = 0; j < 2; j++) begin : h localparam int W = 2; end
         end endmodule"
    );
    assert_eq!(param(&src, "g.P"), 0xA5);
}

#[test]
fn the_nested_declaration_is_a_branch_not_taken() {
    let src = format!(
        "module t; {OUTER} if (1) begin : g {P}
           if (0) begin : h localparam int W = 2; end
         end endmodule"
    );
    assert_eq!(param(&src, "g.P"), 0xA5);
}

// Every way the renamed block can be entered.

#[test]
fn the_renamed_block_is_a_case_arm() {
    let src =
        format!("module t; {OUTER} case (1) 1: begin : g {P} {NESTED_W} end endcase endmodule");
    assert_eq!(param(&src, "g.P"), 0xA5);
}

#[test]
fn the_renamed_block_is_a_loop() {
    let src = format!(
        "module t; {OUTER} for (genvar i = 0; i < 2; i++) begin : g {P} {NESTED_W} end endmodule"
    );
    assert_eq!(param(&src, "g[0].P"), 0xA5);
    assert_eq!(param(&src, "g[1].P"), 0xA5);
}

#[test]
fn the_outer_name_is_a_header_parameter() {
    let src =
        format!("module t #(parameter int W = 8); if (1) begin : g {P} {NESTED_W} end endmodule");
    assert_eq!(param(&src, "g.P"), 0xA5);
}

// A sibling's declaration is no more visible than a child's.

#[test]
fn a_block_does_not_see_its_siblings_declaration() {
    let src = format!(
        "module t; {OUTER} if (1) begin : g
           {NESTED_W}
           if (1) begin : k {P} end
         end endmodule"
    );
    assert_eq!(param(&src, "g.k.P"), 0xA5);
}

// What the rename has to keep doing.

#[test]
fn a_nested_block_sees_its_own_declaration() {
    let src = format!(
        "module t; {OUTER} if (1) begin : g if (1) begin : h
           localparam int W = 2;
           localparam logic [W-1:0] P = 8'hA6;
         end end endmodule"
    );
    assert_eq!(param(&src, "g.h.P"), 2);
}

#[test]
fn a_nested_block_sees_its_parents_declaration() {
    let src = "module t; if (1) begin : g
           localparam int X = 3;
           if (1) begin : h localparam int Y = X; end
         end endmodule";
    assert_eq!(param(src, "g.h.Y"), 3);
}

#[test]
fn a_grandchild_sees_a_declaration_of_each_ancestor() {
    let src = "module t; if (1) begin : g
           localparam int X = 3;
           if (1) begin : h
             localparam int Y = 4;
             if (1) begin : j localparam int Z = X + Y; end
           end
         end endmodule";
    assert_eq!(param(src, "g.h.j.Z"), 7);
}

#[test]
fn each_scope_of_a_shadowed_name_has_its_own_value() {
    let src = format!(
        "module t; {OUTER} if (1) begin : g
           localparam int W = 4;
           localparam logic [W-1:0] P = 8'hFA;
           if (1) begin : h
             localparam int W = 2;
             localparam logic [W-1:0] Q = 8'hFE;
           end
           if (1) begin : k localparam int R = W; end
         end endmodule"
    );
    assert_eq!(param(&src, "g.P"), 0xA);
    assert_eq!(param(&src, "g.h.Q"), 2);
    assert_eq!(param(&src, "g.k.R"), 4);
}

#[test]
fn a_loop_sees_its_iterations_declaration() {
    let src = "module t; for (genvar i = 0; i < 2; i++) begin : g
           localparam int X = i + 5;
           if (1) begin : h localparam int Y = X; end
           for (genvar j = 0; j < 2; j++) begin : l localparam int Z = X + j; end
         end endmodule";
    assert_eq!(param(src, "g[1].h.Y"), 6);
    assert_eq!(param(src, "g[1].l[1].Z"), 7);
}

#[test]
fn a_selector_is_outside_the_block_it_selects() {
    let src = format!(
        "module t; {OUTER} if (1) begin : g
           if (W == 8) begin : h localparam int W = 2; localparam int Y = W; end
           case (W) 8: begin : k localparam int W = 3; localparam int Y = W; end endcase
         end endmodule"
    );
    assert_eq!(param(&src, "g.h.Y"), 2);
    assert_eq!(param(&src, "g.k.Y"), 3);
}

/// The names the elaborated triggers fire (§15.5.1).
fn triggers(source: &str) -> Vec<String> {
    use xezim_core::ast::stmt::{Statement, StatementKind};
    fn walk(s: &Statement, out: &mut Vec<String>) {
        match &s.kind {
            StatementKind::EventTrigger { name, .. } => out.push(name.name.clone()),
            StatementKind::TimingControl { stmt, .. } => walk(stmt, out),
            StatementKind::SeqBlock { stmts, .. } => stmts.iter().for_each(|s| walk(s, out)),
            _ => {}
        }
    }
    let design = xezim_core::parse_and_elaborate_multi(
        &[source.to_string()],
        Some("t"),
        &[],
        &["t.sv".to_string()],
        &[],
    )
    .expect("elaborate")
    .1;
    let mut out = Vec::new();
    design
        .initial_blocks
        .iter()
        .for_each(|b| walk(&b.stmt, &mut out));
    out.sort();
    out
}

#[test]
fn a_trigger_of_a_nested_blocks_event_names_that_events_key() {
    // §15.5.1, §23.9, §27.6: `-> ev` fires the event of its own block.
    let src = "module t;
      if (1) begin : g event ev; initial #1 -> ev;
        if (1) begin : h event ev; initial #2 -> ev; end
      end endmodule";
    assert_eq!(triggers(src), ["g.ev", "g.h.ev"]);
}
