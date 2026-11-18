//! IEEE 1800-2023 §23.10: flat bodies retain their elaborated processes and
//! declaration ownership. Binds (§23.11) and generated hierarchy (§27) still
//! run the complete inlining path.

use xezim_core::ElaboratedModule;
use xezim_core::ast::expr::{ExprKind, Expression};
use xezim_core::ast::stmt::{Statement, StatementKind};

fn elaborate(source: &str) -> ElaboratedModule {
    let (_, mut model) = xezim_core::parse_and_elaborate_multi(
        &[source.to_string()],
        Some("top"),
        &[],
        &["flat-leaf.sv".to_string()],
        &[],
    )
    .expect("elaborate");
    model.materialize_pending();
    model
}

fn ident(expr: &Expression) -> String {
    let ExprKind::Ident(h) = &expr.kind else {
        panic!("expected identifier: {:?}", expr.kind);
    };
    h.path
        .iter()
        .map(|p| p.name.name.as_str())
        .collect::<Vec<_>>()
        .join(".")
}

fn assignment_target(stmt: &Statement) -> String {
    match &stmt.kind {
        StatementKind::BlockingAssign { lvalue, .. }
        | StatementKind::NonblockingAssign { lvalue, .. } => ident(lvalue),
        StatementKind::TimingControl { stmt, .. } => assignment_target(stmt),
        StatementKind::SeqBlock { stmts, .. } if stmts.len() == 1 => assignment_target(&stmts[0]),
        _ => panic!("expected one assignment: {:?}", stmt.kind),
    }
}

fn instances_of(model: &ElaboratedModule, definition: &str) -> Vec<String> {
    let mut paths: Vec<_> = model
        .instances
        .iter()
        .filter(|i| i.def_name == definition)
        .map(|i| i.path.clone())
        .collect();
    paths.sort();
    paths
}

#[test]
fn flat_top_keeps_signals_processes_and_parameter_ownership() {
    let model = elaborate(
        "module top #(parameter int H=4); localparam int L=H+3; \
         logic clk; logic [H-1:0] value; initial value=L; \
         always @(posedge clk) value <= value+1; endmodule",
    );
    assert_eq!(model.signals["value"].width, 4);
    assert_eq!(model.parameters["L"].to_i64(), Some(7));
    assert!(model.declared_parameters.contains("H"));
    assert!(model.declared_parameters.contains("L"));
    assert_eq!(model.initial_blocks.len(), 1);
    assert_eq!(model.always_blocks.len(), 1);
    assert_eq!(assignment_target(&model.initial_blocks[0].stmt), "value");
    assert_eq!(assignment_target(&model.always_blocks[0].stmt), "value");
    assert!(model.instances.is_empty());
}

#[test]
fn flat_sibling_leaves_keep_imports_and_instance_processes() {
    let model = elaborate(
        "package cfg; parameter int W=5; endpackage \
         module leaf #(parameter int STEP=2); import cfg::*; localparam int N=W+STEP; \
         logic clk; logic [N-1:0] value; initial value=STEP; \
         always @(posedge clk) value <= value+1; endmodule \
         module top; leaf #(.STEP(3)) u(); leaf #(.STEP(6)) v(); endmodule",
    );
    for (path, width) in [("u", 8), ("v", 11)] {
        assert_eq!(model.signals[&format!("{path}.value")].width, width);
        assert_eq!(
            model.parameters[&format!("{path}.N")].to_i64(),
            Some(i64::from(width))
        );
        assert!(model.declared_parameters.contains(&format!("{path}.STEP")));
        assert!(model.declared_parameters.contains(&format!("{path}.N")));
        assert!(!model.declared_parameters.contains(&format!("{path}.W")));
    }
    assert_eq!(instances_of(&model, "leaf"), ["u", "v"]);
    assert_eq!(model.initial_blocks.len(), 2);
    assert_eq!(model.always_blocks.len(), 2);
    for path in ["u", "v"] {
        let initial = model
            .initial_blocks
            .iter()
            .find(|p| p.scope == path)
            .unwrap();
        let always = model
            .always_blocks
            .iter()
            .find(|p| p.scope == path)
            .unwrap();
        assert_eq!(assignment_target(&initial.stmt), format!("{path}.value"));
        assert_eq!(assignment_target(&always.stmt), format!("{path}.value"));
    }
}

const OBSERVER: &str = "module observer #(parameter int N=3); logic [N-1:0] seen; \
                       initial seen=N; endmodule ";

#[test]
fn direct_bind_in_an_otherwise_flat_top_is_retained() {
    let model = elaborate(&format!(
        "{OBSERVER} module top; logic retained; \
         bind top observer #(.N(7)) attached(); endmodule"
    ));
    assert_eq!(instances_of(&model, "observer"), ["attached"]);
    assert_eq!(model.signals["attached.seen"].width, 7);
    assert!(model.signals.contains_key("retained"));
    assert!(model.declared_parameters.contains("attached.N"));
    assert_eq!(model.initial_blocks.len(), 1);
    assert_eq!(
        assignment_target(&model.initial_blocks[0].stmt),
        "attached.seen"
    );
}

#[test]
fn external_bind_into_a_flat_leaf_selects_only_its_target() {
    let model = elaborate(&format!(
        "{OBSERVER} module leaf; logic retained; endmodule \
         module top; leaf a(), b(); endmodule \
         bind top.a observer #(.N(9)) attached();"
    ));
    assert_eq!(instances_of(&model, "observer"), ["a.attached"]);
    assert_eq!(model.signals["a.attached.seen"].width, 9);
    assert!(model.signals.contains_key("a.retained"));
    assert!(model.signals.contains_key("b.retained"));
    assert!(!model.signals.contains_key("b.attached.seen"));
    assert!(model.declared_parameters.contains("a.attached.N"));
}

#[test]
fn generate_regions_choices_and_loops_keep_their_active_instances() {
    let model = elaborate(
        "module leaf #(parameter int W=1); localparam int OWN=W; \
         logic [W-1:0] value; initial value=OWN; endmodule \
         module top; generate \
         if (1) begin:enabled localparam int ACTIVE=3; leaf #(.W(ACTIVE)) one(); end \
         else begin:disabled leaf #(.W(9)) never(); end \
         for (genvar i=0; i<2; i++) begin:rep leaf #(.W(i+4)) u(); end \
         case (1) 1: begin:choice leaf #(.W(6)) c(); end \
         default: begin:other leaf #(.W(9)) never(); end endcase \
         endgenerate endmodule",
    );
    let expected = [
        ("choice.c", 6),
        ("enabled.one", 3),
        ("rep[0].u", 4),
        ("rep[1].u", 5),
    ];
    assert_eq!(
        instances_of(&model, "leaf"),
        expected.map(|(path, _)| path.to_string())
    );
    for (path, width) in expected {
        assert_eq!(model.signals[&format!("{path}.value")].width, width);
        assert!(model.declared_parameters.contains(&format!("{path}.OWN")));
    }
    assert!(model.declared_parameters.contains("enabled.ACTIVE"));
    assert_eq!(model.initial_blocks.len(), 4);
}
