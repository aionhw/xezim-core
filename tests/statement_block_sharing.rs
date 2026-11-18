//! IEEE 1800-2023 §9.2/§9.3: registering unchanged processes shares their
//! parsed block bodies; a later rewrite still isolates each process snapshot.

use std::sync::Arc;
use xezim_core::ast::decl::ModuleItem;
use xezim_core::ast::shared_vec::SharedVec;
use xezim_core::ast::stmt::{Statement, StatementKind};
use xezim_core::elaborate::{Definition, elaborate_module_with_defs};
use xezim_core::hasher::HashMap;

fn body(stmt: &Statement) -> &SharedVec<Statement> {
    match &stmt.kind {
        StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => stmts,
        StatementKind::TimingControl { stmt, .. } => body(stmt),
        _ => panic!("process block expected"),
    }
}

fn body_mut(stmt: &mut Statement) -> &mut SharedVec<Statement> {
    match &mut stmt.kind {
        StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => stmts,
        StatementKind::TimingControl { stmt, .. } => body_mut(stmt),
        _ => panic!("process block expected"),
    }
}

#[test]
fn process_registration_shares_parsed_initial_and_always_bodies() {
    for initial in [
        "initial begin a = 0; b = 1; end",
        "initial fork begin a = 0; end begin b = 1; end join",
    ] {
        let source = format!(
            "module top; bit trigger, a, b; {initial} always @(trigger) begin a = trigger; b = ~trigger; end endmodule"
        );
        let parsed = xezim_core::parse(&source);
        assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
        let xezim_core::ast::Description::Module(module) = &parsed.source.descriptions[0] else {
            panic!("module expected");
        };
        // Registration should retain unchanged syntax. A later inlining
        // pass deliberately rebuilds bodies for name/member conversions.
        let model = elaborate_module_with_defs(
            Definition::Module(module),
            &HashMap::default(),
            None,
            &[],
            &[],
            &[],
        )
        .expect("unchanged processes must elaborate");
        let initial = module
            .items
            .iter()
            .find_map(|item| match item {
                ModuleItem::InitialConstruct(initial) => Some(&initial.stmt),
                _ => None,
            })
            .expect("parsed initial");
        let always = module
            .items
            .iter()
            .find_map(|item| match item {
                ModuleItem::AlwaysConstruct(always) => Some(&always.stmt),
                _ => None,
            })
            .expect("parsed always");
        assert_eq!(model.initial_blocks.len(), 1);
        assert_eq!(model.always_blocks.len(), 1);
        assert!(Arc::ptr_eq(
            body(initial).as_arc(),
            body(&model.initial_blocks[0].stmt).as_arc()
        ));
        assert!(Arc::ptr_eq(
            body(always).as_arc(),
            body(&model.always_blocks[0].stmt).as_arc()
        ));

        // A private compiler rewrite cannot mutate the retained source AST
        // or another elaborated process using its unchanged syntax.
        let mut rewritten = model.always_blocks[0].stmt.clone();
        body_mut(&mut rewritten)[0].kind = StatementKind::Null;
        assert!(!Arc::ptr_eq(
            body(always).as_arc(),
            body(&rewritten).as_arc()
        ));
        assert!(!matches!(body(always)[0].kind, StatementKind::Null));
        assert!(!matches!(
            body(&model.always_blocks[0].stmt)[0].kind,
            StatementKind::Null
        ));
    }
}
