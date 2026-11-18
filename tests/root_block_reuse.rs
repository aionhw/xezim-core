//! IEEE 1800-2023 §9.3/§23.10: an unchanged root process retains its
//! shared syntax; a required hierarchical-name conversion still runs.

use std::sync::Arc;
use xezim_core::SourceDefinition;
use xezim_core::ast::decl::ModuleItem;
use xezim_core::ast::expr::ExprKind;
use xezim_core::ast::shared_vec::SharedVec;
use xezim_core::ast::stmt::{Statement, StatementKind};
use xezim_core::elaborate::{Definition, elaborate_module_with_defs, inline_instantiations};
use xezim_core::hasher::HashMap;

fn body(stmt: &Statement) -> &SharedVec<Statement> {
    match &stmt.kind {
        StatementKind::SeqBlock { stmts, .. } | StatementKind::ParBlock { stmts, .. } => stmts,
        StatementKind::TimingControl { stmt, .. } => body(stmt),
        _ => panic!("process block expected"),
    }
}

#[test]
fn full_elaboration_retains_unchanged_root_bodies() {
    for processes in [
        "initial begin a=0; b=1; end always @(trigger) begin a=trigger; b=~trigger; end",
        "initial fork begin a=0; end begin b=1; end join always @(posedge trigger iff b) begin if (b) a=trigger; else a=~trigger; end",
        "initial begin case (trigger) 0: a=b; default: b=a; endcase while (a) begin b=a; end repeat (2) begin a=b; end $display(\"%0d\", a); end always @(trigger) begin case (a) 0: b=trigger; default: b=a; endcase end",
        "initial begin a=b[0]; b[0]=a; end always @(trigger) begin a=b[0:0]; b[trigger +: 1]=a; end",
        "initial begin for(a=0;a<1;a=a+1) begin b[a]=trigger; end end always @(trigger) begin for(a=0;a<1;a=a+1) b=trigger; end",
    ] {
        let source = format!("module top; bit trigger, a, b; {processes} endmodule");
        let (definitions, model) = xezim_core::parse_and_elaborate_multi(
            &[source],
            Some("top"),
            &[],
            &["root-sharing.sv".into()],
            &[],
        )
        .expect("root processes elaborate");
        let SourceDefinition::Module(module) = &definitions["top"] else {
            panic!("module expected");
        };
        let initial = module
            .items
            .iter()
            .find_map(|item| match item {
                ModuleItem::InitialConstruct(p) => Some(&p.stmt),
                _ => None,
            })
            .unwrap();
        let always = module
            .items
            .iter()
            .find_map(|item| match item {
                ModuleItem::AlwaysConstruct(p) => Some(&p.stmt),
                _ => None,
            })
            .unwrap();
        assert!(Arc::ptr_eq(
            body(initial).as_arc(),
            body(&model.initial_blocks[0].stmt).as_arc()
        ));
        assert!(Arc::ptr_eq(
            body(always).as_arc(),
            body(&model.always_blocks[0].stmt).as_arc()
        ));
    }
}

#[test]
fn root_member_access_still_converts_to_a_hierarchical_name() {
    let source = "module child; logic q; endmodule module top; logic a; child u(); initial begin a=u.q; end endmodule";
    let (definitions, model) = xezim_core::parse_and_elaborate_multi(
        &[source.into()],
        Some("top"),
        &[],
        &["root-member.sv".into()],
        &[],
    )
    .expect("hierarchical reference elaborates");
    let SourceDefinition::Module(module) = &definitions["top"] else {
        panic!("module expected");
    };
    let initial = module
        .items
        .iter()
        .find_map(|item| match item {
            ModuleItem::InitialConstruct(p) => Some(&p.stmt),
            _ => None,
        })
        .unwrap();
    let rewritten = &model.initial_blocks[0].stmt;
    assert!(!Arc::ptr_eq(
        body(initial).as_arc(),
        body(rewritten).as_arc()
    ));
    let StatementKind::BlockingAssign { rvalue, .. } = &body(rewritten)[0].kind else {
        panic!("assignment expected");
    };
    let ExprKind::Ident(target) = &rvalue.kind else {
        panic!("hierarchical identifier expected: {:?}", rvalue.kind);
    };
    assert_eq!(
        target
            .path
            .iter()
            .map(|part| part.name.name.as_str())
            .collect::<Vec<_>>()
            .join("."),
        "u.q"
    );
}

/// §11.5.1: equal nested part-selects still need the ordinary collapse.
#[test]
fn root_same_range_select_still_collapses() {
    let source = "module top; bit [3:0] a, b; initial begin a=b[3:0][3:0]; end endmodule";
    let (_, model) = xezim_core::parse_and_elaborate_multi(
        &[source.into()],
        Some("top"),
        &[],
        &["root-select.sv".into()],
        &[],
    )
    .expect("nested ranges elaborate");
    let StatementKind::BlockingAssign { rvalue, .. } =
        &body(&model.initial_blocks[0].stmt)[0].kind
    else {
        panic!("assignment expected");
    };
    let ExprKind::RangeSelect { expr: base, .. } = &rvalue.kind else {
        panic!("part-select expected");
    };
    let ExprKind::Ident(name) = &base.kind else {
        panic!("the repeated part-select must collapse");
    };
    assert_eq!(name.path[0].name.name, "b");
}

/// §9.3/§23.6: rewriting an outer reference does not detach an unchanged
/// nested sequential or parallel block's statement list.
#[test]
fn mixed_root_rewrite_shares_only_unchanged_nested_blocks() {
    let source = "module child; bit q; endmodule module top; bit a,b; child u(); \
                  initial begin begin:safe a=b; b=a; end \
                  fork begin a=b; end join a=u.q; end endmodule";
    let (definitions, model) = xezim_core::parse_and_elaborate_multi(
        &[source.into()],
        Some("top"),
        &[],
        &["mixed-root.sv".into()],
        &[],
    )
    .expect("mixed root body elaborates");
    let SourceDefinition::Module(module) = &definitions["top"] else {
        panic!("module expected");
    };
    let source = module
        .items
        .iter()
        .find_map(|item| match item {
            ModuleItem::InitialConstruct(p) => Some(&p.stmt),
            _ => None,
        })
        .unwrap();
    let rewritten = &model.initial_blocks[0].stmt;
    assert!(!Arc::ptr_eq(body(source).as_arc(), body(rewritten).as_arc()));
    for index in [0, 1] {
        assert!(Arc::ptr_eq(
            body(&body(source)[index]).as_arc(),
            body(&body(rewritten)[index]).as_arc()
        ));
    }
    let StatementKind::BlockingAssign { rvalue, .. } = &body(rewritten)[2].kind else {
        panic!("assignment expected");
    };
    let ExprKind::Ident(name) = &rvalue.kind else {
        panic!("member reference must become hierarchical");
    };
    assert_eq!(
        name.path
            .iter()
            .map(|part| part.name.name.as_str())
            .collect::<Vec<_>>()
            .join("."),
        "u.q"
    );
}

/// §23.6: partial block reuse must still allocate private nested caches
/// when the caller explicitly refreshes or disables contextual memoization.
#[test]
fn mixed_root_rewrite_honors_private_nested_cache_modes() {
    use xezim_core::ast::cache::{with_fresh_scope_caches, without_scope_caches};
    for fresh in [true, false] {
        let parsed = xezim_core::parse(
            "module top; bit [3:0] a,b; initial begin \
             begin:safe a=b[0]; end a=b[3:0][3:0]; end endmodule",
        );
        assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
        let xezim_core::ast::Description::Module(module) = &parsed.source.descriptions[0] else {
            panic!("module expected");
        };
        let definitions = HashMap::from_iter([("top".to_string(), Definition::Module(module))]);
        let mut model = elaborate_module_with_defs(
            Definition::Module(module),
            &HashMap::default(),
            Some(&definitions),
            &[],
            &[],
            &[],
        )
        .unwrap();
        let rewrite = || inline_instantiations(&mut model, &definitions);
        if fresh {
            with_fresh_scope_caches(rewrite).unwrap();
        } else {
            without_scope_caches(rewrite).unwrap();
        }
        let original = module
            .items
            .iter()
            .find_map(|item| match item {
                ModuleItem::InitialConstruct(p) => Some(&p.stmt),
                _ => None,
            })
            .unwrap();
        let source = body(&body(original)[0]);
        let rewritten = body(&body(&model.initial_blocks[0].stmt)[0]);
        assert!(!Arc::ptr_eq(source.as_arc(), rewritten.as_arc()));
        let StatementKind::BlockingAssign { lvalue, .. } = &rewritten[0].kind else {
            panic!("rewritten assignment expected");
        };
        let StatementKind::BlockingAssign {
            lvalue: source_name,
            ..
        } = &source[0].kind
        else {
            panic!("source assignment expected");
        };
        lvalue.cached_width.set(Some(8));
        assert_eq!(lvalue.cached_width.get(), fresh.then_some(8));
        source_name.cached_width.set(Some(16));
        assert_eq!(source_name.cached_width.get(), Some(16));
        assert_eq!(lvalue.cached_width.get(), fresh.then_some(8));
    }
}

/// §23.6: the integrated identity path honors explicit cache ownership,
/// including refreshing a body whose source caches were disabled.
#[test]
fn root_reuse_honors_explicit_cache_clone_modes() {
    use xezim_core::ast::cache::{with_fresh_scope_caches, without_scope_caches};
    for source_disabled in [false, true] {
        let source = "module top; logic trigger, a, b; always @(trigger) begin a=b; end endmodule";
        let parsed = if source_disabled {
            without_scope_caches(|| xezim_core::parse(source))
        } else {
            xezim_core::parse(source)
        };
        assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
        let xezim_core::ast::Description::Module(module) = &parsed.source.descriptions[0] else {
            panic!("module expected");
        };
        let definitions = HashMap::from_iter([("top".to_string(), Definition::Module(module))]);
        let mut model = elaborate_module_with_defs(
            Definition::Module(module),
            &HashMap::default(),
            Some(&definitions),
            &[],
            &[],
            &[],
        )
        .unwrap();
        let rewrite = || inline_instantiations(&mut model, &definitions);
        if source_disabled {
            with_fresh_scope_caches(rewrite).unwrap();
        } else {
            without_scope_caches(rewrite).unwrap();
        }
        let StatementKind::BlockingAssign { lvalue, .. } =
            &body(&model.always_blocks[0].stmt)[0].kind
        else {
            panic!("assignment expected");
        };
        lvalue.cached_width.set(Some(8));
        assert_eq!(lvalue.cached_width.get(), source_disabled.then_some(8));
        let ModuleItem::AlwaysConstruct(original) = &module.items[1] else {
            panic!("source always expected");
        };
        let StatementKind::BlockingAssign {
            lvalue: source_name,
            ..
        } = &body(&original.stmt)[0].kind
        else {
            panic!("source assignment expected");
        };
        assert!(!Arc::ptr_eq(
            body(&original.stmt).as_arc(),
            body(&model.always_blocks[0].stmt).as_arc()
        ));
        source_name.cached_width.set(Some(16));
        assert_eq!(
            source_name.cached_width.get(),
            (!source_disabled).then_some(16)
        );
    }
}
