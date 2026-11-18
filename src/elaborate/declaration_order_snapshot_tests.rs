//! IEEE 1800-2023 §6.5, §6.21: declaration-order snapshots share storage
//! while procedural shadows and generated declarations retain lexical scope.

use super::*;

fn early(source: &str) -> Vec<String> {
    let parsed = crate::parse(source);
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
    let crate::ast::Description::Module(module) = &parsed.source.descriptions[0] else {
        panic!("module expected");
    };
    check_module_use_before_decl(&Definition::Module(module), None, &[], false)
}

#[test]
fn sequential_procedural_snapshots_share_the_module_set() {
    let mut declared = DeclaredModuleNames::default();
    for i in 0..1024 {
        declared.insert(format!("module_{i}"));
    }
    let allocation = Rc::as_ptr(&declared.0);
    for _ in 0..128 {
        let frame = declared.clone();
        assert!(Rc::ptr_eq(&declared.0, &frame.0));
        assert!(frame.contains("module_1023"));
    }
    // After a procedural check returns, the next module declaration must
    // update the unique allocation rather than clone the large snapshot.
    declared.insert("later".into());
    assert_eq!(Rc::as_ptr(&declared.0), allocation);
}

#[test]
fn inserting_a_declaration_keeps_an_earlier_snapshot_unchanged() {
    let mut outer = DeclaredModuleNames::default();
    outer.insert("earlier".into());
    let mut generated = outer.clone();
    generated.insert("inside".into());
    assert!(!Rc::ptr_eq(&outer.0, &generated.0));
    assert!(generated.contains("earlier") && generated.contains("inside"));
    assert!(outer.contains("earlier") && !outer.contains("inside"));
    outer.insert("later".into());
    assert!(!generated.contains("later"));
}

#[test]
fn function_formals_and_locals_shadow_later_module_data() {
    assert!(
        early(
            r#"
        module top;
          int earlier;
          function automatic int f(input int later);
            int shadow;
            shadow = later;
            return shadow + earlier;
          endfunction
          int later;
          int shadow;
        endmodule
    "#
        )
        .is_empty()
    );
}

#[test]
fn each_function_observes_its_declaration_order_snapshot() {
    assert_eq!(
        early(
            r#"
        module top;
          function automatic int before_decl(); return later; endfunction
          int later;
          function automatic int after_decl(); return later; endfunction
        endmodule
    "#
        ),
        ["later"]
    );
    assert!(
        early(
            r#"
        module top;
          int earlier;
          function automatic int f(input bit enabled);
            return enabled && earlier;
          endfunction
        endmodule
    "#
        )
        .is_empty()
    );
}

#[test]
fn a_nested_block_shadow_does_not_escape_its_scope() {
    assert_eq!(
        early(
            r#"
        module top;
          function automatic int f();
            begin : inner
              int later;
              later = 1;
            end
            return later;
          endfunction
          int later;
        endmodule
    "#
        ),
        ["later"]
    );
}

#[test]
fn a_generated_declaration_does_not_leak_into_the_module_snapshot() {
    assert_eq!(
        early(
            r#"
        module top;
          int earlier;
          if (1) begin : generated
            int later;
            initial later = earlier;
          end
          initial later = 1;
          int later;
        endmodule
    "#
        ),
        ["later"]
    );
}
