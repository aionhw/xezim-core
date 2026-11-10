//! #721: ownership changes preserve IEEE 1800-2023 §13.3/§13.4 signatures
//! and §8.3 class scopes while sharing only immutable callable syntax.
use super::*;
use std::sync::Arc;

fn elaborate(source: &str) -> ElaboratedModule {
    crate::parse_and_elaborate_multi(
        &[source.into()],
        Some("top"),
        &[],
        &["callable-sharing.sv".into()],
        &[],
    )
    .expect("elaborate callable sharing case")
    .1
}

#[test]
fn repeated_instances_share_bodies_with_separate_signatures() {
    let elab = elaborate(
        r#"
        module leaf #(parameter W=8);
          function automatic logic [W-1:0] f(input logic [W-1:0] x);
            return x + 1;
          endfunction
          task automatic t(input int x); int y; y=x+1; endtask
          class C;
            function int m(input int x); return x+1; endfunction
          endclass
        endmodule
        module top; leaf #(8) a(); leaf #(16) b(); leaf #(8) c(); endmodule
    "#,
    );
    for right in ["b", "c"] {
        let a = &elab.functions["a.f"];
        let b = &elab.functions[&format!("{right}.f")];
        assert_ne!(a.name.name.name, b.name.name.name);
        assert!(Arc::ptr_eq(a.items.as_arc(), b.items.as_arc()));
        let a = &elab.tasks["a.t"];
        let b = &elab.tasks[&format!("{right}.t")];
        assert!(Arc::ptr_eq(a.items.as_arc(), b.items.as_arc()));
        let method = |name: &str| match &elab.classes[name].methods["m"].kind {
            ClassMethodKind::Function(f) => f.items.as_arc(),
            _ => panic!("function method expected"),
        };
        assert!(Arc::ptr_eq(method("a.C"), method(&format!("{right}.C"))));
    }
    let a = &elab.functions["a.f"];
    let b = &elab.functions["b.f"];
    assert_eq!(
        resolve_type_width(&a.return_type, Some(&elab.parameters), Some(&elab.typedefs)),
        8
    );
    assert_eq!(
        resolve_type_width(&b.return_type, Some(&elab.parameters), Some(&elab.typedefs)),
        16
    );
    // Context caches on a shared expression stay empty after simulated writes.
    let StatementKind::Return(Some(expr)) = &a.items[0].kind else {
        panic!("return expected")
    };
    expr.cached_width.set(Some(8));
    assert!(expr.cached_width.get().is_none());
    let ExprKind::Binary { left, .. } = &expr.kind else {
        panic!("binary expected")
    };
    let ExprKind::Ident(name) = &left.kind else {
        panic!("formal expected")
    };
    assert!(name.cached_resolved_name.set("a.x".into()).is_err());
    name.cached_signal_id.set(Some(7));
    assert_eq!(name.cached_signal_id.get(), None);
}

#[test]
fn constant_shell_shares_table_until_mutated() {
    let source = Rc::new(HashMap::from_iter([("left".into(), 7u32)]));
    let mut shell = LoggedMap::from_shared(Rc::clone(&source));
    assert!(Rc::ptr_eq(&source, &shell.map));
    assert_eq!(shell.remove("absent"), None);
    assert!(Rc::ptr_eq(&source, &shell.map));
    shell.insert("left".into(), 9);
    assert_eq!(source["left"], 7);
    assert_eq!(shell["left"], 9);
    assert!(!Rc::ptr_eq(&source, &shell.map));
}

#[test]
fn class_localparams_size_packed_and_unpacked_declarations() {
    let elab = elaborate(
        r#"
        module top;
          parameter int N=3;
          class C;
            localparam int M=N+2;
            bit [M-1:0] value;
            bit [7:0] bytes[M];
          endclass
        endmodule
    "#,
    );
    let class = &elab.classes["C"];
    assert_eq!(class.properties["value"].width, 5);
    assert_eq!(class.array_properties["bytes"], (0, 4, 8));
}

#[test]
fn shared_callable_body_roundtrip_keeps_context_caches_disabled() {
    let elab = elaborate(
        "module leaf; function int f(input int x); return x+1; endfunction endmodule module top; leaf a(); endmodule",
    );
    let original = &elab.functions["a.f"];
    let cfg = crate::xez_bincode_config();
    let bytes = bincode::serde::encode_to_vec(original, cfg).unwrap();
    let (restored, used): (FunctionDeclaration, usize) =
        bincode::serde::decode_from_slice(&bytes, cfg).unwrap();
    assert_eq!(used, bytes.len());
    assert_eq!(
        bincode::serde::encode_to_vec(&restored, cfg).unwrap(),
        bytes
    );
    let StatementKind::Return(Some(expr)) = &restored.items[0].kind else {
        panic!("return expected")
    };
    expr.cached_width.set(Some(99));
    assert!(expr.cached_width.get().is_none());
}

/// §6.20/§8.13: qualified and escaped reads remain visible; a call or
/// typedef can read an unseen outer name and must retain the full scope.
#[test]
fn class_scope_selection_preserves_direct_names_and_indirect_fallbacks() {
    let scope = HashMap::from_iter([
        ("pkg::N".into(), Value::from_u64(3, 32)),
        ("escaped.name".into(), Value::from_u64(4, 32)),
        ("hidden".into(), Value::from_u64(9, 32)),
    ]);
    for (source, narrowed) in [
        (
            r"class C; localparam M=pkg::N+\escaped.name ; bit[M-1:0] x; endclass",
            true,
        ),
        ("class C; localparam M=f(); bit[M-1:0] x; endclass", false),
        (
            "class C; localparam M=$bits(hidden_t); bit[M-1:0] x; endclass",
            false,
        ),
        ("class C; localparam M=1; hidden_t x; endclass", false),
        (
            "class C extends Base; localparam M=1; bit[M-1:0] x; endclass",
            false,
        ),
    ] {
        let parsed = crate::parse(source);
        assert!(parsed.errors.is_empty(), "{:?}: {source}", parsed.errors);
        let crate::ast::Description::Class(class) = &parsed.source.descriptions[0] else {
            panic!("class expected");
        };
        let selected = class_enclosing_scope(class, Some(&scope));
        assert_eq!(selected.len(), if narrowed { 2 } else { 3 }, "{source}");
        if narrowed {
            assert!(selected.contains_key("pkg::N"));
            assert!(selected.contains_key("escaped.name"));
            let consts = class_const_scope(class, Some(&scope));
            assert_eq!(consts["M"].to_u64(), Some(7));
        }
    }
}
