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

#[test]
fn module_state_instances_share_deferred_bodies_and_materialize_per_instance() {
    let mut elab = elaborate(
        "module element #(parameter int K = 0);
           int state;
           function automatic int read_add(input int v);
             return v + state;
           endfunction
           task automatic bump(input int d);
             state = state + d;
           endtask
         endmodule
         module top;
           element #(0) a();
           element #(0) b();
         endmodule",
    );
    assert!(Arc::ptr_eq(
        elab.functions["a.read_add"].items.as_arc(),
        elab.functions["b.read_add"].items.as_arc()
    ));
    assert!(Arc::ptr_eq(
        elab.tasks["a.bump"].items.as_arc(),
        elab.tasks["b.bump"].items.as_arc()
    ));
    assert!(elab.deferred_function_bodies.contains_key("a.read_add"));
    assert!(elab.deferred_function_bodies.contains_key("b.read_add"));
    assert!(elab.deferred_task_bodies.contains_key("a.bump"));
    assert!(elab.deferred_task_bodies.contains_key("b.bump"));

    // Context caches stay disabled on the shared deferred source.
    let StatementKind::Return(Some(shared_expr)) = &elab.functions["a.read_add"].items[0].kind
    else {
        panic!("return expected")
    };
    shared_expr.cached_width.set(Some(11));
    assert_eq!(shared_expr.cached_width.get(), None);

    // On-demand materialization rewrites each instance into its own signal names.
    let mat_a = elab
        .materialize_function_body("a.read_add", &elab.functions["a.read_add"])
        .expect("deferred a.read_add");
    let mat_b = elab
        .materialize_function_body("b.read_add", &elab.functions["b.read_add"])
        .expect("deferred b.read_add");
    assert!(!Arc::ptr_eq(mat_a.as_arc(), mat_b.as_arc()));
    let return_rhs_name = |stmts: &[Statement]| -> String {
        let StatementKind::Return(Some(expr)) = &stmts[0].kind else {
            panic!("return expected")
        };
        let ExprKind::Binary { right, .. } = &expr.kind else {
            panic!("binary expected")
        };
        let ExprKind::Ident(h) = &right.kind else {
            panic!("ident expected")
        };
        h.path
            .iter()
            .map(|s| s.name.name.as_str())
            .collect::<Vec<_>>()
            .join(".")
    };
    assert_eq!(return_rhs_name(&mat_a), "a.state");
    assert_eq!(return_rhs_name(&mat_b), "b.state");

    let task_a = elab
        .materialize_task_body("a.bump", &elab.tasks["a.bump"])
        .expect("deferred a.bump");
    let StatementKind::BlockingAssign { lvalue, .. } = &task_a[0].kind else {
        panic!("assign expected")
    };
    let ExprKind::Ident(lh) = &lvalue.kind else {
        panic!("ident expected")
    };
    assert_eq!(lh.path[0].name.name, "a.state");

    // `materialize_pending` drains deferred callables and keeps bincode roundtrip intact.
    elab.materialize_pending();
    assert!(elab.deferred_function_bodies.is_empty());
    assert!(elab.deferred_task_bodies.is_empty());
    assert_eq!(return_rhs_name(&elab.functions["a.read_add"].items), "a.state");
    assert_eq!(return_rhs_name(&elab.functions["b.read_add"].items), "b.state");

    let cfg = crate::xez_bincode_config();
    let bytes = bincode::serde::encode_to_vec(&elab, cfg).unwrap();
    let (restored, used): (ElaboratedModule, usize) =
        bincode::serde::decode_from_slice(&bytes, cfg).unwrap();
    assert_eq!(used, bytes.len());
    assert_eq!(return_rhs_name(&restored.functions["b.read_add"].items), "b.state");
}

#[test]
fn deferred_callable_preserves_shadowing_ports_typedefs_type_params_and_const_fn() {
    let elab = elaborate(
        "module leaf #(parameter type T = logic [15:0]) (input int pin);
           typedef logic [7:0] u8_t;
           typedef u8_t u8a_t [0:3];
           int state;
           function automatic int f(input int state);
             int acc;
             u8a_t arr;
             acc = state + pin + $bits(T) + $bits(arr[0]);
             return acc;
           endfunction
           function automatic int cf(input int x);
             return x * 3 + 1;
           endfunction
           function automatic int cf_bits(input int x);
             return x + $bits(T);
           endfunction
           localparam int Q = cf(4);
         endmodule
         module top;
           int bus;
           leaf #(.T(logic [11:0])) u(.pin(bus));
         endmodule",
    );
    assert_eq!(elab.parameters.get("u.Q").and_then(|v| v.to_i64()), Some(13));
    assert!(elab.deferred_function_bodies.contains_key("u.cf_bits"));
    let call = Expression::new(
        ExprKind::Call {
            func: Box::new(make_ident_expr("u.cf_bits")),
            args: vec![genvar_const_expr(4)],
        },
        Span::dummy(),
    );
    let folded = substitute_const_fn_calls(&call, Some(&elab.parameters), &elab, 0)
        .expect("deferred constant function call must fold");
    assert_eq!(eval_const_expr(&folded, &elab.parameters), 16);
    let items = elab
        .materialize_function_body("u.f", &elab.functions["u.f"])
        .expect("deferred u.f");
    let StatementKind::VarDecl { data_type, .. } = &items[1].kind else {
        panic!("arr decl expected")
    };
    let DataType::TypeReference { name, .. } = data_type else {
        panic!("scoped typedef ref expected: {data_type:?}")
    };
    assert_eq!(name.name.name, "u.u8a_t");
    // Statement 2: acc = state + bus + 12 + ...
    let StatementKind::BlockingAssign { rvalue, .. } = &items[2].kind else {
        panic!("assign expected")
    };
    fn collect_idents(e: &Expression, out: &mut Vec<String>) {
        match &e.kind {
            ExprKind::Ident(h) => out.push(
                h.path
                    .iter()
                    .map(|s| s.name.name.as_str())
                    .collect::<Vec<_>>()
                    .join("."),
            ),
            ExprKind::Binary { left, right, .. } => {
                collect_idents(left, out);
                collect_idents(right, out);
            }
            ExprKind::Paren(inner) => collect_idents(inner, out),
            _ => {}
        }
    }
    let mut names = Vec::new();
    collect_idents(rvalue, &mut names);
    assert!(names.contains(&"state".to_string()), "formal shadowed: {names:?}");
    assert!(!names.contains(&"u.state".to_string()), "must stay shadowed: {names:?}");
    assert!(names.contains(&"bus".to_string()), "port substituted: {names:?}");
}

/// §16.6, §16.8: a formal stays local to the call; an instance signal
/// qualifies the same declaration differently in each instance.
#[test]
fn named_sva_shares_only_identical_rewritten_bodies() {
    let elab = elaborate(
        r#"
        module leaf(input logic x);
          logic value;
          property p(x); x; endproperty
          sequence s; value; endsequence
        endmodule
        module top; logic a, b; leaf left(a); leaf right(b); endmodule
    "#,
    );
    let body = &elab.property_decls["left.p"];
    assert!(Rc::ptr_eq(body, &elab.property_decls["right.p"]));
    assert!(!Rc::ptr_eq(
        &elab.property_decls["left.s"],
        &elab.property_decls["right.s"]
    ));
    body.cached_width.set(Some(17));
    assert_eq!(body.cached_width.get(), None);
}
