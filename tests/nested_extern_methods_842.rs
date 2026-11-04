//! IEEE 1800-2023 §8.23/§8.24 (#842): a scoped method in a class body
//! belongs to that nested class, retaining the prototype and alias identity.

use xezim_core::{
    ElaboratedModule,
    ast::{
        decl::{ClassMethodKind, ClassQualifier},
        expr::{ExprKind, NumberLiteral},
        stmt::StatementKind,
    },
};

fn elaborate(source: &str) -> ElaboratedModule {
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

fn returned_number(elab: &ElaboratedModule, class: &str, method: &str) -> String {
    let ClassMethodKind::Function(f) = &elab.classes[class].methods[method].kind else {
        panic!("{class}::{method} is not a function");
    };
    let StatementKind::Return(Some(e)) = &f.items[0].kind else {
        panic!("{class}::{method} has no return body");
    };
    let ExprKind::Number(NumberLiteral::Integer { value, .. }) = &e.kind else {
        panic!("{class}::{method} does not return a number");
    };
    value.clone()
}

#[test]
fn class_body_links_nested_methods_without_replacing_outer_methods() {
    for outer_first in [true, false] {
        let own = "function int m(); return 207; endfunction";
        let nested = "function int inner::m(); return 100; endfunction";
        let methods = if outer_first {
            format!("{own}\n{nested}")
        } else {
            format!("{nested}\n{own}")
        };
        let elab = elaborate(&format!(
            "class outer;\n\
               class inner; int v; extern function int m();\n\
                 extern virtual function int who();\n\
                 extern static function int twice(int x);\n\
                 extern task set(int x); endclass\n\
               {methods}\n\
               function int inner::who(); return 2; endfunction\n\
               function int inner::twice(int x); return x*2; endfunction\n\
               task inner::set(int x); v=x; endtask\n\
             endclass\nmodule top; endmodule"
        ));
        assert_eq!(returned_number(&elab, "outer", "m"), "207");
        assert_eq!(returned_number(&elab, "outer::inner", "m"), "100");
        let inner = &elab.classes["outer::inner"];
        assert!(
            inner.methods["who"]
                .qualifiers
                .contains(&ClassQualifier::Virtual)
        );
        assert!(
            inner.methods["twice"]
                .qualifiers
                .contains(&ClassQualifier::Static)
        );
        assert!(inner.static_methods.contains("twice"));
        assert!(
            matches!(&inner.methods["set"].kind, ClassMethodKind::Task(t) if !t.items.is_empty())
        );
        assert!(!elab.classes["outer"].methods.contains_key("set"));
        assert!(!elab.classes["outer"].methods.contains_key("twice"));
    }
}

#[test]
fn package_homonyms_keep_their_own_nested_bodies() {
    let elab = elaborate(
        r#"
package p;
  class outer;
    class inner; extern function int m(); endclass
    function int inner::m(); return 11; endfunction
  endclass
endpackage
package q;
  class outer;
    class inner; extern function int m(); endclass
    function int inner::m(); return 22; endfunction
  endclass
endpackage
module top; endmodule
"#,
    );
    assert_eq!(returned_number(&elab, "p::outer::inner", "m"), "11");
    assert_eq!(returned_number(&elab, "q::outer::inner", "m"), "22");
    assert!(!elab.classes["p::outer"].methods.contains_key("m"));
    assert!(!elab.classes["q::outer"].methods.contains_key("m"));
}

#[test]
fn module_classes_and_deeper_class_bodies_are_walked() {
    let elab = elaborate(
        r#"
module top;
  class outer;
    class middle;
      class inner; extern function int m(); endclass
      function int inner::m(); return 17; endfunction
    endclass
  endclass
endmodule
"#,
    );
    assert_eq!(returned_number(&elab, "outer::middle::inner", "m"), "17");
    assert!(!elab.classes["outer::middle"].methods.contains_key("m"));
}

#[test]
fn fully_scoped_nested_body_validates_against_its_own_members() {
    let elab = elaborate(
        r#"
class inner; int unrelated_member; endclass
class outer;
  class inner;
    int nested_value;
    extern function void set(int x);
  endclass
endclass
function void outer::inner::set(int x);
  nested_value=x;
endfunction
module top; endmodule
"#,
    );
    assert!(matches!(
        &elab.classes["outer::inner"].methods["set"].kind,
        ClassMethodKind::Function(f) if !f.items.is_empty()
    ));
    assert!(!elab.classes["inner"].methods.contains_key("set"));
}

#[test]
fn parameterized_outer_keeps_linked_body_under_each_nested_alias() {
    let elab = elaborate(
        r#"
package pk;
  class outer_a; class inner; int other; endclass endclass
  class outer_d #(type T=int);
    class inner; T v; extern function T get(); endclass
    function T inner::get(); return v; endfunction
  endclass
endpackage
module top;
  pk::outer_d#(int)::inner d;
  initial d=new();
endmodule
"#,
    );
    let mut count = 0;
    assert!(elab.classes.contains_key("pk::outer_d::inner"));
    for (key, class) in &elab.classes {
        if key.contains("outer_d") && key.contains("inner") {
            count += 1;
            assert!(
                matches!(
                    class.methods.get("get").map(|m| &m.kind),
                    Some(ClassMethodKind::Function(f)) if !f.items.is_empty()
                ),
                "unlinked get under {key}, declared {}",
                class.name
            );
        }
    }
    assert!(count > 0);
}
