//! IEEE 1800-2023 §8.17: constructor argument forwarding. `function
//! new(default);` takes the nearest base constructor's argument list and
//! opens with `super.new` of those arguments; `extends Base(default)` opens
//! an explicit subclass constructor the same way; `super.new(default)`
//! expands to the constructor's formals. A class with no base and
//! `new(default)` takes no arguments (core #74, #75).

use xezim_core::ast::decl::ClassMethodKind;
use xezim_core::ast::expr::ExprKind;
use xezim_core::ast::stmt::StatementKind;

const SRC: &str = r#"
class Base1 #(int VAL = 42);
  int got;
  function new(int a, int b = 7); got = a * 100 + b; endfunction
endclass
class Cls1 extends Base1(default);
endclass
class Cls2 extends Base1;
  function new(default); endfunction
endclass
class Cls3 extends Base1(default);
  function new(int a, int b = 9); endfunction
endclass
class Cls4 extends Base1;
  function new(int a, int b = 5); super.new(default); endfunction
endclass
class ClsDefFwd;
  function new(default);
  endfunction
endclass
module top;
  Cls1 c1; Cls2 c2; Cls3 c3; Cls4 c4; ClsDefFwd c5;
  initial begin
    c1 = new(1, 2); c2 = new(3); c3 = new(4); c4 = new(5, 6); c5 = new;
  end
endmodule
"#;

/// The names of a constructor's formals and the arguments of the
/// `super.new` call that opens its body, if any.
fn ctor_shape(elab: &xezim_core::elaborate::ElaboratedModule, class: &str) -> (Vec<String>, Option<Vec<String>>) {
    let cls = elab.classes.get(class).expect(class);
    let m = cls.methods.get("new").expect("constructor");
    let ClassMethodKind::Function(f) = &m.kind else {
        panic!("{class}: constructor is not a function");
    };
    let formals = f.ports.iter().map(|p| p.name.name.clone()).collect();
    let first = f.items.first().and_then(|s| match &s.kind {
        StatementKind::Expr(e) => match &e.kind {
            ExprKind::Call { func, args } => {
                // `super.new(...)` parses as a two-segment identifier or as
                // a member access on `super`.
                let is_super_new = match &func.kind {
                    ExprKind::Ident(h) => h.path.len() == 2 && h.path[0].name.name == "super",
                    ExprKind::MemberAccess { expr, member } => {
                        member.name == "new"
                            && matches!(&expr.kind, ExprKind::Ident(h) if h.path[0].name.name == "super")
                    }
                    _ => false,
                };
                is_super_new.then(|| {
                    args.iter()
                        .map(|a| match &a.kind {
                            ExprKind::Ident(h) => h.path[0].name.name.clone(),
                            other => format!("{other:?}"),
                        })
                        .collect::<Vec<_>>()
                })
            }
            _ => None,
        },
        _ => None,
    });
    (formals, first)
}

#[test]
fn constructor_default_arguments_forward_to_the_base() {
    xezim_core::sv_parser::set_sv2023(true);
    let (_defs, elab) = xezim_core::parse_and_elaborate_multi(
        &[SRC.to_string()],
        Some("top"),
        &[],
        &["fwd.sv".to_string()],
        &[],
    )
    .expect("elaborate");
    let s = |v: &[&str]| v.iter().map(|x| x.to_string()).collect::<Vec<_>>();
    // `new(default)` takes the base's `(a, b)` and forwards both.
    assert_eq!(ctor_shape(&elab, "Cls2"), (s(&["a", "b"]), Some(s(&["a", "b"]))));
    // `extends Base(default)` forwards the explicit constructor's formals.
    assert_eq!(ctor_shape(&elab, "Cls3"), (s(&["a", "b"]), Some(s(&["a", "b"]))));
    // `super.new(default)` expands to the formals.
    assert_eq!(ctor_shape(&elab, "Cls4"), (s(&["a", "b"]), Some(s(&["a", "b"]))));
    // No base: an empty argument list and no `super.new`.
    assert_eq!(ctor_shape(&elab, "ClsDefFwd"), (s(&[]), None));
    // No constructor of its own: the implicit one forwards at run time.
    assert!(elab.classes["Cls1"].methods.get("new").is_none());
}
