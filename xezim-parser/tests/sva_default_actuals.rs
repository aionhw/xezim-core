//! §16.8, §16.12 (aionhw/xezim#1309): the default actual argument of a formal of a named
//! sequence or property is kept with the declaration, parallel to the formal names. The
//! default of an untyped formal that is an operator expression is cast to its
//! self-determined type; a default that is not one expression is left out, as before.

use sv_parser::ast::Description;
use sv_parser::ast::decl::ModuleItem;
use sv_parser::ast::expr::{ExprKind, Expression};

fn ports_and_defaults(declaration: &str) -> (Vec<String>, Vec<Option<Expression>>) {
    let source = format!("module top; logic clk, a, b; logic [3:0] v; {declaration} endmodule");
    let result = sv_parser::parse(&source);
    assert!(
        result.errors.is_empty(),
        "{declaration}: {:?}",
        result.errors
    );
    let Description::Module(module) = &result.source.descriptions[0] else {
        panic!()
    };
    for item in &module.items {
        match item {
            ModuleItem::PropertyDeclaration(p) => {
                assert!(p.body.is_some(), "{declaration}: no body");
                let names = p.ports.iter().map(|i| i.name.clone()).collect();
                return (names, p.port_defaults.clone());
            }
            ModuleItem::SequenceDeclaration(s) => {
                assert!(s.body.is_some(), "{declaration}: no body");
                let names = s.ports.iter().map(|i| i.name.clone()).collect();
                return (names, s.port_defaults.clone());
            }
            _ => {}
        }
    }
    panic!("{declaration}: no declaration");
}

fn is_name(e: &Option<Expression>, name: &str) -> bool {
    matches!(e.as_ref().map(|e| &e.kind), Some(ExprKind::Ident(h))
        if h.path.len() == 1 && h.path[0].name.name == name)
}

fn is_self_determined(e: &Option<Expression>) -> bool {
    matches!(e.as_ref().map(|e| &e.kind), Some(ExprKind::SystemCall { name, args })
        if name == "$__xz_size_cast"
            && matches!(&args[0].kind, ExprKind::SystemCall { name, .. } if name == "$bits"))
}

#[test]
fn defaults_are_kept_parallel_to_the_formals() {
    let (names, defaults) =
        ports_and_defaults("property p(x = a, y, z = b); @(posedge clk) x |-> y && z; endproperty");
    assert_eq!(names, ["x", "y", "z"]);
    assert_eq!(defaults.len(), 3);
    assert!(is_name(&defaults[0], "a"));
    assert!(defaults[1].is_none());
    assert!(is_name(&defaults[2], "b"));

    let (names, defaults) =
        ports_and_defaults("sequence s(x = a, y = !b); @(posedge clk) x ##1 y; endsequence");
    assert_eq!(names, ["x", "y"]);
    assert!(is_name(&defaults[0], "a"));
    assert!(matches!(
        defaults[1].as_ref().map(|e| &e.kind),
        Some(ExprKind::Unary { .. })
    ));

    let (names, defaults) =
        ports_and_defaults("property p(x, y); @(posedge clk) x |-> y; endproperty");
    assert_eq!(names, ["x", "y"]);
    assert!(defaults.iter().all(Option::is_none));
}

#[test]
fn untyped_operator_default_is_cast_to_its_own_type() {
    for default in ["~v", "-v", "a ? ~v : v", "'1", "v + 1"] {
        let (_, defaults) = ports_and_defaults(&format!(
            "property p(x = {default}); @(posedge clk) x == 8'hff; endproperty"
        ));
        assert!(is_self_determined(&defaults[0]), "{default}: {defaults:?}");
        let (_, defaults) = ports_and_defaults(&format!(
            "property p(untyped x = {default}); @(posedge clk) x == 8'hff; endproperty"
        ));
        assert!(is_self_determined(&defaults[0]), "untyped {default}");
        // A typed formal gives the default its type.
        let (_, defaults) = ports_and_defaults(&format!(
            "property p(logic [7:0] x = {default}); @(posedge clk) x == 8'hff; endproperty"
        ));
        assert!(
            defaults[0].is_some() && !is_self_determined(&defaults[0]),
            "typed {default}"
        );
    }
    // Sized by themselves, or a sequence: left as written.
    for default in ["v", "a && b", "a ##1 b", "{a, b}", "v[1:0]"] {
        let (_, defaults) = ports_and_defaults(&format!(
            "property p(x = {default}); @(posedge clk) x; endproperty"
        ));
        assert!(
            defaults[0].is_some() && !is_self_determined(&defaults[0]),
            "{default}"
        );
    }
}

#[test]
fn default_that_is_not_one_expression_is_left_out() {
    let (names, defaults) =
        ports_and_defaults("property p(ev = posedge clk, x = a); @(ev) x; endproperty");
    assert_eq!(names, ["ev", "x"]);
    assert!(defaults[0].is_none());
    assert!(is_name(&defaults[1], "a"));
}
