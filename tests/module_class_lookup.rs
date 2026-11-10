//! §23.9/§18.5: inherited constraint names use the nearest class scope,
//! including enclosing generate scopes and instantiated module bodies.

fn elaborate(src: &str) -> Result<xezim_core::ElaboratedModule, String> {
    xezim_core::parse_and_elaborate_multi(
        &[src.to_string()],
        Some("top"),
        &[],
        &["t.sv".to_string()],
        &[],
    )
    .map(|(_, m)| m)
}

#[test]
fn instance_constraints_see_local_base_and_scoped_class() {
    elaborate(
        r#"
module worker;
  class limits; const static int MAX=100; endclass
  class base; rand int lo, hi; endclass
  class derived extends base; constraint c { lo < hi; hi < limits::MAX; } endclass
endmodule
module top; worker a(), b(); endmodule
"#,
    )
    .expect("module-local inheritance");
}

#[test]
fn generate_constraints_see_the_enclosing_module_base() {
    for body in [
        "if (1) begin : g",
        "for (genvar i=0; i<2; i++) begin : g",
        "case (1) 1: begin : g",
    ] {
        let close = if body.starts_with("case") {
            "end endcase"
        } else {
            "end"
        };
        let src = format!(
            "module top; class base; rand int x; endclass {body} class derived extends base; constraint c {{x>0;}} endclass {close} endmodule"
        );
        elaborate(&src).expect("enclosing class is visible");
    }
}

#[test]
fn unrelated_and_undeclared_members_remain_errors() {
    for member in ["missing", "unrelated"] {
        let src = format!(
            "module worker; class base; rand int lo; endclass class other; rand int unrelated; endclass class derived extends base; constraint c {{lo < {member};}} endclass endmodule module top; worker u(); endmodule"
        );
        let err = match elaborate(&src) {
            Err(err) => err,
            Ok(_) => panic!("reject unknown member"),
        };
        assert!(
            err.contains(&format!("Undeclared identifier '{member}'")),
            "{err}"
        );
    }
}

#[test]
fn module_and_unit_classes_keep_separate_entries() {
    let m=elaborate("class base; int unit_value; endclass module top; class base; int local_value; endclass class derived extends base; endclass endmodule").unwrap();
    assert!(m.classes["base"].properties.contains_key("unit_value"));
    assert!(
        m.classes["top::base"]
            .properties
            .contains_key("local_value")
    );
    assert_eq!(m.classes["derived"].extends.as_deref(), Some("top::base"));
}

#[test]
fn module_type_parameter_binding_survives_instance_elaboration() {
    let m = elaborate("class base; int x=5; endclass module worker #(parameter type T=base); T value; endmodule module top; worker u(); endmodule").unwrap();
    assert_eq!(m.signals["u.value"].type_name.as_deref(), Some("u.T"));
    let xezim_core::ast::types::DataType::TypeReference { name, .. } = &m.typedef_types["u.T"]
    else {
        panic!("class type binding lost")
    };
    assert_eq!(name.name.name, "base");
}

#[test]
fn forward_class_typedef_does_not_replace_the_unit_class() {
    let m = elaborate("class base; int x=5; endclass module top; typedef class base; class base; int x=7; endclass endmodule").unwrap();
    assert!(!m.typedef_types.contains_key("base"));
    assert!(m.classes.contains_key("top::base"));
}

#[test]
fn generate_constructor_initializer_is_scheduled_before_initial_blocks() {
    let m = elaborate(
        "module top; class C; int x=1; endclass if(1) begin:g C value=new(); end endmodule",
    )
    .unwrap();
    assert!(
        m.static_init_blocks
            .iter()
            .any(|b| format!("{:?}", b.stmt).contains("g.value")),
        "constructor initializer was discarded"
    );
}
