//! IEEE 1800-2023 §8.3/§8.6/§23.9: class methods see their lexical
//! declarations without acquiring the members of unrelated classes.

fn elaborate(source: &str) -> Result<(), String> {
    xezim_core::parse_and_elaborate_multi(
        &[source.to_string()],
        Some("top"),
        &[],
        &["subroutine-namespace.sv".to_string()],
        &[],
    )
    .map(|_| ())
}

#[test]
fn methods_keep_own_inherited_and_enclosing_names() {
    elaborate(
        "module top; int global_value; \
         class Base; protected int inherited; endclass \
         class Derived extends Base; int own; \
         function int f(); return own + inherited + global_value; endfunction endclass \
         function int module_f(); return global_value; endfunction \
         initial begin Derived d; d=new; global_value=d.f()+module_f(); end endmodule",
    )
    .expect("visible declarations remain available");
}

#[test]
fn unrelated_class_property_does_not_become_a_method_global() {
    let error = elaborate(
        "class Other; int unrelated; endclass \
         class Reader; function int f(); return unrelated; endfunction endclass \
         module top; Reader r; initial begin r=new; $display(r.f()); end endmodule",
    )
    .expect_err("an unrelated class cannot declare the method's bare name");
    assert!(
        error.contains("Undeclared identifier 'unrelated'"),
        "{error}"
    );
}
