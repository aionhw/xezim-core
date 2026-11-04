//! IEEE 1800-2017 A.4.1.1: every comma in a parameter value list separates
//! two assignments; a trailing comma does not supply an empty/default slot.
//! Class specializations use this same grammar (§8.25, A.2.2.1). Function
//! and constructor arguments have their separate optional-argument grammar.

use sv_parser::parse;

const TRAILING: &str = "a parameter value list cannot end with a comma";

#[track_caller]
fn rejected(source: &str) {
    let result = parse(source);
    let diagnostic = result
        .errors
        .iter()
        .find(|d| d.message.contains(TRAILING))
        .unwrap_or_else(|| {
            panic!(
                "accepted trailing parameter comma: {source}\n{:?}",
                result.errors
            )
        });
    assert_eq!(
        source.get(diagnostic.span.start..diagnostic.span.end),
        Some(","),
        "the diagnostic must identify the separator: {source}"
    );
}

#[track_caller]
fn accepted(source: &str) {
    let result = parse(source);
    assert!(result.errors.is_empty(), "{source}\n{:?}", result.errors);
}

#[test]
fn extends_parameter_list_requires_an_assignment_after_the_comma() {
    for declaration in [
        "class Base#(int WIDTH=32); endclass",
        "class Base#(int WIDTH=32, int DEPTH=4); endclass",
    ] {
        rejected(&format!(
            "{declaration} class Derived#(int WIDTH=32) extends Base#(WIDTH,); endclass"
        ));
    }
    rejected("class Derived extends Base#(.WIDTH(32),); endclass");
}

#[test]
fn instances_and_binds_share_the_parameter_list_check() {
    for source in [
        "module t; leaf #(1,) u(); endmodule",
        "module t; leaf #(.WIDTH(1),) u(); endmodule",
        "bind t leaf #(1,) u();",
        "module t; if (0) begin leaf #(1,) u(); end endmodule",
    ] {
        rejected(source);
    }
}

#[test]
fn type_specializations_share_the_parameter_list_check() {
    for source in [
        "module t; Base#(int,) h; endmodule",
        "module t; initial begin Base#(int,) h; end endmodule",
        "typedef Base#(int,) alias_t;",
        "module t; virtual iface#(32,) vif; endmodule",
    ] {
        rejected(source);
    }
}

#[test]
fn expression_specializations_share_the_parameter_list_check() {
    for source in [
        "module t; initial $display(Base#(1,)::VALUE); endmodule",
        "module t; initial $display(pkg::Base#(1,)::VALUE); endmodule",
        "module t; initial $display(pkg::Outer#(1)::Inner#(2,)::VALUE); endmodule",
        "module t; leaf #(.T(Base#(int,))) u(); endmodule",
    ] {
        rejected(source);
    }
}

#[test]
fn empty_lists_named_defaults_and_nested_commas_remain_legal() {
    for source in [
        "module t; leaf #() u(); endmodule",
        "module t; leaf #(.WIDTH(), .DEPTH(4)) u(); endmodule",
        "class Derived extends Base#(); endclass",
        "class Derived extends Base#(.WIDTH()); endclass",
        "module t; Base#(int, 4) h; endmodule",
        "module t; initial $display(pkg::Base#(.WIDTH())::VALUE); endmodule",
        "module t; leaf #(f(1,), 4) u(); endmodule",
        "module t; leaf #(.WIDTH(f(, 2)), .DEPTH(4)) u(); endmodule",
        "module t; leaf #('{a: 1, b: 2}, x[f(1, 2)]) u(); endmodule",
    ] {
        accepted(source);
    }
}

#[test]
fn constructor_and_function_omitted_arguments_keep_their_own_grammar() {
    accepted(
        "class Base; function new(int a=1, int b=2); endfunction endclass \
         class Derived extends Base(1,); endclass \
         module t; Base h; int value; \
         function int f(int a=1, int b=2); return a+b; endfunction \
         initial begin h=new(1,); value=f(, 2); value=f(1,); end endmodule",
    );
}
