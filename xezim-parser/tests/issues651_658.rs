//! Parser and preprocessor regressions for aionhw/xezim#651-#658 (reported
//! by amal-khailtash). The simulator-level tests live in the xezim repo;
//! these pin that each form parses, and the AST shape each fix relies on.

use sv_parser::ast::Description;
use sv_parser::ast::decl::{ClassItem, PackageItem};
use sv_parser::parse;
use sv_parser::preprocessor::Preprocessor;

fn clean(src: &str) -> sv_parser::ParseResult {
    let result = parse(src);
    assert!(result.errors.is_empty(), "{src}: {:?}", result.errors);
    result
}

/// §19.6.1.4: a cross bin given as a list of value tuples is read as the
/// `||` of `&&`-joined `binsof(...) intersect` selects (#651).
#[test]
fn cross_bin_tuple_list() {
    let r = clean(
        "module top; int a, b;\n covergroup cg;\n  ca: coverpoint a;\n  cb: coverpoint b;\n  \
         ab: cross ca, cb { bins tuples = '{'{1,2}, '{3,4}}; }\n endgroup\nendmodule\n",
    );
    let ast = format!("{:?}", r.source);
    assert!(
        ast.contains("Or(") && ast.contains("And(") && ast.contains("Binsof"),
        "{ast}"
    );
    let bad = parse(
        "module top; int a, b;\n covergroup cg;\n  ca: coverpoint a;\n  cb: coverpoint b;\n  \
         ab: cross ca, cb { bins t = '{'{1,2,3}}; }\n endgroup\nendmodule\n",
    );
    assert!(
        !bad.errors.is_empty(),
        "a tuple of the wrong size is an error"
    );
}

/// §16.9.3, §9.4.2: `@clk` without parentheses as a sampled-value
/// function's clocking argument (#652).
#[test]
fn bare_clocking_argument() {
    clean("module top; bit clk, s, r;\n always @(s) r = $changed(s, @clk);\nendmodule\n");
}

/// §3.12.1, A.1.11: property and sequence declarations at compilation-unit
/// scope (#653).
#[test]
fn unit_scope_property_and_sequence() {
    let r = clean(
        "property p(a, b); a |-> b; endproperty\nsequence s(x); x ##1 x; endsequence\n\
         module top; endmodule\n",
    );
    let kinds: Vec<bool> = r
        .source
        .descriptions
        .iter()
        .map(|d| {
            matches!(
                d,
                Description::PackageItem(PackageItem::Property(_) | PackageItem::Sequence(_))
            )
        })
        .collect();
    assert_eq!(kinds, [true, true, false]);
}

/// §18.5.1: a package's out-of-block constraint fills its class's extern
/// prototype; naming no such prototype is an error (#654).
#[test]
fn package_out_of_block_constraint() {
    let r = clean(
        "package p;\n class item;\n  rand int value;\n  extern constraint bounded;\n endclass\n \
         constraint item::bounded { value inside {[1:4]}; }\nendpackage\n",
    );
    let Some(Description::Package(pkg)) = r.source.descriptions.first() else {
        panic!("missing package");
    };
    let PackageItem::Class(c) = &pkg.items[0] else {
        panic!("missing class");
    };
    let filled = c.items.iter().any(|i| {
        matches!(i, ClassItem::Constraint(k) if k.name.name == "bounded" && k.has_body && !k.items.is_empty())
    });
    assert!(filled, "{:?}", c.items);
    let bad =
        parse("package p;\n class item; endclass\n constraint item::nope { 1; }\nendpackage\n");
    assert!(!bad.errors.is_empty());
}

/// A.2.7: an unnamed formal in a DPI import or an `extern` prototype, but
/// not in a function declaration (#655).
#[test]
fn unnamed_prototype_formals() {
    clean("package p;\n import \"DPI-C\" function int f(int, bit [3:0]);\nendpackage\n");
    clean("class c;\n extern function int f(int);\n extern task t(output int);\nendclass\n");
    assert!(
        !parse("module m; function int f(int); return 0; endfunction endmodule\n")
            .errors
            .is_empty()
    );
}

/// §22.5.1: a define whose formal list spans lines keeps a body that holds
/// conditional directives (#656).
#[test]
fn multiline_formals_with_conditional_body() {
    let src = "`define ENABLE_PROBE\n`define DECLARE(tag,\n               unused_arg) \\\n\
               `ifdef ENABLE_PROBE \\\n  probe probe_``tag``(); \\\n`endif\n\
               module top;\n `DECLARE(one, 0)\nendmodule\n";
    let mut pp = Preprocessor::new();
    let out = pp.preprocess(src);
    assert!(pp.errors().is_empty(), "{:?}", pp.errors());
    assert!(out.contains("probe probe_one();"), "{out}");
}

/// §7.4.2, A.2.3: `input a[4];` is a port with an unpacked dimension, and
/// `input pair_t [2:0] b;` a typedef with a packed one (#657).
#[test]
fn nonansi_port_dimensions() {
    clean(
        "typedef logic [1:0] pair_t;\nmodule m(a, b);\n input a[4];\n input pair_t [2:0] b;\nendmodule\n",
    );
}

/// A.1.11: `;` is an empty package item, also right before `endpackage`
/// and after a subroutine (#658).
#[test]
fn empty_package_items() {
    clean("package p;\n ;\nendpackage\n");
    clean("package q;\n function void f(); endfunction\n ;\nendpackage\n");
}
