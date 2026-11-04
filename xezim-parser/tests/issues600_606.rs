//! Parser and preprocessor regressions for aionhw/xezim#600 and #602-#606
//! (reported by amal-khailtash). The simulator-level tests live in the
//! xezim repo; these pin the front-end shape each fix relies on.

use sv_parser::ast::Description;
use sv_parser::ast::decl::{CovergroupItem, ModuleItem, PackageItem};
use sv_parser::ast::expr::{BinaryOp, ExprKind, NumberLiteral};
use sv_parser::parse;
use sv_parser::preprocessor::Preprocessor;

fn preprocess(src: &str) -> (String, Vec<String>) {
    let mut pp = Preprocessor::new();
    let out = pp.preprocess(src);
    (out, pp.errors().to_vec())
}

fn resetall_rejected(src: &str) -> bool {
    preprocess(src)
        .1
        .iter()
        .any(|e| e.contains("`resetall is illegal inside a design element"))
}

/// §22.3: `` `resetall `` is legal after a module closed on its own line,
/// and after `interface class` (a class, §8.26), but not inside a module,
/// whatever a comment or string on the opening line says (#600).
#[test]
fn resetall_after_a_design_element_closed_on_one_line() {
    for src in [
        "module empty; endmodule\n`resetall\nmodule top; endmodule\n",
        "module a; endmodule module b; endmodule\n`resetall\nmodule top; endmodule\n",
        "interface class ic; endclass\n`resetall\nmodule top; endmodule\n",
    ] {
        assert!(!resetall_rejected(src), "{src}");
    }
    for src in [
        "module m;\n`resetall\nendmodule\n",
        "module m; // endmodule\n`resetall\nendmodule\n",
        "module m; string s = \"endmodule\";\n`resetall\nendmodule\n",
        "module m; /* endmodule */\n`resetall\nendmodule\n",
    ] {
        assert!(resetall_rejected(src), "{src}");
    }
}

/// §26.2, A.1.11: a package net with an implicit data type is package data
/// starting at z (§6.6), as an explicitly typed one is (#602).
#[test]
fn package_nets_are_package_data() {
    let result = parse(
        "package p;\n parameter W = 8;\n wire [p::W-1:0] t;\n wire u, v;\n tri [1:0] w;\n \
         wire logic [3:0] x;\nendpackage\n",
    );
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    let Some(Description::Package(package)) = result.source.descriptions.first() else {
        panic!("missing package");
    };
    let mut names = Vec::new();
    for item in &package.items {
        if let PackageItem::Data(d) = item {
            for decl in &d.declarators {
                names.push(decl.name.name.clone());
                let init = decl.init.as_ref().expect("an undriven net starts at z");
                assert!(
                    matches!(
                        init.kind,
                        ExprKind::Number(NumberLiteral::UnbasedUnsized('z'))
                    ),
                    "{}: {:?}",
                    decl.name.name,
                    init.kind
                );
            }
        }
    }
    assert_eq!(names, ["t", "u", "v", "w", "x"]);
}

/// §33.4: a configuration is read through `endconfig` (and its end label),
/// with a warning and no description; the design around it parses (#603).
#[test]
fn configuration_is_set_aside_with_a_warning() {
    let result = parse(
        "module top; endmodule\nconfig cfg;\n design work.top;\n default liblist work;\n \
         instance top.u use work.m;\nendconfig : cfg\nmodule other; endmodule\n",
    );
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    assert_eq!(result.source.descriptions.len(), 2);
    assert!(
        result
            .warnings
            .iter()
            .any(|w| format!("{w:?}").contains("configuration 'cfg' is ignored")),
        "{:?}",
        result.warnings
    );
}

/// The `until` node of an assertion's property, and the operator joining
/// its right operand.
fn until_shape(src: &str) -> (BinaryOp, Option<BinaryOp>) {
    let result = parse(src);
    assert!(result.errors.is_empty(), "{src}: {:?}", result.errors);
    let ast = format!("{:?}", result.source);
    let op = if ast.contains("op: SUntil") {
        BinaryOp::SUntil
    } else {
        assert!(ast.contains("op: Until"), "{ast}");
        BinaryOp::Until
    };
    let and = if ast.contains("op: SvaAnd") {
        Some(BinaryOp::SvaAnd)
    } else if ast.contains("op: LogAnd") {
        Some(BinaryOp::LogAnd)
    } else {
        None
    };
    (op, and)
}

/// §16.12.12: `p until_with q` is `p until (p and q)`, `s_until_with`
/// likewise from `s_until`; parenthesized forms parse (#604). A Boolean
/// operand keeps a Boolean `&&`, a temporal one the property `and`.
#[test]
fn until_with_is_until_over_a_conjunction() {
    let wrap = |p: &str| {
        format!("module m; bit clk, a, b; assert property (@(posedge clk) a |-> {p}); endmodule")
    };
    assert_eq!(
        until_shape(&wrap("(!a until_with b)")),
        (BinaryOp::Until, Some(BinaryOp::LogAnd))
    );
    assert_eq!(
        until_shape(&wrap("!a until_with b")),
        (BinaryOp::Until, Some(BinaryOp::LogAnd))
    );
    assert_eq!(
        until_shape(&wrap("(a s_until_with b)")),
        (BinaryOp::SUntil, Some(BinaryOp::LogAnd))
    );
    assert_eq!(
        until_shape(&wrap("((a ##1 b) until_with b)")),
        (BinaryOp::Until, Some(BinaryOp::SvaAnd))
    );
    // The plain form is unchanged.
    assert_eq!(until_shape(&wrap("(a until b)")), (BinaryOp::Until, None));
}

/// §19.5: a coverpoint bin's `iff (expr)` guard is kept on the bin,
/// whatever the expression (#605).
#[test]
fn cover_bin_iff_guard_is_kept() {
    let result = parse(
        "module top; int value, format;\n covergroup cg;\n  cp: coverpoint value {\n   \
         bins limited = {1} iff (format inside {2,3});\n   bins plain = {5};\n   \
         bins eq = {7} iff (format == 4);\n  }\n endgroup\nendmodule\n",
    );
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    let Some(Description::Module(m)) = result.source.descriptions.first() else {
        panic!("missing module");
    };
    let cg = m
        .items
        .iter()
        .find_map(|i| match i {
            ModuleItem::CovergroupDeclaration(cg) => Some(cg),
            _ => None,
        })
        .expect("covergroup");
    let cp = cg
        .items
        .iter()
        .find_map(|i| match i {
            CovergroupItem::Coverpoint(cp) => Some(cp),
            _ => None,
        })
        .expect("coverpoint");
    let guards: Vec<(&str, bool)> = cp
        .bins
        .iter()
        .map(|b| (b.name.name.as_str(), b.iff_guard.is_some()))
        .collect();
    assert_eq!(guards, [("limited", true), ("plain", false), ("eq", true)]);
    assert!(matches!(
        cp.bins[0].iff_guard.as_ref().map(|g| &g.kind),
        Some(ExprKind::Inside { .. })
    ));
}

/// §22.5.1, §5.2: a macro's formal argument list may span lines, with or
/// without defaults, and the lines after the definition keep their numbers
/// (#606).
#[test]
fn macro_formals_span_lines() {
    let src = "`define ADD(a,\n            b) (a + b)\n`define MUL(x = 2,\n            y = 3,\n            \
               z\n           ) (x * y * z)\nmodule m;\n  initial $display(`ADD(1, 2), `MUL(, , 4));\n  \
               initial $display(`__LINE__);\nendmodule\n";
    let (out, errors) = preprocess(src);
    assert!(errors.is_empty(), "{errors:?}");
    let flat: String = out.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(flat.contains("(1 + 2)"), "{out}");
    assert!(flat.contains("(2 * 3 * 4)"), "{out}");
    assert!(flat.contains("$display(9)"), "{out}");
}
