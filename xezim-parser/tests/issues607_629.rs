//! Parser and preprocessor regressions for aionhw/xezim#609-#611 and
//! #614-#619 (reported by git-hevangel). The simulator-level tests live in
//! the xezim repo; these pin the front-end shape each fix relies on. The
//! opt-in `RelaxFlag` switches of the same batch (#608, #622-#629) are
//! process-wide and are not exercised here.

use sv_parser::ast::Description;
use sv_parser::ast::decl::{CovergroupItem, ModuleItem, PackageItem};
use sv_parser::ast::expr::{ExprKind, NumberLiteral};
use sv_parser::ast::types::NetType;
use sv_parser::parse;
use sv_parser::preprocessor::Preprocessor;

fn preprocess(src: &str) -> (String, Vec<String>, Preprocessor) {
    let mut pp = Preprocessor::new();
    let out = pp.preprocess(src);
    let errors = pp.errors().to_vec();
    (out, errors, pp)
}

/// Parses `src`, asserts it has no errors, and returns the AST's Debug text.
fn parse_clean(src: &str) -> String {
    let result = parse(src);
    assert!(result.errors.is_empty(), "{src}: {:?}", result.errors);
    format!("{:?}", result.source)
}

/// §16.7 `cycle_delay_range ::= ## constant_primary`: a name after `##`,
/// or `pkg::name`, is the count and a `(` after it starts the next
/// sequence; it is not a call `N(x)` (#609).
#[test]
fn name_after_double_hash_is_the_delay_count() {
    for p in [
        "go ##N (x != y)",
        "go |-> ##N (x)",
        "go ##pkg::N (x)",
        "go |-> ##pkg::N (x != y)",
    ] {
        let src = format!(
            "package pkg; localparam int N = 2; endpackage\nmodule m; localparam int N = 3;\n \
             bit clk, go, x, y;\n assert property (@(posedge clk) {p});\nendmodule\n"
        );
        let ast = parse_clean(&src);
        assert!(!ast.contains("Call {"), "{p}: {ast}");
        assert!(ast.contains("op: HashHash"), "{p}: {ast}");
    }
    // A parenthesized count still parses as an expression.
    let ast = parse_clean(
        "module m; bit clk, a, b; function int f(int v); return v; endfunction\n \
         assert property (@(posedge clk) a ##(f(1)) b);\nendmodule\n",
    );
    assert!(ast.contains("Call {"), "{ast}");
}

/// §26.2, §6.6: a package net keeps its net kind on the data declaration;
/// an undriven net starts at z, a supply net at its constant (#610).
#[test]
fn package_nets_keep_their_net_kind() {
    let result = parse(
        "package nets;\n wire w;\n tri t;\n supply0 gnd;\n supply1 vdd;\n wand wa;\n \
         logic v;\nendpackage\n",
    );
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    let Some(Description::Package(package)) = result.source.descriptions.first() else {
        panic!("missing package");
    };
    let mut seen = Vec::new();
    for item in &package.items {
        if let PackageItem::Data(d) = item {
            for decl in &d.declarators {
                let fill = match decl.init.as_ref().map(|e| &e.kind) {
                    Some(ExprKind::Number(NumberLiteral::UnbasedUnsized(c))) => Some(*c),
                    _ => None,
                };
                seen.push((decl.name.name.clone(), d.net_type, fill));
            }
        }
    }
    let expect = [
        ("w", Some(NetType::Wire), Some('z')),
        ("t", Some(NetType::Tri), Some('z')),
        ("gnd", Some(NetType::Supply0), Some('0')),
        ("vdd", Some(NetType::Supply1), Some('1')),
        ("wa", Some(NetType::Wand), Some('z')),
        ("v", None, None),
    ];
    assert_eq!(seen.len(), expect.len(), "{seen:?}");
    for ((name, net, fill), (en, enet, efill)) in seen.iter().zip(expect) {
        assert_eq!(name, en);
        assert_eq!(*net, enet, "{name}");
        assert_eq!(*fill, efill, "{name}");
    }
}

/// §19.5.1.1: a bin's `with (expr)` filter is kept on the bin, before any
/// `iff`, and the rest of the covergroup parses (#611).
#[test]
fn cover_bin_with_filter_is_kept() {
    let result = parse(
        "module top; int value; bit en;\n covergroup cg;\n  cp: coverpoint value {\n   \
         bins sel[] = {4, 5, 6} with (item inside {5, 6});\n   \
         bins pos = {[1:3]} with (item > 1) iff (en);\n   bins plain = {7};\n  }\n  \
         other: coverpoint en;\n endgroup\nendmodule\n",
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
    let cps: Vec<_> = cg
        .items
        .iter()
        .filter_map(|i| match i {
            CovergroupItem::Coverpoint(cp) => Some(cp),
            _ => None,
        })
        .collect();
    assert_eq!(cps.len(), 2, "the coverpoint after the filter is kept");
    let shape: Vec<(&str, bool, bool)> = cps[0]
        .bins
        .iter()
        .map(|b| {
            (
                b.name.name.as_str(),
                b.with_filter.is_some(),
                b.iff_guard.is_some(),
            )
        })
        .collect();
    assert_eq!(
        shape,
        [
            ("sel", true, false),
            ("pos", true, true),
            ("plain", false, false)
        ]
    );
    assert!(matches!(
        cps[0].bins[0].with_filter.as_ref().map(|f| &f.kind),
        Some(ExprKind::Inside { .. })
    ));
}

/// §16.14.4: `restrict property (...)` is read and set aside as a module
/// item, labelled or not, and as a statement; the module around it is kept
/// (#614).
#[test]
fn restrict_property_is_set_aside() {
    let ast = parse_clean(
        "module m; bit clk, a, b;\n restrict property (@(posedge clk) a |-> (b || !a));\n \
         r1: restrict property (a);\n wire kept_after;\n initial begin\n  \
         restrict property (a);\n  kept_stmt = 1;\n end\nendmodule\n",
    );
    assert!(ast.contains("\"kept_after\""), "{ast}");
    assert!(ast.contains("\"kept_stmt\""), "{ast}");
}

/// §3.14.3, A.2.2.3: `1step` after `#`, or alone inside `#( )`, is one delay
/// value, the identifier `1step`; `a = #1step b;` and `#1step;` parse
/// (#615). This parser sets an intra-assignment delay aside (xezim rewrites
/// it to `$__xz_intra_delay(d, b)` first), so that form is pinned too.
#[test]
fn one_step_is_a_delay_value() {
    let ast = parse_clean(
        "module m; logic a, b, x, y;\n assign #(1step) y = x;\n initial begin\n  \
         a = #1step b;\n  #1step;\n  #(1step) a = 0;\n  a = $__xz_intra_delay(1step, b);\n \
         end\nendmodule\n",
    );
    assert_eq!(ast.matches("\"1step\"").count(), 4, "{ast}");
    assert!(!ast.contains("\"step\""), "{ast}");
    // Every pair of a long run joins, and the tokens between stay in order.
    let body: String = (0..200).map(|k| format!("#1step a = {k};\n")).collect();
    let ast = parse_clean(&format!(
        "module m; int a;\n initial begin\n{body} end\nendmodule\n"
    ));
    assert_eq!(ast.matches("\"1step\"").count(), 200, "{ast}");
    assert!(!ast.contains("\"step\""), "{ast}");
    let at = |v: &str| ast.find(&format!("value: \"{v}\"")).expect(v);
    assert!(at("0") < at("199"), "{ast}");
    // Outside a delay the pair stays apart, an error.
    assert!(
        !parse("module m; int x; initial x = 1step; endmodule\n")
            .errors
            .is_empty()
    );
}

/// §22.5.1: a macro usage ends at a `` paste, so `` `JOIN(unit_`TAG, _n) ``
/// is `unit_alpha_n`, not a use of `TAG_n`; a pasted name that is itself a
/// macro (`` `x``y `` with `AB` defined, `` `P``A``B `` with `PAB`) is still
/// pasted whole (#616).
#[test]
fn token_paste_ends_a_macro_usage() {
    let (out, errors, _) = preprocess(
        "`define JOIN(A, B) A``B\n`define TAG alpha\nmodule m; int `JOIN(unit_`TAG, _n);\n\
         endmodule\n",
    );
    assert!(errors.is_empty(), "{errors:?}");
    let flat = out.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(flat.contains("int unit_alpha_n;"), "{out}");
    assert!(!out.contains('\u{1}'), "the paste separator is removed");

    let (out, errors, _) = preprocess(
        "`define A 1\n`define B 2\n`define AB 99\n`define PASTE(x,y) `x``y\n\
         module m; int v = `PASTE(A,B);\nendmodule\n",
    );
    assert!(errors.is_empty(), "{errors:?}");
    let flat = out.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(flat.contains("int v = 99;"), "{out}");

    // A paste chain forms its name whole: `P``A``B with PAB defined.
    let (out, errors, _) = preprocess(
        "`define P 1\n`define PAB 77\n`define CHAIN(x,y) `P``x``y\n\
         module m; int v = `CHAIN(A,B);\nendmodule\n",
    );
    assert!(errors.is_empty(), "{errors:?}");
    let flat = out.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(flat.contains("int v = 77;"), "{out}");

    // A 0x01 byte of the source survives an expansion that pasted nothing.
    let (out, errors, _) =
        preprocess("`define V 7\nmodule m; int v = `V; string s = \"\u{1}\";\nendmodule\n");
    assert!(errors.is_empty(), "{errors:?}");
    assert!(out.contains("int v = 7; string s = \"\u{1}\";"), "{out:?}");
}

/// §22.5.1: a paste that ends a macro name right before its argument list
/// keeps the arguments with the usage. UVM's field macros build their packer
/// calls this way (`` `uvm_pack_``TYPE``(ARG, __local_packer__) ``).
#[test]
fn token_paste_before_macro_arguments() {
    let (out, errors, _) = preprocess(
        "`define uvm_pack_da(VAR,P=packer) pk(VAR, P);\n\
         `define FLD(ARG,TYPE) `uvm_pack_``TYPE``(ARG, lp)\n\
         module m; initial begin `FLD(x, da) end\nendmodule\n",
    );
    assert!(errors.is_empty(), "{errors:?}");
    let flat = out.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(flat.contains("begin pk(x, lp); end"), "{out}");
}

/// §8.24, §8.23: an out-of-block method of a nested class names every scope
/// (`function int outer::inner::m(...)`), for a function and a task (#617).
#[test]
fn nested_class_method_out_of_block() {
    let result = parse(
        "class outer;\n class inner;\n  extern function int m(int a);\n  extern task t();\n \
         endclass\nendclass\nfunction int outer::inner::m(int a);\n return a + 1;\nendfunction\n\
         task outer::inner::t();\nendtask\n",
    );
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    let mut names = Vec::new();
    for d in &result.source.descriptions {
        let name = match d {
            Description::PackageItem(PackageItem::Function(f)) => &f.name,
            Description::PackageItem(PackageItem::Task(t)) => &t.name,
            _ => continue,
        };
        let scopes: Vec<&str> = name.scopes.iter().map(|s| s.name.name.as_str()).collect();
        names.push((scopes, name.name.name.as_str()));
    }
    assert_eq!(
        names,
        [(vec!["outer", "inner"], "m"), (vec!["outer", "inner"], "t")]
    );
}

/// §16.10, A.2.4: a property or sequence local may carry unpacked
/// dimensions (#618).
#[test]
fn assertion_local_with_unpacked_dimensions() {
    parse_clean(
        "module m; bit clk, go; bit [3:0] d;\n property p;\n  bit flags[3:0];\n  \
         @(posedge clk) (go, flags[0] = d[0]) |-> ##1 flags[0] == d[0];\n endproperty\n \
         sequence s;\n  logic [3:0] words[2];\n  (go, words[1] = d) ##1 words[1] == d;\n \
         endsequence\n property q;\n  bit a[1:0], b[7:0];\n  \
         @(posedge clk) (go, a[1] = 1, b[7] = 0) |-> a[1] != b[7];\n endproperty\n \
         assert property (p);\n cover property (@(posedge clk) s);\n assert property (q);\n\
         endmodule\n",
    );
    let diagnostics_for = |local: &str| {
        let result = parse(&format!(
            "module m; bit clk, go;\n property p;\n  {local}\n  \
             @(posedge clk) go |-> go;\n endproperty\nendmodule\n"
        ));
        let text = |ds: &[sv_parser::diagnostics::Diagnostic]| {
            ds.iter().map(|d| d.message.clone()).collect::<Vec<_>>()
        };
        (text(&result.errors), text(&result.warnings))
    };
    // §11.8.1: a signed element folds into a packed array whose element
    // selects read unsigned; it is accepted with a warning.
    for local in ["int counts[4];", "bit signed [7:0] s[2];", "integer i[2];"] {
        let (errors, warnings) = diagnostics_for(local);
        assert!(errors.is_empty(), "{local}: {errors:?}");
        assert!(
            warnings.iter().any(|w| w.contains("read unsigned")),
            "{local}: {warnings:?}"
        );
    }
    for local in ["bit flags[3:0];", "int unsigned u[4];", "int scalar;"] {
        let (errors, warnings) = diagnostics_for(local);
        assert!(
            errors.is_empty() && warnings.is_empty(),
            "{local}: {errors:?} {warnings:?}"
        );
    }
    // A type that does not fold, or a dimension that is not fixed-size, is
    // an error rather than a silently scalar local.
    for local in [
        "struct packed { bit a; } pairs[2];",
        "real samples[2];",
        "bit queue_of[$];",
        "int dyn[];",
    ] {
        let (errors, _) = diagnostics_for(local);
        assert!(
            errors.iter().any(|e| e.contains("not supported")),
            "{local}: {errors:?}"
        );
    }
}

/// §22.5.2: `` `undef `` names one macro; the text after the name on its line
/// is kept as source (#619).
#[test]
fn undef_keeps_the_rest_of_its_line() {
    let (out, errors, pp) = preprocess(
        "`define LIMIT 4\nmodule m;\n int head = `LIMIT;\n`undef LIMIT int tail_one = 5;\n\
         `ifdef LIMIT\n int wrong;\n`endif\nendmodule\n",
    );
    assert!(errors.is_empty(), "{errors:?}");
    let flat = out.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(flat.contains("int head = 4;"), "{out}");
    assert!(flat.contains("int tail_one = 5;"), "{out}");
    assert!(!out.contains("wrong"), "{out}");
    assert!(!pp.is_defined("LIMIT"));
}

/// §22.14, Table 22-2: a `begin_keywords` set reserves its own version's
/// words only, so a word a later version added is a name there (#608).
#[test]
fn keyword_set_frees_later_words() {
    use sv_parser::lexer::{Lexer, TokenKind};
    let reserved = |version: &str, word: &str| {
        let src = format!("`begin_keywords \"{version}\"\n{word}\n`end_keywords\n");
        let tokens = Lexer::new(&src).tokenize();
        let tok = tokens.iter().find(|t| t.text == word).expect("word token");
        tok.kind != TokenKind::Identifier
    };
    for (version, names, keywords) in [
        (
            "1364-1995",
            &["generate", "cell", "uwire"][..],
            &["reg"][..],
        ),
        ("1364-2001", &["uwire", "logic"], &["generate", "cell"]),
        ("1364-2001-noconfig", &["cell"], &["generate"]),
        ("1364-2005", &["logic", "until"], &["uwire", "cell"]),
        (
            "1800-2005",
            &["until", "checker", "unique0", "nettype"],
            &["logic", "uwire"],
        ),
        (
            "1800-2009",
            &["nettype", "soft", "implements", "interconnect"],
            &["until", "let"],
        ),
        ("1800-2012", &[], &["nettype", "soft", "untyped", "logic"]),
        ("1800-2023", &[], &["nettype", "cell"]),
    ] {
        for w in names {
            assert!(!reserved(version, w), "{version}: {w} is a name");
        }
        for w in keywords {
            assert!(reserved(version, w), "{version}: {w} is reserved");
        }
    }
}
