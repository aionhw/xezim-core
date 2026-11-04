//! White space between tokens (§5.3) in three places the lexer, the
//! preprocessor and the parser did not allow it (aionhw/xezim#578-#580):
//! inside a based literal (§5.7.1), between a macro's name and its actual
//! arguments (§22.5.1), and between a UDP's name, strength, delay and an
//! unnamed instance (§29.3).

use sv_parser::preprocessor::Preprocessor;
use sv_parser::{parse, tokenize};

fn literals(src: &str) -> Vec<String> {
    tokenize(src)
        .into_iter()
        .filter(|t| format!("{:?}", t.kind) == "IntegerLiteral")
        .map(|t| t.text)
        .collect()
}

/// §5.7.1: the size, base and value are one literal across spaces, tabs and
/// newlines, and its text carries no white space, so the size is kept.
#[test]
fn based_literal_spans_white_space() {
    assert_eq!(literals("a = 2 'd1;"), ["2'd1"]);
    assert_eq!(literals("a = 12 'sh 3;"), ["12'sh3"]);
    assert_eq!(literals("a = 8\t'b1;"), ["8'b1"]);
    assert_eq!(literals("a = {2\n  'd1};"), ["2'd1"]);
    assert_eq!(literals("a = 2'd\n  1;"), ["2'd1"]);
    assert_eq!(literals("a = 2\n'd\n\t1;"), ["2'd1"]);
    // Not a based literal: a spaced cast keeps its bare apostrophe.
    let casts = literals("a = (w) ' (v);");
    assert!(casts.iter().any(|t| t == "'"), "{casts:?}");
}

fn preprocess(src: &str) -> (String, Vec<String>) {
    let mut pp = Preprocessor::new();
    let out = pp.preprocess(src);
    (out, pp.errors().to_vec())
}

fn norm(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// §22.5.1: the actual-argument list may follow the name on a later line,
/// after blank lines and comments; a use with no list stays an error.
#[test]
fn macro_arguments_on_a_later_line() {
    let (out, errs) = preprocess(
        "`define ADD(a, b) ((a) + (b))\nmodule t; int r; initial begin\n  r = `ADD\n    // c\n\n    (7, 8);\n  r = `ADD\n    ( 5\n    , 6\n    );\nend endmodule\n",
    );
    assert!(errs.is_empty(), "{errs:?}");
    let out = norm(&out);
    assert!(out.contains("r = ((7) + (8));"), "{out}");
    assert!(
        out.contains("r = (( 5) + ( 6));") || out.contains("r = ((5) + (6));"),
        "{out}"
    );
    assert!(!out.contains("`ADD"), "{out}");
}

/// §29.3: `udp [drive_strength] [delay] [name] (terminals)`, the delay a
/// number, a parameter name (A.2.2.3) or `(min:typ:max)`.
#[test]
fn unnamed_udp_instance_after_strength_or_delay() {
    let src = "primitive p (z, a); output z; input a; table 0 : 0; 1 : 1; endtable endprimitive
module t; localparam int D = 2; reg a; wire z0, z1, z2, z3, z4, z5, z6, z7;
  p #0 (z0, a);
  p #0 (z1, a), (z2, a);
  p (strong0, weak1) (z3, a);
  p (strong0, weak1) #1.5 (z4, a);
  p #D (z5, a);
  p #D u (z6, a);
  p #(1:2:3) (z7, a);
endmodule";
    let r = parse(src);
    assert!(r.errors.is_empty(), "{:?}", r.errors);
}

/// A.5.3 (aionhw/xezim#841): a UDP table row may write its symbols next to
/// each other; the lexer joins them into one token, and each character is
/// still one symbol.
#[test]
fn udp_row_symbols_may_be_adjacent() {
    let src = "primitive p (o, a, b, c);\n  output o; input a, b, c;\n  table\n    00?:0;\n    1bB:1;\n    x0?:x;\n  endtable\nendprimitive\n";
    let r = sv_parser::parse(src);
    assert!(r.errors.is_empty(), "{:?}", r.errors);
    let tree = format!("{:?}", r.source);
    assert!(tree.contains("Udp("), "the primitive was not kept as a UDP: {tree}");
    assert!(
        !r.warnings.iter().any(|d| d.message.contains("UNSUPPORTED UDP TABLE")),
        "{:?}",
        r.warnings
    );
}
