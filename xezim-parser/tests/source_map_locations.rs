//! Diagnostics locate through the preprocessor's line map: `file:line:col`
//! of the ORIGINAL source (an `include`d file, not the file that included it;
//! a macro invocation for macro text), the source line, and a caret span.

use std::path::{Path, PathBuf};

use sv_parser::ast::Span;
use sv_parser::diagnostics::render_diagnostic;
use sv_parser::parse_file;
use sv_parser::preprocessor::Preprocessor;

fn temp_dir(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "sv-parser-srcmap-{}-{}-{}",
        tag,
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("clock")
            .as_nanos()
    ));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    dir
}

fn write(dir: &Path, name: &str, text: &str) -> String {
    let p = dir.join(name);
    std::fs::write(&p, text).expect("write source");
    p.to_string_lossy().into_owned()
}

/// Render the first parse error of `path`.
fn first_error(path: &str) -> String {
    let result = parse_file(path, &[], &[]).expect("read");
    let err = result.errors.first().expect("a parse error");
    render_diagnostic(err, &result.source_text, result.line_map.as_ref(), path)
}

/// Byte span of the first `needle` in the preprocessed text of `path`.
fn locate_token(path: &str, needle: &str) -> String {
    let mut pp = Preprocessor::new();
    let src = std::fs::read_to_string(path).expect("read");
    let text = pp.preprocess_file(&src, Some(Path::new(path)));
    let map = pp.take_line_map().expect("line map");
    let at = text
        .find(needle)
        .unwrap_or_else(|| panic!("{needle:?} not in:\n{text}"));
    map.location_string(&text, Span::from_usize(at, at + needle.len()))
        .expect("mapped")
}

#[test]
fn syntax_error_in_top_file() {
    let dir = temp_dir("top");
    let top = write(
        &dir,
        "top.sv",
        "module top;\n  logic [7:0] a;\n  initial begin\n    a = 8'h1\n    $display(\"a=%0d\", a);\n  end\nendmodule\n",
    );
    assert_eq!(
        first_error(&top),
        format!(
            concat!(
                "{top}:5:5: error: expected Semicolon, found SystemIdentifier '$display'\n",
                "    5 |     $display(\"a=%0d\", a);\n",
                "      |     ^~~~~~~~",
            ),
            top = top
        )
    );
}

#[test]
fn syntax_error_in_included_file() {
    let dir = temp_dir("inc");
    let body = write(
        &dir,
        "body.svh",
        "// helper\ntask automatic show;\n  int x;\n  x = 3 +;\nendtask\n",
    );
    let top = write(
        &dir,
        "top.sv",
        "module top;\n`include \"body.svh\"\n  initial show();\nendmodule\n",
    );
    assert_eq!(
        first_error(&top),
        format!(
            concat!(
                "In file included from {top}:2:\n",
                "{body}:4:10: error: expected expression, found Semicolon ';'\n",
                "    4 |   x = 3 +;\n",
                "      |          ^",
            ),
            top = top,
            body = body
        )
    );
}

#[test]
fn error_inside_macro_points_at_the_invocation() {
    let dir = temp_dir("macro");
    let top = write(
        &dir,
        "m.sv",
        r#"`define CHECK(sig) \
  if (sig !== 1'b1) begin \
    $display("bad") \
  end
module top;
  logic a = 1;
  initial begin
    `CHECK(a)
  end
endmodule
"#,
    );
    assert_eq!(
        first_error(&top),
        format!(
            concat!(
                "{top}:8:5: error: expected Semicolon, found KwEnd 'end'\n",
                "    8 |     `CHECK(a)\n",
                "      |     ^~~~~~\n",
                "{top}:8:5: note: in expansion of macro `CHECK`",
            ),
            top = top
        )
    );
}

#[test]
fn text_before_a_macro_keeps_its_own_column() {
    let dir = temp_dir("macro-prefix");
    let top = write(
        &dir,
        "p.sv",
        "`define W 8\nmodule top;\n  logic [`W-1:0] q;\nendmodule\n",
    );
    let loc = locate_token(&top, "logic");
    assert_eq!(loc, format!("{top}:3:3"));
}

#[test]
fn text_after_a_macro_keeps_its_own_column() {
    // `data` merely FOLLOWS the `` `W `` expansion on the same line, so it
    // must be located at its real (original) column, not redirected to the
    // invocation column of the macro (issue #398 defect 3).
    let dir = temp_dir("macro-suffix");
    let top = write(
        &dir,
        "m.sv",
        "`define W 8\nmodule t;\n  logic [`W-1:0] data;\nendmodule\n",
    );
    // Original line: `  logic [`W-1:0] data;`; `data` sits at col 18 in the
    // SOURCE, but the `W -> 8 substitution shrank the line by one, so the
    // preprocessed `data` is at col 17. The map must restore the original 18.
    assert_eq!(locate_token(&top, "data"), format!("{top}:3:18"));
    // A macro that GROWS the line shifts following tokens the other way.
    let grow = write(
        &dir,
        "g.sv",
        "`define BIG 127\nmodule t;\n  logic [`BIG-1:0] tail;\nendmodule\n",
    );
    // `tail` is at original col 20 (`BIG` at cols 11-13 of the source, but
    // the `BIG -> 127 substitution shrinks the line so `tail` sits earlier).
    assert_eq!(locate_token(&grow, "tail"), format!("{grow}:3:20"));
}

#[test]
fn columns_survive_inline_conditional_split() {
    let dir = temp_dir("split");
    let top = write(
        &dir,
        "s.sv",
        "module top;\n  initial begin\n    a = 1; `ifdef FOO a = 2; `endif b = 3;\n  end\nendmodule\n",
    );
    assert_eq!(locate_token(&top, "b = 3"), format!("{top}:3:37"));
}

#[test]
fn lines_after_a_multi_line_define_stay_exact() {
    let dir = temp_dir("define");
    let top = write(
        &dir,
        "d.sv",
        r#"`define SUM(x) \
   x + \
   x
module top;
  initial $display("%0d %0d", `__LINE__, `SUM(2));
  wire MARK_A;
endmodule
"#,
    );
    assert_eq!(locate_token(&top, "MARK_A"), format!("{top}:6:8"));
    // `__LINE__` counts the define's continuation lines too.
    let mut pp = Preprocessor::new();
    let text = pp.preprocess_file(
        &std::fs::read_to_string(&top).unwrap(),
        Some(Path::new(&top)),
    );
    assert!(
        text.contains("$display(\"%0d %0d\", 5,"),
        "__LINE__ drifted:\n{text}"
    );
}

#[test]
fn every_output_line_is_mapped() {
    let dir = temp_dir("cover");
    write(
        &dir,
        "inc.svh",
        r#"wire from_inc;
`define INC_M(a) (a + \
  1)
"#,
    );
    let top = write(
        &dir,
        "c.sv",
        r#"`timescale 1ns/1ps
`include "inc.svh"
module top;
(* keep = 1,
   dont_touch = 1 *) wire attr_w;
`pragma protect begin_protected
garbage garbage
`pragma protect end_protected
  initial $display("%0d", `INC_M(
     3));
`line 100 "virtual.sv" 0
  wire MARK_V;
endmodule
"#,
    );
    let mut pp = Preprocessor::new();
    let text = pp.preprocess_file(
        &std::fs::read_to_string(&top).unwrap(),
        Some(Path::new(&top)),
    );
    let map = pp
        .take_line_map()
        .expect("the map covers the text line for line");
    let mut off = 0;
    for line in text.split_inclusive('\n') {
        assert!(
            map.locate(&text, Span::from_usize(off, off)).is_some(),
            "unmapped line at {off}:\n{text}"
        );
        off += line.len();
    }
    assert_eq!(
        locate_token(&top, "from_inc"),
        format!("{}:1:6", dir.join("inc.svh").display())
    );
    assert_eq!(locate_token(&top, "attr_w"), format!("{top}:5:27"));
    assert_eq!(locate_token(&top, "MARK_V"), "virtual.sv:100:8");
}

#[test]
fn missing_include_is_a_located_error() {
    let dir = temp_dir("missing");
    let top = write(
        &dir,
        "t.sv",
        "module top;\n  `include \"nope.svh\"\nendmodule\n",
    );
    let mut pp = Preprocessor::new();
    pp.preprocess_file(
        &std::fs::read_to_string(&top).unwrap(),
        Some(Path::new(&top)),
    );
    assert_eq!(pp.errors().len(), 1);
    assert_eq!(
        pp.errors()[0],
        format!(
            concat!(
                "{top}:2:3: error: cannot find `include file 'nope.svh' (searched the including ",
                "file's directory and 1 include dir(s))\n",
                "    2 |   `include \"nope.svh\"\n",
                "      |   ^~~~~~~~",
            ),
            top = top
        )
    );
}
