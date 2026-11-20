//! IEEE 1800-2023 §22.5.1: a `` `" `` "indicates that the expansion shall
//! include the quotation mark, substitution of actual arguments, and
//! expansions of embedded macros". A macro whose text holds another macro
//! expands one level per preprocessor pass, and the pass that expanded the
//! first level already wrote the region's delimiters as quotes, so the next
//! pass read the rest as a string literal (where nothing expands): with
//! `` `define INST `TOP.u0 ``, `` `STR(`INST.x) `` gave "`TOP.u0.x"
//! (aionhw/xezim#1338). The region now keeps its delimiters until the macros
//! in it are expanded to the end; a plain string literal still expands
//! nothing.

use std::path::{Path, PathBuf};

use sv_parser::preprocessor::Preprocessor;

const DEFINES: &str = r#"
`define TOP top
`define INST `TOP.u0
`define LEAF `INST.sig
`define STR(p) `"p`"
`define BODY `"`INST.q`"
`define BRACKET(p) `"[p]`"
`define MSG(a, b) `"a: `\`"b`\`"`"
`define PASTE(p) `"p``_sfx`"
"#;

/// `text` without the white space outside string literals, so a check does
/// not depend on where the expansion leaves spaces between tokens.
fn squeeze(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars();
    let mut in_string = false;
    while let Some(c) = chars.next() {
        match c {
            '\\' if in_string => {
                out.push(c);
                out.extend(chars.next());
            }
            '"' => {
                in_string = !in_string;
                out.push(c);
            }
            c if c.is_whitespace() && !in_string => {}
            c => out.push(c),
        }
    }
    out
}

/// The preprocessed text of `DEFINES` followed by `body`, squeezed line by
/// line.
fn pp(body: &str) -> Vec<String> {
    let mut p = Preprocessor::new();
    let out = p.preprocess(&format!("{DEFINES}{body}\n"));
    assert!(
        !out.contains("`\""),
        "a stringify delimiter reached the output:\n{out}"
    );
    out.lines().map(squeeze).filter(|l| !l.is_empty()).collect()
}

/// The preprocessed line `x = <usage>;`, squeezed.
fn assign(usage: &str) -> String {
    let lines = pp(&format!("x = {usage};"));
    lines
        .iter()
        .find(|l| l.starts_with("x="))
        .unwrap_or_else(|| panic!("no assignment in {lines:?}"))
        .clone()
}

/// Whether the squeezed output of `body` has the line `want`.
fn has(body: &str, want: &str) {
    let lines = pp(body);
    assert!(lines.iter().any(|l| l == want), "{want} not in {lines:?}");
}

#[test]
fn chain_in_an_actual() {
    assert_eq!(assign("`STR(`INST.x)"), r#"x="top.u0.x";"#);
}

#[test]
fn three_level_chain() {
    assert_eq!(assign("`STR(`LEAF)"), r#"x="top.u0.sig";"#);
}

#[test]
fn chain_in_the_body_of_the_macro() {
    assert_eq!(assign("`BODY"), r#"x="top.u0.q";"#);
}

#[test]
fn chain_with_text_around_it() {
    assert_eq!(assign("`BRACKET(`INST)"), r#"x="[top.u0]";"#);
}

/// The example of the clause, and the same macro with chains in both
/// actuals: the escaped quotes stay escaped quotes of the one string.
#[test]
fn escaped_quotes_with_and_without_chains() {
    assert_eq!(
        assign("`MSG(left side,right side)"),
        r#"x="left side: \"right side\"";"#
    );
    assert_eq!(
        assign("`MSG(`INST, `LEAF)"),
        r#"x="top.u0: \"top.u0.sig\"";"#
    );
}

#[test]
fn paste_inside_the_region() {
    assert_eq!(assign("`PASTE(`INST)"), r#"x="top.u0_sfx";"#);
}

/// A chain through a stringifying macro passed on by another macro, through
/// a macro with arguments, a paste and a default actual.
#[test]
fn chains_through_other_macro_forms() {
    let body = r#"
`define WRAP(p) `STR(p)
`define F(a) a.u0
`define G `F(top)
`define PRE(x) x``_q
`define CH `PRE(top)
`define STRD(p=`INST) `"p`"
a = `WRAP(`INST);
b = `STR(`G);
c = `STR(`CH);
d = `STRD();
"#;
    for want in [
        r#"a="top.u0";"#,
        r#"b="top.u0";"#,
        r#"c="top_q";"#,
        r#"d="top.u0";"#,
    ] {
        has(body, want);
    }
}

/// The white space after the formal list of a macro with arguments is not
/// part of the string a region builds from its text, at any level.
#[test]
fn macro_with_arguments_in_a_region_has_no_leading_space() {
    let body = r#"
`define F(a) a.u0
`define E(a) a
`define T2 `F(top)
`define G2(a)    `E(a)
w1 = `STR(`F(top));
w2 = `STR(x`F(top));
w3 = `STR([`E(q)]);
w4 = `STR(`T2);
w5 = `STR(`G2(z));
w6 = `STR(a `E(q) b);
"#;
    for want in [
        r#"w1="top.u0";"#,
        r#"w2="xtop.u0";"#,
        r#"w3="[q]";"#,
        r#"w4="top.u0";"#,
        r#"w5="z";"#,
        r#"w6="a q b";"#,
    ] {
        has(body, want);
    }
}

/// Several regions and plain string literals on one line: only the regions
/// expand, and a region next to a literal leaves the literal as written.
#[test]
fn regions_and_string_literals_on_one_line() {
    assert_eq!(
        assign(r#"{`STR(`TOP), "`INST", `STR(`INST), "-`LEAF-"}"#),
        r#"x={"top","`INST","top.u0","-`LEAF-"};"#
    );
}

#[test]
fn plain_string_literal_expands_nothing() {
    assert_eq!(assign(r#""`INST""#), r#"x="`INST";"#);
}

/// A region whose macro is undefined keeps the name and still becomes a
/// string literal; a chain next to it is expanded.
#[test]
fn undefined_macro_in_a_region() {
    assert_eq!(assign("`STR(`NOPE)"), r#"x="`NOPE";"#);
    assert_eq!(assign("`STR(`NOPE `INST)"), r#"x="`NOPE top.u0";"#);
}

/// A macro that never stops expanding ends at the pass cap, and its region is
/// still closed as a string literal.
#[test]
fn endless_chain_in_a_region_terminates() {
    let lines = pp("`define SELF `SELF\n`define S `\"`S`\"\nx = `STR(`SELF);\ny = `S;");
    assert!(lines.iter().any(|l| l == r#"x="`SELF";"#), "{lines:?}");
    assert!(
        lines
            .iter()
            .any(|l| l.starts_with("y=") && l.ends_with(';')),
        "{lines:?}"
    );
}

#[test]
fn one_level_and_no_level_are_unchanged() {
    assert_eq!(assign("`STR(abc)"), r#"x="abc";"#);
    assert_eq!(assign("`STR(`TOP)"), r#"x="top";"#);
}

#[test]
fn unclosed_delimiter_is_a_quote() {
    has("`define OPEN `\"abc\nx = `OPEN\";", r#"x="abc";"#);
}

fn temp_dir() -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "sv-parser-stringify-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("clock")
            .as_nanos()
    ));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    dir
}

/// §22.5.1 builds an `include file name with a `" region; a chain in it
/// names the file to the end.
#[test]
fn include_name_built_by_a_chain() {
    let dir = temp_dir();
    std::fs::write(dir.join("chained.svh"), "`define FROM_INC 7\n").expect("write");
    let top = dir.join("top.sv");
    let src = "`define BASE chained\n`define NAME `BASE.svh\n`define HOME(f) `\"f`\"\n\
               `include `HOME(`NAME)\nx = `FROM_INC;\n";
    std::fs::write(&top, src).expect("write");
    let mut p = Preprocessor::new();
    let out = p.preprocess_file(src, Some(Path::new(&top)));
    assert!(out.lines().any(|l| squeeze(l) == "x=7;"), "{out}");
    let _ = std::fs::remove_dir_all(&dir);
}
