//! IEEE 1800-2017 §22.6: `` `ifdef ``/`` `ifndef ``/`` `elsif ``/`` `else ``/
//! `` `endif `` may appear MID-LINE, not only at the start of a line.
//!
//! UVM 2020.3.1 writes
//!   `static `ifndef UVM_ENABLE_DEPRECATED_API local `endif bit m;`
//! The line-based directive resolver only recognised a directive at the start
//! of a line, so the inline form passed through verbatim and the parser choked
//! on the `local` keyword — the whole UVM 2020 package failed to compile.

use sv_parser::preprocess;

/// Collapse whitespace so the assertions don't depend on how the split lands.
fn norm(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

#[test]
fn inline_ifndef_keeps_the_body_when_the_macro_is_undefined() {
    let out = preprocess("static `ifndef FOO local `endif bit x;\n");
    assert!(
        norm(&out).contains("static local bit x ;")
            || norm(&out).contains("static local bit x;"),
        "inline `ifndef should keep `local` when FOO is undefined; got: {:?}",
        norm(&out)
    );
}

#[test]
fn inline_ifndef_drops_the_body_when_the_macro_is_defined() {
    let out = preprocess("`define FOO\nstatic `ifndef FOO local `endif bit x;\n");
    let n = norm(&out);
    assert!(n.contains("static bit x"), "expected `static bit x`, got: {:?}", n);
    assert!(!n.contains("local"), "`local` must be dropped when FOO is defined; got: {:?}", n);
}

#[test]
fn inline_ifdef_keeps_the_body_when_the_macro_is_defined() {
    let out = preprocess("`define FOO\nstatic `ifdef FOO local `endif bit x;\n");
    assert!(norm(&out).contains("static local bit x"), "got: {:?}", norm(&out));
}

#[test]
fn inline_conditional_inside_a_string_is_not_treated_as_a_directive() {
    // A backtick inside a string literal is data, not a directive.
    let out = preprocess("string s = \"a `ifndef b\";\nint y;\n");
    assert!(norm(&out).contains("`ifndef"), "string content must be preserved: {:?}", norm(&out));
}

#[test]
fn a_conditional_in_a_define_body_is_not_split() {
    // The `ifdef inside a macro BODY belongs to the body; splitting it at
    // define time would break the `define. The pre-pass must leave the define
    // line untouched, so code AFTER it preprocesses cleanly. (Whether xezim
    // then resolves a body conditional on expansion is a separate matter and
    // not what this fix touches.)
    let out = preprocess("`define PICK `ifdef FOO 1 `else 2 `endif\nint after = 7;\n");
    assert!(
        norm(&out).contains("int after = 7"),
        "a `define with an inline conditional in its body must not disturb later code: {:?}",
        norm(&out)
    );
}

// ── line accounting ───────────────────────────────────────────────────────

/// A conditional directive on its OWN line must not shift the lines after it.
///
/// The splitter lifts every inline conditional onto its own line, then flushed
/// whatever followed the directive as one more line. When the directive WAS
/// the whole line, that trailing flush was empty — and emitted a blank line
/// anyway. Every `` `ifdef ``/`` `ifndef ``/`` `else ``/`` `elsif ``/
/// `` `endif `` in a file therefore pushed everything below it down by one,
/// which is every file with an include guard.
///
/// IEEE 1800-2023 §22.13 makes this observable through `` `__LINE__ ``, and it
/// silently skewed `file:line` in every diagnostic below a guard.
#[test]
fn an_own_line_conditional_does_not_shift_later_line_numbers() {
    use std::path::Path;
    use sv_parser::preprocessor::Preprocessor;

    // marker sits on source line 7, behind two guards.
    let src = "`ifndef __FILE__\n\
               `define __FILE__ 0\n\
               `endif\n\
               `ifndef __LINE__\n\
               `define __LINE__ 0\n\
               `endif\n\
               marker `__LINE__\n";
    let mut pp = Preprocessor::new();
    let out = pp.preprocess_file(src, Some(Path::new("/w/f.svh")));
    assert!(out.contains("marker 7"), "expected `marker 7`, got:\n{out}");
    assert_eq!(
        out.lines().count(),
        7,
        "the preprocessed text must stay line-for-line with the source:\n{out}"
    );
}

/// The ubiquitous include-guard shape, checked one directive at a time so a
/// regression names which one drifted.
#[test]
fn every_conditional_directive_keeps_the_line_count() {
    for directive in ["`ifdef X", "`ifndef X", "`endif", "`else", "`elsif X"] {
        let src = format!("{directive}\n`endif\nlast\n");
        let out = sv_parser::preprocess(&src);
        assert_eq!(
            out.lines().count(),
            3,
            "`{directive}` changed the line count:\n{out}"
        );
    }
}

/// The mid-line form still splits onto separate lines — that is what makes the
/// line-based resolver see it at all — so it necessarily adds lines. Pinned so
/// the behaviour is deliberate rather than assumed: a fix would need the
/// splitter to carry an output→source line map.
#[test]
fn a_mid_line_conditional_still_splits_and_is_known_to_add_lines() {
    let out = sv_parser::preprocess("static `ifndef FOO local `endif bit x;\n");
    assert!(
        out.lines().count() > 1,
        "the inline form must be lifted onto its own lines: {out:?}"
    );
}
