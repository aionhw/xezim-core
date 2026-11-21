//! Integration tests for SystemVerilog IEEE 1800-2023 parser support.
//!
//! ## History — why this file shrank
//!
//! This file previously held 33 tests and had **never compiled**. It was
//! written against a per-call standard-selection API (`parse_with_std`,
//! `SvStandard`, `Lexer::with_standard`, `Preprocessor::with_standard`) that
//! was never implemented — `git log -S` finds no commit introducing any of
//! those symbols into `src/`. Because the crate's own suite therefore never
//! built, the breakage stayed invisible: CI runs `cargo test` in the `xezim`
//! repo only, which never compiles this crate's tests.
//!
//! Standard selection is a process-global (`set_sv2023` / `is_sv2023`), not a
//! per-parse argument, so the salvageable tests were ported to that. The ones
//! that could NOT be ported asserted on AST members that do not exist:
//! `PortDirection::RefStatic`, `ModuleItem::DefaultDisableIff`,
//! `StructUnionType::soft`, `Coverpoint::is_real`,
//! `CovergroupDeclaration::sample_args`, `PropertyDeclaration::body_text` /
//! `disable_iff`, `SequenceDeclaration::body_text`, `ClassConstraint::is_pure`.
//!
//! Those were removed rather than left failing. Note the distinction: the
//! parser mostly *accepts* that syntax — `ref static`, `default disable iff`,
//! `pure constraint`, triple-quoted strings and `covergroup … with function
//! sample()` all parse clean today — it just does not *model* the construct in
//! the AST, so there is nothing for a test to assert on. Re-adding those tests
//! is feature work on the AST, not test maintenance. Two constructs are not
//! accepted at all and are worth tracking separately: `union soft packed`
//! (§7.3.2) and `coverpoint real` (§19.5).
//!
//! What remains are the tests whose assertions the parser can satisfy today.
//!
//! ## Note on `set_sv2023`
//!
//! The standard is global mutable state, so these tests must not race. Each
//! one selects the standard through `with_sv2023`, which serialises on a mutex
//! and restores the previous value.

use std::sync::{Mutex, OnceLock};
use sv_parser::ast::Description;
use sv_parser::ast::decl::{ClassItem, ModuleItem};
use sv_parser::ast::types::PortDirection;
use sv_parser::{ParseResult, is_sv2023, parse, set_sv2023};

/// Serialise access to the global standard flag and restore it afterwards, so
/// these tests are safe under the default multi-threaded test runner.
fn with_sv2023<R>(enabled: bool, f: impl FnOnce() -> R) -> R {
    static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    let _guard = LOCK
        .get_or_init(|| Mutex::new(()))
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let prev = is_sv2023();
    set_sv2023(enabled);
    let out = f();
    set_sv2023(prev);
    out
}

fn parse_2023(src: &str) -> ParseResult {
    with_sv2023(true, || parse(src))
}

// ---------------------------------------------------------------------------
// `ref` argument direction (§13.5.2)
// ---------------------------------------------------------------------------

fn first_function_first_port_direction(src: &str) -> Option<PortDirection> {
    let result = parse_2023(src);
    assert!(
        result.errors.is_empty(),
        "parse errors: {:?}",
        result.errors
    );
    for desc in &result.source.descriptions {
        if let Description::Module(m) = desc {
            for item in &m.items {
                if let ModuleItem::FunctionDeclaration(f) = item {
                    return f.ports.first().map(|p| p.direction);
                }
            }
        }
    }
    None
}

/// A plain `ref` formal keeps the `Ref` direction under SV-2023. (The SV-2023
/// `ref static` form parses but is not distinguished in the AST, so there is
/// no separate direction to assert — see the module note.)
#[test]
fn ref_keyword_alone_stays_as_ref_under_sv2023() {
    let src = "module m; function void f(ref int a); endfunction endmodule";
    assert_eq!(
        first_function_first_port_direction(src),
        Some(PortDirection::Ref)
    );
}

// ---------------------------------------------------------------------------
// `randsequence` statement (§18.17)
// ---------------------------------------------------------------------------

#[test]
fn randsequence_parses_without_errors() {
    let src = "module m;\n\
                 initial begin\n\
                   randsequence (main)\n\
                     main : first second ;\n\
                     first : { $display(\"first\"); } ;\n\
                     second : { $display(\"second\"); } ;\n\
                   endsequence\n\
                 end\n\
               endmodule";
    let r = parse_2023(src);
    assert!(r.errors.is_empty(), "parse errors: {:?}", r.errors);
}

// ---------------------------------------------------------------------------
// `pragma protect` envelope skipping (§34)
// ---------------------------------------------------------------------------

#[test]
fn pragma_protect_envelope_is_dropped() {
    // The garbage between begin_protected / end_protected must not reach the
    // lexer. If it did it would explode into Unknown tokens and the
    // surrounding module/endmodule pair would not pair up.
    let src = "module m;\n\
               `pragma protect begin_protected\n\
                 this is not legal SV at all !!!! @#$\n\
                 \"\"unterminated and weird\n\
               `pragma protect end_protected\n\
               endmodule";
    let r = parse_2023(src);
    assert!(
        r.errors.is_empty(),
        "pragma-protect envelope must not surface errors: {:?}",
        r.errors
    );
}

#[test]
fn pragma_protect_short_form_envelope_is_dropped() {
    let src = "module m;\n\
               `pragma protect begin\n\
                 zzzz !!! unparsable\n\
               `pragma protect end\n\
               endmodule";
    let r = parse_2023(src);
    assert!(
        r.errors.is_empty(),
        "short-form pragma-protect envelope must not surface errors: {:?}",
        r.errors
    );
}

// ---------------------------------------------------------------------------
// Streaming concatenation (§11.4.14)
// ---------------------------------------------------------------------------

#[test]
fn streaming_concat_pack_form_parses() {
    let src = "module m;\n\
                 logic [31:0] packed_w;\n\
                 logic [7:0] a, b, c, d;\n\
                 assign packed_w = {>>{a, b, c, d}};\n\
               endmodule";
    let r = parse_2023(src);
    assert!(r.errors.is_empty(), "parse errors: {:?}", r.errors);
}

#[test]
fn streaming_concat_with_byte_slice_parses() {
    let src = "module m;\n\
                 logic [31:0] w;\n\
                 logic [31:0] r;\n\
                 assign r = {<<byte{w}};\n\
               endmodule";
    let r = parse_2023(src);
    assert!(r.errors.is_empty(), "parse errors: {:?}", r.errors);
}

#[test]
fn streaming_concat_into_dynamic_array_parses() {
    let src = "module m;\n\
                 bit [7:0] arr [];\n\
                 bit [31:0] w;\n\
                 initial begin\n\
                   arr = new[4];\n\
                   {>>{arr}} = w;\n\
                 end\n\
               endmodule";
    let r = parse_2023(src);
    assert!(r.errors.is_empty(), "parse errors: {:?}", r.errors);
}

// ---------------------------------------------------------------------------
// `extern constraint` (§18.5.1)
// ---------------------------------------------------------------------------

#[test]
fn extern_constraint_in_class_parses_with_no_body() {
    let src = "class C; extern constraint c1; endclass";
    let r = parse_2023(src);
    assert!(r.errors.is_empty(), "parse errors: {:?}", r.errors);
    for desc in r.source.descriptions {
        if let Description::Class(c) = desc {
            for item in c.items {
                if let ClassItem::Constraint(cc) = item {
                    assert!(cc.is_extern, "extern constraint must set is_extern");
                    assert!(!cc.has_body, "extern constraint must have no body");
                    assert_eq!(cc.name.name, "c1");
                    return;
                }
            }
        }
    }
    panic!("no class-level constraint found in source");
}

// ---------------------------------------------------------------------------
// `union soft` — IEEE 1800-2023 §7.3.2
// ---------------------------------------------------------------------------

fn first_data_decl_type(src: &str, sv2023: bool) -> sv_parser::ast::types::DataType {
    let r = with_sv2023(sv2023, || parse(src));
    assert!(r.errors.is_empty(), "parse errors: {:?}", r.errors);
    for desc in r.source.descriptions {
        if let Description::Module(m) = desc {
            for item in m.items {
                if let ModuleItem::DataDeclaration(dd) = item {
                    return dd.data_type;
                }
            }
        }
    }
    panic!("no data declaration found in source");
}

fn as_struct(dt: sv_parser::ast::types::DataType) -> sv_parser::ast::types::StructUnionType {
    match dt {
        sv_parser::ast::types::DataType::Struct(su) => su,
        other => panic!("expected a struct/union type, got {:?}", other),
    }
}

/// Members of differing widths — the precise case a plain `union packed`
/// rejects.
#[test]
fn union_soft_packed_parses_and_sets_soft_flag() {
    let src = "module m;\n\
                 union soft packed {\n\
                   bit [7:0]  a;\n\
                   bit [15:0] b;\n\
                   bit [31:0] c;\n\
                 } u;\n\
               endmodule";
    let su = as_struct(first_data_decl_type(src, true));
    assert_eq!(su.kind, sv_parser::ast::types::StructUnionKind::Union);
    assert!(su.soft, "`union soft packed` must set the soft flag");
    assert!(su.packed, "`union soft packed` is still packed");
}

/// `soft` is optional-`packed`: `union soft { … }` is also legal.
#[test]
fn union_soft_without_packed_parses() {
    let src = "module m;\n\
                 union soft { bit [7:0] a; bit [3:0] b; } u;\n\
               endmodule";
    let su = as_struct(first_data_decl_type(src, true));
    assert!(su.soft, "`union soft` must set the soft flag");
}

#[test]
fn plain_union_packed_keeps_soft_false() {
    let src = "module m;\n\
                 union packed { bit [7:0] a; bit [7:0] b; } u;\n\
               endmodule";
    let su = as_struct(first_data_decl_type(src, true));
    assert!(!su.soft, "a plain `union packed` must leave soft false");
}

/// Under SV-2017 `soft` is not a union modifier, so the declaration must NOT
/// parse clean — the flag must never be set outside SV-2023.
#[test]
fn union_soft_is_not_recognized_under_sv2017() {
    let src = "module m;\n\
                 union soft packed { bit [7:0] a; } u;\n\
               endmodule";
    let r = with_sv2023(false, || parse(src));
    assert!(
        !r.errors.is_empty(),
        "`union soft` must not be accepted under SV-2017"
    );
}

/// The modifier is union-only; `struct soft` must not be accepted.
#[test]
fn soft_modifier_does_not_apply_to_structs() {
    let src = "module m;\n\
                 struct soft packed { bit [7:0] a; } s;\n\
               endmodule";
    let r = with_sv2023(true, || parse(src));
    assert!(!r.errors.is_empty(), "`struct soft` must not be accepted");
}

// ---------------------------------------------------------------------------
// Real-valued coverpoints — IEEE 1800-2023 §19.5
// ---------------------------------------------------------------------------

fn first_coverpoint(src: &str, sv2023: bool) -> sv_parser::ast::decl::Coverpoint {
    let r = with_sv2023(sv2023, || parse(src));
    assert!(r.errors.is_empty(), "parse errors: {:?}", r.errors);
    for desc in r.source.descriptions {
        if let Description::Module(m) = desc {
            for item in m.items {
                if let ModuleItem::CovergroupDeclaration(cg) = item {
                    for cgi in cg.items {
                        if let sv_parser::ast::decl::CovergroupItem::Coverpoint(cp) = cgi {
                            return cp;
                        }
                    }
                }
            }
        }
    }
    panic!("no coverpoint found in source");
}

#[test]
fn coverpoint_real_keyword_marks_is_real() {
    let src = "module m;\n\
                 real r;\n\
                 covergroup cg;\n\
                   cp: coverpoint real r;\n\
                 endgroup\n\
               endmodule";
    let cp = first_coverpoint(src, true);
    assert!(cp.is_real, "`coverpoint real` must set is_real");
}

#[test]
fn plain_coverpoint_keeps_is_real_false() {
    let src = "module m;\n\
                 int v;\n\
                 covergroup cg;\n\
                   cp: coverpoint v;\n\
                 endgroup\n\
               endmodule";
    let cp = first_coverpoint(src, true);
    assert!(
        !cp.is_real,
        "an integral coverpoint must leave is_real false"
    );
}

/// Under SV-2017 `real` is not a coverpoint modifier, so the declaration must
/// not parse clean — the flag must never be set outside SV-2023.
#[test]
fn coverpoint_real_is_not_recognized_under_sv2017() {
    let src = "module m;\n\
                 real r;\n\
                 covergroup cg;\n\
                   cp: coverpoint real r;\n\
                 endgroup\n\
               endmodule";
    let r = with_sv2023(false, || parse(src));
    assert!(
        !r.errors.is_empty(),
        "`coverpoint real` must not be accepted under SV-2017"
    );
}

/// §6.24.1, §19.5: a real cast is the operand in both modes. Its keyword
/// does not mark the coverpoint declaration; the expression carries the type.
#[test]
fn coverpoint_real_cast_is_an_expression() {
    use sv_parser::ast::expr::ExprKind;
    use sv_parser::ast::types::DataType;

    for sv2023 in [false, true] {
        for cast in ["real'(x)", "real /* casting type */ ' (x)"] {
            let src = format!(
                "module m; int x; covergroup cg;
                   cp: coverpoint {cast} iff (x != 0) {{ bins three = {{3.0}}; }}
                 endgroup endmodule"
            );
            let cp = first_coverpoint(&src, sv2023);
            assert!(!cp.is_real);
            assert!(cp.iff_guard.is_some());
            assert_eq!(cp.bins.len(), 1);
            let ExprKind::SystemCall { name, args } = cp.expr.kind else {
                panic!("missing cast in {cast}");
            };
            assert_eq!(name, "$__xz_type_cast");
            assert!(matches!(&args[0].kind, ExprKind::TypeLiteral(dt)
                if matches!(&**dt, DataType::Real { .. })));
            assert!(matches!(&args[1].kind, ExprKind::Ident(_)));
        }
    }
}
