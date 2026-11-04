//! §6.24: a cast target may be a parenthesized constant primary.
//! `(9)'(x)` and `(WIDTH)'(x)` were lowered as the operand alone, so the
//! cast never reached elaboration.

use sv_parser::parse;

fn rendered(src: &str) -> String {
    let r = parse(src);
    assert!(r.errors.is_empty(), "{:?}", r.errors);
    format!("{:?}", r.source)
}

#[test]
fn parenthesized_cast_target_is_kept() {
    let src = "module t; logic [7:0] a; assign a = (9)'(a) + (W)'(a) + ((9))'(a); endmodule";
    let tree = rendered(src);
    let size_casts = tree.matches("$__xz_size_cast").count();
    assert!(
        tree.contains("$__xz_named_cast"),
        "parameter cast dropped: {tree}"
    );
    assert!(
        size_casts >= 2,
        "expected (9) and ((9)) to be size casts, found {size_casts}: {tree}"
    );
}

/// §6.24.1: the size may be any constant expression, `(W+1)'(x)`,
/// `$clog2(N)'(x)`, `(C ? 8 : 4)'(x)` or a constant function call. They were
/// lowered as the operand alone.
#[test]
fn constant_expression_cast_size_is_kept() {
    let src = "module t; logic [7:0] a, b; \
               assign b = (W+1)'(a) + $clog2(N)'(a) + (N > 4 ? 8 : 4)'(a) + sz(3)'(a) + (-W)'(a); \
               endmodule";
    let tree = rendered(src);
    let size_casts = tree.matches("$__xz_size_cast").count();
    assert_eq!(size_casts, 5, "a cast size was dropped: {tree}");
}
