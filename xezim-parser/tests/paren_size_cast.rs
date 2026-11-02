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
