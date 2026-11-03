//! `--no-strict` keeps accepting a mixed parameter value list (#150). The strict
//! flag is process-wide, so this has its own test binary.

#[test]
fn no_strict_accepts_a_mixed_list() {
    sv_parser::set_strict_checks(false);
    let r = sv_parser::parse(
        "module t; c #(1, .B(2)) u(); initial $display(k#(.A(1), 2)::v); endmodule",
    );
    assert!(r.errors.is_empty(), "{:?}", r.errors);
}
