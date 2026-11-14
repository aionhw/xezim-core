//! `numeric_std."="` of a packed vector and an integer returns from the
//! wrapper when the vector holds a metavalue, instead of the interpreted
//! IEEE body.

use xezim_core::vhdl;

fn lowered(src: &str) -> String {
    vhdl::lower_design(&[("work", "t.vhd", src.as_bytes())])
        .unwrap_or_else(|e| panic!("{}", e.join("\n")))
}

#[test]
fn unsigned_eq_integer_metavalue_returns_in_the_wrapper() {
    let sv = lowered(
        r#"
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
entity t is end;
architecture a of t is
  signal u : unsigned(7 downto 0);
  signal hit : boolean;
begin
  hit <= u = 4;
end architecture;
"#,
    );
    let start = sv
        .find("function automatic byte unsigned vh_in_s")
        .expect("unsigned/integer compare wrapper");
    let end = sv[start..]
        .find("\n  endfunction")
        .map(|i| start + i)
        .expect("wrapper end");
    let f = &sv[start..end];
    assert!(
        f.contains("vh_cmp4_8((a & ~32'h44444444))"),
        "L/H are not stripped before the compare:\n{f}"
    );
    assert!(
        f.contains("metavalue detected, returning FALSE"),
        "a metavalue still falls into the IEEE body:\n{f}"
    );
    assert!(
        f.contains("vh_meta_rel(1873,"),
        "the warning is not the unsigned/natural assert:\n{f}"
    );
    let meta = f.find("metavalue detected").expect("meta");
    let fallback = f.rfind("return vh_f").expect("fallback");
    assert!(meta < fallback, "the metavalue return is after the fallback");
}
