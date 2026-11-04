//! §29.3.2, A.5.2: a sequential UDP declares its output `reg`, either as a
//! separate `reg q;` or within the output declaration, `output reg q;`, in the
//! body of a non-ANSI header as in an ANSI header. `output reg q = v` also
//! gives the start state (§29.3.3). The body form `output reg q;` was skipped
//! whole, so the UDP was taken for a combinational one (aionhw/xezim#868).

use sv_parser::ast::Description;
use sv_parser::ast::decl::UdpDecl;

fn udp(src: &str) -> UdpDecl {
    let r = sv_parser::parse(src);
    assert!(r.errors.is_empty(), "{:?}", r.errors);
    r.source
        .descriptions
        .into_iter()
        .find_map(|d| match d {
            Description::Udp(u) => Some(u),
            _ => None,
        })
        .expect("a UDP")
}

const TABLE: &str = "  table\n    ? : ? : -;\n  endtable\nendprimitive\n";

#[test]
fn output_reg_in_the_body_is_sequential() {
    let u = udp(&format!(
        "primitive p (q, a);\n  output reg q; input a;\n{TABLE}"
    ));
    assert!(u.is_sequential);
    assert_eq!(u.init, None);
    let u = udp(&format!(
        "primitive p (q, a);\n  input a; output reg q;\n{TABLE}"
    ));
    assert!(u.is_sequential);
}

#[test]
fn the_other_declaration_forms_stay_as_they_were() {
    let sep = udp(&format!(
        "primitive p (q, a);\n  output q; reg q; input a;\n{TABLE}"
    ));
    assert!(sep.is_sequential);
    let ansi = udp(&format!("primitive p (output reg q, input a);\n{TABLE}"));
    assert!(ansi.is_sequential);
    let comb = udp(
        "primitive p (q, a);\n  output q; input a;\n  table\n    0 : 1;\n    1 : 0;\n  endtable\nendprimitive\n",
    );
    assert!(!comb.is_sequential);
}

#[test]
fn output_reg_with_a_value_gives_the_start_state() {
    let body = udp(&format!(
        "primitive p (q, a);\n  output reg q = 1'b1; input a;\n{TABLE}"
    ));
    assert!(body.is_sequential);
    assert_eq!(body.init, Some('1'));
    let ansi = udp(&format!(
        "primitive p (output reg q = 1'b0, input a);\n{TABLE}"
    ));
    assert!(ansi.is_sequential);
    assert_eq!(ansi.init, Some('0'));
    assert_eq!(ansi.ports.len(), 2, "{:?}", ansi.ports);
    let initial = udp(&format!(
        "primitive p (q, a);\n  output reg q; input a;\n  initial q = 1'bx;\n{TABLE}"
    ));
    assert_eq!(initial.init, Some('x'));
}
