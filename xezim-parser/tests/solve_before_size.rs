//! §18.5.10: a `solve … before` operand may be an array's size, written
//! `arr.size()`. The operand keeps the array as its root, which the solver
//! orders by, and reads as the same call the constraints use.

use sv_parser::parse;

#[test]
fn size_operand_parses_as_the_size_call() {
    let r = parse(
        "class c; rand bit s; rand bit [7:0] a[]; rand bit [7:0] q[$];\n \
         constraint k { solve s before a.size(); solve a.size(), q.size() before s;\n \
         if (s) a.size() == 8; else a.size() == 1; }\nendclass\n",
    );
    assert!(r.errors.is_empty(), "{:?}", r.errors);
    let ast = format!("{:?}", r.source);
    let solves: Vec<&str> = ast.split("Solve {").skip(1).collect();
    assert_eq!(solves.len(), 2, "{ast}");
    for s in &solves {
        let s = &s[..s.find("IfElse").unwrap_or(s.len())];
        assert!(s.contains("Call {") && s.contains("name: \"size\""), "{s}");
    }
    // The array, not `size`, is the operand's root.
    let first = &solves[0][..solves[0].find("before_paths").unwrap()];
    assert!(first.contains("name: \"a\""), "{first}");
}

#[test]
fn a_call_on_a_plain_name_is_still_an_error() {
    let r = parse("class c; rand bit s, t; constraint k { solve s before t(); } endclass\n");
    assert!(!r.errors.is_empty());
}
