//! IEEE 1800-2017 §5.3, §5.12, §9.4.2.2: white space and comments
//! between the tokens of @(*) do not turn it into an attribute instance.
use sv_parser::preprocessor::Preprocessor;

#[test]
fn spaced_implicit_event_does_not_consume_the_following_process() {
    for event in [
        "@(*)",
        "@(* )",
        "@(*\t)",
        "@(*\n)",
        "@( * )",
        "@ ( *\n )",
        "@(* /* comment */ )",
    ] {
        let src = format!(
            "module top; logic source, first, second;\n\
             always {event} first = source;\n\
             always @(*) second = source;\nendmodule\n"
        );
        let mut pp = Preprocessor::new();
        let out = pp.preprocess(&src);
        assert!(pp.errors().is_empty(), "{event}: {:?}", pp.errors());
        assert!(out.contains("first = source;"), "{event}: {out}");
        assert!(
            out.contains("always @(*) second = source;"),
            "{event}: {out}"
        );
        let parsed = sv_parser::parse(&out);
        assert!(parsed.errors.is_empty(), "{event}: {:?}", parsed.errors);
    }
}

#[test]
fn real_attributes_are_still_blanked_without_moving_source_columns() {
    let src = "module top; logic source, first, second;\n\
               always @(* ) first = source;\n\
               (* keep = 1 *) wire kept;\n\
               always @(*) second = source;\n\
               string label = \"(* literal *)\";\nendmodule\n";
    let mut pp = Preprocessor::new();
    let out = pp.preprocess(src);
    assert!(pp.errors().is_empty(), "{:?}", pp.errors());
    let attr = "(* keep = 1 *)";
    assert_eq!(out, src.replace(attr, &" ".repeat(attr.len())));
}
