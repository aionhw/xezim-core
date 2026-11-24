//! §25.9 / §22.5 / Annex A: declaration recovery and source locations.

use sv_parser::ast::decl::ModuleItem;
use sv_parser::ast::expr::{ExprKind, Expression};
use sv_parser::ast::stmt::StatementKind;
use sv_parser::ast::{Description, Span};
use sv_parser::preprocessor::Preprocessor;

#[test]
fn malformed_virtual_interface_recovers_to_the_next_module() {
    let result = sv_parser::parse(
        "module top; virtual interface vif; endmodule module after_error; endmodule",
    );
    assert!(!result.errors.is_empty());
    assert!(result.errors.len() < 8, "{:?}", result.errors);
    assert!(result.source.descriptions.iter().any(|item| {
        matches!(item, Description::Module(module) if module.name.name == "after_error")
    }));
    for declaration in [
        "virtual interface bus_if vif;",
        "virtual interface bus_if #(4).driver vif;",
        "virtual bus_if vif;",
    ] {
        let source = format!("module top; {declaration} endmodule");
        let result = sv_parser::parse(&source);
        assert!(result.errors.is_empty(), "{source}: {:?}", result.errors);
    }
}

#[test]
fn unit_instances_remain_invalid_but_module_instances_parse() {
    // Annex A.1.2 / A.1.11 admits net declarations, but not module or
    // interface instantiations, as compilation-unit descriptions.
    for instance in [
        "foo bar();",
        "foo bar(.a(x), .b(y));",
        "foo #(.W(8)) bar(.a(x));",
        "bus_if b();",
    ] {
        let result = sv_parser::parse(instance);
        assert!(!result.errors.is_empty(), "{instance}");
        let source = format!("module top; {instance} endmodule");
        let result = sv_parser::parse(&source);
        assert!(result.errors.is_empty(), "{source}: {:?}", result.errors);
    }
}

fn assert_base_span(source: &str, expression: &Expression, target: &str) {
    let start = source.find(target).unwrap();
    assert_eq!(
        &source[expression.span.start as usize..expression.span.end as usize],
        target
    );
    let mut node = expression;
    loop {
        assert_eq!(node.span.start as usize, start, "{target}: {node:?}");
        node = match &node.kind {
            ExprKind::MemberAccess { expr, .. }
            | ExprKind::Index { expr, .. }
            | ExprKind::RangeSelect { expr, .. } => expr,
            _ => break,
        };
    }
}

#[test]
fn postfix_spans_include_the_base_on_both_sides_of_assignments() {
    for target in [
        "h.req.payload",
        "h.req[3]",
        "h.req[7:4]",
        "h.req[base +: 2]",
        "h.req[base -: 2]",
        "h.req.payload[3:0]",
    ] {
        for statement in [
            format!("{target} = 1;"),
            format!("{target} <= 1;"),
            format!("sink = {target};"),
        ] {
            let source = format!("module top; initial {statement} endmodule");
            let result = sv_parser::parse(&source);
            assert!(result.errors.is_empty(), "{source}: {:?}", result.errors);
            let Description::Module(module) = &result.source.descriptions[0] else {
                panic!("missing module")
            };
            let ModuleItem::InitialConstruct(initial) = &module.items[0] else {
                panic!("missing initial statement")
            };
            let expression = match &initial.stmt.kind {
                StatementKind::BlockingAssign { rvalue, .. } if statement.starts_with("sink") => {
                    rvalue
                }
                StatementKind::BlockingAssign { lvalue, .. }
                | StatementKind::NonblockingAssign { lvalue, .. } => lvalue,
                other => panic!("{other:?}"),
            };
            assert_base_span(&source, expression, target);
        }
    }
}

#[test]
fn macro_columns_cover_each_expansion_and_the_following_text() {
    for line in [
        "  logic [`W-1:0] data;",
        "  logic [`W-1:0] [`BIG-1:0] data;",
        "  logic [`BIG-1:0] [`W-1:0] data;",
        "  logic [`WRAP(`W)-1:0] [`BIG-1:0] data;",
        "  logic [`W-1:0] data; int count = `BIG;",
        "  logic `EMPTY data;",
        "  logic `EMPTY [`W-1:0] data;",
        "  logic [`W-1:0] data; int count = `__LINE__;",
        "  logic [`W-1:0] data; string path = `__FILE__;",
    ] {
        let source = format!(
            "`define W 8\n`define BIG 127\n`define WRAP(x) (x)\n`define EMPTY\nmodule top;\n{line}\nendmodule\n"
        );
        let mut pp = Preprocessor::new();
        let text = pp.preprocess(&source);
        let map = pp.take_line_map().expect("line map");
        for token in ["logic", "data"] {
            let start = text.find(token).unwrap();
            let location = map
                .locate(&text, Span::from_usize(start, start + token.len()))
                .unwrap();
            assert_eq!(location.line, 6, "{line}: {location:?}");
            assert_eq!(
                location.col as usize,
                line.find(token).unwrap() + 1,
                "{line}"
            );
            assert_eq!(location.macro_name, None, "{line}");
        }
    }
}

#[test]
fn each_macro_body_points_at_its_own_invocation() {
    let line = "  int a = `W; int b = `BIG;";
    let source = format!("`define W 8\n`define BIG 127\nmodule top;\n{line}\nendmodule\n");
    let mut pp = Preprocessor::new();
    let text = pp.preprocess(&source);
    let map = pp.take_line_map().unwrap();
    for (body, name) in [("8", "W"), ("127", "BIG")] {
        let start = text.find(body).unwrap();
        let location = map
            .locate(&text, Span::from_usize(start, start + body.len()))
            .unwrap();
        assert_eq!(location.line, 4);
        assert_eq!(
            location.col as usize,
            line.find(&format!("`{name}")).unwrap() + 1
        );
        assert_eq!(location.macro_name.as_deref(), Some(name));
    }
}

#[test]
fn object_macros_keep_their_arguments_and_repeated_suffix_in_source() {
    for (definition, line, token) in [
        ("`define FUNC $clog2", "  int data = `FUNC(8);", "8"),
        ("`define DECL int x; int data;", "  `DECL int data;", "data"),
    ] {
        let source = format!("{definition}\nmodule top;\n{line}\nendmodule\n");
        let mut pp = Preprocessor::new();
        let text = pp.preprocess(&source);
        let map = pp.take_line_map().unwrap();
        let start = text.rfind(token).unwrap();
        let location = map
            .locate(&text, Span::from_usize(start, start + token.len()))
            .unwrap();
        assert_eq!(location.line, 3);
        assert_eq!(
            location.col as usize,
            line.find(token).unwrap() + 1,
            "{line}"
        );
        assert_eq!(location.macro_name, None, "{line}");
    }
}
