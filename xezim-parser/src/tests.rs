use crate::ast::{Description, decl::ModuleItem};
use crate::parse;

/// §16.10: assertion-local variable declarations, including typedef and
/// packed local types, are kept with the body as `$sva_local` declarations.
#[test]
fn assertion_local_declarations_are_kept() {
    for kind in ["property", "sequence"] {
        for declaration in [
            "time stamp;",
            "var stamp;",
            "var stamp = 1'b0;",
            "var [3:0] stamp;",
            "int counter;",
            "logic [7:0] sample;",
            "stamp_t stamp;",
            "scope_pkg::stamp_t stamp;",
            "int a, b = 2;",
        ] {
            let source = format!(
                "module m; bit clk; typedef time stamp_t; \
                 {kind} p; {declaration} @(posedge clk) 1'b0; end{kind} \
                 endmodule"
            );
            let result = parse(&source);
            assert!(
                result.errors.is_empty(),
                "{kind} {declaration}: {:?}",
                result.errors
            );
            let Some(Description::Module(m)) = result.source.descriptions.first() else {
                panic!("not a module");
            };
            let body = m
                .items
                .iter()
                .find_map(|i| match i {
                    ModuleItem::PropertyDeclaration(p) => p.body.clone(),
                    ModuleItem::SequenceDeclaration(s) => s.body.clone(),
                    _ => None,
                })
                .unwrap_or_else(|| panic!("{kind} {declaration}: body dropped"));
            let text = format!("{body:?}");
            assert!(
                text.contains("$sva_locals") && text.contains("$sva_local\""),
                "{kind} {declaration}: {text}"
            );
        }
    }
}

/// §16.10 / §16.11: sequence match items parse as `$sva_match`.
#[test]
fn sequence_match_items_parse() {
    let source = r#"
module m;
  bit clk, a, b; int d;
  function void note(); endfunction
  property p; int x; @(posedge clk) (a, x = d, x += 1, x++) ##1 (b, note()) |-> d == x; endproperty
  sequence s(local input int v); (a, v = v + 1) ##1 d == v; endsequence
endmodule
"#;
    let result = parse(source);
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    let text = format!("{:?}", result.source.descriptions);
    assert!(text.contains("$sva_match"), "{text}");
    assert!(text.contains("v$lf"), "{text}");
}

#[test]
fn assertion_body_expressions_are_not_local_declarations() {
    let source = r#"
module m;
  bit clk, a, b;
  typedef int sample_t;
  property p; @(posedge clk) a |=> b; endproperty
  property with_input(input bit expected); @(posedge clk) expected |=> b; endproperty
  sequence s; a ##1 b; endsequence
  sequence with_output(input bit expected, local output int stamp); expected ##1 b; endsequence
  sequence typed; sample_t'(a) == 0; endsequence
  sequence builtin; int'(a) == 0; endsequence
endmodule
"#;
    let result = parse(source);
    assert!(result.errors.is_empty(), "{:?}", result.errors);
}

#[test]
fn test_function_ports_implicit_packed() {
    let source = "module m; function void f(input [7:0] a); endfunction endmodule";
    let result = parse(source);
    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
}

#[test]
fn test_top_level_function() {
    let source = "function void f(input [7:0] a); endfunction";
    let result = parse(source);
    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
}

#[test]
fn test_begin_at_module_level() {
    let source = "module m; begin wire a; end endmodule";
    let result = parse(source);
    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
}

#[test]
fn test_assignment_pattern() {
    let source = "module m; initial pair = '{a:4'hA, b:4'h5}; endmodule";
    let result = parse(source);
    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
}

#[test]
fn test_associative_arrays() {
    let source = "module m; int aa [string]; int aa2 [*]; endmodule";
    let result = parse(source);
    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
}

#[test]
fn test_queues() {
    let source = "module m; int q [$]; int q2 [$:255]; endmodule";
    let result = parse(source);
    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
}

#[test]
fn test_interfaces_modports() {
    let source = "
        interface req_gnt_if;
          logic req;
          logic gnt;
          modport master (output req, input gnt);
          modport slave  (input req, output gnt);
        endinterface

        module req_master(req_gnt_if.master bus);
          initial bus.req = 1'b1;
        endmodule

        module req_slave(req_gnt_if.slave bus);
          always @(*) bus.gnt = bus.req;
        endmodule
    ";
    let result = parse(source);
    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
}

#[test]
fn test_module_header_imports() {
    let source = "
        package p;
        endpackage

        module m import p::*; (input logic a);
          initial a = 1'b0;
        endmodule
    ";
    let result = parse(source);
    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);

    let module = result
        .source
        .descriptions
        .iter()
        .find_map(|desc| match desc {
            Description::Module(module) if module.name.name == "m" => Some(module),
            _ => None,
        })
        .expect("module m not found");

    match module.items.first() {
        Some(ModuleItem::ImportDeclaration(import)) => {
            assert_eq!(import.items.len(), 1);
            assert_eq!(import.items[0].package.name, "p");
            assert!(import.items[0].item.is_none());
        }
        other => panic!(
            "expected header import as first module item, got {:?}",
            other
        ),
    }
}

#[test]
fn test_numeric_size_cast_expression() {
    let source = "module m; logic [31:0] x; initial x = 32'(1); endmodule";
    let result = parse(source);
    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
}

#[test]
fn test_scoped_constant_unpacked_dimension() {
    let source = "
        package ibex_pkg;
          localparam int IC_NUM_WAYS = 4;
        endpackage

        module m;
          logic [7:0] a [ibex_pkg::IC_NUM_WAYS-1:0];
        endmodule
    ";
    let result = parse(source);
    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
}

#[test]
fn test_processes_events() {
    let source = "
        module test;
          event ev;
          initial begin
            -> ev;
            ->> ev;
            @ev;
          end
        endmodule
    ";
    let result = parse(source);
    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
}

#[test]
fn test_semaphores() {
    let source = "
        module test;
          semaphore sem;
          initial begin
            sem = new(1);
            sem.get(1);
            sem.put(1);
          end
        endmodule
    ";
    let result = parse(source);
    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
}

/// §30.4 module path forms: parallel and full connections with polarity,
/// edge-sensitive paths with a data source, `if`/`ifnone`, selects on the
/// terminals, and 1/2/6/12-value delay lists with or without parentheses.
#[test]
fn test_specify_module_paths() {
    let source = "
        module c(input a, b, clk, input [1:0] d, output y, q, output [1:0] z);
          specify
            (a => y) = 5;
            (a, b *> y, q) = (1, 2);
            (a +=> y) = 1, 2;
            (d[0], d[1] -*> z[1:0]) = (1, 2, 3, 4, 5, 6);
            (posedge clk => (q +: b)) = (1:2:3, 4);
            (negedge clk *> (q : 1'b0)) = 1;
            if (a && !b) (a => y) = (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12);
            ifnone (a => y) = 7;
            showcancelled y;
          endspecify
        endmodule
    ";
    let result = parse(source);
    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
    let Some(Description::Module(m)) = result.source.descriptions.first() else {
        panic!("module expected");
    };
    let sb = m
        .items
        .iter()
        .find_map(|i| match i {
            ModuleItem::SpecifyBlock(sb) => Some(sb),
            _ => None,
        })
        .expect("specify block");
    let names =
        |ids: &[crate::ast::Identifier]| ids.iter().map(|i| i.name.clone()).collect::<Vec<_>>();
    let p = &sb.paths;
    assert_eq!(p.len(), 8);
    assert_eq!(
        (names(&p[0].srcs), names(&p[0].dsts)),
        (vec!["a".into()], vec!["y".into()])
    );
    assert_eq!(p[0].delays.len(), 1);
    assert_eq!(names(&p[1].srcs), vec!["a", "b"]);
    assert_eq!(names(&p[1].dsts), vec!["y", "q"]);
    assert_eq!(p[1].delays.len(), 2);
    assert_eq!(p[2].delays.len(), 2);
    assert_eq!(names(&p[3].srcs), vec!["d", "d"]);
    assert_eq!(names(&p[3].dsts), vec!["z"]);
    assert_eq!(p[3].delays.len(), 6);
    assert_eq!(
        (names(&p[4].srcs), names(&p[4].dsts)),
        (vec!["clk".into()], vec!["q".into()])
    );
    assert_eq!(p[4].delays.len(), 2);
    assert_eq!(names(&p[5].dsts), vec!["q"]);
    assert!(p[6].cond.is_some() && !p[6].ifnone);
    assert_eq!(p[6].delays.len(), 12);
    assert!(p[7].cond.is_none() && p[7].ifnone);
}

/// §31 timing checks: edge controls (keyword and descriptor list), `&&&`
/// conditions, omitted arguments, and a specify-block `specparam` hoisted
/// to a module-level localparam.
#[test]
fn test_specify_timing_checks() {
    use crate::ast::decl::{TIMING_NEGEDGE, TIMING_POSEDGE, timing_edge_bit};
    let source = "
        module ff(input d, input clk, input en);
          reg n;
          specify
            specparam tSU = 1.5;
            $setuphold(posedge clk &&& en, d, tSU, 1, n, , , dclk, dd);
            $width(negedge clk, 2);
            $setup(d, edge[01, x1] clk, 3);
          endspecify
        endmodule
    ";
    let result = parse(source);
    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
    let Some(Description::Module(m)) = result.source.descriptions.first() else {
        panic!("module expected");
    };
    assert!(
        m.items
            .iter()
            .any(|i| matches!(i, ModuleItem::LocalparamDeclaration(_)))
    );
    let sb = m
        .items
        .iter()
        .find_map(|i| match i {
            ModuleItem::SpecifyBlock(sb) => Some(sb),
            _ => None,
        })
        .expect("specify block");
    let tc = &sb.timing_checks;
    assert_eq!(tc.len(), 3);
    assert_eq!(tc[0].name, "$setuphold");
    assert_eq!(tc[0].args.len(), 9);
    let r = tc[0].args[0].as_ref().unwrap();
    assert_eq!(r.edges, Some(TIMING_POSEDGE));
    assert!(r.cond.is_some());
    assert_eq!(r.text, "posedge clk &&& en");
    assert!(tc[0].args[5].is_none() && tc[0].args[6].is_none());
    assert_eq!(sb.delayed_nets.len(), 2);
    assert_eq!(tc[1].args[0].as_ref().unwrap().edges, Some(TIMING_NEGEDGE));
    assert_eq!(
        tc[2].args[1].as_ref().unwrap().edges,
        Some(timing_edge_bit(0, 1) | timing_edge_bit(2, 1))
    );
}

/// §16.10: a match item can assign only a local variable.
#[test]
fn match_item_assignment_needs_a_local() {
    for body in [
        "property p; @(posedge clk) (a, d = 1) |-> b; endproperty",
        "sequence s; int v; (a, d++) ##1 b; endsequence",
        "ap: assert property (@(posedge clk) (a, d = 1) |-> b);",
    ] {
        let source = format!("module m; bit clk, a, b; int d; {body} endmodule");
        let result = parse(&source);
        assert!(
            result.errors.iter().any(|e| e
                .message
                .contains("illegal assignment to 'd' in a match item list")),
            "{body}: {:?}",
            result.errors
        );
    }
}

/// §16.9 Table 16-3: `##` binds looser than the expression operators and
/// tighter than the sequence `and` / `or`.
#[test]
fn cycle_delay_binds_looser_than_expression_operators() {
    let source = r#"
module m;
  bit clk, a, b, c, d;
  ap: assert property (@(posedge clk) a ##1 b == c);
  aq: assert property (@(posedge clk) a && b ##1 c || d);
  ar: assert property (@(posedge clk) a ##1 b and c ##1 d);
endmodule
"#;
    let result = parse(source);
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    let text = format!("{:?}", result.source.descriptions);
    // `a ##1 (b == c)`: the equality is the delayed operand.
    let eq = text.find("op: Eq").expect("no equality");
    let hh = text.find("op: HashHash").expect("no delay");
    assert!(hh < eq, "`==` parsed outside the `##` operand: {text}");
    // `(a && b) ##1 (c || d)`: the conjunction is the left operand.
    let and = text.find("op: LogAnd").expect("no &&");
    let or = text.find("op: LogOr").expect("no ||");
    assert!(and < or, "{text}");
}

/// §16.9.3: sampled clock arguments do not change ordinary sequence actual parsing.
#[test]
fn sampled_clock_arguments_preserve_sequence_actuals() {
    let result = parse(
        "module m; bit clk, a; ap: assert property (@(posedge clk) $rose(a, @(posedge clk))); aq: assert property (seq(@(posedge clk) a)); endmodule",
    );
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    let Some(Description::Module(module)) = result.source.descriptions.first() else {
        panic!("not a module")
    };
    let assertions: Vec<_> = module
        .items
        .iter()
        .filter_map(|item| {
            if let ModuleItem::AssertionItem(a) = item {
                Some(a)
            } else {
                None
            }
        })
        .collect();
    assert!(format!("{:?}", assertions[0]).contains("$__xz_clocking_arg"));
    let sequence = format!("{:?}", assertions[1]);
    assert!(sequence.contains("name: \"a\""), "{sequence}");
    assert!(!sequence.contains("$__xz_clocking_arg"), "{sequence}");
}

/// §16.12.9 / Table 16-3: a followed-by RHS is a property, associated right.
#[test]
fn followed_by_keeps_right_associated_property() {
    use crate::ast::expr::{BinaryOp, ExprKind};
    let result = parse(
        "module m; bit clk,a,b,c; ap: assert property (@(posedge clk) a #-# b |-> c); endmodule",
    );
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    let Some(Description::Module(module)) = result.source.descriptions.first() else {
        panic!("not a module")
    };
    let a = module
        .items
        .iter()
        .find_map(|item| {
            if let ModuleItem::AssertionItem(a) = item {
                Some(a)
            } else {
                None
            }
        })
        .unwrap();
    let ExprKind::SvaClocked { body, .. } = &a.expr.kind else {
        panic!("{:?}", a.expr)
    };
    let ExprKind::SystemCall { name, args } = &body.kind else {
        panic!("{body:?}")
    };
    assert_eq!(name, "$sva_follow_overlap");
    assert!(
        matches!(
            args[1].kind,
            ExprKind::Binary {
                op: BinaryOp::OrMinusArrow,
                ..
            }
        ),
        "{:?}",
        args[1]
    );
}

/// §6.11 / §8.25: explicit atom signing survives a type argument.
#[test]
fn type_keyword_specialization_keeps_signing() {
    let result = parse(
        "class C #(type T=int); endclass module m; C #(byte unsigned) u; C #(logic signed) s; endmodule",
    );
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    let text = format!("{:?}", result.source.descriptions);
    assert!(
        text.contains("TypeLiteral") && text.contains("Unsigned") && text.contains("Signed"),
        "{text}"
    );
}

fn class_constraint_items(result: &crate::ParseResult) -> Vec<crate::ast::decl::ConstraintItem> {
    use crate::ast::decl::ClassItem;
    let Some(Description::Class(class)) = result.source.descriptions.first() else {
        panic!("not a class")
    };
    class
        .items
        .iter()
        .find_map(|item| match item {
            ClassItem::Constraint(c) => Some(c.items.clone()),
            _ => None,
        })
        .expect("no constraint")
}

/// §18.5.3: `constraint_expression ::= expression [ -> constraint_set ]`. The
/// `->` is the constraint separator, not `LogImplies`, so its right side is a
/// `constraint_set` — here a block with two items.
#[test]
fn constraint_implication_rhs_is_block() {
    use crate::ast::decl::ConstraintItem;
    let result = parse("class c; rand int a,b; constraint k { a -> { b == 1; b == 2; } } endclass");
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    let items = class_constraint_items(&result);
    let ConstraintItem::Implication { constraint, .. } = &items[0] else {
        panic!("{:?}", items[0])
    };
    let ConstraintItem::Block(inner) = &**constraint else {
        panic!("{constraint:?}")
    };
    assert_eq!(inner.len(), 2);
}

/// `a -> b;` used to be swallowed by the expression parser as
/// `BinaryOp::LogImplies`, so the solver never saw a constraint implication.
#[test]
fn constraint_implication_is_a_constraint_item() {
    use crate::ast::decl::ConstraintItem;
    use crate::ast::expr::ExprKind;
    let result = parse("class c; rand int a,b; constraint k { a -> b; } endclass");
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    let items = class_constraint_items(&result);
    let ConstraintItem::Implication {
        condition,
        constraint,
        ..
    } = &items[0]
    else {
        panic!("{:?}", items[0])
    };
    assert!(
        matches!(condition.kind, ExprKind::Ident(_)),
        "{condition:?}"
    );
    let ConstraintItem::Expr(expr) = &**constraint else {
        panic!("{constraint:?}")
    };
    assert!(matches!(expr.kind, ExprKind::Ident(_)), "{expr:?}");
}

/// `->` is only a separator at the constraint-expression level: inside
/// parentheses it is the ordinary `LogImplies` operator (§11.4.8). The
/// `no_arrow` flag is scoped to one chain, not to the whole constraint.
#[test]
fn constraint_implication_inside_parens_is_logimplies() {
    use crate::ast::decl::ConstraintItem;
    use crate::ast::expr::{BinaryOp, ExprKind};
    let result = parse("class c; rand int a,b; constraint k { (a -> b); } endclass");
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    let items = class_constraint_items(&result);
    let ConstraintItem::Expr(expr) = &items[0] else {
        panic!("{:?}", items[0])
    };
    let ExprKind::Paren(inner) = &expr.kind else {
        panic!("{expr:?}")
    };
    let ExprKind::Binary { op, .. } = &inner.kind else {
        panic!("{inner:?}")
    };
    assert_eq!(*op, BinaryOp::LogImplies);
}
