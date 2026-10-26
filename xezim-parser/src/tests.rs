use crate::ast::{Description, decl::ModuleItem};
use crate::parse;

/// §10.4.2 / §25.9: calls within an NBA target do not turn `<=` into a
/// relational expression. A comparison inside an argument remains one.
#[test]
fn nonblocking_assignment_through_returned_receiver() {
    for target in [
        "get_v().data",
        "p::get_v().data[0]",
        "h.get_v().data[3:0]",
        "get_v().data[i +: 2]",
        "get_obj().nested.get_v().data",
    ] {
        let result = parse(&format!("module m; initial {target} <= 1; endmodule"));
        assert!(result.errors.is_empty(), "{target}: {:?}", result.errors);
        let ast = format!("{:?}", result.source);
        assert!(ast.contains("NonblockingAssign"), "{target}: {ast}");
        assert!(ast.contains("Call {"), "{target}: receiver call missing");
    }
    let result = parse("module m; initial use_value(get_v().data <= 1); endmodule");
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    let ast = format!("{:?}", result.source);
    assert!(
        !ast.contains("NonblockingAssign") && ast.contains("Leq"),
        "{ast}"
    );
}

/// §25.9 / §26.2: virtual-interface variables are package data declarations,
/// including the optional `interface` keyword, type arguments and modports.
#[test]
fn package_virtual_interface_declarations() {
    for declaration in [
        "virtual bus_if v;",
        "virtual interface bus_if v;",
        "virtual bus_if.mp v;",
        "virtual interface bus_if #(8).mp v;",
        "virtual bus_if v = null;",
        "virtual bus_if v, other;",
        "virtual bus_if v[2];",
        "virtual bus_if v[];",
        "virtual bus_if v[$];",
        "virtual bus_if v[string];",
        "var virtual bus_if v;",
    ] {
        let result = parse(&format!("package p; {declaration} endpackage"));
        assert!(
            result.errors.is_empty(),
            "{declaration}: {:?}",
            result.errors
        );
        let Some(Description::Package(package)) = result.source.descriptions.first() else {
            panic!("missing package for {declaration}");
        };
        let crate::ast::decl::PackageItem::Data(data) = &package.items[0] else {
            panic!("missing data declaration for {declaration}");
        };
        assert!(matches!(
            data.data_type,
            crate::ast::types::DataType::Interface { .. }
        ));
        assert_eq!(data.declarators[0].name.name, "v");
    }
    let result = parse("package p; virtual class base; endclass endpackage");
    assert!(result.errors.is_empty(), "{:?}", result.errors);
}

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

/// `pkg::type_t'{...}` is a typed assignment pattern. Release 0.11.3 only
/// folded a bare typedef name, so `dm::hartinfo_t'{...}` inside a
/// concatenation failed with `expected RBrace`.
#[test]
fn test_scoped_typed_assignment_pattern() {
    let source = "module m; initial p = {dm::hartinfo_t'{8'h0, 4'h2, 3'b0, 1'b1, dm::DataCount, dm::DataAddr}}; endmodule";
    let result = parse(source);
    assert!(result.errors.is_empty(), "Errors: {:?}", result.errors);
    let ast = format!("{:?}", result.source);
    assert!(
        ast.contains("AssignmentPattern"),
        "scoped type prefix was not folded into an assignment pattern: {ast}"
    );
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

/// §23.11: selected segments retain constant expressions in either bind form.
#[test]
fn bind_generate_target_selects() {
    for directive in [
        "bind top.bank[1-1].w.m mif mi();",
        "bind mem : top.bank[0].w.m, top.bank[1].w.m mif mi();",
    ] {
        let result = parse(directive);
        assert!(result.errors.is_empty(), "{:?}", result.errors);
        let Some(Description::Bind(bind)) = result.source.descriptions.first() else {
            panic!("missing bind");
        };
        assert_eq!(bind.target_path.len(), 4);
        assert_eq!(bind.target_path[1].selects.len(), 1);
        if !bind.extra_paths.is_empty() {
            assert_eq!(bind.extra_paths[0][1].selects.len(), 1);
        }
    }
}

/// §23.8/§23.11: absolute bind paths start at the root hierarchy scope.
#[test]
fn bind_root_hierarchy_paths() {
    for directive in [
        "bind $root.top.m monitor b();",
        "bind $root.top.bank[2].m monitor b();",
        "bind mem : $root.top.m monitor b();",
        "bind mem : $root.top.m[0], $root.top.m[1] monitor b();",
        "bind $root.top.bank[SEL-1].m monitor b();",
    ] {
        let result = parse(directive);
        assert!(result.errors.is_empty(), "{:?}", result.errors);
        let Some(Description::Bind(bind)) = result.source.descriptions.first() else {
            panic!("missing bind")
        };
        assert_eq!(bind.target_path[0].name.name, "$root");
        assert_eq!(bind.target_path[1].name.name, "top");
        for path in &bind.extra_paths {
            assert_eq!(path[0].name.name, "$root");
        }
    }
}

/// §25.9: a module-scope `virtual interface` declaration must report a
/// diagnostic instead of hanging. Previously `virtual interface vif;` shipped
/// the still-keyword `virtual` into `parse_identifier_starting_item`, whose
/// `parse_identifier()` returned `<e>` from the keyword WITHOUT bumping, and
/// `parse_module_items`'s progress guard (which only fired on a `None`)
/// never triggered -> the loop pushed a ModuleItem + Diagnostic per iteration
/// until it OOM'd. Now the `interface` spelling routes through
/// `parse_data_declaration` (like the `virtual <type> <name>;` spelling), and
/// the no-progress guard also covers a `Some` that consumed nothing.
#[test]
fn module_virtual_interface_spelling_does_not_loop() {
    // Malformed: `vif` is mistaken for the interface type, leaving no
    // declarator for the `;`.
    let result = parse("module top; virtual interface vif; endmodule");
    assert!(
        !result.errors.is_empty(),
        "expected a diagnostic, not a hang"
    );

    // Valid §25.9 spellings parse clean.
    for src in [
        "module top; virtual bus_if vif; endmodule",
        "module top; virtual req_if #(4).driver rd; endmodule",
        "interface bus_if; logic [3:0] d; modport driver(output d); endinterface \
         module top; virtual bus_if vif; endmodule",
    ] {
        let result = parse(src);
        assert!(result.errors.is_empty(), "{src}: {:?}", result.errors);
    }
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

/// §18.5.2: `constraint_block_item ::= solve ... | constraint_expression`, so a
/// bare `{` at block-item level can only start an expression — here a
/// concatenation, which must not be consumed as a nested block.
#[test]
fn constraint_block_item_lbrace_is_concatenation() {
    use crate::ast::decl::ConstraintItem;
    let result = parse("class c; rand int a,b; constraint k { {a,b} inside {1,2}; } endclass");
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    let items = class_constraint_items(&result);
    // `inside` is an expression operator (§11.4.13), so the item is an
    // `Expr`, not the dedicated `ConstraintItem::Inside` fast path.
    let expr = match &items[0] {
        ConstraintItem::Expr(e) => e,
        ConstraintItem::Inside { expr, .. } => expr,
        other => panic!("{other:?}"),
    };
    let inner = match &expr.kind {
        crate::ast::expr::ExprKind::Inside { expr, .. } => expr,
        other => panic!("{other:?}"),
    };
    assert!(
        matches!(inner.kind, crate::ast::expr::ExprKind::Concatenation(_)),
        "{inner:?}"
    );
}

/// §18.5.2: after `if (...)` the position is a `constraint_set`, where `{`
/// opens a nested block.
#[test]
fn constraint_set_lbrace_is_block() {
    use crate::ast::decl::ConstraintItem;
    let result =
        parse("class c; rand int a,b; constraint k { if (a) { b == 1; b == 2; } } endclass");
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    let items = class_constraint_items(&result);
    let ConstraintItem::IfElse { then_item, .. } = &items[0] else {
        panic!("{:?}", items[0])
    };
    let ConstraintItem::Block(inner) = &**then_item else {
        panic!("{then_item:?}")
    };
    assert_eq!(inner.len(), 2);
}

fn implication_constraint_items(
    result: &crate::ParseResult,
) -> Vec<crate::ast::decl::ConstraintItem> {
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
    let items = implication_constraint_items(&result);
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
    let items = implication_constraint_items(&result);
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
    let items = implication_constraint_items(&result);
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

/// §A.2.5: `packed_dimension ::= [ constant_range ] | unsized_dimension`, so
/// `bit [8]` is not legal. It is named once and recovered as `[7:0]`, instead
/// of the `expect(Colon)` cascade that also fails on the same `]`.
#[test]
fn packed_dimension_size_is_reported_once_and_recovered() {
    use crate::ast::decl::ModuleItem;
    use crate::ast::expr::{BinaryOp, ExprKind};
    use crate::ast::types::PackedDimension;
    let result = parse("module m; bit [8] x; endmodule");
    assert_eq!(result.errors.len(), 1, "{:?}", result.errors);
    assert!(
        result.errors[0].message.contains("packed dimension"),
        "{:?}",
        result.errors
    );
    let Some(Description::Module(m)) = result.source.descriptions.first() else {
        panic!("not a module")
    };
    let Some(ModuleItem::DataDeclaration(decl)) = m.items.first() else {
        panic!("{:?}", m.items.first())
    };
    let crate::ast::types::DataType::IntegerVector { dimensions, .. } = &decl.data_type else {
        panic!("{:?}", decl.data_type)
    };
    let PackedDimension::Range { left, right, .. } = &dimensions[0] else {
        panic!("{:?}", dimensions[0])
    };
    let ExprKind::Binary {
        op: BinaryOp::Sub, ..
    } = &left.kind
    else {
        panic!("{left:?}")
    };
    assert!(matches!(right.kind, ExprKind::Number(_)), "{right:?}");
}

/// The same bracket is legal as an unpacked dimension (§A.2.5:
/// `unpacked_dimension ::= [ constant_expression ]`), so it stays silent.
#[test]
fn unpacked_dimension_size_is_legal() {
    let result = parse("module m; bit x [8]; endmodule");
    assert!(result.errors.is_empty(), "{:?}", result.errors);
}

/// The first expression statement of the first method in the first class.
fn class_method_expr(result: &crate::ParseResult) -> &crate::ast::expr::Expression {
    use crate::ast::decl::{ClassItem, ClassMethodKind};
    let Some(Description::Class(class)) = result.source.descriptions.first() else {
        panic!("not a class")
    };
    class
        .items
        .iter()
        .find_map(|item| match item {
            ClassItem::Method(m) => match &m.kind {
                ClassMethodKind::Function(f) => f.items.iter().find_map(|s| match &s.kind {
                    crate::ast::stmt::StatementKind::Expr(e) => Some(e),
                    _ => None,
                }),
                _ => None,
            },
            _ => None,
        })
        .expect("no expression statement")
}

/// §18.8 `randomize_call`: the argument parentheses are optional, so
/// `randomize with { ... }` is a complete inline-constraint clause.
#[test]
fn randomize_with_bare_constraint_block() {
    use crate::ast::expr::ExprKind;
    let result = parse(
        "class c; rand int x; \
         function void f(); this.randomize with { x > 0; }; endfunction endclass",
    );
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    let ExprKind::RandomizeWith { call, constraints } = &class_method_expr(&result).kind else {
        panic!("{:?}", class_method_expr(&result))
    };
    assert!(
        matches!(call.kind, ExprKind::MemberAccess { .. }),
        "{call:?}"
    );
    assert_eq!(constraints.len(), 1);
}

/// §18.8: `[ ( [ identifier_list ] ) ] constraint_block` — the parenthesized
/// identifier list may precede the block. The list names the variables to
/// randomize; the AST keeps only the block, so this pins that it is consumed.
#[test]
fn randomize_with_identifier_list_and_block() {
    use crate::ast::expr::ExprKind;
    let result = parse(
        "class c; rand int x, y; \
         function void f(); this.randomize() with (x, y) { x > y; }; endfunction endclass",
    );
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    let text = format!("{:?}", result.source.descriptions);
    assert!(text.contains("RandomizeWith"), "{text}");
    let statement = class_method_expr(&result);
    let ExprKind::RandomizeWith { constraints, .. } = &statement.kind else {
        panic!("{statement:?}")
    };
    assert_eq!(constraints.len(), 1);
}

/// §18.8 requires the constraint block: the identifier list does not replace
/// it, so `with (x)` alone is a syntax error.
#[test]
fn randomize_with_identifier_list_requires_block() {
    let result = parse(
        "class c; rand int x; \
         function void f(); this.randomize with (x); endfunction endclass",
    );
    assert!(
        !result.errors.is_empty(),
        "{:?}",
        result.source.descriptions
    );
}

/// §18.8 vs. A.8.2: `with ( expression )` is the array-method filter, not a
/// randomize clause, so a non-randomize receiver keeps `WithClause`.
#[test]
fn array_method_with_filter_is_not_randomize() {
    let result = parse(
        "module m; int arr[$]; int y; \
         initial y = arr.sum with (item * 2); endmodule",
    );
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    let text = format!("{:?}", result.source.descriptions);
    assert!(text.contains("WithClause"), "{text}");
    assert!(!text.contains("RandomizeWith"), "{text}");
}

/// A compiler directive is not a statement — the A.6 statement grammar has no
/// directive production. A protected envelope inside a nested block ends just
/// before the if-block's `end`; dispatching `` `endprotect `` to
/// `parse_statement` consumed that `end` and desynced the rest of the file
/// (one such envelope produced 15 cascade errors in the corpus).
#[test]
fn protected_envelope_in_block_keeps_the_blocks_end() {
    let result =
        parse("module m; initial begin if (1) begin `protect x = 1; `endprotect end end endmodule");
    assert!(result.errors.is_empty(), "{:?}", result.errors);
}

/// Same desync at a function body's terminator: that loop guards on
/// `endfunction`, not `end`, so the skip must hand the token back untouched.
#[test]
fn protected_envelope_in_function_keeps_the_endfunction() {
    let result =
        parse("module m; function void f(); `protect x = 1; `endprotect endfunction endmodule");
    assert!(result.errors.is_empty(), "{:?}", result.errors);
}

/// And at a fork's `join`, which is the parallel block's terminator.
#[test]
fn protected_envelope_in_fork_keeps_the_join() {
    let result = parse("module m; initial fork `protect x = 1; `endprotect join endmodule");
    assert!(result.errors.is_empty(), "{:?}", result.errors);
}

/// §18.5.3: operator recursion retains the constraint implication separator.
#[test]
fn constraint_operator_boundary_neighbors() {
    for head in [
        "a ? b : d",
        "a && b",
        "a ? (b -> d) : b",
        "(a ? b : d)",
        "a ? b : (d ? a : b)",
    ] {
        let source =
            format!("class c; rand bit a,b,d; constraint k {{ {head} -> {{ d == 1; }} }} endclass");
        let result = parse(&source);
        assert!(result.errors.is_empty(), "{source}: {:?}", result.errors);
        let items = class_constraint_items(&result);
        assert!(
            matches!(
                items[0],
                crate::ast::decl::ConstraintItem::Implication { .. }
            ),
            "{items:?}"
        );
    }
}

/// §18.5.2: a concatenation followed by an operator remains an expression.
#[test]
fn constraint_concatenation_operator_neighbors() {
    for tail in ["<-> a", "== 2'b01", "!= 2'b00", "inside {1,2}", "|| a"] {
        let source =
            format!("class c; rand bit a,b,d; constraint k {{ if (a) {{b,d}} {tail}; }} endclass");
        let result = parse(&source);
        assert!(result.errors.is_empty(), "{source}: {:?}", result.errors);
        let items = class_constraint_items(&result);
        let crate::ast::decl::ConstraintItem::IfElse { then_item, .. } = &items[0] else {
            panic!("{items:?}")
        };
        assert!(
            !matches!(**then_item, crate::ast::decl::ConstraintItem::Block(_)),
            "{then_item:?}"
        );
    }
}

/// §10.3.1: declaration drive strengths survive parsing into elaboration.
#[test]
fn net_declaration_strength_pairs_survive_parsing() {
    for pair in [
        "weak1,weak0",
        "strong1,strong0",
        "pull1,pull0",
        "supply1,supply0",
        "strong1,weak0",
    ] {
        let source = format!("module top; wire ({pair}) w=1'b1; endmodule");
        let result = parse(&source);
        assert!(result.errors.is_empty(), "{source}: {:?}", result.errors);
        let Description::Module(module) = &result.source.descriptions[0] else {
            panic!("module")
        };
        let crate::ast::decl::ModuleItem::NetDeclaration(net) = &module.items[0] else {
            panic!("net")
        };
        assert_eq!(net.strength.as_deref(), Some(pair));
    }
}
