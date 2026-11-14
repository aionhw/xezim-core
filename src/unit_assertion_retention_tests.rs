//! §3.12.1 / §16.8 / §16.12: unit assertions remain visible without copying
//! unused expression trees into every module definition.

use crate::ast::decl::ModuleItem;
use crate::{SourceDefinition, parse_and_elaborate_multi};

fn names(definition: &SourceDefinition) -> Vec<&str> {
    definition
        .items()
        .iter()
        .filter_map(|item| match item {
            ModuleItem::PropertyDeclaration(p) => Some(p.name.name.as_str()),
            ModuleItem::SequenceDeclaration(s) => Some(s.name.name.as_str()),
            _ => None,
        })
        .collect()
}

#[test]
fn unused_unit_assertions_have_one_definition_carrier() {
    let mut source = "sequence unused_s(logic x); x; endsequence\nproperty unused_p(logic x); unused_s(x); endproperty\n".to_string();
    for i in 0..64 {
        source.push_str(&format!("module unused_{i}; endmodule\n"));
    }
    source.push_str("module top; endmodule\n");
    let (definitions, _) =
        parse_and_elaborate_multi(&[source], Some("top"), &[], &[], &[]).unwrap();
    assert_eq!(names(&definitions["top"]).len(), 2);
    for i in 0..64 {
        assert!(names(&definitions[&format!("unused_{i}")]).is_empty());
    }
}

#[test]
fn used_unit_property_keeps_its_sequence_dependency() {
    let source = r#"
sequence needed_s(logic x); x; endsequence
property needed_p(logic x); needed_s(x); endproperty
property unused_p(logic x); !x; endproperty
module child(input logic clk, input logic value);
  a: assert property (@(posedge clk) needed_p(value));
endmodule
module unused; endmodule
module top;
  logic clk=0;
  child u(clk, 1'b1);
endmodule
"#;
    let (definitions, _) =
        parse_and_elaborate_multi(&[source.to_string()], Some("top"), &[], &[], &[]).unwrap();
    let child = names(&definitions["child"]);
    assert!(child.contains(&"needed_p"));
    assert!(child.contains(&"needed_s"));
    assert!(!child.contains(&"unused_p"));
    assert_eq!(names(&definitions["top"]).len(), 3);
}
