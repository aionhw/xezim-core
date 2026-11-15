//! §3.12.1 / §6.7 / §6.8: compilation-unit variables and nets reach the
//! definitions that name them (directly, through a unit subroutine, a unit
//! class or another unit declaration) without being copied into the others.

use crate::ast::decl::ModuleItem;
use crate::{SourceDefinition, parse_and_elaborate_multi};

fn storage(definition: &SourceDefinition) -> Vec<&str> {
    let mut names: Vec<&str> = definition
        .items()
        .iter()
        .flat_map(|item| match item {
            ModuleItem::DataDeclaration(d) => {
                d.declarators.iter().map(|v| v.name.name.as_str()).collect()
            }
            ModuleItem::NetDeclaration(n) => {
                n.declarators.iter().map(|v| v.name.name.as_str()).collect()
            }
            _ => Vec::new(),
        })
        .collect();
    names.sort_unstable();
    names
}

const SOURCE: &str = r#"
int base = 40, spare = 1;
int unused_var = 7;
wire [7:0] derived = base + 2;
wire [7:0] unused_net = 8'd9;
function automatic int bump(int n); return n + spare; endfunction
module via_net(output int y); assign y = derived; endmodule
module via_func(output int y); assign y = bump(1); endmodule
module via_qualified(output int y); int base = 5; assign y = $unit::base + base; endmodule
module plain(input int a, output int y); assign y = a + 1; endmodule
module never_used; logic q; endmodule
module top;
  int a, b, c, f;
  via_net u1(a);
  via_func u2(b);
  via_qualified u3(c);
  plain u4(3, f);
endmodule
"#;

#[test]
fn unit_storage_reaches_only_the_definitions_that_name_it() {
    let (definitions, elab) =
        parse_and_elaborate_multi(&[SOURCE.to_string()], Some("top"), &[], &[], &[]).unwrap();
    // The carrier keeps every unit declaration.
    assert_eq!(
        storage(&definitions["top"]),
        ["a", "b", "base", "c", "derived", "f", "spare", "unused_net", "unused_var"]
    );
    // A net's initializer brings the variable it reads.
    assert_eq!(storage(&definitions["via_net"]), ["base", "derived"]);
    // A unit function brings the storage its body reads.
    assert_eq!(storage(&definitions["via_func"]), ["spare"]);
    // `$unit::base` names the unit variable beside a local `base`.
    assert_eq!(storage(&definitions["via_qualified"]), ["$unit::base", "base"]);
    assert!(storage(&definitions["plain"]).is_empty());
    assert_eq!(storage(&definitions["never_used"]), ["q"]);
    // No signal of an unrelated instance stands for unit storage.
    assert!(!elab.signals.contains_key("u4.base"));
    assert!(!elab.signals.contains_key("u4.derived"));
    assert!(elab.signals.contains_key("u1.derived"));
}

#[test]
fn unit_storage_named_by_a_unit_class_stays_in_every_definition() {
    let source = r#"
int seen = 3;
class reader; function int get(); return seen; endfunction endclass
module child; endmodule
module top; child u(); endmodule
"#;
    let (definitions, _) =
        parse_and_elaborate_multi(&[source.to_string()], Some("top"), &[], &[], &[]).unwrap();
    assert_eq!(storage(&definitions["child"]), ["seen"]);
    assert_eq!(storage(&definitions["top"]), ["seen"]);
}
