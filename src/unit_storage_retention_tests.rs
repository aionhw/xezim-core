//! §3.12.1 / §6.7 / §6.8: a compilation-unit variable or net is one object.
//! The hierarchy root declares it once; no other definition receives a copy.

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
fn unit_storage_is_declared_once_in_the_root() {
    let (definitions, elab) =
        parse_and_elaborate_multi(&[SOURCE.to_string()], Some("top"), &[], &[], &[]).unwrap();
    assert_eq!(
        storage(&definitions["top"]),
        [
            "a",
            "b",
            "base",
            "c",
            "derived",
            "f",
            "spare",
            "unused_net",
            "unused_var"
        ]
    );
    // No other definition declares unit storage, whatever it names.
    assert!(storage(&definitions["via_net"]).is_empty());
    assert!(storage(&definitions["via_func"]).is_empty());
    assert_eq!(storage(&definitions["via_qualified"]), ["base"]);
    assert!(storage(&definitions["plain"]).is_empty());
    assert_eq!(storage(&definitions["never_used"]), ["q"]);
    // One signal each, under the root's flat name.
    for name in ["base", "spare", "derived", "unused_net", "unused_var"] {
        assert!(elab.signals.contains_key(name), "{name}");
        let copies: Vec<&String> = elab
            .signals
            .keys()
            .filter(|k| k.ends_with(&format!(".{name}")) || k.ends_with(&format!("::{name}")))
            .collect();
        // `u3.base` is the module's own variable.
        let own: &[&str] = if name == "base" { &["u3.base"] } else { &[] };
        assert_eq!(copies, own, "{name}");
    }
}

#[test]
fn unit_storage_named_by_a_unit_class_is_not_copied() {
    let source = r#"
int seen = 3;
class reader; function int get(); return seen; endfunction endclass
module child; endmodule
module top; child u(); endmodule
"#;
    let (definitions, elab) =
        parse_and_elaborate_multi(&[source.to_string()], Some("top"), &[], &[], &[]).unwrap();
    assert!(storage(&definitions["child"]).is_empty());
    assert_eq!(storage(&definitions["top"]), ["seen"]);
    assert!(!elab.signals.contains_key("u.seen"));
}

/// A root that declares the name keeps the unit object under the reserved
/// name, and a child's plain reference names that object.
#[test]
fn root_declaration_shadows_and_unit_storage_keeps_reserved_name() {
    let source = r#"
int g = 5;
module child(output int y); assign y = g; endmodule
module top; int g = 7; int y; child u(y); endmodule
"#;
    let (definitions, elab) =
        parse_and_elaborate_multi(&[source.to_string()], Some("top"), &[], &[], &[]).unwrap();
    assert_eq!(storage(&definitions["top"]), ["$unit::g", "g", "y"]);
    assert!(storage(&definitions["child"]).is_empty());
    assert!(elab.signals.contains_key("$unit::g"));
    assert!(!elab.signals.contains_key("u.g"));
    assert!(!elab.signals.contains_key("u.$unit::g"));
}

/// Several roots: the wrapper that instantiates them holds the storage, so
/// no top owns it.
#[test]
fn several_roots_share_one_unit_storage() {
    let source = r#"
int g = 5;
wire [3:0] n = 4'd9;
module ta; initial g = 6; endmodule
module tb; int g = 1; logic [3:0] y; assign y = n; endmodule
"#;
    let (definitions, elab) =
        parse_and_elaborate_multi(&[source.to_string()], None, &[], &[], &[]).unwrap();
    assert_eq!(storage(&definitions[crate::MULTI_TOP_WRAPPER]), ["g", "n"]);
    assert!(storage(&definitions["ta"]).is_empty());
    assert_eq!(storage(&definitions["tb"]), ["g", "y"]);
    assert!(elab.signals.contains_key("g"));
    assert!(elab.signals.contains_key("n"));
    assert!(elab.signals.contains_key("tb.g"));
    assert!(!elab.signals.contains_key("ta.g"));
    assert!(!elab.signals.contains_key("tb.n"));
}
