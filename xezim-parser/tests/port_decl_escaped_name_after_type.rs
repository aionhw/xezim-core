//! IEEE 1800-2023 §5.6.1, §13.4, §23.2.2.1: an escaped identifier is an
//! identifier, so in `input s_t \in ;` (a subroutine body port) and in a
//! module's non-ANSI `input s_t \pi ;` the user-defined type is `s_t` and the
//! port is `in` / `pi`, as with a plain name. The type lookahead only took an
//! identifier as a type when a plain identifier followed it, so `s_t` became
//! the port and the escaped name was left behind as a statement.

use sv_parser::ast::Description;
use sv_parser::ast::decl::ModuleItem;
use sv_parser::ast::types::DataType;
use sv_parser::parse;
use sv_parser::strict_check::strict_diagnostics;

const SRC: &str = r#"
typedef struct packed { logic a; logic b; } s_t;
module m (\pi , \pk , y);
  input s_t \pi ;
  input s_t [1:0] \pk ;
  output logic y;
  assign y = \pi .b ^ \pk [1].a;
endmodule
module top;
  function automatic logic f1;
    input s_t \in1 ;
    logic r;
    begin
      r = \in1 .b;
      f1 = r;
    end
  endfunction
  function automatic logic f2;
    input s_t [1:0] \in2 ;
    logic r;
    begin
      r = \in2 [1].a;
      f2 = r;
    end
  endfunction
  task automatic tk;
    output s_t \o1 , \o2 ;
    begin
      \o1 = '0;
      \o2 = '1;
    end
  endtask
endmodule
"#;

/// (port name, packed dims of its user-defined type)
fn tf_ports(items: &[ModuleItem], sub: &str) -> Vec<(String, usize)> {
    let ports = items
        .iter()
        .find_map(|it| match it {
            ModuleItem::FunctionDeclaration(f) if f.name.name.name == sub => Some(&f.ports),
            ModuleItem::TaskDeclaration(t) if t.name.name.name == sub => Some(&t.ports),
            _ => None,
        })
        .unwrap_or_else(|| panic!("subroutine {sub}"));
    ports
        .iter()
        .map(|p| match &p.data_type {
            DataType::TypeReference { dimensions, .. } => (p.name.name.clone(), dimensions.len()),
            other => panic!("port {}: unexpected type {other:?}", p.name.name),
        })
        .collect()
}

fn module_items<'a>(descs: &'a [Description], name: &str) -> &'a [ModuleItem] {
    descs
        .iter()
        .find_map(|d| match d {
            Description::Module(m) if m.name.name == name => Some(m.items.as_slice()),
            _ => None,
        })
        .unwrap_or_else(|| panic!("module {name}"))
}

#[test]
fn escaped_port_name_after_a_user_type() {
    let r = parse(SRC);
    assert!(r.errors.is_empty(), "{:?}", r.errors);
    let strict = strict_diagnostics(&r.source.descriptions);
    assert!(strict.is_empty(), "{strict:?}");
    let top = module_items(&r.source.descriptions, "top");
    assert_eq!(tf_ports(top, "f1"), vec![("in1".into(), 0)]);
    assert_eq!(tf_ports(top, "f2"), vec![("in2".into(), 1)]);
    assert_eq!(
        tf_ports(top, "tk"),
        vec![("o1".into(), 0), ("o2".into(), 0)]
    );
    let m = module_items(&r.source.descriptions, "m");
    let ports: Vec<(String, usize)> = m
        .iter()
        .filter_map(|it| match it {
            ModuleItem::PortDeclaration(pd) => Some(pd),
            _ => None,
        })
        .flat_map(|pd| {
            let packed = match &pd.data_type {
                DataType::TypeReference { dimensions, .. } => dimensions.len(),
                _ => usize::MAX,
            };
            pd.declarators
                .iter()
                .map(move |d| (d.name.name.clone(), packed))
        })
        .collect();
    assert_eq!(
        ports,
        vec![("pi".into(), 0), ("pk".into(), 1), ("y".into(), usize::MAX)]
    );
}
