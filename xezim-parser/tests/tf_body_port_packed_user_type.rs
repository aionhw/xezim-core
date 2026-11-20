//! IEEE 1800-2023 §13.4, A.2.7: a subroutine body's tf_port_declaration
//! takes a data_type_or_implicit, and a user-defined type may carry packed
//! dimensions (A.2.2.1 `type_identifier { packed_dimension }`). In
//! `input s_t [1:0] in;` the type is `s_t` and the port is `in`. The parser
//! used to take `s_t` as the port name with an unpacked dimension, leaving
//! `in;` as an expression statement, so the strict pass reported the body's
//! next declaration as following a statement (§9.3.1). A port name with an
//! unpacked dimension, `input x [3:0];`, keeps its meaning.

use sv_parser::ast::Description;
use sv_parser::ast::decl::ModuleItem;
use sv_parser::ast::types::DataType;
use sv_parser::parse;
use sv_parser::strict_check::strict_diagnostics;

const SRC: &str = r#"
package p;
  typedef struct packed { logic a; logic b; } s_t;
  typedef struct packed { logic a; } t_t;
endpackage
module top;
  import p::*;
  localparam int N = 2;
  function automatic t_t [N-1:0] conv;
    input s_t [N-1:0] in;
    t_t [N-1:0] out;
    begin
      for (int i = 0; i < N; i++) out[i] = '{a: in[i].a};
      conv = out;
    end
  endfunction
  task automatic tk;
    output t_t [1:0] o;
    input s_t [1:0][1:0] a, b;
    input var s_t [1:0] c;
    input s_t [1:0] u [2];
    t_t [1:0] tmp;
    begin
      tmp = '0;
      o = tmp;
    end
  endtask
  function automatic logic legacy;
    input x [3:0];
    logic y;
    begin
      y = x[0];
      legacy = y;
    end
  endfunction
endmodule
"#;

/// (port name, `Some(packed dims)` of a user-defined type or `None` for an
/// implicit type, unpacked dims)
fn ports_of(items: &[ModuleItem], sub: &str) -> Vec<(String, Option<usize>, usize)> {
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
        .map(|p| {
            let packed = match &p.data_type {
                DataType::TypeReference { dimensions, .. } => Some(dimensions.len()),
                DataType::Implicit { .. } => None,
                other => panic!("port {}: unexpected type {other:?}", p.name.name),
            };
            (p.name.name.clone(), packed, p.dimensions.len())
        })
        .collect()
}

#[test]
fn body_port_of_packed_user_type_names_the_port() {
    let r = parse(SRC);
    assert!(r.errors.is_empty(), "{:?}", r.errors);
    let strict = strict_diagnostics(&r.source.descriptions);
    assert!(strict.is_empty(), "{strict:?}");
    let items = r
        .source
        .descriptions
        .iter()
        .find_map(|d| match d {
            Description::Module(m) if m.name.name == "top" => Some(&m.items),
            _ => None,
        })
        .expect("module top");
    assert_eq!(ports_of(items, "conv"), vec![("in".into(), Some(1), 0)]);
    assert_eq!(
        ports_of(items, "tk"),
        vec![
            ("o".into(), Some(1), 0),
            ("a".into(), Some(2), 0),
            ("b".into(), Some(2), 0),
            ("c".into(), Some(1), 0),
            ("u".into(), Some(1), 1),
        ]
    );
    assert_eq!(ports_of(items, "legacy"), vec![("x".into(), None, 1)]);
}
