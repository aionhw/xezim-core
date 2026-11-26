//! IEEE 1800-2023 §13.5: a formal written with neither a data type nor a
//! direction takes the data type of the previous formal (`input int a, b`:
//! `b` is an `int`); the first formal, or one with its own direction, is
//! `logic`. The parser left such a formal untyped, so the simulator did not
//! size `b` like `a`, and a DPI import passed it to C as an svLogic
//! (aionhw/xezim#1256).

use sv_parser::ast::Description;
use sv_parser::ast::decl::{DPIProto, FunctionPort, ModuleItem};
use sv_parser::ast::types::DataType;
use sv_parser::parse;

fn kind(p: &FunctionPort) -> &'static str {
    match &p.data_type {
        DataType::IntegerAtom { .. } => "atom",
        DataType::IntegerVector { dimensions, .. } if dimensions.is_empty() => "vector",
        DataType::IntegerVector { .. } => "packed vector",
        DataType::Implicit { dimensions, .. } if dimensions.is_empty() => "implicit",
        DataType::Implicit { .. } => "implicit packed",
        DataType::Simple { .. } => "simple",
        _ => "other",
    }
}

#[test]
fn untyped_formal_without_direction_takes_previous_type() {
    let r = parse(
        r#"
module top;
  function int f(input int a, b, output logic [7:0] c, d, input e);
    return a;
  endfunction
  task t(string s, q[$], input [3:0] u, w);
  endtask
  import "DPI-C" function int g(input int a, b);
endmodule
"#,
    );
    assert!(r.errors.is_empty(), "{:?}", r.errors);
    let Description::Module(m) = &r.source.descriptions[0] else {
        panic!("module expected");
    };
    let mut seen = Vec::new();
    for item in &m.items {
        match item {
            ModuleItem::FunctionDeclaration(fd) => {
                seen.push(("f", fd.ports.iter().map(kind).collect::<Vec<_>>()));
            }
            ModuleItem::TaskDeclaration(td) => {
                seen.push(("t", td.ports.iter().map(kind).collect::<Vec<_>>()));
            }
            ModuleItem::DPIImport(di) => {
                if let DPIProto::Function(fd) = &di.proto {
                    seen.push(("g", fd.ports.iter().map(kind).collect::<Vec<_>>()));
                }
            }
            _ => {}
        }
    }
    assert_eq!(
        seen,
        [
            (
                "f",
                vec!["atom", "atom", "packed vector", "packed vector", "implicit"]
            ),
            (
                "t",
                vec!["simple", "simple", "implicit packed", "implicit packed"]
            ),
            ("g", vec!["atom", "atom"]),
        ]
    );
}
