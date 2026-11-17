//! IEEE 1800-2023 §3.12.1, §35.5.4 (aionhw/xezim#721): a compilation-unit DPI
//! import is one declaration of the unit. A definition receives the imports
//! it names, directly or through a unit subroutine it calls; every import
//! used to be copied into every definition. The import itself registers
//! once, under its global name, whichever definitions hold it.

use xezim_core::{SourceDefinition, ast::decl::ModuleItem};

fn elaborate(
    source: &str,
) -> (
    xezim_core::hasher::HashMap<String, SourceDefinition>,
    xezim_core::ElaboratedModule,
) {
    xezim_core::parse_and_elaborate_multi(
        &[source.to_string()],
        Some("top"),
        &[],
        &["unit.sv".to_string()],
        &[],
    )
    .unwrap_or_else(|error| panic!("{error}\n{source}"))
}

fn imports(definition: &SourceDefinition) -> Vec<String> {
    let mut names: Vec<String> = definition
        .items()
        .iter()
        .filter_map(|item| match item {
            ModuleItem::DPIImport(import) => Some(match &import.proto {
                xezim_core::ast::decl::DPIProto::Function(f) => f.name.name.name.clone(),
                xezim_core::ast::decl::DPIProto::Task(t) => t.name.name.name.clone(),
            }),
            _ => None,
        })
        .collect();
    names.sort_unstable();
    names
}

const SRC: &str = r#"
import "DPI-C" function int c_direct(input int v);
import "DPI-C" function int c_through_function(input int v);
import "DPI-C" context task c_task(input int v);
import "DPI-C" pure function int c_unused(input int v);
function automatic int unit_wrap(input int v);
  return c_through_function(v) + 1;
endfunction
module calls_import (output int q);
  initial q = c_direct(3);
endmodule
module calls_wrapper (output int q);
  initial q = unit_wrap(4);
endmodule
module calls_task;
  initial c_task(5);
endmodule
module calls_nothing (output int q);
  assign q = 7;
endmodule
module top;
  int a, b, c, d;
  calls_import u_a (.q(a));
  calls_wrapper u_b (.q(b));
  calls_task u_t ();
  calls_nothing u_n0 (.q(c));
  calls_nothing u_n1 (.q(d));
endmodule
"#;

#[test]
fn a_definition_receives_the_unit_imports_it_names() {
    let (defs, design) = elaborate(SRC);
    assert_eq!(imports(&defs["calls_import"]), ["c_direct"]);
    assert_eq!(imports(&defs["calls_wrapper"]), ["c_through_function"]);
    assert_eq!(imports(&defs["calls_task"]), ["c_task"]);
    assert!(imports(&defs["calls_nothing"]).is_empty());
    // The root keeps every declaration of the unit.
    assert_eq!(
        imports(&defs["top"]),
        ["c_direct", "c_task", "c_through_function", "c_unused"]
    );
    // One registration each, under the global name (§35.5.2).
    let mut registered: Vec<&str> = design.dpi_imports.keys().map(String::as_str).collect();
    registered.sort_unstable();
    assert_eq!(
        registered,
        ["c_direct", "c_task", "c_through_function", "c_unused"]
    );
    assert_eq!(design.dpi_imports["c_task"].c_name, "c_task");
    assert!(design.functions.contains_key("u_b.unit_wrap"));
    assert!(!design.functions.contains_key("u_n0.unit_wrap"));
}

/// 64 imports and 32 definitions that name none of them held 64 x 32
/// injected declarations; now the root's 64.
#[test]
fn unused_unit_imports_are_held_once() {
    let mut source = String::new();
    for i in 0..64 {
        source.push_str(&format!(
            "import \"DPI-C\" function int c_fn{i}(input int v);\n"
        ));
    }
    for i in 0..32 {
        source.push_str(&format!(
            "module m{i} (output int q); assign q = {i}; endmodule\n"
        ));
    }
    source.push_str("module top;\n");
    for i in 0..32 {
        source.push_str(&format!("  int q{i}; m{i} u{i} (.q(q{i}));\n"));
    }
    source.push_str("  initial q0 = c_fn9(1);\nendmodule\n");
    let (defs, design) = elaborate(&source);
    let injected: usize = defs.values().map(|d| imports(d).len()).sum();
    assert_eq!(injected, 64);
    assert_eq!(imports(&defs["top"]).len(), 64);
    assert_eq!(design.dpi_imports.len(), 64);
}
