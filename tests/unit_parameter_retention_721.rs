//! IEEE 1800-2023 §3.12.1 / §6.20: unit constants retain lexical visibility
//! without multiplying unused declaration ownership across the hierarchy.

use xezim_core::{
    SourceDefinition,
    ast::decl::{ModuleItem, ParameterKind},
};

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
    .expect("elaborate")
}

fn constants(definition: &SourceDefinition) -> Vec<String> {
    definition
        .items()
        .iter()
        .filter_map(|item| match item {
            ModuleItem::LocalparamDeclaration(p) => Some(match &p.kind {
                ParameterKind::Data { assignments, .. } => assignments
                    .iter()
                    .map(|a| a.name.name.clone())
                    .collect::<Vec<_>>(),
                ParameterKind::Type { assignments } => assignments
                    .iter()
                    .map(|a| a.name.name.clone())
                    .collect::<Vec<_>>(),
            }),
            _ => None,
        })
        .flatten()
        .collect()
}

#[test]
fn unused_unit_constants_are_owned_once_not_per_definition_or_instance() {
    let mut source = String::new();
    for i in 0..512 {
        source.push_str(&format!("localparam int UNIT_P_{i}={i};\n"));
    }
    source.push_str("module leaf; endmodule\n");
    for i in 0..256 {
        source.push_str(&format!("module unused_{i}; endmodule\n"));
    }
    source.push_str("module top;\n");
    for i in 0..256 {
        source.push_str(&format!("leaf u{i}();\n"));
    }
    source.push_str("endmodule\n");
    let (defs, design) = elaborate(&source);
    assert_eq!(constants(&defs["top"]).len(), 512);
    assert!(constants(&defs["leaf"]).is_empty());
    for i in 0..256 {
        assert!(constants(&defs[&format!("unused_{i}")]).is_empty());
    }
    // Previously 512 * (256 + 1) entries in each table, despite no use.
    assert_eq!(design.parameters.len(), 512);
    assert_eq!(design.param_decl_types.len(), 512);
    assert!(!design.signals.contains_key("u0.UNIT_P_0"));
    assert_eq!(design.parameters["UNIT_P_511"].to_u64(), Some(511));
}

#[test]
fn unused_module_parameters_remain_instance_objects() {
    let (_, design) = elaborate(
        r#"
localparam int UNUSED_UNIT=99;
module leaf #(parameter int OWN=3);
  localparam int OWN_LOCAL=OWN+1;
endmodule
module top; leaf #(.OWN(7)) a(); leaf b(); endmodule
"#,
    );
    assert_eq!(design.parameters.len(), 5);
    assert_eq!(design.parameters["a.OWN"].to_u64(), Some(7));
    assert_eq!(design.parameters["a.OWN_LOCAL"].to_u64(), Some(8));
    assert_eq!(design.parameters["b.OWN"].to_u64(), Some(3));
    assert_eq!(design.parameters["b.OWN_LOCAL"].to_u64(), Some(4));
    for name in ["a.OWN", "a.OWN_LOCAL", "b.OWN", "b.OWN_LOCAL"] {
        let signal_key = design.signals.shared_key(name).expect("signal key");
        let type_key = design.param_decl_types.shared_key(name).expect("type key");
        assert!(
            signal_key.ptr_eq(type_key),
            "{name}: map keys share storage"
        );
        assert!(
            signal_key.ptr_eq(&design.signals[name].name),
            "{name}: signal name shares storage"
        );
    }
}

#[test]
fn artifact_round_trip_preserves_shared_parameter_names() {
    let (_, design) = elaborate(
        "module leaf; localparam int P=37; endmodule module top; leaf a(), b(); endmodule",
    );
    let path = std::env::temp_dir().join(format!(
        "xezim_core_shared_names_{}.xez",
        std::process::id()
    ));
    xezim_core::write_compiled(&design, path.to_str().unwrap()).expect("write artifact");
    let from_file = xezim_core::read_compiled(path.to_str().unwrap())
        .expect("read artifact")
        .expect("compiled artifact");
    let bytes = std::fs::read(&path).expect("read bytes");
    let from_bytes = xezim_core::read_compiled_bytes(&bytes).expect("read artifact bytes");
    std::fs::remove_file(&path).expect("remove temporary artifact");
    for decoded in [from_file, from_bytes] {
        for name in ["a.P", "b.P"] {
            assert_eq!(decoded.parameters[name].to_u64(), Some(37));
            let key = decoded.signals.shared_key(name).expect("signal key");
            assert!(key.ptr_eq(&decoded.signals[name].name));
            assert!(key.ptr_eq(decoded.param_decl_types.shared_key(name).expect("type key")));
        }
    }
}

#[test]
fn dependencies_widths_hierarchical_reads_and_shadowing_are_preserved() {
    let (defs, design) = elaborate(
        r#"
localparam int BASE=3, WIDTH=BASE+2;
localparam int HIER=17;
localparam int SHADOW=4;
localparam int UNUSED=99;
module leaf;
  localparam int SHADOW=7;
  localparam int RESULT=WIDTH+SHADOW;
  logic [WIDTH-1:0] word;
endmodule
module top;
  leaf a(), b();
  initial $display("%0d", a.HIER);
endmodule
"#,
    );
    let names = constants(&defs["leaf"]);
    for name in ["BASE", "WIDTH", "HIER"] {
        assert!(names.iter().any(|n| n == name), "{names:?}");
    }
    assert_eq!(names.iter().filter(|n| *n == "SHADOW").count(), 1);
    assert!(!names.iter().any(|n| n == "UNUSED"));
    for instance in ["a", "b"] {
        assert_eq!(design.signals[&format!("{instance}.word")].width, 5);
        assert_eq!(
            design.parameters[&format!("{instance}.RESULT")].to_u64(),
            Some(12)
        );
        assert_eq!(
            design.parameters[&format!("{instance}.HIER")].to_u64(),
            Some(17)
        );
    }
}

#[test]
fn unit_function_typedef_class_and_variable_dependencies_are_retained() {
    let (defs, design) = elaborate(
        r#"
localparam int FN_VALUE=11;
localparam int TYPE_WIDTH=6;
localparam int CLASS_VALUE=13;
localparam int INITIAL_VALUE=19;
localparam int UNUSED=99;
function automatic int unit_fn(); return FN_VALUE; endfunction
typedef logic [TYPE_WIDTH-1:0] word_t;
class reader; function int get(); return CLASS_VALUE; endfunction endclass
int unit_variable=INITIAL_VALUE;
module leaf;
  localparam int RESULT=unit_fn();
  word_t word;
  reader obj;
endmodule
module top; leaf a(), b(); endmodule
"#,
    );
    let names = constants(&defs["leaf"]);
    for name in ["FN_VALUE", "TYPE_WIDTH", "CLASS_VALUE", "INITIAL_VALUE"] {
        assert!(names.iter().any(|n| n == name), "{names:?}");
    }
    assert!(!names.iter().any(|n| n == "UNUSED"));
    assert_eq!(design.parameters["a.RESULT"].to_u64(), Some(11));
    assert_eq!(design.signals["a.word"].width, 6);
    assert!(design.signals.contains_key("a.unit_variable"));
    assert!(design.signals.contains_key("b.unit_variable"));
}

#[test]
fn multiple_sources_and_automatic_roots_keep_one_unused_carrier() {
    let (defs, design) = xezim_core::parse_and_elaborate_multi(
        &[
            "localparam int USED=5; localparam int UNUSED=99; module leaf; localparam int RESULT=USED; endmodule module first; leaf a(); endmodule".to_string(),
            "module second; leaf b(); endmodule".to_string(),
        ], None, &[], &["first.sv".to_string(), "second.sv".to_string()], &[],
    ).expect("elaborate multiple roots");
    assert!(constants(&defs["first"]).iter().any(|n| n == "UNUSED"));
    assert!(!constants(&defs["second"]).iter().any(|n| n == "UNUSED"));
    assert!(!constants(&defs["leaf"]).iter().any(|n| n == "UNUSED"));
    assert_eq!(design.parameters["first.a.RESULT"].to_u64(), Some(5));
    assert_eq!(design.parameters["second.b.RESULT"].to_u64(), Some(5));
}
