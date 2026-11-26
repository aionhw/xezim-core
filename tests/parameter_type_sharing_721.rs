//! IEEE 1800-2023 §6.20.2 (aionhw/xezim#721): the explicitly typed value
//! parameters of one declaration hold one copy of its declared type, in
//! every instance of the definition. Each parameter of each instance used to
//! hold a copy of the whole type tree. What the type means stays per
//! instance: a range written with a parameter resolves with the parameters
//! of the instance, and a type that names a typedef of the instance is
//! scoped to that instance and not shared.

use std::rc::Rc;
use xezim_core::ast::types::DataType;

fn elaborate(src: &str) -> xezim_core::ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[src.to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .unwrap_or_else(|error| panic!("{error}\n{src}"))
    .1
}

const SRC: &str = r#"
package p;
  typedef struct packed { logic [7:0] a; logic [3:0] b; } pair_t;
  localparam pair_t PA = '{a: 8'h11, b: 4'h2}, PB = '{a: 8'h33, b: 4'h4};
endpackage
module leaf #(
  parameter int W = 8,
  parameter struct packed { logic [3:0] hi; logic [3:0] lo; } S0 = '0, S1 = '1,
  parameter logic [W-1:0] MASK = '1
) ();
  typedef logic [W-1:0] word_t;
  localparam word_t LOCAL = '1;
  localparam p::pair_t NAMED = p::PA;
  for (genvar i = 0; i < 2; i++) begin : g
    localparam logic [W-1:0] STEP = i + 1;
  end
endmodule
module other #(parameter int W = 8, parameter logic [W-1:0] MASK = '1) ();
endmodule
module top;
  localparam logic [3:0] TOP_A = 4'h5, TOP_B = 4'h6;
  leaf #(.W(8)) a ();
  leaf #(.W(16)) b ();
  leaf #(.W(8), .S1(8'h5a)) c ();
  other o ();
endmodule
"#;

fn shared<'a>(m: &'a xezim_core::ElaboratedModule, name: &str) -> &'a Rc<DataType> {
    m.param_decl_types
        .get_shared(name)
        .unwrap_or_else(|| panic!("no declared type for {name}"))
}

#[test]
fn instances_share_the_type_of_a_parameter_declaration() {
    let m = elaborate(SRC);
    for name in ["W", "S0", "S1", "MASK", "NAMED", "g[0].STEP", "g[1].STEP"] {
        let a = shared(&m, &format!("a.{name}"));
        // §6.20.2, §23.10: a range written with `W` holds the instance's
        // folded bounds, so `b` (W = 16) has a type of its own and `c`
        // (W = 8) shares `a`'s.
        let w_dependent = name == "MASK" || name.ends_with("STEP");
        for inst in ["b", "c"] {
            let same = Rc::ptr_eq(a, shared(&m, &format!("{inst}.{name}")));
            assert_eq!(same, !(w_dependent && inst == "b"), "{inst}.{name}");
        }
    }
    // The parameters of one declaration share it too, in a module, the top
    // and a package.
    assert!(Rc::ptr_eq(shared(&m, "a.S0"), shared(&m, "b.S1")));
    assert!(Rc::ptr_eq(
        shared(&m, "a.g[0].STEP"),
        shared(&m, "c.g[1].STEP")
    ));
    assert!(Rc::ptr_eq(shared(&m, "TOP_A"), shared(&m, "TOP_B")));
    assert!(Rc::ptr_eq(shared(&m, "p::PA"), shared(&m, "p::PB")));
    // Another declaration, or the same text in another definition, is
    // another type.
    assert!(!Rc::ptr_eq(shared(&m, "a.S0"), shared(&m, "a.MASK")));
    assert!(!Rc::ptr_eq(shared(&m, "a.MASK"), shared(&m, "o.MASK")));
}

#[test]
fn a_shared_parameter_type_resolves_per_instance() {
    let m = elaborate(SRC);
    for (inst, w) in [("a", 8u32), ("b", 16), ("c", 8)] {
        let params: xezim_core::hasher::HashMap<String, xezim_core::Value> = m
            .parameters
            .iter()
            .filter_map(|(k, v)| {
                k.strip_prefix(&format!("{inst}."))
                    .map(|bare| (bare.to_string(), v.clone()))
            })
            .collect();
        for name in ["MASK", "g[1].STEP"] {
            let width = xezim_core::elaborate::resolve_type_width(
                shared(&m, &format!("{inst}.{name}")),
                Some(&params),
                Some(&m.typedefs),
            );
            assert_eq!(
                width, w,
                "{inst}.{name} read with its instance's parameters"
            );
        }
        assert_eq!(m.parameters[&format!("{inst}.MASK")].width, w);
        assert_eq!(m.parameters[&format!("{inst}.LOCAL")].width, w);
        assert_eq!(m.parameters[&format!("{inst}.g[1].STEP")].to_u64(), Some(2));
        assert_eq!(m.parameters[&format!("{inst}.NAMED")].to_u64(), Some(0x112));
    }
    assert_eq!(m.parameters["a.S1"].to_u64(), Some(0xff));
    assert_eq!(m.parameters["c.S1"].to_u64(), Some(0x5a));
}

#[test]
fn a_parameter_type_naming_an_instance_typedef_is_not_shared() {
    let m = elaborate(SRC);
    for (inst, other) in [("a", "b"), ("a", "c")] {
        let mine = shared(&m, &format!("{inst}.LOCAL"));
        let theirs = shared(&m, &format!("{other}.LOCAL"));
        assert!(!Rc::ptr_eq(mine, theirs));
        for (ty, owner) in [(mine, inst), (theirs, other)] {
            let DataType::TypeReference { name, .. } = &**ty else {
                panic!("named type expected, got {ty:?}");
            };
            assert_eq!(name.name.name, format!("{owner}.word_t"));
        }
    }
}

/// The table has one entry for each typed parameter and, for 64 instances of
/// a definition with 8 parameters of one declaration, one type.
#[test]
fn many_instances_hold_one_type() {
    let mut src = String::from(
        "module leaf #(parameter struct packed {logic [1:0] f0; logic [1:0] f1;} \
         P0='0, P1='0, P2='0, P3='0, P4='0, P5='0, P6='0, P7='0)(); endmodule\nmodule top;\n",
    );
    for i in 0..64 {
        src += &format!("  leaf u{i}();\n");
    }
    src += "endmodule\n";
    let m = elaborate(&src);
    assert_eq!(m.param_decl_types.len(), 64 * 8);
    let first = shared(&m, "u0.P0");
    for i in 0..64 {
        for p in 0..8 {
            assert!(Rc::ptr_eq(first, shared(&m, &format!("u{i}.P{p}"))));
        }
    }
    assert_eq!(Rc::strong_count(first), 64 * 8);
}

/// The artifact holds the plain map it always did; a loaded design owns a
/// type per parameter, equal to the shared one it was written from.
#[test]
fn the_artifact_is_unchanged_by_sharing() {
    let m = elaborate(SRC);
    let dir = std::env::temp_dir().join(format!("xezim_core_param_types_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("mkdir");
    let path = dir.join("design.xez");
    xezim_core::write_compiled(&m, path.to_str().unwrap()).expect("write artifact");
    let bytes = std::fs::read(&path).expect("read artifact");
    let loaded = xezim_core::read_compiled_bytes(&bytes).expect("load artifact");
    assert_eq!(loaded.param_decl_types.len(), m.param_decl_types.len());
    assert!(!Rc::ptr_eq(
        shared(&loaded, "a.S0"),
        shared(&loaded, "b.S0")
    ));
    let config = bincode::config::standard();
    for name in ["a.S0", "b.MASK", "c.LOCAL", "o.MASK", "TOP_B", "p::PA"] {
        let encode = |m: &xezim_core::ElaboratedModule| {
            bincode::serde::encode_to_vec(m.param_decl_types.get(name).unwrap(), config).unwrap()
        };
        assert_eq!(encode(&loaded), encode(&m), "{name}");
    }
    // The map is written as a map of plain types.
    let plain: xezim_core::hasher::HashMap<String, DataType> = m
        .param_decl_types
        .iter()
        .map(|(name, ty)| (name.clone(), ty.clone()))
        .collect();
    let (decoded, _): (xezim_core::hasher::HashMap<String, DataType>, usize) =
        bincode::serde::decode_from_slice(
            &bincode::serde::encode_to_vec(&m.param_decl_types, config).unwrap(),
            config,
        )
        .unwrap();
    assert_eq!(decoded.len(), plain.len());
    for (name, ty) in &plain {
        assert_eq!(
            bincode::serde::encode_to_vec(&decoded[name], config).unwrap(),
            bincode::serde::encode_to_vec(ty, config).unwrap(),
            "{name}"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}
