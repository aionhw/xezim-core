//! IEEE 1800-2023 §6.8 (aionhw/xezim#721): the signals of one declaration
//! hold one copy of its declared type, in every instance of the definition.
//! Each signal used to hold a copy of the whole type tree. What a type
//! means stays per instance: a range written with a parameter resolves with
//! the parameters of the instance the signal is in, and a type that names a
//! typedef of the instance is scoped to that instance and not shared.

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
endpackage
module leaf #(parameter int W = 8) (input logic clk);
  logic [W-1:0] r0, r1;
  logic [15:0] fixed;
  struct packed { logic [7:0] x; logic [W-1:0] y; } inl;
  p::pair_t named;
  typedef logic [W-1:0] word_t;
  word_t local_word;
  wire [W-1:0] n0;
  always @(posedge clk) begin
    r0 <= r1;
    fixed <= fixed + 1'b1;
    inl <= '0;
    named <= '0;
    local_word <= r0;
  end
  assign n0 = r0;
endmodule
module other (input logic clk);
  logic [15:0] fixed;
  always @(posedge clk) fixed <= ~fixed;
endmodule
module top;
  logic clk;
  leaf #(8) a (.clk(clk));
  leaf #(16) b (.clk(clk));
  leaf #(8) c (.clk(clk));
  other o (.clk(clk));
endmodule
"#;

fn shared<'a>(m: &'a xezim_core::ElaboratedModule, name: &str) -> &'a Rc<DataType> {
    m.var_decl_types
        .get_shared(name)
        .unwrap_or_else(|| panic!("no declared type for {name}"))
}

#[test]
fn instances_share_the_type_of_a_declaration() {
    let m = elaborate(SRC);
    for name in ["r0", "fixed", "inl", "named", "n0"] {
        let a = shared(&m, &format!("a.{name}"));
        for inst in ["b", "c"] {
            assert!(
                Rc::ptr_eq(a, shared(&m, &format!("{inst}.{name}"))),
                "{inst}.{name}"
            );
        }
    }
    // The declarators of one declaration share it too.
    assert!(Rc::ptr_eq(shared(&m, "a.r0"), shared(&m, "a.r1")));
    assert!(Rc::ptr_eq(shared(&m, "a.r0"), shared(&m, "b.r1")));
    // Another declaration, or the same text in another definition, is
    // another type.
    assert!(!Rc::ptr_eq(shared(&m, "a.r0"), shared(&m, "a.n0")));
    assert!(!Rc::ptr_eq(shared(&m, "a.fixed"), shared(&m, "o.fixed")));
}

#[test]
fn a_shared_type_resolves_per_instance() {
    let m = elaborate(SRC);
    for (inst, w) in [("a", 8), ("b", 16), ("c", 8)] {
        for name in ["r0", "r1", "n0", "local_word"] {
            assert_eq!(
                m.signals[&format!("{inst}.{name}")].width,
                w,
                "{inst}.{name}"
            );
        }
        assert_eq!(m.signals[&format!("{inst}.fixed")].width, 16);
        assert_eq!(m.signals[&format!("{inst}.inl")].width, 8 + w);
        assert_eq!(m.signals[&format!("{inst}.named")].width, 12);
        let params: xezim_core::hasher::HashMap<String, xezim_core::Value> = m
            .parameters
            .iter()
            .filter_map(|(k, v)| {
                k.strip_prefix(&format!("{inst}."))
                    .map(|bare| (bare.to_string(), v.clone()))
            })
            .collect();
        let width = xezim_core::elaborate::resolve_type_width(
            shared(&m, &format!("{inst}.r0")),
            Some(&params),
            Some(&m.typedefs),
        );
        assert_eq!(width, w, "{inst}.r0 read with its instance's parameters");
    }
}

#[test]
fn a_type_naming_an_instance_typedef_is_not_shared() {
    let m = elaborate(SRC);
    for (inst, other) in [("a", "b"), ("a", "c")] {
        let mine = shared(&m, &format!("{inst}.local_word"));
        let theirs = shared(&m, &format!("{other}.local_word"));
        assert!(!Rc::ptr_eq(mine, theirs));
        for (ty, owner) in [(mine, inst), (theirs, other)] {
            let DataType::TypeReference { name, .. } = &**ty else {
                panic!("named type expected, got {ty:?}");
            };
            assert_eq!(name.name.name, format!("{owner}.word_t"));
        }
    }
}

/// The artifact holds the plain map it always did; a loaded design owns a
/// type per signal, equal to the shared one it was written from.
#[test]
fn the_artifact_is_unchanged_by_sharing() {
    let m = elaborate(SRC);
    let dir = std::env::temp_dir().join(format!("xezim_core_decl_types_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("mkdir");
    let path = dir.join("design.xez");
    xezim_core::write_compiled(&m, path.to_str().unwrap()).expect("write artifact");
    let bytes = std::fs::read(&path).expect("read artifact");
    let loaded = xezim_core::read_compiled_bytes(&bytes).expect("load artifact");
    assert_eq!(loaded.var_decl_types.len(), m.var_decl_types.len());
    assert!(!Rc::ptr_eq(
        shared(&loaded, "a.r0"),
        shared(&loaded, "b.r0")
    ));
    for name in ["a.r0", "b.inl", "c.local_word", "o.fixed"] {
        let encode = |m: &xezim_core::ElaboratedModule| {
            let ty = m.var_decl_types.get(name).unwrap();
            bincode::serde::encode_to_vec(ty, bincode::config::standard()).unwrap()
        };
        assert_eq!(encode(&loaded), encode(&m), "{name}");
    }
    let _ = std::fs::remove_dir_all(&dir);
}
