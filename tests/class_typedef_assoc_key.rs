//! An associative array key typed by a class typedef over a class parameter
//! has that typedef's width (§6.18, §8.25).
fn elaborate(source: &str) -> xezim_core::ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[source.to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .expect("elaborate")
    .1
}

#[test]
fn class_typedef_key_takes_the_class_parameter_width() {
    let design = elaborate(
        r#"
module top #(int AW = 8); child c(); endmodule
module child;
class mem #(int AW = 32);
  typedef logic [AW-1:0] addr_t;
  typedef logic [11:0] fixed_t;
  typedef addr_t chain_t;
  logic [7:0] m[addr_t];
  logic [7:0] f[fixed_t];
  logic [7:0] g[chain_t];
  localparam int DEPTH = AW;
  typedef logic [$clog2(DEPTH):0] log_t;
  logic [7:0] q[log_t];
endclass
mem h; endmodule
"#,
    );
    let c = &design.classes["mem"];
    assert_eq!(c.assoc_index_props.get("m"), Some(&(32, false)));
    assert_eq!(c.assoc_index_props.get("f"), Some(&(12, false)));
    assert_eq!(c.assoc_index_props.get("g"), Some(&(32, false)));
    // Only the keys that depend on a class parameter are re-sized per object.
    assert!(c.assoc_key_decl_types.contains_key("m"));
    assert!(c.assoc_key_decl_types.contains_key("g"));
    assert!(c.assoc_key_decl_types.contains_key("q"));
    assert!(!c.assoc_key_decl_types.contains_key("f"));
}
