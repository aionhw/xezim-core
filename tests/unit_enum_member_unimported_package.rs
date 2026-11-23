//! IEEE 1800-2023 §26.3, §6.19: a package's enum members are visible only
//! through an import or a `pkg::` prefix. Registering an un-imported package
//! must not replace the bare entry of a `$unit` or module enum member of the
//! same name; the package's member stays reachable as `pkg::NAME`.

fn elaborate(src: &str) -> xezim_core::ElaboratedModule {
    let (_, d) =
        xezim_core::parse_and_elaborate_multi(&[src.into()], Some("t"), &[], &["t.sv".into()], &[])
            .expect("elaborate");
    d
}

#[test]
fn unit_member_keeps_its_bare_entry() {
    let d = elaborate(
        r#"
typedef enum logic [2:0] {EEW_NONE, EEW1, EEW8} EEW_e;
package tb_pkg;
  typedef enum int {EEW_NONE = 0, EEW1 = 1, EEW8 = 8} eew_e;
endpackage
module t;
  EEW_e e;
  initial e = EEW8;
endmodule
"#,
    );
    assert_eq!(d.parameters["EEW8"].to_i64(), Some(2));
    assert_eq!(d.signals["EEW8"].width, 3);
    assert_eq!(d.parameters["tb_pkg::EEW8"].to_i64(), Some(8));
}

/// §26.3: a module constant reads the imported enum member ahead of the
/// parameter in the enclosing compilation unit.
#[test]
fn imported_member_in_a_constant_beats_unit_parameter() {
    let d = elaborate(
        r#"
parameter RED = 0;
package p; typedef enum int { RED = 64 } op_t; endpackage
module t;
  import p::*;
  localparam int SELECTED = RED;
endmodule
"#,
    );
    assert_eq!(d.parameters["SELECTED"].to_i64(), Some(64));
}

#[test]
fn module_member_keeps_its_bare_entry() {
    let d = elaborate(
        r#"
package tb_pkg;
  typedef enum int {EEW_NONE = 0, EEW1 = 1, EEW8 = 8} eew_e;
  localparam int PE = EEW8;
endpackage
module t;
  typedef enum logic [2:0] {EEW_NONE, EEW1, EEW8} EEW_e;
  EEW_e e;
  initial e = EEW8;
endmodule
"#,
    );
    assert_eq!(d.parameters["EEW8"].to_i64(), Some(2));
    assert_eq!(d.signals["EEW8"].width, 3);
    assert_eq!(d.parameters["tb_pkg::EEW8"].to_i64(), Some(8));
    assert_eq!(d.parameters["tb_pkg::PE"].to_i64(), Some(8));
}

#[test]
fn module_member_beats_a_wildcard_imported_member() {
    let d = elaborate(
        r#"
package tb_pkg;
  typedef enum int {EEW_NONE = 0, EEW1 = 1, EEW8 = 8} eew_e;
  localparam int PE = EEW8;
endpackage
module t;
  import tb_pkg::*;
  typedef enum logic [2:0] {EEW_NONE, EEW1, EEW8} EEW_e;
  EEW_e e;
  initial e = EEW8;
endmodule
"#,
    );
    assert_eq!(d.parameters["EEW8"].to_i64(), Some(2));
    assert_eq!(d.parameters["PE"].to_i64(), Some(8));
    assert_eq!(d.parameters["tb_pkg::PE"].to_i64(), Some(8));
}

#[test]
fn package_constants_still_read_their_own_member() {
    let d = elaborate(
        r#"
typedef enum logic [2:0] {EEW_NONE, EEW1, EEW8} EEW_e;
package tb_pkg;
  typedef enum int {EEW_NONE = 0, EEW1 = 1, EEW8 = 8} eew_e;
  localparam int PE = EEW8;
endpackage
module t;
  import tb_pkg::PE;
  localparam int L = PE;
  localparam int U = EEW8;
endmodule
"#,
    );
    assert_eq!(d.parameters["tb_pkg::PE"].to_i64(), Some(8));
    assert_eq!(d.parameters["L"].to_i64(), Some(8));
    assert_eq!(d.parameters["U"].to_i64(), Some(2));
}

#[test]
fn members_two_packages_declare_stay_qualified() {
    let d = elaborate(
        r#"
package p1;
  typedef enum logic [3:0] {A = 3, B = 4} e1_t;
endpackage
package p2;
  typedef enum logic [3:0] {A = 9, C = 10} e2_t;
endpackage
module t;
  import p1::*;
  int o;
  initial o = A;
endmodule
"#,
    );
    assert_eq!(d.parameters["p1::A"].to_i64(), Some(3));
    assert_eq!(d.parameters["p2::A"].to_i64(), Some(9));
    assert_eq!(d.parameters["B"].to_i64(), Some(4));
    assert_eq!(d.parameters["C"].to_i64(), Some(10));
}

/// Putting the `$unit` member back leaves the top module's own enum members
/// and typedefs alone: only `B` collides with the package, so the module's
/// `A` and its own `U` keep their values and width.
#[test]
fn only_the_colliding_unit_member_is_put_back() {
    let d = elaborate(
        r#"
typedef enum logic [2:0] {A = 1, B = 2} U;
package tb_pkg;
  typedef enum int {B = 8} P;
endpackage
module t;
  typedef enum logic [3:0] {A = 5} U;
  U u;
  initial u = A;
endmodule
"#,
    );
    assert_eq!(d.parameters["A"].to_i64(), Some(5));
    assert_eq!(d.signals["A"].width, 4);
    assert_eq!(d.parameters["B"].to_i64(), Some(2));
    assert_eq!(d.typedefs["U"], 4);
}

/// §6.19: `A[2]` declares `A0` and `A1`, and a package's `A0` collides with
/// the generated name like with any other.
#[test]
fn ranged_unit_member_keeps_its_bare_entry() {
    let d = elaborate(
        r#"
typedef enum int {A[2] = 1} U;
package tb_pkg;
  typedef enum int {A0 = 8, Z} P;
endpackage
module t;
  U u;
  initial u = A0;
endmodule
"#,
    );
    assert_eq!(d.parameters["A0"].to_i64(), Some(1));
    assert_eq!(d.parameters["A1"].to_i64(), Some(2));
    assert_eq!(d.parameters["tb_pkg::A0"].to_i64(), Some(8));
}

/// A `$unit` member initialized from a package parameter that reads one of
/// the package's own enum members is put back with the settled value.
#[test]
fn unit_member_from_a_package_parameter_keeps_its_value() {
    let d = elaborate(
        r#"
package p;
  typedef enum int {E = 3} T;
  localparam int K = E;
endpackage
typedef enum int {A = p::K, A2} U;
package q;
  typedef enum int {A = 8} Q;
endpackage
module t;
  U u;
  initial u = A;
endmodule
"#,
    );
    assert_eq!(d.parameters["A"].to_i64(), Some(3));
    assert_eq!(d.parameters["A2"].to_i64(), Some(4));
    assert_eq!(d.parameters["q::A"].to_i64(), Some(8));
}

/// IEEE 1800-2023 §6.19, §26.3. Qualification preserves the enum's
/// signedness, width and four-state value in a constant expression.
#[test]
fn imported_enum_constants_keep_their_declared_type() {
    let d = elaborate(
        r#"
package p;
  typedef enum int { RED = -1 } op_t;
  typedef enum bit [31:0] { MASK = '1 } mask_t;
  typedef enum logic [3:0] { UNK = 4'b1x0z } unknown_t;
  typedef enum logic signed [79:0] { WIDE = -1 } wide_t;
endpackage
package q;
  typedef enum int { RED, MASK, UNK, WIDE } collision_t;
endpackage
module t;
  import p::*;
  localparam bit NEG = RED < 0;
  localparam bit UNS = MASK < 0;
  localparam bit FOUR = UNK === 4'b1x0z;
  localparam bit WNEG = WIDE < 0;
endmodule
"#,
    );
    for (name, expected) in [("NEG", 1), ("UNS", 0), ("FOUR", 1), ("WNEG", 1)] {
        assert_eq!(d.parameters[name].to_u64(), Some(expected), "{name}");
    }
}
