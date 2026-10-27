//! Typed unpacked parameter elements remain constants in every scope (§6.20.2 / §26.3).
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
fn package_array_bounds_and_dependent_constants() {
    let design = elaborate(
        r#"
package p;
 localparam int A[4:5]='{17,29};
 localparam int B=A[5]+2;
 localparam int M[2][2]='{'{3,5},'{7,11}};
 localparam int N=M[0][1];
endpackage
module top; int memory[p::B]; endmodule
"#,
    );
    assert_eq!(design.arrays["p::A"], (4, 5, 32));
    assert_eq!(design.unpacked_decl_dims["p::A"], vec![(4, 5)]);
    assert_eq!(design.parameters["p::B"].to_i64(), Some(31));
    assert_eq!(design.parameters["p::N"].to_i64(), Some(5));
    assert_eq!(
        design.arrays["memory"].1 - design.arrays["memory"].0 + 1,
        31
    );
}

#[test]
fn negative_and_descending_package_indices() {
    let design = elaborate(
        r#"
package p; localparam int A[-2:-1]='{17,29}; localparam int B[5:4]='{31,43}; endpackage
module top; localparam int N=p::A[-1]; localparam int M=p::B[4]; endmodule
"#,
    );
    assert_eq!(design.parameters["N"].to_i64(), Some(29));
    assert_eq!(design.parameters["M"].to_i64(), Some(43));
    assert_eq!(design.unpacked_decl_dims["p::B"], vec![(5, 4)]);
}

#[test]
fn body_array_override_sizes_dependent_declarations() {
    let design = elaborate(
        r#"
module leaf;
 parameter int A[2]='{3,5}; localparam int N=A[1]+2; logic[N-1:0] q;
endmodule
module top; leaf u_default(); leaf #(.A('{7,9})) u_override(); endmodule
"#,
    );
    assert_eq!(design.parameters["u_default.N"].to_i64(), Some(7));
    assert_eq!(design.parameters["u_override.N"].to_i64(), Some(11));
    assert_eq!(design.signals["u_default.q"].width, 7);
    assert_eq!(design.signals["u_override.q"].width, 11);
    assert_eq!(design.parameters["u_override.A[1]"].to_i64(), Some(9));
}

#[test]
fn imported_array_elements_size_constants() {
    let design = elaborate(
        r#"
package p; localparam int A[2]='{3,5}; endpackage
module top; import p::A; localparam int N=A[1]+2; logic[N-1:0] q; endmodule
"#,
    );
    assert_eq!(design.parameters["N"].to_i64(), Some(7));
    assert_eq!(design.signals["q"].width, 7);
}

#[test]
fn qualified_out_of_bounds_does_not_select_local_homonym() {
    let design = elaborate(
        r#"
package p; localparam int A[1]='{17}; endpackage
module top; localparam int A[2]='{91,93}; localparam int N=p::A[1]; endmodule
"#,
    );
    assert_eq!(design.parameters["N"].to_u64(), Some(0));
    let four_state = elaborate(
        r#"
package p; localparam integer A[1]='{17}; endpackage
module top; localparam integer A[2]='{91,93}; localparam integer N=p::A[1]; endmodule
"#,
    );
    assert!(four_state.parameters["N"].has_xz());
    assert!(!design.parameters["N"].has_xz());
}

#[test]
fn imported_array_uses_exporting_package_bounds_and_values() {
    let design = elaborate(
        r#"
package p; localparam int L=4, R=5, V=17; localparam int A[L:R]='{V,V+12}; endpackage
module top; localparam int L=8, R=9, V=91; import p::A; localparam int N=A[5]; logic [N-1:0] data; endmodule
"#,
    );
    assert_eq!(design.arrays["A"], (4, 5, 32));
    assert_eq!(design.parameters["N"].to_u64(), Some(29));
    assert_eq!(design.signals["data"].width, 29);
}

/// Copying an unpacked array of packed structs from a package parameter,
/// then again through an instance override. A scalar fold left every element
/// at x, so a predecoder mask never matched.
#[test]
fn struct_array_copy_keeps_element_fields() {
    let design = elaborate(
        r#"
package pkg;
  typedef struct packed { logic a; logic b; logic [2:0] c; } rsp_t;
  typedef struct packed {
    logic [31:0] instr_data;
    logic [31:0] instr_mask;
    rsp_t prd_rsp;
  } offload_instr_t;
  parameter int unsigned NumInstr = 2;
  parameter offload_instr_t OffloadInstr[NumInstr] = '{
    '{ instr_data: 32'h00000053, instr_mask: 32'hfe00007f, prd_rsp: '{ a: 1'b1, b: 1'b1, c: 3'b011 } },
    '{ instr_data: 32'h00000047, instr_mask: 32'h0000007f, prd_rsp: '{ a: 1'b1, b: 1'b0, c: 3'b000 } }
  };
endpackage
module pre #(
  parameter int NumInstr = 1,
  parameter pkg::offload_instr_t OffloadInstr[NumInstr] = '{default: '0}
) ();
  localparam int D = OffloadInstr[0].instr_data;
  localparam int M = OffloadInstr[0].instr_mask;
  localparam int A = OffloadInstr[0].prd_rsp.a;
endmodule
module top;
  localparam pkg::offload_instr_t OFF[pkg::NumInstr] = pkg::OffloadInstr;
  localparam int PD = OFF[0].instr_data;
  pre #(.NumInstr(pkg::NumInstr), .OffloadInstr(pkg::OffloadInstr)) u_direct ();
  pre #(.NumInstr(pkg::NumInstr), .OffloadInstr(OFF)) u_local ();
endmodule
"#,
    );
    let get = |k: &str| design.parameters[k].to_u64();
    assert_eq!(get("PD"), Some(0x53));
    assert_eq!(get("u_direct.D"), Some(0x53));
    assert_eq!(get("u_direct.M"), Some(0xfe00007f));
    assert_eq!(get("u_direct.A"), Some(1));
    assert_eq!(get("u_local.D"), Some(0x53));
    assert_eq!(get("u_local.M"), Some(0xfe00007f));
    assert_eq!(get("u_local.A"), Some(1));
}

#[test]
fn packed_enum_array_default_pattern_keeps_members() {
    // fpnew's implementation struct: a packed array of a packed array of an
    // enum, filled with `'{default: MERGED}`. A zero here is DISABLED, which
    // ties every format's in_ready to 0.
    let design = elaborate(
        r#"
package p;
  typedef enum logic [1:0] { DISABLED, PARALLEL, MERGED } unit_type_t;
  typedef unit_type_t [0:4] fmt_unit_types_t;
  typedef fmt_unit_types_t [0:3] opgrp_fmt_unit_types_t;
  typedef struct packed {
    opgrp_fmt_unit_types_t UnitTypes;
    logic [1:0] PipeConfig;
  } impl_t;
  parameter impl_t IMPL = '{
    UnitTypes: '{
      '{default: MERGED},
      '{default: MERGED},
      '{default: PARALLEL},
      '{default: MERGED}
    },
    PipeConfig: 2'b00
  };
endpackage
module top;
  localparam int unsigned G0 = p::IMPL.UnitTypes[0];
  localparam int unsigned G2 = p::IMPL.UnitTypes[2];
endmodule
"#,
    );
    let get = |k: &str| design.parameters[k].to_u64();
    assert_eq!(get("G0"), Some(0x2aa));
    assert_eq!(get("G2"), Some(0x155));
}

#[test]
fn ascending_mask_index_zero_is_the_high_bit() {
    let design = elaborate(
        r#"
package p;
  typedef logic [0:4] mask_t;
  typedef struct packed { mask_t FpFmtMask; } feat_t;
  parameter feat_t F = '{ FpFmtMask: 5'b10000 };
endpackage
module top;
  localparam bit B0 = p::F.FpFmtMask[0];
  localparam bit B4 = p::F.FpFmtMask[4];
endmodule
"#,
    );
    let get = |k: &str| design.parameters[k].to_u64();
    assert_eq!(get("B0"), Some(1));
    assert_eq!(get("B4"), Some(0));
}

#[test]
fn ascending_parameter_index_zero_is_the_high_bit() {
    let design = elaborate(
        r#"
package p;
  typedef logic [0:4] mask_t;
endpackage
module top;
  parameter p::mask_t M = 5'b10000;
  localparam bit B0 = M[0];
  localparam bit B4 = M[4];
endmodule
"#,
    );
    let get = |k: &str| design.parameters[k].to_u64();
    assert_eq!(get("B0"), Some(1));
    assert_eq!(get("B4"), Some(0));
}

#[test]
fn ascending_struct_array_field_in_const_function() {
    let design = elaborate(
        r#"
package p;
  typedef struct packed {
    int unsigned exp_bits;
    int unsigned man_bits;
  } enc_t;
  localparam enc_t [0:4] ENC = '{
    '{8, 23}, '{11, 52}, '{5, 10}, '{5, 2}, '{8, 7}
  };
  function automatic int unsigned width(int unsigned fmt);
    return ENC[fmt].exp_bits + ENC[fmt].man_bits + 1;
  endfunction
endpackage
module slice #(parameter int unsigned Fmt = 0);
  localparam int unsigned W = p::width(Fmt);
endmodule
module top;
  localparam int unsigned D = p::width(0);
  slice #(.Fmt(0)) u0();
  slice #(.Fmt(1)) u1();
  slice #(.Fmt(4)) u4();
endmodule
"#,
    );
    let get = |k: &str| design.parameters[k].to_u64();
    assert_eq!(get("D"), Some(32));
    assert_eq!(get("u0.W"), Some(32));
    assert_eq!(get("u1.W"), Some(64));
    assert_eq!(get("u4.W"), Some(16));
}

#[test]
fn ascending_enum_array_and_mask_in_const_function() {
    let design = elaborate(
        r#"
package p;
  typedef enum logic [1:0] { DISABLED, PARALLEL, MERGED } unit_type_t;
  typedef unit_type_t [0:4] fmt_t;
  typedef logic [0:4] mask_t;
  localparam fmt_t U = '{default: MERGED};
  localparam mask_t M = 5'b10000;
  function automatic logic any_merged(fmt_t types, mask_t cfg);
    for (int unsigned i = 0; i < 5; i++)
      if (cfg[i] && types[i] == MERGED)
        return 1'b1;
    return 1'b0;
  endfunction
  function automatic int unsigned elem(fmt_t types, int unsigned i);
    return types[i];
  endfunction
  localparam logic ANY = any_merged(U, M);
  localparam int unsigned E0 = elem(U, 0);
endpackage
module blk #(
  parameter p::fmt_t FmtUnitTypes = '{default: p::DISABLED},
  parameter p::mask_t FpFmtMask = '0
);
  localparam logic ANY = p::any_merged(FmtUnitTypes, FpFmtMask);
  localparam logic IS_MERGED = (FmtUnitTypes[0] == p::MERGED);
endmodule
module top;
  localparam logic ANY = p::ANY;
  localparam int unsigned E0 = p::E0;
  blk #(.FmtUnitTypes(p::U), .FpFmtMask(p::M)) u();
endmodule
"#,
    );
    let get = |k: &str| design.parameters[k].to_u64();
    assert_eq!(get("ANY"), Some(1));
    assert_eq!(get("E0"), Some(2));
    assert_eq!(get("u.ANY"), Some(1));
    assert_eq!(get("u.IS_MERGED"), Some(1));
}

/// A generate-if condition is folded in an empty shell, not the module that
/// owns the typedefs. Without the shell seeing typedef widths, `types` is
/// widened to 32 bits and `[0:N]` index 0 reads the zero-extended top, so the
/// merged branch is dropped.
#[test]
fn generate_if_calls_ascending_enum_array_function() {
    let design = elaborate(
        r#"
package p;
  typedef enum logic [1:0] { DISABLED, PARALLEL, MERGED } unit_type_t;
  typedef unit_type_t [0:4] fmt_t;
  typedef logic [0:4] mask_t;
  function automatic logic any_merged(fmt_t types, mask_t cfg);
    for (int unsigned i = 0; i < 5; i++)
      if (cfg[i] && types[i] == MERGED)
        return 1'b1;
    return 1'b0;
  endfunction
endpackage
module blk #(
  parameter p::fmt_t FmtUnitTypes = '{default: p::DISABLED},
  parameter p::mask_t FpFmtMask = '0
);
  if (p::any_merged(FmtUnitTypes, FpFmtMask)) begin : gen_merged
    logic flag = 1'b1;
  end
endmodule
module top;
  localparam p::fmt_t MERGED_U = '{default: p::MERGED};
  localparam p::fmt_t PAR_U = '{default: p::PARALLEL};
  localparam p::mask_t M = 5'b10000;
  blk #(.FmtUnitTypes(MERGED_U), .FpFmtMask(M)) u_on();
  blk #(.FmtUnitTypes(PAR_U), .FpFmtMask(M)) u_off();
endmodule
"#,
    );
    assert!(design.signals.contains_key("u_on.gen_merged.flag"));
    assert!(!design.signals.contains_key("u_off.gen_merged.flag"));
}
