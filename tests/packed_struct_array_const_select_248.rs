//! A constant element select of a packed array reads the element its index
//! labels (IEEE 1800-2023 §7.4.1, §7.4.5): the left bound of the range is the
//! most significant element whether the elements are vectors, enums, packed
//! structures or packed unions, the range may be ascending or start away
//! from 0, and a second select takes an element of the next packed
//! dimension. Expected values are the reference simulator's.
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

const SRC: &str = r#"
package p;
  typedef struct packed { logic [7:0] a; logic [7:0] b; } s_t;
  typedef union packed { logic [15:0] w; s_t s; } u_t;
  typedef enum logic [3:0] { E0 = 4'h3, E1 = 4'h5, E2 = 4'h9 } e_t;
  localparam s_t [0:2] PS = {16'h0102, 16'h0304, 16'h0506};
  typedef struct packed { int unsigned exp_bits; int unsigned man_bits; } enc_t;
  localparam enc_t [0:4] ENC = '{'{8, 23}, '{11, 52}, '{5, 10}, '{5, 2}, '{8, 7}};
  function automatic int unsigned eb(int fmt); return ENC[fmt].exp_bits; endfunction
  function automatic int unsigned mb(int fmt); return p::ENC[fmt].man_bits; endfunction
endpackage
module top;
  import p::*;
  localparam s_t [0:2] S = {16'h0102, 16'h0304, 16'h0506};
  localparam s_t [2:0] D = {16'h0102, 16'h0304, 16'h0506};
  localparam s_t [1:3] O = {16'h0102, 16'h0304, 16'h0506};
  localparam s_t [3:1] OD = {16'h0102, 16'h0304, 16'h0506};
  localparam u_t [0:2] U = {16'h0102, 16'h0304, 16'h0506};
  localparam e_t [0:2] E = {E0, E1, E2};
  localparam logic [0:2][15:0] V = {16'h0102, 16'h0304, 16'h0506};
  localparam s_t [0:1][0:2] M = {16'h0102, 16'h0304, 16'h0506, 16'h0708, 16'h090a, 16'h0b0c};
  typedef s_t [0:2] arr_t;
  localparam arr_t T = {16'h0102, 16'h0304, 16'h0506};
  localparam logic [15:0] C0 = S[0], C1 = S[1], C2 = S[2];
  localparam logic [7:0] A0 = S[0].a, B2 = S[2].b;
  localparam logic [15:0] D0 = D[0], D2 = D[2];
  localparam logic [15:0] O1 = O[1], O3 = O[3], OD1 = OD[1], OD3 = OD[3];
  localparam logic [7:0] O1a = O[1].a, OD3b = OD[3].b;
  localparam logic [15:0] U0 = U[0], U2 = U[2];
  localparam logic [7:0] U0a = U[0].s.a;
  localparam logic [3:0] EE0 = E[0], EE2 = E[2];
  localparam logic [15:0] V0 = V[0], V2 = V[2];
  localparam logic [15:0] M01 = M[0][1], M12 = M[1][2];
  localparam logic [7:0] M10a = M[1][0].a;
  localparam logic [15:0] T0 = T[0], T2 = T[2];
  localparam logic [15:0] P0 = p::PS[0], P2 = PS[2];
  localparam logic [7:0] P0a = p::PS[0].a;
  localparam int unsigned X0 = eb(0), X1 = mb(1), X4 = p::eb(4);
  localparam int unsigned Y0 = ENC[0].exp_bits, Y3 = p::ENC[3].man_bits;
  localparam int I = 1;
  localparam logic [15:0] SI = S[I], SI1 = S[I+1];
  localparam int GEN = (S[0].a == 8'd1) ? 1 : 2;
endmodule
"#;

#[test]
fn constant_element_selects_read_the_labelled_element() {
    let design = elaborate(SRC);
    let expected: &[(&str, u64)] = &[
        // Ascending array of packed structs (the report).
        ("C0", 0x0102),
        ("C1", 0x0304),
        ("C2", 0x0506),
        ("A0", 1),
        ("B2", 6),
        // Descending array.
        ("D0", 0x0506),
        ("D2", 0x0102),
        // Ranges that start at 1, ascending and descending.
        ("O1", 0x0102),
        ("O3", 0x0506),
        ("OD1", 0x0506),
        ("OD3", 0x0102),
        ("O1a", 1),
        ("OD3b", 2),
        // Packed unions, enums and vectors.
        ("U0", 0x0102),
        ("U2", 0x0506),
        ("U0a", 1),
        ("EE0", 3),
        ("EE2", 9),
        ("V0", 0x0102),
        ("V2", 0x0506),
        // Two packed dimensions of structs; dimensions on a typedef.
        ("M01", 0x0304),
        ("M12", 0x0b0c),
        ("M10a", 7),
        ("T0", 0x0102),
        ("T2", 0x0506),
        // Through a package, and in a package function.
        ("P0", 0x0102),
        ("P2", 0x0506),
        ("P0a", 1),
        ("X0", 8),
        ("X1", 52),
        ("X4", 8),
        ("Y0", 8),
        ("Y3", 2),
        // A parameter as the index.
        ("SI", 0x0304),
        ("SI1", 0x0506),
        ("GEN", 1),
    ];
    for (name, value) in expected {
        assert_eq!(
            design.parameters.get(*name).and_then(|v| v.to_u64()),
            Some(*value),
            "{name}"
        );
    }
}
