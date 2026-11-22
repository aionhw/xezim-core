//! §23.3.3.7, §11.8.1: an input port's own declaration decides whether the
//! module body reads it as signed, and the connection converts the actual to
//! that type. Renaming the port to its actual is only sound when the two
//! agree: a concatenation or a select is unsigned, so substituting
//! `{c[11], c}` for `input logic signed [12:0] e_i` made `e_i < 0` false and
//! `a_i - e_i` unsigned in the body. Such a port keeps its own net, driven by
//! the connection; an actual of the formal's signedness is still renamed.

fn elaborate(src: &str) -> xezim_core::ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[src.to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .expect("elaborate")
    .1
}

#[test]
fn an_input_is_renamed_only_to_an_actual_of_its_signedness() {
    let m = elaborate(
        r#"
module ks (input logic signed [12:0] e_i);
  wire lt = e_i < 0;
endmodule
module ku (input logic [12:0] e_i);
  wire lt = e_i < 0;
endmodule
module top;
  logic signed [11:0] c = -12'sd27;
  logic signed [12:0] sv = -13'sd27;
  logic [12:0] uv = 13'h1fe5;
  ks s_concat (.e_i({c[11], c}));
  ks s_unsigned (.e_i(uv));
  ks s_signed (.e_i(sv));
  ks s_part (.e_i(sv[12:0]));
  ku u_signed (.e_i(sv));
  ku u_concat (.e_i({c[11], c}));
  ku u_unsigned (.e_i(uv));
endmodule
"#,
    );
    let renamed = |inst: &str| {
        m.input_port_actuals
            .iter()
            .map(|p| p.formal())
            .any(|f| f.rsplit('.').nth(1) == Some(inst) && f.ends_with(".e_i"))
    };
    // A signed formal keeps its net for an unsigned actual.
    assert!(!renamed("s_concat"));
    assert!(!renamed("s_unsigned"));
    assert!(!renamed("s_part"));
    // An unsigned formal keeps its net for a signed actual.
    assert!(!renamed("u_signed"));
    // Matching signedness is still a rename.
    assert!(renamed("s_signed"));
    assert!(renamed("u_concat"));
    assert!(renamed("u_unsigned"));
}

/// An element of an unpacked array or a struct member of the other
/// signedness keeps the formal: renaming `sa[0]` of
/// `logic signed [12:0] sa [2]` into an unsigned port made `e_i < 0` true in
/// the body.
#[test]
fn an_element_or_member_of_the_other_signedness_keeps_the_formal() {
    let m = elaborate(
        r#"
module ks (input logic signed [12:0] e_i);
  wire lt = e_i < 0;
endmodule
module ku (input logic [12:0] e_i);
  wire lt = e_i < 0;
endmodule
module top;
  typedef struct packed { logic signed [12:0] f; logic [2:0] g; } st_t;
  logic signed [12:0] sa [2];
  logic [12:0] ua [2];
  st_t st;
  ku u_elem (.e_i(sa[0]));
  ku u_member (.e_i(st.f));
  ks s_elem (.e_i(ua[1]));
endmodule
"#,
    );
    let renamed = |inst: &str| {
        m.input_port_actuals
            .iter()
            .map(|p| p.formal())
            .any(|f| f.rsplit('.').nth(1) == Some(inst) && f.ends_with(".e_i"))
    };
    assert!(!renamed("u_elem"));
    assert!(!renamed("u_member"));
    assert!(!renamed("s_elem"));
}

/// §11.8.1: a select through several packed dimensions (`q[1][7:0]`) is
/// unsigned like a one-level select, even of a signed vector, so it renames
/// an unsigned formal of its width and keeps a signed formal's net. A nested
/// select whose width elaboration can't measure here (`p[1][2]`) keeps the
/// formal, so a narrower port still truncates it.
#[test]
fn a_select_through_packed_dimensions_is_unsigned() {
    let m = elaborate(
        r#"
module ks (input logic signed [7:0] e_i);
  wire lt = e_i < 0;
endmodule
module ku (input logic [7:0] e_i);
  wire lt = e_i < 0;
endmodule
module ku4 (input logic [3:0] e_i);
  wire hi = e_i == 4'hf;
endmodule
module top;
  logic [3:0][7:0] q;
  logic signed [3:0][7:0] sq;
  logic [3:0][3:0][7:0] p;
  ku u_range (.e_i(q[1][7:0]));
  ku u_signed_base (.e_i(sq[1][7:0]));
  ks s_range (.e_i(sq[1][7:0]));
  ku4 u_narrow (.e_i(p[1][2]));
endmodule
"#,
    );
    let renamed = |inst: &str| {
        m.input_port_actuals
            .iter()
            .map(|p| p.formal())
            .any(|f| f.rsplit('.').nth(1) == Some(inst) && f.ends_with(".e_i"))
    };
    assert!(renamed("u_range"));
    assert!(renamed("u_signed_base"));
    assert!(!renamed("s_range"));
    assert!(!renamed("u_narrow"));
}

/// §26.3: a package parameter actual (`p::U`) is bound under its scoped
/// name, and its own signedness decides the rename as a local net's does.
#[test]
fn a_package_parameter_actual_is_renamed_by_its_signedness() {
    let m = elaborate(
        r#"
package p;
  parameter logic [12:0] U = 13'h1fe5;
  parameter logic signed [12:0] S = -13'sd27;
endpackage
module ks (input logic signed [12:0] e_i);
  wire lt = e_i < 0;
endmodule
module ku (input logic [12:0] e_i);
  wire lt = e_i < 0;
endmodule
module top;
  ku u_unsigned (.e_i(p::U));
  ks s_signed (.e_i(p::S));
  ku u_signed (.e_i(p::S));
  ks s_unsigned (.e_i(p::U));
endmodule
"#,
    );
    let renamed = |inst: &str| {
        m.input_port_actuals
            .iter()
            .map(|p| p.formal())
            .any(|f| f.rsplit('.').nth(1) == Some(inst) && f.ends_with(".e_i"))
    };
    assert!(renamed("u_unsigned"));
    assert!(renamed("s_signed"));
    assert!(!renamed("u_signed"));
    assert!(!renamed("s_unsigned"));
}

/// A literal actual is converted to the formal's type in place, so it is
/// still substituted whatever its own signedness: `.en(1)` (an unsized
/// decimal, signed) into `input logic en` and a real literal into a real
/// formal.
#[test]
fn a_literal_actual_is_renamed_whatever_its_signedness() {
    let m = elaborate(
        r#"
module ku (input logic [7:0] e_i);
  wire lt = e_i < 0;
endmodule
module ks (input logic signed [7:0] e_i);
  wire lt = e_i < 0;
endmodule
module kr (input real e_i);
  real r;
  always_comb r = e_i;
endmodule
module top;
  ku u_unsized (.e_i(1));
  ku u_signed (.e_i(8'sd3));
  ks s_unsigned (.e_i(8'd3));
  kr r_real (.e_i(1.5));
endmodule
"#,
    );
    let renamed = |inst: &str| {
        m.input_port_actuals
            .iter()
            .map(|p| p.formal())
            .any(|f| f.rsplit('.').nth(1) == Some(inst) && f.ends_with(".e_i"))
    };
    assert!(renamed("u_unsized"));
    assert!(renamed("u_signed"));
    assert!(renamed("s_unsigned"));
    assert!(renamed("r_real"));
}

/// §7.2.1, §7.4: an element of an unpacked array has the array's element
/// type and a struct member its own declared type, so an actual of the
/// formal's signedness and width is still renamed, and one of the other
/// signedness, or of another width, keeps the formal.
#[test]
fn an_element_or_member_actual_is_renamed_by_its_declared_type() {
    let m = elaborate(
        r#"
module ks (input logic signed [7:0] e_i);
  wire lt = e_i < 0;
endmodule
module ku (input logic [7:0] e_i);
  wire lt = e_i < 0;
endmodule
module ku4 (input logic [3:0] e_i);
  wire hi = e_i == 4'hf;
endmodule
module top;
  typedef struct packed { logic signed [7:0] a; logic [7:0] b; } in_t;
  typedef struct packed { in_t i; logic [7:0] c; } out_t;
  logic signed [7:0] sa [2];
  logic [7:0] ua [2];
  logic [7:0] u2 [2][2];
  in_t ia [2];
  out_t o;
  ks s_elem (.e_i(sa[1]));
  ku u_elem (.e_i(ua[0]));
  ku u_elem2 (.e_i(u2[1][0]));
  ku u_selem (.e_i(sa[0]));
  ks s_member (.e_i(o.i.a));
  ku u_member (.e_i(o.c));
  ku u_smember (.e_i(o.i.a));
  ku u_arrmem (.e_i(ia[1].b));
  ks s_arrmem (.e_i(ia[0].a));
  ks s_uarrmem (.e_i(ia[0].b));
  ku4 u_narrow (.e_i(o.c));
endmodule
"#,
    );
    let renamed = |inst: &str| {
        m.input_port_actuals
            .iter()
            .map(|p| p.formal())
            .any(|f| f.rsplit('.').nth(1) == Some(inst) && f.ends_with(".e_i"))
    };
    assert!(renamed("s_elem"));
    assert!(renamed("u_elem"));
    assert!(renamed("u_elem2"));
    assert!(renamed("s_member"));
    assert!(renamed("u_member"));
    assert!(renamed("u_arrmem"));
    assert!(renamed("s_arrmem"));
    assert!(!renamed("u_selem"));
    assert!(!renamed("u_smember"));
    assert!(!renamed("s_uarrmem"));
    assert!(!renamed("u_narrow"));
}
