//! IEEE 1800-2023 §7.4.1 / §23.2.2.1 (#942): a non-ANSI port declared with a
//! typedef'd element and its own packed dimensions (`output u8_t [0:7] o;`)
//! keeps the declared shape, as the same variable declaration does.
//!
//! Three holes, all on the non-ANSI port path of the elaborator:
//! * the packed dimensions were never chained with the typedef's, so the
//!   ascending `[0:7]` fell back to the `[7:0]` element order and every
//!   element came out mirrored across the port;
//! * an inlined instance sized its non-ANSI ports BEFORE its own body
//!   typedefs were registered, so a local `typedef logic [7:0] u8_t` sized
//!   each element as 32 bits;
//! * a packed array of a struct typedef (`output s_t [0:3] o;`) recorded no
//!   dimensions at all.
//!
//! A module-local typedef with unpacked dimensions (`typedef u8_t u8a_t
//! [0:7]`) shapes the inlined instance's declarations of it (bare key, for
//! the inlining only) and its subroutine signatures and locals (the
//! instance-scoped key); a variable of it was a single element.

const SRC: &str = r#"package P;
  typedef logic [7:0] u8_t;
  typedef struct packed { logic [3:0] a; logic [3:0] b; } s_t;
endpackage
module pk(o); import P::*; output u8_t [0:7] o; endmodule
module lc(o, i); typedef logic [7:0] u8_t; output u8_t [0:7] o; input u8_t [1:4] i; endmodule
module st(o); import P::*; output s_t [0:3] o; endmodule
module nd(o); typedef logic [7:0] u8_t; output u8_t [0:1][0:3] o; endmodule
module fr;
  typedef logic [7:0] u8_t;
  typedef u8_t u8a_t [0:7];
  u8a_t g;
  function automatic u8a_t mk(); u8a_t r; return r; endfunction
endmodule
module top(o); import P::*; output u8_t [0:3] o;
  u8_t [0:7] a, b;
  P::s_t [0:3] s;
  u8_t [0:7] c;
  u8_t [0:1][0:3] d;
  pk u1(.o(a));
  lc u2(.o(b), .i(c[0:3]));
  st u3(.o(s));
  nd u4(.o(d));
  fr u5();
endmodule"#;

fn design() -> xezim_core::elaborate::ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[SRC.to_string()],
        Some("top"),
        &[],
        &["ports942.sv".to_string()],
        &[],
    )
    .expect("elaborate")
    .1
}

#[test]
fn typedef_element_port_keeps_ascending_dims() {
    let m = design();
    let dims = |n: &str| m.packed_full_dims.get(n).cloned();
    assert_eq!(dims("u1.o"), Some(vec![(0, 7), (7, 0)]));
    assert_eq!(dims("u2.o"), Some(vec![(0, 7), (7, 0)]));
    assert_eq!(dims("u2.i"), Some(vec![(1, 4), (7, 0)]));
    assert_eq!(dims("u3.o"), Some(vec![(0, 3), (7, 0)]));
    assert_eq!(dims("u4.o"), Some(vec![(0, 1), (0, 3), (7, 0)]));
    // The root module's own non-ANSI port.
    assert_eq!(dims("o"), Some(vec![(0, 3), (7, 0)]));
}

#[test]
fn local_typedef_sizes_nonansi_port() {
    let m = design();
    let w = |n: &str| m.signals.get(n).map(|s| s.width);
    assert_eq!(w("u2.o"), Some(64));
    assert_eq!(w("u2.i"), Some(32));
    assert_eq!(w("u4.o"), Some(64));
}

#[test]
fn local_unpacked_typedef_is_instance_scoped() {
    let m = design();
    // A module-scope variable of it is an array of 8 elements of 8 bits.
    assert_eq!(m.arrays.get("u5.g").copied(), Some((0, 7, 8)));
    // The bare key is this instance's only while it is inlined.
    assert!(!m.typedef_unpacked_dims.contains_key("u8a_t"));
    assert!(
        m.typedef_unpacked_dims.contains_key("u5.u8a_t"),
        "no scoped unpacked dims: {:?}",
        m.typedef_unpacked_dims.keys().collect::<Vec<_>>()
    );
}
