//! aionhw/xezim#680 (reported by git-hevangel): a struct typedef declared in
//! a module body is seen by the constants of the module's first instance.
//! It reached the design-wide typedef table only once that instance's
//! constants were settled, so a constant function's struct formal and a
//! struct localparam's members read 0 there.

use xezim_core::value::Value;

const SRC: &str = "\
module leaf #(parameter int W = 6);
  typedef struct packed { logic [W-1:0] a; logic [3:0] b; } cfg_t;
  function automatic int pick_b(input cfg_t c); return c.b + 1; endfunction
  function automatic int sum_local(input int x);
    cfg_t t; t.a = x; t.b = x + 1; return t.a + t.b;
  endfunction
  localparam cfg_t K = '{a: 5, b: 7};
  localparam int FORMAL = pick_b(K);
  localparam int PATTERN = pick_b('{b: 7, a: 5});
  localparam int LOCAL = sum_local(3);
  localparam int MEMBER = K.b;
endmodule
module top; leaf u0 (); leaf #(.W(9)) u1 (); endmodule
";

#[test]
fn first_instance_constants_see_body_struct_typedef() {
    let (_, m) = xezim_core::parse_and_elaborate_multi(
        &[SRC.to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .unwrap_or_else(|e| panic!("elaboration failed: {e}"));
    let get = |k: &str| m.parameters.get(k).and_then(Value::to_u64);
    for inst in ["u0", "u1"] {
        assert_eq!(get(&format!("{inst}.FORMAL")), Some(8), "{inst}.FORMAL");
        assert_eq!(get(&format!("{inst}.PATTERN")), Some(8), "{inst}.PATTERN");
        assert_eq!(get(&format!("{inst}.LOCAL")), Some(7), "{inst}.LOCAL");
        assert_eq!(get(&format!("{inst}.MEMBER")), Some(7), "{inst}.MEMBER");
    }
}
