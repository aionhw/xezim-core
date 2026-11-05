//! A parameter declared in a generate scope has the same shapes as one in the
//! module body (§27, §6.20.2, §7.4): an unpacked array has an element per
//! index, and an index of a multi-dimensional packed one is an element select.
//! Run-time reads are pinned in xezim's
//! `tests/hierarchy/generate_array_localparam.rs`.

fn elaborate(source: &str) -> xezim_core::ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[source.to_string()],
        Some("t"),
        &[],
        &["t.sv".to_string()],
        &[],
    )
    .expect("elaborate")
    .1
}

#[track_caller]
fn elements(source: &str, a: &str, b: &str) {
    let design = elaborate(source);
    let read = |key: &str| {
        design
            .parameters
            .get(key)
            .unwrap_or_else(|| {
                let mut known: Vec<_> = design.parameters.keys().collect();
                known.sort();
                panic!("no parameter '{key}' in {known:?}")
            })
            .to_i64()
    };
    assert_eq!((read(a), read(b)), (Some(9), Some(0x3ff)));
}

const L: &str = "localparam logic [31:0] L [2] = '{32'h9, 32'h3FF};";

#[test]
fn in_a_generate_if() {
    let src = format!("module t; if (1) begin : g {L} end endmodule");
    elements(&src, "g.L[0]", "g.L[1]");
}

#[test]
fn in_an_else_branch() {
    let src = format!("module t; if (0) begin : o end else begin : g {L} end endmodule");
    elements(&src, "g.L[0]", "g.L[1]");
}

#[test]
fn in_a_generate_case() {
    let src = format!("module t; case (1) 1: begin : g {L} end endcase endmodule");
    elements(&src, "g.L[0]", "g.L[1]");
}

#[test]
fn in_a_generate_for() {
    let src = format!("module t; for (genvar i = 0; i < 1; i++) begin : g {L} end endmodule");
    elements(&src, "g[0].L[0]", "g[0].L[1]");
}

#[test]
fn dimension_from_a_sibling_localparam() {
    let src = "module t; if (1) begin : g
      localparam int N = 2;
      localparam logic [31:0] L [N] = '{32'h9, 32'h3FF};
    end endmodule";
    elements(src, "g.L[0]", "g.L[1]");
}

#[test]
fn element_width_from_a_sibling_localparam() {
    let src = "module t; if (1) begin : g
      localparam int W = 12;
      localparam logic [W-1:0] L [2] = '{12'h9, 12'h3FF};
    end endmodule";
    elements(src, "g.L[0]", "g.L[1]");
}

#[test]
fn read_by_a_sibling_localparam() {
    let src = format!(
        "module t; if (1) begin : g {L}
          localparam int A = L[0];
          localparam int B = L[1];
        end endmodule"
    );
    elements(&src, "g.A", "g.B");
}

#[test]
fn packed_two_dimensional_element_select() {
    let src = "module t; if (1) begin : g
      localparam logic [1:0][31:0] L = {32'h3FF, 32'h9};
      localparam int A = L[0];
      localparam int B = L[1];
    end endmodule";
    elements(src, "g.A", "g.B");
}

/// `[N]` parses as an associative dimension keyed by a type name until `N` is
/// known to be a parameter, so a renamed `N` has to be resolved in that form.
#[test]
fn data_array_sized_by_a_sibling_localparam() {
    let design = elaborate(
        "module t;
          localparam int M = 4;
          logic [31:0] m [M];
          if (1) begin : g
            localparam int N = 4;
            logic [31:0] r [N];
          end
        endmodule",
    );
    assert!(design.arrays.contains_key("m"));
    assert_eq!(design.arrays.get("g.r"), design.arrays.get("m"));
    assert!(!design.associative_arrays.contains_key("g.r"));
}

#[test]
fn same_name_in_two_scopes_stays_apart() {
    let design = elaborate(
        "module t;
          if (1) begin : a localparam int L [2] = '{1, 2}; end
          if (1) begin : b localparam int L [2] = '{3, 4}; end
          localparam int L [2] = '{5, 6};
        endmodule",
    );
    let read = |k: &str| design.parameters[k].to_i64().unwrap();
    assert_eq!([read("a.L[1]"), read("b.L[1]"), read("L[1]")], [2, 4, 6]);
}
