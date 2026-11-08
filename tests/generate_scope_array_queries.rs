//! The array queries and `$bits` over a variable declared in a generate block
//! are constant (§20.7, §20.6.2, §27), the same as over one declared in the
//! module body: `localparam int M = $size(r)` in the block is the declared
//! size. Every expected value is the reference simulator's.

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
fn param(design: &xezim_core::ElaboratedModule, key: &str) -> i64 {
    design
        .parameters
        .get(key)
        .unwrap_or_else(|| {
            let mut known: Vec<_> = design.parameters.keys().collect();
            known.sort();
            panic!("no parameter '{key}' in {known:?}")
        })
        .to_i64()
        .unwrap_or_else(|| panic!("parameter '{key}' is not a number"))
}

#[test]
fn queries_over_block_variables_in_a_generate_if() {
    let design = elaborate(
        "module t;
          if (1) begin : g
            localparam int N = 4;
            logic [31:0] r [N];
            logic [31:0] f [4];
            logic [7:0] v;
            logic [3:0][7:0] pk;
            int u [2:5];
            localparam int A = $size(r);
            localparam int B = $size(f);
            localparam int C = $bits(r);
            localparam int D = $size(v);
            localparam int E = $left(u);
            localparam int F = $size(pk, 1);
          end
        endmodule",
    );
    let got: Vec<i64> = ["g.A", "g.B", "g.C", "g.D", "g.E", "g.F"]
        .iter()
        .map(|k| param(&design, k))
        .collect();
    assert_eq!(got, [4, 4, 128, 8, 2, 4]);
}

/// A width built from the query sizes the vector.
#[test]
fn query_sizes_a_vector_in_the_block() {
    let design = elaborate(
        "module t;
          if (1) begin : g
            logic [31:0] f [4];
            logic [$size(f)-1:0] w;
          end
        endmodule",
    );
    assert_eq!(design.signals["g.w"].width, 4);
}

#[test]
fn in_a_generate_for() {
    let design = elaborate(
        "module t;
          for (genvar i = 0; i < 2; i++) begin : l
            logic [31:0] q [3];
            localparam int H = $size(q);
          end
        endmodule",
    );
    assert_eq!([param(&design, "l[0].H"), param(&design, "l[1].H")], [3, 3]);
}

#[test]
fn in_a_nested_block() {
    let design = elaborate(
        "module t;
          if (1) begin : o
            if (1) begin : n
              logic [31:0] z [5];
              localparam int I = $size(z);
            end
          end
        endmodule",
    );
    assert_eq!(param(&design, "o.n.I"), 5);
}

#[test]
fn in_a_generate_case() {
    let design = elaborate(
        "module t;
          case (1)
            1: begin : k
              logic [31:0] kc [5];
              localparam int D = $size(kc);
            end
          endcase
        endmodule",
    );
    assert_eq!(param(&design, "k.D"), 5);
}

/// An unlabeled block's own declarations answer too. Its data is keyed by
/// bare name today and by its implicit name (`genblk1.w`, §27.6) once
/// unlabeled blocks are scoped like labeled ones; either key is accepted.
#[test]
fn in_an_unlabeled_block() {
    let design = elaborate(
        "module t;
          if (1) begin
            logic [31:0] ub [3];
            logic [$size(ub)-1:0] w;
          end
        endmodule",
    );
    let w = design
        .signals
        .get("genblk1.w")
        .or_else(|| design.signals.get("w"));
    assert_eq!(w.map(|s| s.width), Some(3));
}

/// The block's own declaration hides a module-level one of the same name.
#[test]
fn block_declaration_hides_a_module_one() {
    let design = elaborate(
        "module t;
          logic [31:0] sh [7];
          if (1) begin : g
            logic [31:0] sh [2];
            localparam int B = $size(sh);
          end
        endmodule",
    );
    assert_eq!(param(&design, "g.B"), 2);
}

/// Guard: a module-level variable queried from a block already answers.
#[test]
fn module_variable_queried_from_a_block() {
    let design = elaborate(
        "module t;
          logic [31:0] top [6];
          if (1) begin : g
            localparam int A = $size(top);
          end
        endmodule",
    );
    assert_eq!(param(&design, "g.A"), 6);
}

/// A `generate` region is not a scope (§27.3): its declarations are the
/// module's.
#[test]
fn in_a_generate_region() {
    let design = elaborate(
        "module t;
          generate
            logic [31:0] gr [4];
            localparam int A = $size(gr);
          endgenerate
        endmodule",
    );
    assert_eq!(param(&design, "A"), 4);
}

/// A block variable typed by the module's type parameter takes the instance's
/// binding.
#[test]
fn element_typed_by_a_module_type_parameter() {
    let design = elaborate(
        "module t #(type T = logic [7:0]);
          if (1) begin : g
            T x [3];
            localparam int B = $size(x);
            localparam int C = $bits(x);
          end
        endmodule",
    );
    assert_eq!([param(&design, "g.B"), param(&design, "g.C")], [3, 24]);
}
