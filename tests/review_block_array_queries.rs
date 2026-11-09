//! §20.7, §20.6.2, §23.6: an array query over a generate block's variable
//! from outside the block (`$size(g[0].arr)`, `$size(g[1].n.deep, 2)`)
//! answers from the block's declared shape. Expected values are the reference
//! simulator's.

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
fn an_array_query_from_outside_a_block_reads_its_declared_shape() {
    let design = elaborate(
        "module top;
          for (genvar i = 0; i < 2; i++) begin : g
            logic [7:0] arr [4];
            if (1) begin : n int deep [3][5]; end
          end
          localparam int OUT = $size(g[0].arr);
          localparam int D2 = $size(g[1].n.deep, 2);
          localparam int B = $bits(g[1].arr);
        endmodule",
    );
    assert_eq!(param(&design, "OUT"), 4);
    assert_eq!(param(&design, "D2"), 5);
    assert_eq!(param(&design, "B"), 32);
}
