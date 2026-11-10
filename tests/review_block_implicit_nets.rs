//! §6.10, §27: an implicit net is declared in the generate block that uses
//! it, keyed under the block (`g[0].n`), one per loop iteration (found
//! reviewing the #952 series; the reference simulator reads each iteration's
//! net by path).

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
fn each_loop_iteration_has_its_own_implicit_nets() {
    let design = elaborate(
        "module sub(input a, output y); assign y = a; endmodule
        module top;
          reg [1:0] r;
          for (genvar i = 0; i < 2; i++) begin : g
            sub s(.a(r[i]), .y(n));
            assign m = ~n;
          end
        endmodule",
    );
    for key in ["g[0].n", "g[1].n", "g[0].m", "g[1].m"] {
        assert!(
            design.implicit_nets.contains(key),
            "{key}: {:?}",
            design.implicit_nets
        );
    }
    assert!(
        !design.implicit_nets.contains("n"),
        "{:?}",
        design.implicit_nets
    );
    assert!(
        !design.implicit_nets.contains("m"),
        "{:?}",
        design.implicit_nets
    );
}
