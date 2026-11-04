//! IEEE 1800-2023 §7.4.1 / §7.4.5: instantiated packed body constants
//! expose the same element geometry as top-level constants and variables.

const BASIC: &str = r#"module leaf;
  localparam bit [1:0][1:0] L = 4'b0010;
  localparam bit [0:1][1:0] A = 4'b1001;
  localparam bit [3:2][1:0] R = 4'b0110;
  initial $display("%m elem=%0d bits=%0d A0=%0d A1=%0d R2=%0d R3=%0d", L[0], $bits(L[0]), A[0], A[1], R[2], R[3]);
endmodule
module top;
  localparam bit [1:0][1:0] ROOT = 4'b0010;
  leaf u();
  initial begin
    $display("hier elem=%0d bits=%0d", u.L[0], $bits(u.L[0]));
    #1 $finish;
  end
endmodule"#;

const SHAPES: &str = r#"module shapes #(parameter int N = 2, W = 2);
  typedef bit [W-1:0] word_t;
  localparam bit [N-1:0][W-1:0] D = '1;
  localparam word_t [N-1:0] T = '1;
  localparam bit [N-1:0][1:0][W-1:0] C = '1;
  localparam int FIRST = D[0];
  initial $display("%m D=%0d bits=%0d T=%0d tbits=%0d C=%0d cbits=%0d leafbits=%0d FIRST=%0d", D[0], $bits(D[0]), T[0], $bits(T[0]), C[0], $bits(C[0]), $bits(C[0][0]), FIRST);
  if (1) begin : g
    localparam bit [N-1:0][W-1:0] G = '1;
    initial $display("%m elem=%0d bits=%0d", G[0], $bits(G[0]));
  end
endmodule
module top #(parameter int N = 17, W = 19);
  shapes a();
  shapes #(.N(3), .W(5)) b();
  initial #2 $finish;
endmodule"#;

fn design(src: &str) -> xezim_core::elaborate::ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[src.to_string()],
        Some("top"),
        &[],
        &["packed.sv".to_string()],
        &[],
    )
    .expect("elaborate")
    .1
}

#[test]
fn body_localparams_keep_scoped_packed_geometry() {
    let model = design(BASIC);
    for key in ["ROOT", "u.L", "u.A", "u.R"] {
        assert_eq!(model.packed_signal_elem_widths.get(key), Some(&2), "{key}");
    }
    assert_eq!(
        model.packed_full_dims.get("u.L"),
        Some(&vec![(1, 0), (1, 0)])
    );
    assert_eq!(
        model.packed_full_dims.get("u.A"),
        Some(&vec![(0, 1), (1, 0)])
    );
    assert_eq!(
        model.packed_full_dims.get("u.R"),
        Some(&vec![(3, 2), (1, 0)])
    );
}

#[test]
fn body_geometry_uses_each_instances_resolved_types_and_parameters() {
    let model = design(SHAPES);
    for (instance, n, w) in [("a", 2, 2), ("b", 3, 5)] {
        for name in ["D", "T", "g.G"] {
            let key = format!("{instance}.{name}");
            assert_eq!(model.packed_signal_elem_widths.get(&key), Some(&w), "{key}");
            assert_eq!(
                model.packed_full_dims.get(&key),
                Some(&vec![(n - 1, 0), (i64::from(w) - 1, 0)]),
                "{key}"
            );
        }
        let key = format!("{instance}.C");
        assert_eq!(
            model.packed_signal_elem_widths.get(&key),
            Some(&(2 * w)),
            "{key}"
        );
        assert_eq!(
            model.packed_full_dims.get(&key),
            Some(&vec![(n - 1, 0), (1, 0), (i64::from(w) - 1, 0)])
        );
        assert_eq!(
            model.parameters[&format!("{instance}.FIRST")].to_i64(),
            Some((1_i64 << w) - 1)
        );
    }
}
