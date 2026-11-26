//! IEEE 1800-2023 §13.4.3 (aionhw/xezim#721): a constant-function call reads
//! the module parameter table in place. Each call used to copy the whole
//! table (every parameter of every instance elaborated so far) to size its
//! formals, so a design of N instances that each call one constant function
//! cost N x N. Four times the instances must cost about four times the
//! work; the old cost was about twenty times.

use std::time::{Duration, Instant};

fn design(instances: usize) -> String {
    let mut s = String::from(
        "package fn;\n\
           function automatic int unsigned clog2u(input int unsigned v);\n\
             int unsigned r;\n\
             r = 0;\n\
             while ((32'd1 << r) < v) r++;\n\
             return r;\n\
           endfunction\n\
         endpackage\n\
         module leaf #(parameter int D = 2, parameter int A = 1, parameter int B = 2,\n\
                       parameter int E = 3) (output logic [7:0] w);\n\
           localparam int unsigned AW = fn::clog2u(D);\n\
           localparam int S = A + B + E;\n\
           localparam int T = S * 2;\n\
           localparam int U = T + D;\n\
           assign w = AW;\n\
         endmodule\n\
         module top;\n",
    );
    s.push_str(&format!("  logic [7:0] w [{instances}];\n"));
    s.push_str(&format!(
        "  for (genvar i = 0; i < {instances}; i++) begin : g\n    \
           leaf #(.D(i + 2)) u (.w(w[i]));\n  end\nendmodule\n"
    ));
    s
}

fn elaborate(instances: usize) -> (Duration, xezim_core::ElaboratedModule) {
    let src = design(instances);
    let start = Instant::now();
    let (_, m) = xezim_core::parse_and_elaborate_multi(
        &[src],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .unwrap_or_else(|error| panic!("{error}"));
    (start.elapsed(), m)
}

fn best_of_three(instances: usize) -> Duration {
    (0..3).map(|_| elaborate(instances).0).min().unwrap()
}

#[test]
fn each_instance_gets_its_own_function_result() {
    let (_, m) = elaborate(40);
    for i in [0usize, 1, 2, 6, 14, 30, 39] {
        let d = i as u64 + 2;
        let want = (0..32).find(|r| (1u64 << r) >= d).unwrap();
        let aw = m.parameters[&format!("g[{i}].u.AW")].to_u64();
        assert_eq!(aw, Some(want), "g[{i}].u.AW for D={d}");
    }
}

#[test]
fn constant_function_calls_scale_with_the_instances() {
    let small = best_of_three(1000);
    let large = best_of_three(4000);
    let ratio = large.as_secs_f64() / small.as_secs_f64().max(1e-6);
    assert!(
        ratio < 10.0,
        "4x the instances took {ratio:.1}x the time ({small:?} -> {large:?})"
    );
}
