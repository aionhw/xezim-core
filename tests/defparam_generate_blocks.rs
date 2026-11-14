//! §23.10.1: a `defparam` in a generate block names its targets from the
//! block, so `defparam u.A = 9;` next to `c u ();` in `gb` sets `gb.u.A`, and
//! it is judged like any other `defparam`. §6.20.1: every parameter declared
//! in a generate block is a local parameter, so a `defparam` into one of a
//! child's (`u.g.P`) is rejected. Both were dropped without a message: the
//! first matched no instance, the second matched no instance below `u`.

fn elaborate(sources: &[&str]) -> Result<xezim_core::ElaboratedModule, String> {
    let names: Vec<String> = (0..sources.len()).map(|i| format!("f{i}.sv")).collect();
    let sources: Vec<String> = sources.iter().map(|s| s.to_string()).collect();
    xezim_core::parse_and_elaborate_multi(&sources, Some("t"), &[], &names, &[]).map(|r| r.1)
}

const CHILD: &str = "module c #(parameter int A = 0) (output int y); parameter int L = 1; \
                     assign y = A + L; endmodule\n";

fn param(m: &xezim_core::ElaboratedModule, key: &str) -> Option<i64> {
    m.parameters.get(key).and_then(|v| v.to_i64())
}

#[test]
fn defparam_in_a_generate_block_reaches_its_instance() {
    let t = "module t; int y, y2, y3;
      if (1) begin : gb
        c u (y);
        defparam u.A = 9;
      end
      for (genvar i = 0; i < 2; i++) begin : gl
        c u (y2);
        defparam u.A = 4 + i;
      end
      if (1) begin : outer
        if (1) begin : inner
          c u (y3);
        end
        defparam inner.u.A = 6;
      end
    endmodule\n";
    let m = elaborate(&[CHILD, t]).expect("must elaborate");
    assert_eq!(param(&m, "gb.u.A"), Some(9));
    assert_eq!(param(&m, "gl[0].u.A"), Some(4));
    assert_eq!(param(&m, "gl[1].u.A"), Some(5));
    assert_eq!(param(&m, "outer.inner.u.A"), Some(6));
}

#[test]
fn defparam_in_a_generate_block_into_a_local_parameter() {
    let t = "module t; int y; if (1) begin : gb c u (y); defparam u.L = 9; end endmodule\n";
    let e = elaborate(&[CHILD, t]).err().expect("must be rejected");
    assert!(e.contains("defparam cannot override 'L'"), "{e}");
}

#[test]
fn defparam_into_a_parameter_of_a_child_generate_block() {
    let child = "module c (output int y); if (1) begin : g parameter int P = 5; assign y = P; end \
                 for (genvar i = 0; i < 2; i++) begin : h localparam int Q = i; end endmodule\n";
    for target in ["u.g.P", "u.h[1].Q"] {
        let t = format!("module t; int y; c u (y); defparam {target} = 9; endmodule\n");
        let e = elaborate(&[child, &t]).err().expect("must be rejected");
        assert!(
            e.contains("declared in a generate block is a local parameter"),
            "{target}: {e}"
        );
        assert!(e.contains("f1.sv:1:"), "{target}: {e}");
    }
    // A path into an instance of a generate block still reaches it.
    let child2 = "module d (output int y); if (1) begin : g c k (y); end endmodule\n";
    let t = "module t; int y; d u (y); defparam u.g.k.A = 3; endmodule\n";
    let m = elaborate(&[CHILD, child2, t]).expect("must elaborate");
    assert_eq!(param(&m, "u.g.k.A"), Some(3));
}
