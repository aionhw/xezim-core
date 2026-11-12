//! §23.11, §23.3.2: a bind instantiation is a complete instantiation, so it
//! can declare an array of instances, alone or in a list. The bound items were
//! added after the target's own arrays of instances were expanded, so the
//! array's elements were never built and `t.d[0]` named nothing.

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

const CHILD: &str =
    "module c #(parameter int A = 0) (input int x, output int y); assign y = A + x; endmodule\n";

#[test]
fn bound_array_of_instances() {
    for bind in [
        "bind t c #(.A(5)) d[1:0](.x(r), .y());",
        "bind t c #(.A(5)) a(.x(r), .y()), d[1:0](.x(r), .y());",
    ] {
        let src = format!(
            "{CHILD}module t; int r = 10; endmodule\nmodule top; t u (); endmodule\n{bind}\n"
        );
        let m = elaborate(&src);
        for inst in ["u.d[0]", "u.d[1]"] {
            assert_eq!(
                m.parameters
                    .get(&format!("{inst}.A"))
                    .and_then(|v| v.to_i64()),
                Some(5),
                "{bind}: no {inst}"
            );
        }
        assert!(
            !m.parameters.contains_key("u.d.A"),
            "{bind}: unexpanded array"
        );
    }
}
