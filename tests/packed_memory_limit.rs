use xezim_core::parse_and_elaborate_multi;

#[test]
fn parameterized_child_above_the_packed_limit_fails_elaboration() {
    let limit = xezim_core::elaborate::max_packed_width();
    let depth = limit / 40 + 1;
    let src = r#"
      module child #(parameter N = 1)(output bit v);
        reg [N-1:0][39:0] mem;
        initial begin mem[N-1] = '1; v = |mem[N-1]; end
      endmodule
      module top; wire out; child #(.N(DEPTH)) u(out); endmodule
    "#.replace("DEPTH", &depth.to_string());
    let result = parse_and_elaborate_multi(
        &[src], Some("top"), &[], &["memory.sv".to_owned()], &[],
    );
    let error = result.err().expect("oversized child memory must fail");
    assert!(error.contains(&format!("packed width {} exceeds implementation limit {limit}", u64::from(depth) * 40)), "{error}");
}
