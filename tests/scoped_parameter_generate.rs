//! §11.2.1 / §26.3 / §27.5: indexing a scoped parameter in a generate condition.
use xezim_core::{ElaboratedModule, parse_and_elaborate_multi};

fn elaborate(index: &str) -> Result<ElaboratedModule, String> {
    let src = format!(
        r#"
package cfg;
  typedef struct packed {{ bit enabled; }} entry_t;
  parameter entry_t Entries [2] = '{{'{{0}}, '{{1}}}};
endpackage
module top;
  localparam bit [3:0] SELECTOR = 4'b1001;
  int runtime_index;
  for (genvar k = 0; k < 2; k++) begin : g
    if (cfg::Entries[{index}].enabled) begin : selected
      logic found;
    end
  end
endmodule
"#
    );
    parse_and_elaborate_multi(&[src], Some("top"), &[], &["top.sv".to_owned()], &[])
        .map(|(_, module)| module)
}

#[test]
fn scoped_parameter_member_accepts_a_genvar_index() {
    let design = elaborate("k").expect("constant generate condition");
    assert!(design.signals.get("g[1].selected.found").is_some());
    assert!(design.signals.get("g[0].selected.found").is_none());
}

#[test]
fn scoped_parameter_member_rejects_a_variable_index() {
    let error = elaborate("runtime_index")
        .err()
        .expect("variable index must fail");
    assert!(
        error.contains("Generate if condition must be a constant expression"),
        "{error}"
    );
}

#[test]
fn scoped_parameter_member_accepts_a_constant_part_select_index() {
    let design = elaborate("SELECTOR[1:0]").expect("constant part-select index");
    for signal in ["g[0].selected.found", "g[1].selected.found"] {
        assert!(design.signals.get(signal).is_some(), "{signal}");
    }
}
