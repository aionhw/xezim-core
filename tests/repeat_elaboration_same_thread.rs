//! aionhw/xezim#739 (reported by git-hevangel): elaborating the same design
//! twice in one thread gives the same design. The constant evaluator's
//! package-parameter fallback was a thread-local the first elaboration left
//! behind, so the second rendered an interface parameter default against it.

/// An interface whose parameter default names a package constant; the
/// default is rendered when the interface is registered, before any
/// instance is inlined.
const SRC: &str = "\
package pk; parameter int BASE = 7; endpackage
interface cfg_if import pk::*; #(parameter int V = BASE) (); endinterface
module top; cfg_if c0 (); initial $finish; endmodule
";

fn defaults() -> Vec<(String, Option<String>)> {
    let (_, m) = xezim_core::parse_and_elaborate_multi(
        &[SRC.to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .unwrap_or_else(|e| panic!("elaboration failed: {e}"));
    m.interface_param_defaults["cfg_if"].clone()
}

#[test]
fn the_second_elaboration_in_a_thread_equals_the_first() {
    let first = defaults();
    let second = defaults();
    assert_eq!(first, second);
}
