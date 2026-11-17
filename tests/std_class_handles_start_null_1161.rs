//! §8.4, §15.3, §15.4: a handle of a built-in class of package `std`
//! (`mailbox`, `semaphore`, `process`), declared directly or through a
//! typedef, starts null like a user class's handle; it started x, so
//! `m == null` was x (aionhw/xezim#1161).
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
fn std_class_handles_start_null() {
    let d = elaborate(
        r#"
package tp;
  typedef mailbox #(int) pmbox_t;
endpackage
module top;
  typedef semaphore sem_t;
  mailbox #(int) m;
  semaphore s;
  process p;
  tp::pmbox_t pm;
  sem_t ts;
endmodule
"#,
    );
    for name in ["m", "s", "p", "pm", "ts"] {
        let sig = d
            .signals
            .get(name)
            .unwrap_or_else(|| panic!("no signal {name}"));
        assert!(
            !sig.value.has_xz() && sig.value.to_u64() == Some(0),
            "{name} starts {:?}",
            sig.value
        );
    }
}
