//! IEEE 1076-2008 §16.2.4, §14.7.3: part activity follows applied
//! scalar transactions, independently of value changes and resolution.

use xezim_core::vhdl;

fn lower(decls: &str, body: &str) -> Result<String, Vec<String>> {
    let src = format!("entity t is end; architecture a of t is {decls} begin {body} end;");
    vhdl::lower_design(&[("work", "activity.vhd", src.as_bytes())])
}

#[test]
fn pending_leaf_activity_is_selected_by_scalar_key() {
    let sv = lower(
        "signal q : bit_vector(2 downto 0);",
        "process begin q(0) <= '0'; q(1) <= '0'; wait for 0 ns; assert q(2)'quiet(1 ns); wait; end process;",
    )
    .unwrap();
    assert!(sv.contains("bit vh_pa0; longint vh_pa0_last;"));
    assert!(sv.contains("if (((0 + vh_lk) <= 0 && (0 + vh_lk) >= 0)) vh_pa0 = 1;"));
    assert!(sv.contains("vh_pa0 = 0;"));
    assert!(sv.contains("if (vh_pa0) vh_pa0_last = vh_now;"));
}

#[test]
fn queued_leaf_activity_is_selected_from_popped_key() {
    let sv = lower("signal q : bit_vector(2 downto 0);", "process begin q(0) <= '0' after 1 ns; wait; end process; process begin wait for 1 ns; assert q(0)'active; wait; end process;").unwrap();
    assert!(sv.contains("k = vh_dk0_0_c0.pop_front();"));
    assert!(sv.contains("if (((0 + k) <= 2 && (0 + k) >= 2)) vh_pa0 = 1;"));
}

#[test]
fn whole_pending_and_queued_transactions_mark_selected_parts() {
    for assignment in [
        "q <= \"000\";",
        "q <= \"000\" after 1 ns;",
        "q <= \"000\"; q <= \"111\" after 1 ns;",
    ] {
        let sv = lower("signal q : bit_vector(2 downto 0);", &format!("process begin {assignment} wait; end process; process begin assert not q(0)'active; wait; end process;")).unwrap();
        assert!(sv.contains("vh_s0_act = 1; vh_pa0 = 1;"), "{assignment}");
    }
}

#[test]
fn pending_array_words_mark_only_the_applied_word_range() {
    let sv = lower("type words is array (0 to 1) of bit_vector(3 downto 0); signal q : words;", "process begin q(0) <= \"0000\"; wait for 0 ns; assert q(1)(0)'quiet(1 ns); wait; end process;").unwrap();
    assert!(sv.contains("((0 + vh_lk * 4) <= 7 && (0 + (vh_lk + 1) * 4 - 1) >= 7)"));
}

#[test]
fn unsupported_dynamic_part_activity_is_diagnosed() {
    let errors = lower(
        "signal q : bit_vector(2 downto 0);",
        "process variable i : integer := 0; begin assert not q(i)'active; wait; end process;",
    )
    .unwrap_err();
    assert!(
        errors
            .iter()
            .any(|e| e.contains("requires static scalar selections"))
    );
}

#[test]
fn forced_part_activity_is_diagnosed_after_driver_discovery() {
    let errors = lower("signal q : bit_vector(2 downto 0);", "process begin assert not q(0)'active; wait; end process; process begin q <= force \"000\"; wait; end process;").unwrap_err();
    assert!(
        errors
            .iter()
            .any(|e| e.contains("forced or converted signal part"))
    );
}

#[test]
fn whole_signal_activity_timestamp_exists_only_for_observed_signals() {
    let sv = lower(
        "signal q : bit; signal initialized : boolean := q'last_active > 0 ns;",
        "process begin q <= '0'; wait for 1 ns; assert initialized; wait; end process;",
    )
    .unwrap();
    assert!(sv.contains("longint vh_s0_lact;"));
    let init = sv.find("vh_s0_lact = vh_s0_lev;").unwrap();
    let read = sv.find("vh_now - vh_s0_lact").unwrap();
    assert!(init < read);
    assert!(!sv.contains("vh_s1_lact"));
}
