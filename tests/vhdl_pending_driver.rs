//! IEEE 1076-2008 §10.5.2, §14.7.2: specialize a driver's projected
//! waveform only when every write is one implicit-zero inertial value.

use xezim_core::vhdl;

fn lowered(decls: &str, body: &str) -> String {
    let source = format!(
        "entity t is end; architecture a of t is signal q : bit := '0'; {decls} begin {body} end;"
    );
    vhdl::lower_design(&[("work", "pending.vhd", source.as_bytes())])
        .unwrap_or_else(|errors| panic!("{}", errors.join("\n")))
}

fn has_queue(sv: &str, signal: usize, process: usize) -> bool {
    sv.contains(&format!("longint vh_dt{signal}_{process}[$];"))
}

#[test]
fn implicit_zero_driver_has_no_projected_waveform_queue() {
    let sv = lowered("", "process begin q <= '1'; q <= '0'; wait; end process;");
    assert!(sv.contains("bit vh_pend0_0;"));
    assert!(sv.contains("vh_pv0_0 = 1; vh_pend0_0 = 1;"));
    assert!(sv.contains("vh_pv0_0 = 0; vh_pend0_0 = 1;"));
    assert!(!has_queue(&sv, 0, 0));
    assert!(!sv.contains("vh_qn0_0"));
    assert!(!sv.contains("vh_drv_0_0"));
}

#[test]
fn any_nontrivial_waveform_keeps_the_queue() {
    for assignment in [
        "q <= '0' after 1 ns;",
        "q <= '0' after 0 ns;",
        "q <= transport '0';",
        "q <= reject 0 ns inertial '0';",
        "q <= '0', '1' after 1 ns;",
    ] {
        let sv = lowered(
            "",
            &format!("process begin q <= '1'; {assignment} wait; end process;"),
        );
        assert!(has_queue(&sv, 0, 0), "queue omitted for {assignment}");
        assert!(sv.contains("vh_drv_0_0"), "missing waveform updater");
    }
}

#[test]
fn eligibility_is_per_driver() {
    let sv = lowered(
        "signal r : bit;",
        "process begin q <= '1'; r <= '1' after 1 ns; wait; end process;",
    );
    assert!(!has_queue(&sv, 0, 0));
    assert!(has_queue(&sv, 1, 0));
}

#[test]
fn signal_procedure_actuals_keep_the_queue() {
    let sv = lowered(
        "procedure delayed(signal x : out bit) is begin x <= '0' after 1 ns; end;",
        "process begin q <= '1'; delayed(q); wait; end process;",
    );
    assert!(has_queue(&sv, 0, 0));
    assert!(sv.contains("vh_drv_0_0"));
}

#[test]
fn transitive_global_procedure_writes_keep_the_queue() {
    let sv = lowered(
        "procedure inner is begin q <= '0' after 1 ns; end; procedure outer is begin inner; end;",
        "process begin q <= '1'; outer; wait; end process;",
    );
    assert!(has_queue(&sv, 0, 0));
}

#[test]
fn procedure_force_is_discovered_before_driver_selection() {
    let sv = lowered(
        "procedure force_q is begin q <= force '1'; end;",
        "process begin q <= '0'; wait; end process; process begin force_q; wait; end process;",
    );
    assert!(has_queue(&sv, 0, 0));
}

#[test]
fn multi_leaf_driver_keeps_pending_leaf_state_without_future_queues() {
    let source = b"entity t is end; architecture a of t is signal q : bit_vector(1 downto 0); begin process begin q(0) <= '1'; q(1) <= '0'; wait; end process; end;";
    let sv = vhdl::lower_design(&[("work", "partial.vhd", source)])
        .unwrap_or_else(|errors| panic!("{}", errors.join("\n")));
    for state in ["vh_pf0_0_c0", "vh_pm0_0_c0", "vh_pl0_0_c0", "vh_pn0_0_c0"] {
        assert!(sv.contains(state), "missing pending leaf state {state}");
    }
    assert_no_slot_queue(&sv);
    assert!(!sv.contains("bit vh_pend0_0;"));
}

fn partial_lowered(decls: &str, body: &str) -> String {
    let source = format!(
        "entity t is end; architecture a of t is signal q : bit_vector(2 downto 0) := \"000\"; {decls} begin {body} end;"
    );
    vhdl::lower_design(&[("work", "partial.vhd", source.as_bytes())])
        .unwrap_or_else(|errors| panic!("{}", errors.join("\n")))
}

fn assert_no_slot_queue(sv: &str) {
    for name in [
        "vh_dt0_0_c",
        "vh_dk0_0_c",
        "vh_dq0_0_c",
        "vh_sqn0_0_c",
        "vh_drs_0_0_c",
        "vh_drd_0_0_c",
        "vh_drv_0_0",
    ] {
        assert!(
            !sv.contains(name),
            "unused future transaction reference {name}"
        );
    }
}

/// The old per-leaf queue requirement remains covered by this timed variant;
/// the immediate variant above retains its pending-state coverage.
#[test]
fn partial_driver_with_delay_retains_per_leaf_transactions() {
    for suffix in ["after 1 ns", "after 0 ns"] {
        let sv = partial_lowered(
            "",
            &format!("process begin q(0) <= '1'; q(1) <= '0' {suffix}; wait; end process;"),
        );
        assert!(sv.contains("vh_sqn0_0_c0"));
        assert!(sv.contains("function automatic void vh_drs_0_0_c0"));
        assert!(sv.contains("function automatic void vh_drd_0_0_c0"));
    }
}

#[test]
fn nontrivial_partial_waveforms_keep_future_transaction_support() {
    for assignment in [
        "q(0) <= transport '1';",
        "q(0) <= reject 0 ns inertial '1';",
        "q(0) <= '0', '1' after 1 ns;",
    ] {
        let sv = partial_lowered(
            "",
            &format!("process begin {assignment} wait; end process;"),
        );
        assert!(
            sv.contains("vh_sqn0_0_c0"),
            "queue omitted for {assignment}"
        );
        assert!(sv.contains("vh_drs_0_0_c0"));
    }
}

#[test]
fn whole_and_partial_implicit_writes_keep_word_and_leaf_state() {
    let sv = partial_lowered(
        "",
        "process begin q <= \"101\"; q(0) <= '0'; q(1) <= '1'; q <= \"011\"; wait; end process;",
    );
    assert!(sv.contains("vh_pw0_0_c0"));
    assert!(sv.contains("vh_pwf0_0_c0"));
    assert!(sv.contains("vh_pf0_0_c0"));
    assert_no_slot_queue(&sv);
}

#[test]
fn signal_procedure_parts_keep_future_transaction_support() {
    let sv = partial_lowered(
        "procedure put(signal x : out bit) is begin x <= '0'; end;",
        "process begin q(0) <= '1'; put(q(1)); wait; end process;",
    );
    assert!(sv.contains("vh_sqn0_0_c0"));
    assert!(sv.contains("vh_drs_0_0_c0"));
}

#[test]
fn forced_partial_driver_keeps_future_transaction_support() {
    let sv = partial_lowered(
        "procedure force_q is begin q <= force \"111\"; end;",
        "process begin q(0) <= '0'; wait; end process; process begin force_q; wait; end process;",
    );
    assert!(sv.contains("vh_sqn0_0_c0"));
}

#[test]
fn array_words_keep_word_pending_lists_without_future_queues() {
    let source = b"entity t is end; architecture a of t is type words is array (0 to 1) of bit_vector(3 downto 0); signal q : words; begin process begin q(0) <= \"1010\"; q(0)(0) <= '1'; q(1)(1) <= '0'; q(1) <= \"0110\"; wait; end process; end;";
    let sv = vhdl::lower_design(&[("work", "words.vhd", source)])
        .unwrap_or_else(|errors| panic!("{}", errors.join("\n")));
    assert!(sv.contains("vh_pww0_0_c0"));
    assert!(sv.contains("vh_pwwi0_0_c0"));
    assert!(sv.contains("vh_pwwm0_0_c0"));
    assert!(sv.contains("vh_pwwn0_0_c0"));
    assert_no_slot_queue(&sv);
}

#[test]
fn packed_record_parts_keep_pending_overlays_without_future_queues() {
    let source = b"entity t is end; architecture a of t is type row is record value : bit_vector(3 downto 0); flag : bit; end record; type rows is array (0 to 1) of row; signal q : rows; begin process begin q(0).value <= \"1010\"; q(0).flag <= '1'; q(0).value(0) <= '1'; wait; end process; end;";
    let sv = vhdl::lower_design(&[("work", "records.vhd", source)])
        .unwrap_or_else(|errors| panic!("{}", errors.join("\n")));
    assert!(sv.contains("vh_pw0_0_c0"));
    assert!(sv.contains("vh_pwf0_0_c0"));
    assert_no_slot_queue(&sv);
}

#[test]
fn guarded_driver_keeps_null_transaction_support() {
    let source = b"library ieee; use ieee.std_logic_1164.all; entity t is end; architecture a of t is signal q : std_logic bus; begin b : block (true) begin q <= guarded '1'; end block; end;";
    let sv = vhdl::lower_design(&[("work", "guarded.vhd", source)])
        .unwrap_or_else(|errors| panic!("{}", errors.join("\n")));
    assert!(sv.contains("bit vh_don0_0;"));
    assert!(has_queue(&sv, 0, 0));
    assert!(sv.contains("bit vh_dn0_0[$];"));
}
