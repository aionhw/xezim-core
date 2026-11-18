//! IEEE 1076-2008 §10.5.2, §14.7.2, §16.2.4: a static scalar part
//! with only implicit-zero writes needs one pending value, retaining activity.

use xezim_core::vhdl;

fn lower(decls: &str, body: &str) -> String {
    let src = format!("entity t is end; architecture a of t is {decls} begin {body} end;");
    vhdl::lower_design(&[("work", "singleton.vhd", src.as_bytes())])
        .unwrap_or_else(|errors| panic!("{}", errors.join("\n")))
}

fn scalar_state_only(sv: &str, signal: usize, process: usize) {
    assert!(sv.contains(&format!("vh_spv{signal}_{process}")));
    assert!(sv.contains(&format!("bit vh_spend{signal}_{process};")));
    assert!(sv.contains(&format!("vh_dv{signal}_{process}")));
    // Requirements formerly covered through leaf masks/lists now use the
    // scalar pending state; no reference to omitted machinery may survive.
    for prefix in [
        "vh_pf", "vh_pm", "vh_pl", "vh_pn", "vh_pw", "vh_pww", "vh_dt", "vh_dk", "vh_dq", "vh_sqn",
        "vh_drs_", "vh_drd_", "vh_drv_",
    ] {
        assert!(
            !sv.contains(&format!("{prefix}{signal}_{process}")),
            "unused {prefix} reference"
        );
    }
}

#[test]
fn repeated_scalar_part_writes_keep_value_and_flag_only() {
    let sv = lower(
        "signal q : bit_vector(31 downto 0);",
        "process begin q(7) <= '0'; q(7) <= '1'; wait; end process;",
    );
    scalar_state_only(&sv, 0, 0);
    assert!(sv.contains("vh_lk = 24;"));
    assert!(sv.contains("vh_spv0_0 = vh_tv"));
    assert!(sv.contains("vh_spend0_0 = 1;"));
    assert!(sv.contains("vh_spend0_0 = 1; vh_delta_pending = 1;"));
    assert!(!sv.contains("if (vh_spend0_0) vh_n = vh_now;"));
    assert!(sv.contains("vh_spend0_0 = 0; vh_s0_act = 1;"));
}

#[test]
fn record_field_uses_its_scalar_type_and_static_destination() {
    let sv = lower(
        "type row is record a : bit; b : integer; end record; signal q : row;",
        "process begin q.b <= 7; wait; end process;",
    );
    scalar_state_only(&sv, 0, 0);
    assert!(sv.contains("int vh_spv0_0;"));
    assert!(sv.contains("vh_dv0_0.f1 = vh_spv0_0;"));
}

#[test]
fn one_element_field_and_slice_writes_share_the_scalar() {
    let sv = lower(
        "type row is record a : bit_vector(0 to 0); b : bit; end record; signal q : row;",
        "process begin q.a <= \"1\"; q.a(0) <= '0'; q.a(0 to 0) <= \"1\"; wait; end process;",
    );
    scalar_state_only(&sv, 0, 0);
}

#[test]
fn one_bit_of_nested_words_has_no_word_or_leaf_pending_arrays() {
    let sv = lower(
        "type words is array (0 to 1) of bit_vector(3 downto 0); signal q : words;",
        "process begin q(1)(2) <= '1'; wait; end process;",
    );
    scalar_state_only(&sv, 0, 0);
    assert!(sv.contains("vh_dv0_0.d["));
}

#[test]
fn equal_value_transactions_mark_only_the_selected_scalar() {
    let sv = lower(
        "signal q : bit_vector(2 downto 0) := \"000\";",
        "process begin q(0) <= '0'; wait for 0 ns; assert q(0)'active and q(2)'quiet(1 ns); wait; end process;",
    );
    scalar_state_only(&sv, 0, 0);
    assert!(sv.contains("((2) <= 2 && (2) >= 2)"));
    assert!(sv.contains("((2) <= 0 && (2) >= 0)"));
}

#[test]
fn coverage_of_two_leaves_or_whole_and_part_keeps_lists() {
    for body in ["q(0) <= '0'; q(1) <= '1';", "q <= \"000\"; q(0) <= '1';"] {
        let sv = lower(
            "signal q : bit_vector(2 downto 0);",
            &format!("process begin {body} wait; end process;"),
        );
        assert!(!sv.contains("vh_spend0_0"));
        assert!(sv.contains("vh_pf0_0_c0"));
    }
}

#[test]
fn dynamic_index_in_one_element_dimension_is_not_a_static_proof() {
    let sv = lower(
        "signal q : bit_vector(0 to 0);",
        "process variable i : integer := 0; begin q(i) <= '1'; wait; end process;",
    );
    assert!(!sv.contains("vh_spend0_0"));
    assert!(sv.contains("vh_pf0_0_c0"));
    assert!(sv.contains("vh_ix("));
}

#[test]
fn invalid_nested_index_cannot_alias_a_valid_scalar() {
    let sv = lower(
        "type words is array (0 to 1) of bit_vector(1 downto 0); signal q : words;",
        "process begin q(0)(-1) <= '1'; wait; end process;",
    );
    assert!(!sv.contains("vh_spend0_0"));
    assert!(sv.contains("vh_ix("));
}

#[test]
fn timed_and_nontrivial_waveforms_keep_queues() {
    for assignment in [
        "q(0) <= '1' after 0 ns;",
        "q(0) <= '1' after 1 ns;",
        "q(0) <= transport '1';",
        "q(0) <= reject 0 ns inertial '1';",
        "q(0) <= '0', '1' after 1 ns;",
    ] {
        let sv = lower(
            "signal q : bit_vector(1 downto 0);",
            &format!("process begin {assignment} wait; end process;"),
        );
        assert!(!sv.contains("vh_spend0_0"));
        assert!(sv.contains("vh_drs_0_0_c0"));
    }
}

#[test]
fn signal_procedure_and_force_keep_existing_driver_forms() {
    for (decls, body) in [
        (
            "procedure put(signal x : out bit) is begin x <= '1'; end;",
            "process begin q(0) <= '0'; put(q(0)); wait; end process;",
        ),
        (
            "",
            "process begin q(0) <= '0'; q <= force \"00\"; wait; end process;",
        ),
    ] {
        let sv = lower(&format!("signal q : bit_vector(1 downto 0); {decls}"), body);
        assert!(!sv.contains("vh_spend0_0"));
        assert!(sv.contains("vh_drs_0_0_c0"));
    }
}

#[test]
fn packed_record_array_parts_keep_composite_pending_storage() {
    let sv = lower(
        "type row is record a : bit; b : bit; end record; type rows is array (0 to 1) of row; signal q : rows;",
        "process begin q(0).a <= '1'; wait; end process;",
    );
    assert!(!sv.contains("vh_spend0_0"));
    assert!(sv.contains("vh_pw0_0_c0"));
}

#[test]
fn resolved_scalar_parts_keep_separate_driver_values() {
    let src = b"library ieee; use ieee.std_logic_1164.all; entity t is end; architecture a of t is signal q : std_logic_vector(1 downto 0) := \"00\"; begin process begin q(0) <= '0'; wait; end process; process begin q(0) <= '1'; wait; end process; end;";
    let sv = vhdl::lower_design(&[("work", "resolved.vhd", src)]).unwrap();
    scalar_state_only(&sv, 0, 0);
    scalar_state_only(&sv, 0, 1);
    assert!(sv.contains("vh_upd0"));
}
