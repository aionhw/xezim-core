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
fn partial_driver_keeps_per_leaf_transactions() {
    let source = b"entity t is end; architecture a of t is signal q : bit_vector(1 downto 0); begin process begin q(0) <= '1'; wait; end process; end;";
    let sv = vhdl::lower_design(&[("work", "partial.vhd", source)])
        .unwrap_or_else(|errors| panic!("{}", errors.join("\n")));
    assert!(sv.contains("vh_sqn0_0_c0"));
    assert!(!sv.contains("bit vh_pend0_0;"));
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
