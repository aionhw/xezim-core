//! IEEE 1076-2008 §11.3, §14.7.5: one process body serves initialization
//! and resumption, with automatic helper-local temporaries.

use xezim_core::vhdl;

#[test]
fn cycle_scan_reuses_the_process_body() {
    let source = b"entity t is end; architecture a of t is signal clk, q : bit := '0'; begin clk <= not clk after 5 ns; process(clk) begin if rising_edge(clk) then q <= not q; end if; end process; end;";
    let sv = vhdl::lower_design(&[("work", "shared.vhd", source)]).unwrap();
    assert_eq!(
        sv.matches("vh_pv1_1 =").count(),
        1,
        "process assignment was duplicated"
    );
    assert!(
        sv.matches("vh_run1();").count() >= 3,
        "initialization and scan must share the helper"
    );
}

#[test]
fn scalar_process_temporaries_stay_local() {
    let source = b"entity t is end; architecture a of t is signal clk : bit := '0'; signal q : bit_vector(3 downto 0); begin clk <= not clk after 5 ns; process(clk) begin if rising_edge(clk) then q(0) <= not q(0); end if; end process; end;";
    let sv = vhdl::lower_design(&[("work", "locals.vhd", source)]).unwrap();
    assert!(sv.contains("vh_tv"), "exercise a partial-write temporary");
    assert!(
        !sv.lines().any(|line| line
            .strip_prefix("  ")
            .is_some_and(|body| !body.starts_with(' ') && body.contains(" vh_tv"))),
        "process-local temporary became a module signal"
    );
}

#[test]
fn disabled_clocked_process_skips_only_an_empty_action() {
    fn dispatch(action: &str) -> String {
        let source = format!(
            "entity t is end; architecture a of t is signal clk, en, q: bit; begin
             process(clk) begin if rising_edge(clk) then {action} end if; end process; end;"
        );
        let sv = vhdl::lower_design(&[("work", "enable.vhd", source.as_bytes())]).unwrap();
        sv.lines().find(|line| line.contains("vh_from <= 0")).unwrap().to_owned()
    }
    let gated = dispatch("if en = '1' then q <= not q; end if;");
    assert!(gated.contains("vh_s1"), "{gated}");
    let with_else = dispatch("if en = '1' then q <= not q; else q <= '0'; end if;");
    assert!(!with_else.contains("vh_s1"), "{with_else}");
}
