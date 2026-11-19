//! IEEE 1076-2008 §4.2.2.3, §16.2.4: signal arguments carry only
//! observed attributes; unused activity must not constrain actual selections.

use xezim_core::vhdl;

fn lower(decls: &str, body: &str) -> Result<String, Vec<String>> {
    let src = format!(
        "entity t is end; architecture a of t is signal q : bit_vector(2 downto 0) := \"000\"; {decls} begin {body} end;"
    );
    vhdl::lower_design(&[("work", "forwarding.vhd", src.as_bytes())])
}

#[test]
fn value_only_dynamic_signal_actual_needs_no_activity() {
    let sv = lower(
        "function f(signal x : bit) return bit is begin return x; end;",
        "process variable i : integer := 0; begin assert f(q(i)) = '0'; wait; end process;",
    )
    .unwrap();
    assert!(!sv.contains("_lev"));
    assert!(!sv.contains("bit vh_pa"));
}

#[test]
fn event_only_dynamic_signal_actual_needs_no_activity() {
    let sv = lower(
        "function f(signal x : bit) return boolean is begin return x'event; end;",
        "process variable i : integer := 0; begin assert not f(q(i)); wait; end process;",
    )
    .unwrap();
    assert!(!sv.contains("bit vh_pa"));
}

#[test]
fn nested_value_and_event_only_part_arguments_need_no_activity() {
    for ret in ["x = '0'", "x'event"] {
        let decls = format!(
            "function f(signal x : bit) return boolean is begin return {ret}; end; function g(signal x : bit_vector(2 downto 0)) return boolean is begin return f(x(0)); end;"
        );
        let sv = lower(
            &decls,
            "process begin assert g(q) or not g(q); wait; end process;",
        )
        .unwrap();
        assert!(!sv.contains("bit vh_pa"));
    }
}

#[test]
fn value_only_forced_part_actual_needs_no_activity() {
    lower(
        "function f(signal x : bit) return bit is begin return x; end;",
        "process begin assert f(q(0)) = '0'; q <= force \"000\"; wait; end process;",
    )
    .unwrap();
}

#[test]
fn transitive_whole_parameter_activity_remains_forwarded() {
    let sv = lower("function f(signal x : bit) return boolean is begin return x'active; end; function g(signal x : bit) return boolean is begin return f(x); end;", "process begin assert not g(q(0)); wait; end process;").unwrap();
    assert!(sv.contains("bit vh_pa0;"));
}

#[test]
fn actual_activity_consumers_keep_precise_diagnostics() {
    for (decls, body, expected) in [
        (
            "function f(signal x : bit) return boolean is begin return x'active; end;",
            "process variable i : integer := 0; begin assert not f(q(i)); wait; end process;",
            "requires static scalar selections",
        ),
        (
            "function f(signal x : bit) return boolean is begin return x'active; end; function g(signal x : bit_vector(2 downto 0)) return boolean is begin return f(x(0)); end;",
            "process begin assert not g(q); wait; end process;",
            "activity of a signal parameter part",
        ),
    ] {
        let errors = lower(decls, body).unwrap_err();
        assert!(errors.iter().any(|e| e.contains(expected)), "{errors:?}");
    }
}

#[test]
fn large_static_full_range_keeps_exact_whole_activity() {
    let src = b"entity t is end; architecture a of t is signal q : bit_vector(0 to 65536); begin process begin assert not q(0 to 65536)'active; wait; end process; end;";
    let sv = vhdl::lower_design(&[("work", "full.vhd", src)]).unwrap();
    assert!(sv.contains("bit vh_pa0;"));
}

#[test]
fn large_static_subset_is_not_mistaken_for_whole_activity() {
    let src = b"entity t is end; architecture a of t is signal q : bit_vector(0 to 70000); begin process begin assert not q(0 to 65536)'active; wait; end process; end;";
    let errors = vhdl::lower_design(&[("work", "subset.vhd", src)]).unwrap_err();
    assert!(
        errors
            .iter()
            .any(|e| e.contains("requires static scalar selections"))
    );
}

#[test]
fn event_time_observed_through_a_signal_formal_is_forwarded() {
    let sv = lower(
        "function age(signal x : bit) return time is begin return x'last_event; end;",
        "process begin q(0) <= '1'; wait for 1 ns; assert age(q(0)) = 1 ns; wait; end process;",
    )
    .unwrap();
    assert!(sv.contains("vh_s0_lev ="));
    assert!(sv.contains("64'sd9223372036854775807 : (vh_now - "));
}
