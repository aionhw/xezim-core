//! IEEE 1076-2008 §8.4, §8.5, §16.2.4: activity selectors must name
//! existing scalar subelements; null slices select no subelements.

use xezim_core::vhdl;

fn lower(decls: &str, body: &str) -> Result<String, Vec<String>> {
    let src = format!(
        "entity t is end; architecture a of t is {decls} begin process begin {body} wait; end process; end;"
    );
    vhdl::lower_design(&[("work", "bounds.vhd", src.as_bytes())])
}

#[test]
fn out_of_range_static_vector_activity_is_diagnosed() {
    let errors = lower(
        "signal q : bit_vector(2 downto 0);",
        "assert not q(3)'active;",
    )
    .unwrap_err();
    assert!(
        errors
            .iter()
            .any(|e| e.contains("activity selection is out of bounds"))
    );
}

#[test]
fn out_of_range_nested_index_cannot_alias_a_valid_leaf() {
    let errors = lower(
        "type words is array (0 to 1) of bit_vector(1 downto 0); signal q : words;",
        "assert not q(0)(-1)'active;",
    )
    .unwrap_err();
    assert!(
        errors
            .iter()
            .any(|e| e.contains("activity selection is out of bounds")),
        "{errors:?}"
    );
}

#[test]
fn out_of_range_nonnull_slice_activity_is_diagnosed() {
    let errors = lower(
        "signal q : bit_vector(0 to 2);",
        "assert not q(0 to 3)'active;",
    )
    .unwrap_err();
    assert!(
        errors
            .iter()
            .any(|e| e.contains("activity selection is out of bounds"))
    );
}

#[test]
fn null_slice_activity_permits_outside_endpoints() {
    let sv = lower(
        "signal q : bit_vector(0 to 2);",
        "assert not q(4 to 3)'active;",
    )
    .unwrap();
    assert!(!sv.contains("bit vh_pa"));
}

#[test]
fn indexing_a_slice_keeps_the_intermediate_bounds() {
    let errors = lower(
        "signal q : bit_vector(0 to 2);",
        "assert not q(0 to 0)(1)'active;",
    )
    .unwrap_err();
    assert!(
        errors
            .iter()
            .any(|e| e.contains("activity selection is out of bounds")),
        "{errors:?}"
    );
}

#[test]
fn nonnull_slice_keeps_the_array_direction() {
    let errors = lower(
        "signal q : bit_vector(0 to 2);",
        "assert not q(1 downto 0)'active;",
    )
    .unwrap_err();
    assert!(
        errors
            .iter()
            .any(|e| e.contains("activity selection is out of bounds")),
        "{errors:?}"
    );
}
