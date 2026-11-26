//! aionhw/xezim#721: the continuous assignments of instances are deferred
//! during instance expansion and moved into the design's table when the
//! design is published. The table is reserved once for all of them; grown a
//! push at a time it was copied at every doubling and ended up to twice the
//! size it needed.

fn elaborate(src: &str) -> xezim_core::ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[src.to_string()],
        Some("top"),
        &[],
        &["t.sv".to_string()],
        &[],
    )
    .map(|(_, m)| m)
    .expect("elaborates")
}

/// 100 instances of 11 assignments each.
fn design() -> String {
    let mut src = String::from("module unit(input wire pulse);\n");
    for j in 0..11 {
        src.push_str(&format!("wire tap{j}; assign tap{j} = pulse;\n"));
    }
    src.push_str("endmodule\nmodule top; reg pulse = 0; wire seen; assign seen = pulse;\n");
    for i in 0..100 {
        src.push_str(&format!("unit u{i}(.pulse(pulse));\n"));
    }
    src.push_str("endmodule\n");
    src
}

#[test]
fn deferred_assignments_fill_a_table_reserved_once() {
    let mut m = elaborate(&design());
    let deferred = m.pending_cont_assign.len();
    assert_eq!(
        deferred, 1100,
        "the assignments of the instances are deferred"
    );
    let before = m.continuous_assigns.len();
    m.materialize_pending();
    assert!(m.pending_cont_assign.is_empty());
    assert_eq!(m.continuous_assigns.len(), before + deferred);
    // Doubling from the top module's handful would leave room for 2,048
    // or more.
    let room = m.continuous_assigns.capacity();
    assert!(
        room < before + deferred + deferred / 8,
        "{room} slots for {} assignments",
        before + deferred
    );
}

/// The order of the table is the order the assignments were deferred in.
#[test]
fn the_table_keeps_the_instances_in_order() {
    let mut m = elaborate(&design());
    m.materialize_pending();
    let scopes: Vec<&str> = m
        .continuous_assigns
        .iter()
        .filter_map(|ca| ca.origin.as_ref().map(|(_, scope)| &**scope))
        .filter(|scope| !scope.is_empty())
        .collect();
    assert_eq!(scopes.len(), 1100);
    for (i, block) in scopes.chunks(11).enumerate() {
        assert!(block.iter().all(|s| *s == format!("u{i}")), "{block:?}");
    }
}
