//! IEEE 1800-2023 §23.8, §23.8.1, §13.4 (#193): an instance function or task
//! whose body names another scope (a dotted or member-access name, which may
//! resolve upward or downward through the hierarchy, or a call left to the
//! hierarchy) is rewritten into its instance while the instance is inlined,
//! against the instance tree as it stands then. Only bodies that name no
//! other scope keep the shared definition body until they are used.

fn elaborate(src: &str) -> xezim_core::ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[src.to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .map(|(_, m)| m)
    .expect("elaborate")
}

const SRC: &str = r#"
interface leaf_if; int id; endinterface
interface port_if;
  leaf_if tx ();
  function int tx_id(); return port_if.tx.id; endfunction
endinterface
module child; int sig = 5; endmodule
typedef struct packed { logic [3:0] a; logic [3:0] b; } pair_t;
module element;
  int state;
  pair_t p;
  child c ();
  function int own(input int v); return v + state; endfunction
  function int down(); return c.sig; endfunction
  function int member(); return p.a; endfunction
  task automatic bump(input int v); state = state + v; endtask
  task automatic poke(); c.sig = state; endtask
endmodule
module top;
  port_if pi ();
  element e0 (), e1 ();
endmodule
"#;

#[test]
fn bodies_naming_other_scopes_are_rewritten_with_their_instance() {
    let m = elaborate(SRC);
    for key in ["e0.own", "e1.own"] {
        assert!(m.deferred_function_bodies.contains_key(key), "{key} shared");
    }
    for key in ["e0.bump", "e1.bump"] {
        assert!(m.deferred_task_bodies.contains_key(key), "{key} shared");
    }
    for key in ["e0.down", "e1.down", "e0.member", "pi.tx_id"] {
        assert!(m.functions.contains_key(key), "{key} registered");
        assert!(
            !m.deferred_function_bodies.contains_key(key),
            "{key} rewritten now"
        );
    }
    for key in ["e0.poke", "e1.poke"] {
        assert!(m.tasks.contains_key(key), "{key} registered");
        assert!(
            !m.deferred_task_bodies.contains_key(key),
            "{key} rewritten now"
        );
    }
}
