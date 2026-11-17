//! IEEE 1800-2023 §23.3.3 (aionhw/xezim#721): the expression connected to an
//! input port is held once per instance. The instance's deferred bodies
//! (`RewriteCtx::port_map`) and its input-port records (`InputPortActual`)
//! read the same port table; each used to hold a deep copy of every actual.
//! The table is per instance: two instances of one module keep their own
//! actuals, and a design loaded from an artifact reads the same expressions.

use xezim_core::ast::expr::{ExprKind, Expression};
use xezim_core::elaborate::{InputPortActual, RewriteCtx};

fn elaborate(src: &str) -> xezim_core::ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[src.to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .unwrap_or_else(|error| panic!("{error}\n{src}"))
    .1
}

const SRC: &str = r#"
module leaf (input logic [7:0] a, input logic [7:0] b, input logic en, output logic [7:0] y);
  logic [7:0] q;
  always_comb q = en ? (a ^ b) : a;
  always @(posedge en) y <= q + b;
endmodule
module top;
  logic [3:0] p, r;
  logic [7:0] s, t, y0, y1, y2;
  logic go, stop;
  leaf u0 (.a({p, r}), .b(s), .en(go), .y(y0));
  leaf u1 (.a({r, p}), .b(t), .en(stop), .y(y1));
  leaf u2 (.a({r, r}), .b(~s), .en(go & p[0]), .y(y2));
endmodule
"#;

fn port<'a>(m: &'a xezim_core::ElaboratedModule, formal: &str) -> &'a InputPortActual {
    m.input_port_actuals
        .iter()
        .find(|port| port.formal() == formal)
        .unwrap_or_else(|| {
            let have: Vec<_> = m.input_port_actuals.iter().map(|p| p.formal()).collect();
            panic!("no input-port record for {formal} among {have:?}")
        })
}

fn ctx<'a>(m: &'a xezim_core::ElaboratedModule, prefix: &str) -> &'a RewriteCtx {
    m.pending_always
        .iter()
        .map(|pending| &*pending.ctx)
        .find(|ctx| ctx.prefix == prefix)
        .unwrap_or_else(|| panic!("no deferred body under {prefix}"))
}

/// The first name a concatenation or a plain reference reads.
fn first_name(e: &Expression) -> &str {
    match &e.kind {
        ExprKind::Concatenation(parts) => first_name(&parts[0]),
        ExprKind::Ident(h) => &h.path[0].name.name,
        other => panic!("unexpected actual {other:?}"),
    }
}

#[test]
fn an_instance_holds_each_input_actual_once() {
    let m = elaborate(SRC);
    for inst in ["u0", "u1"] {
        let ctx = ctx(&m, &format!("{inst}."));
        for name in ["a", "b", "en"] {
            let port = port(&m, &format!("{inst}.{name}"));
            assert!(port.reads_table(&ctx.port_map), "{inst}.{name}");
            // The record answers with the table's entry, not a copy of it.
            assert!(
                std::ptr::eq(port.actual(), &ctx.port_map[name]),
                "{inst}.{name}"
            );
        }
        assert!(port(&m, &format!("{inst}.a")).shares_table_with(port(&m, &format!("{inst}.b"))));
        // Every deferred body of the instance holds that one table.
        let tables: Vec<_> = m
            .pending_always
            .iter()
            .filter(|pending| pending.ctx.prefix == format!("{inst}."))
            .map(|pending| std::rc::Rc::as_ptr(&pending.ctx.port_map))
            .collect();
        assert_eq!(tables.len(), 2, "{inst}");
        assert!(tables.iter().all(|table| *table == tables[0]), "{inst}");
    }
}

#[test]
fn instances_keep_their_own_actuals() {
    let m = elaborate(SRC);
    assert!(!port(&m, "u0.a").shares_table_with(port(&m, "u1.a")));
    assert!(!std::rc::Rc::ptr_eq(
        &ctx(&m, "u0.").port_map,
        &ctx(&m, "u1.").port_map
    ));
    assert_eq!(first_name(port(&m, "u0.a").actual()), "p");
    assert_eq!(first_name(port(&m, "u1.a").actual()), "r");
    assert!(matches!(
        port(&m, "u0.a").actual().kind,
        ExprKind::Concatenation(_)
    ));
    assert_eq!(first_name(port(&m, "u0.b").actual()), "s");
    assert_eq!(first_name(port(&m, "u1.b").actual()), "t");
    assert_eq!(first_name(port(&m, "u0.en").actual()), "go");
    assert_eq!(first_name(port(&m, "u1.en").actual()), "stop");
    // An operator expression is not renamed into the body: the port keeps
    // its own net, so it has no record and no entry in the table.
    assert_eq!(first_name(port(&m, "u2.a").actual()), "r");
    for name in ["b", "en"] {
        assert!(
            m.input_port_actuals
                .iter()
                .all(|p| p.formal() != format!("u2.{name}"))
        );
        assert!(!ctx(&m, "u2.").port_map.contains_key(name));
    }
    for inst in ["u0", "u1"] {
        for name in ["a", "b", "en"] {
            assert!(!port(&m, &format!("{inst}.{name}")).two_state());
        }
    }
}

/// The serialized record is the `(formal, actual, two_state)` tuple it has
/// always been; a loaded design owns its actuals and writes the same bytes.
#[test]
fn a_loaded_design_reads_the_same_actuals() {
    let m = elaborate(SRC);
    let config = bincode::config::standard();
    let tuples: Vec<(String, Expression, bool)> = m
        .input_port_actuals
        .iter()
        .map(|port| {
            (
                port.formal().to_string(),
                port.actual().clone(),
                port.two_state(),
            )
        })
        .collect();
    let bytes = bincode::serde::encode_to_vec(&m.input_port_actuals, config).unwrap();
    assert_eq!(
        bytes,
        bincode::serde::encode_to_vec(&tuples, config).unwrap()
    );
    let (loaded, _): (Vec<InputPortActual>, usize) =
        bincode::serde::decode_from_slice(&bytes, config).unwrap();
    assert_eq!(loaded.len(), m.input_port_actuals.len());
    for (loaded, built) in loaded.iter().zip(&m.input_port_actuals) {
        assert_eq!(loaded.formal(), built.formal());
        assert_eq!(loaded.two_state(), built.two_state());
        assert!(!loaded.shares_table_with(built));
        assert!(!std::ptr::eq(loaded.actual(), built.actual()));
    }
    assert_eq!(
        bincode::serde::encode_to_vec(&loaded, config).unwrap(),
        bytes
    );
}
