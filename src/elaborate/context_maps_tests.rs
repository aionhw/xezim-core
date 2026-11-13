//! §6.20.3 / §20.7: equal instance contexts share storage without aliasing
//! different types or array-query bounds.

use super::*;

#[test]
fn map_index_does_not_keep_discarded_contexts_alive() {
    let mut pool = context_maps::MapInterner::default();
    let value = pool.intern([("T".into(), 8_u32)].into_iter().collect());
    let discarded = Rc::downgrade(&value);
    drop(value);
    assert!(discarded.upgrade().is_none());
    let replacement = pool.intern([("T".into(), 8_u32)].into_iter().collect());
    assert_eq!(replacement["T"], 8);
}

#[test]
fn map_hash_collisions_do_not_alias_different_bindings() {
    let mut pool = context_maps::MapInterner::default();
    let a = pool.intern_bucket([("T".into(), 8_u32)].into_iter().collect(), (1, 1));
    let b = pool.intern_bucket([("T".into(), 9_u32)].into_iter().collect(), (1, 1));
    let again = pool.intern_bucket([("T".into(), 8_u32)].into_iter().collect(), (1, 1));
    assert!(!Rc::ptr_eq(&a, &b));
    assert!(!Rc::ptr_eq(&b, &again));
    assert_eq!(a["T"], 8);
    assert_eq!(b["T"], 9);
    assert_eq!(again["T"], 8);
}

#[test]
fn map_sharing_does_not_depend_on_capacity_or_insertion_order() {
    let mut pool = context_maps::MapInterner::default();
    let mut first = HashMap::with_capacity_and_hasher(8, Default::default());
    let mut second = HashMap::with_capacity_and_hasher(128, Default::default());
    for n in 0..8 {
        first.insert(format!("T{n}"), n);
    }
    for n in (0..8).rev() {
        second.insert(format!("T{n}"), n);
    }
    let first = pool.intern(first);
    let second = pool.intern(second);
    assert!(Rc::ptr_eq(&first, &second));
    let mut changed = (*second).clone();
    changed.insert("T0".into(), 99);
    let changed = pool.intern(changed);
    assert!(!Rc::ptr_eq(&first, &changed));
    assert_eq!(first["T0"], 0);
    assert_eq!(changed["T0"], 99);
}

#[test]
fn same_width_types_keep_different_query_bounds() {
    let mut pool = context_maps::MapInterner::default();
    let descending = TypeQueryDims {
        dims: vec![(7, 4)],
        unpacked: 0,
        whole: None,
    };
    let ascending = TypeQueryDims {
        dims: vec![(0, 3)],
        unpacked: 0,
        whole: None,
    };
    let a = pool.intern([("T".into(), descending.clone())].into_iter().collect());
    let b = pool.intern([("T".into(), ascending)].into_iter().collect());
    let again = pool.intern([("T".into(), descending)].into_iter().collect());
    assert!(Rc::ptr_eq(&a, &again));
    assert!(!Rc::ptr_eq(&a, &b));
    assert_eq!(a["T"].dims, [(7, 4)]);
    assert_eq!(b["T"].dims, [(0, 3)]);
}

#[test]
fn equal_instances_share_all_three_type_context_maps() {
    let source = r#"
module leaf #(parameter int W=8, parameter type T=logic [W-1:0]);
  initial begin T value; value='1; end
endmodule
module top;
  leaf a(), b();
  leaf #(.W(9)) c();
  leaf #(.W(9), .T(bit [8:0])) d();
endmodule
"#;
    let (_, model) =
        crate::parse_and_elaborate_multi(&[source.to_string()], Some("top"), &[], &[], &[])
            .unwrap();
    let context = |name: &str| {
        &model
            .pending_initial
            .iter()
            .find(|p| p.ctx.prefix == name)
            .unwrap()
            .ctx
    };
    let (a, b, c, d) = (context("a."), context("b."), context("c."), context("d."));
    assert!(Rc::ptr_eq(&a.type_binds, &b.type_binds));
    assert!(Rc::ptr_eq(&a.type_bind_widths, &b.type_bind_widths));
    assert!(Rc::ptr_eq(&a.type_bind_queries, &b.type_bind_queries));
    // The default's syntax can still name W in both instances. Width and
    // query snapshots must distinguish its effective 8- and 9-bit bindings.
    assert!(!Rc::ptr_eq(&a.type_bind_widths, &c.type_bind_widths));
    assert!(!Rc::ptr_eq(&a.type_bind_queries, &c.type_bind_queries));
    assert!(!Rc::ptr_eq(&a.type_binds, &d.type_binds));
    assert_eq!(a.type_bind_widths["T"], 8);
    assert_eq!(c.type_bind_widths["T"], 9);
}
