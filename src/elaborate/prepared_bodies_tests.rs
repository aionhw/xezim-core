//! IEEE 1800-2023 §23.10, §27 (aionhw/xezim#721): which prepared bodies an
//! inlining pass holds on to.

use super::*;
use prepared_bodies::UNSHARED_WINDOW;

/// A leaf whose body depends on `BASE` (its generate block is `bucket[BASE]`)
/// and not on `TAG`.
const LEAF: &str = "module leaf #(parameter integer BASE=0, TAG=0)(output wire [7:0] probe);
  generate for (genvar k=BASE; k<BASE+1; k++) begin : bucket
    localparam integer number = k + 1;
    assign probe = number;
  end endgenerate
endmodule";

/// Call `run` with a function preparing `leaf` under `(BASE, TAG)` for a new
/// instance, as elaboration does: where the instance is written and again
/// when its body is inlined.
fn with_leaf(
    run: impl FnOnce(&mut dyn FnMut(u64, u64, &mut InlineCache) -> Rc<PreparedModuleItems>),
) {
    let mut parsed = crate::parse(LEAF);
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
    let _ = bind::audit_design(&mut parsed.source.descriptions);
    let crate::ast::Description::Module(module) = &parsed.source.descriptions[0] else {
        panic!("module expected");
    };
    let definitions = HashMap::from_iter([("leaf".to_string(), Definition::Module(module))]);
    let empty = HashMap::default();
    let scope = param_scope::ParamScope::new(
        &empty,
        &definitions,
        &HashMap::default(),
        &HashMap::default(),
    );
    let mut instances = 0;
    run(&mut |base, tag, cache| {
        let params = HashMap::from_iter([
            ("BASE".into(), Value::from_u64(base, 32)),
            ("TAG".into(), Value::from_u64(tag, 32)),
        ]);
        instances += 1;
        cache.prepared.enter_instance(&format!("u{instances}."));
        let mut prepare = || {
            prepare_module_items(
                definitions["leaf"],
                &definitions,
                &params,
                &HashMap::default(),
                cache,
                &scope,
            )
        };
        let written = prepare();
        let inlined = prepare();
        assert!(Rc::ptr_eq(&written, &inlined));
        inlined
    });
}

/// A definition prepared under a distinct environment for each instance
/// holds its most recent bodies only; the older ones are released.
#[test]
fn bodies_of_environments_that_never_recur_are_released() {
    with_leaf(|prepare| {
        let mut cache = InlineCache::default();
        let mut bodies = Vec::new();
        for base in 0..200 {
            bodies.push(Rc::downgrade(&prepare(base, 0, &mut cache)));
            assert!(cache.len() <= UNSHARED_WINDOW, "after {base}");
        }
        let live = bodies.iter().filter(|b| b.strong_count() > 0).count();
        assert_eq!(live, UNSHARED_WINDOW);
        assert_eq!(cache.prepared.releases, 200 - UNSHARED_WINDOW);
        assert!(bodies[0].upgrade().is_none());
        assert!(bodies[199].upgrade().is_some());
        // The index of equal bodies owns none and drops the released ones.
        let equal = cache.equal_prepared.values().next().expect("leaf");
        assert!(equal.by_content.len() <= 2 * UNSHARED_WINDOW + 2);
    });
}

/// An environment that was reused once stays for the whole pass, however
/// many other environments follow it.
#[test]
fn a_reused_body_is_kept() {
    with_leaf(|prepare| {
        let mut cache = InlineCache::default();
        let first = prepare(1000, 0, &mut cache);
        let again = prepare(1000, 0, &mut cache);
        assert!(Rc::ptr_eq(&first, &again));
        let first = {
            let held = Rc::downgrade(&first);
            drop((first, again));
            held
        };
        for base in 0..200 {
            prepare(base, 0, &mut cache);
        }
        let kept = first.upgrade().expect("the reused body is held");
        assert!(Rc::ptr_eq(&kept, &prepare(1000, 0, &mut cache)));
        assert_eq!(cache.len(), UNSHARED_WINDOW + 1);
    });
}

/// A released environment that comes back is prepared a second time and then
/// kept: its body is equal, and no third preparation follows.
#[test]
fn a_released_body_that_comes_back_is_kept_from_then_on() {
    with_leaf(|prepare| {
        let mut cache = InlineCache::default();
        let first = Rc::downgrade(&prepare(1000, 0, &mut cache));
        for base in 0..100 {
            prepare(base, 0, &mut cache);
        }
        assert!(first.upgrade().is_none());
        let second = prepare(1000, 0, &mut cache);
        let probe = |body: &PreparedModuleItems| {
            bincode::serde::encode_to_vec(PreparedView(body), crate::xez_bincode_config())
                .expect("encode")
        };
        let bytes = probe(&second);
        let second = {
            let held = Rc::downgrade(&second);
            drop(second);
            held
        };
        for base in 100..300 {
            prepare(base, 0, &mut cache);
        }
        let third = prepare(1000, 0, &mut cache);
        assert!(Rc::ptr_eq(&second.upgrade().expect("kept"), &third));
        assert_eq!(probe(&third), bytes);
        // The body of another environment differs.
        assert_ne!(probe(&prepare(1, 0, &mut cache)), bytes);
    });
}

/// Environments whose bodies are equal share one body while one of them is
/// held, and a later one finds no released body to share.
#[test]
fn equal_bodies_are_shared_while_one_is_held() {
    with_leaf(|prepare| {
        let mut cache = InlineCache::default();
        let first = prepare(7, 0, &mut cache);
        for tag in 1..100 {
            assert!(Rc::ptr_eq(&first, &prepare(7, tag, &mut cache)), "{tag}");
        }
        let first = {
            let held = Rc::downgrade(&first);
            drop(first);
            held
        };
        assert!(first.upgrade().is_some());
        // Other bodies push every key of the shared one out of the window.
        for base in 100..200 {
            prepare(base, 0, &mut cache);
        }
        assert!(first.upgrade().is_none());
        let fresh = prepare(7, 100, &mut cache);
        assert!(Rc::ptr_eq(&fresh, &prepare(7, 101, &mut cache)));
    });
}
