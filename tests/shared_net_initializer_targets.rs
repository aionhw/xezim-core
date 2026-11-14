//! §10.3.1: instance net initializer targets share source storage but resolve locally.
#[test]
fn sibling_initializers_share_targets_without_sharing_destinations() {
    let (_, design) = xezim_core::parse_and_elaborate_multi(
        &[
            "module leaf(input wire a, output wire y); wire n=a; assign y=n; endmodule
module top; wire a,b,x,y; leaf u(a,x); leaf v(b,y); endmodule"
                .into(),
        ],
        Some("top"),
        &[],
        &["top.sv".into()],
        &[],
    )
    .expect("elaborate");
    let pending: Vec<_> = design
        .pending_cont_assign
        .iter()
        .filter(|p| p.lhs_is_net_initializer)
        .collect();
    assert_eq!(pending.len(), 2);
    assert!(std::rc::Rc::ptr_eq(
        &pending[0].lhs_source,
        &pending[1].lhs_source
    ));
    assert_ne!(
        format!("{:?}", pending[0].materialize_lhs()),
        format!("{:?}", pending[1].materialize_lhs())
    );
}
