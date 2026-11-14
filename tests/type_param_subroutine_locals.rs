//! §6.20.3: a local of a task or function of an instantiated module,
//! interface or program declared with one of its type parameters (`MT loc;`)
//! has the type bound for that instance, as a local of its initial or always
//! blocks does. The body kept the bare `MT`, which names nothing once the
//! instance is inlined, so the local was 32 bits wide with no members
//! (aionhw/xezim#1082).

use xezim_core::ast::stmt::StatementKind;
use xezim_core::ast::types::DataType;

fn elaborate(src: &str) -> xezim_core::ElaboratedModule {
    xezim_core::parse_and_elaborate_multi(
        &[src.to_string()],
        Some("top"),
        &[],
        &["top.sv".to_string()],
        &[],
    )
    .expect("elaborate")
    .1
}

fn first_local_type(items: &[xezim_core::ast::stmt::Statement]) -> Option<&DataType> {
    items.iter().find_map(|s| match &s.kind {
        StatementKind::VarDecl { data_type, .. } => Some(data_type),
        _ => None,
    })
}

#[test]
fn subroutine_locals_take_the_instance_binding() {
    let src = "typedef struct packed { logic v; logic [7:0] d; } s_t;
module m #(type MT = s_t, parameter type BT = int) ();
  task automatic t(); MT loc; loc = '0; endtask
  function automatic int f(); BT b; b = 0; return b; endfunction
endmodule
interface i #(type IT = s_t) (); task automatic t(); IT loc; loc = '0; endtask endinterface
module top; m u (); m #(.BT(byte)) w (); i k (); endmodule\n";
    let m = elaborate(src);
    for task in ["u.t", "k.t"] {
        let td = m
            .tasks
            .get(task)
            .unwrap_or_else(|| panic!("no task {task}"));
        let dt = first_local_type(&td.items).expect("a local");
        assert!(matches!(dt, DataType::Struct(_)), "{task}: {dt:?}");
    }
    let f = m.functions.get("w.f").expect("no w.f");
    let dt = first_local_type(&f.items).expect("a local");
    assert!(!matches!(dt, DataType::TypeReference { .. }), "w.f: {dt:?}");
}
