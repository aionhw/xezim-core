//! §23.9: the binder's hidden names (locals, formals, members) come back in
//! scope when the block that hid them ends, at any depth and with many names
//! in one scope (found reviewing the #952 series).

use xezim_core::elaborate::bind::audit_design;

/// The bindings of every mention of `name`, in walk order.
fn bindings(src: &str, name: &str) -> Vec<String> {
    let parsed = xezim_core::parse(src);
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
    let mut descs = parsed.source.descriptions;
    audit_design(&mut descs)
        .into_iter()
        .filter(|l| l.name == name)
        .map(|l| l.binding)
        .collect()
}

#[test]
fn a_hidden_name_comes_back_when_its_blocks_end() {
    // Three locals named `a` nest; each read binds to the innermost one in
    // scope, and the module's `a` once every block has ended.
    let src = "module top;
      int a, x;
      initial begin
        begin
          int a;
          begin
            int a;
            x = a;
          end
          x = a;
        end
        x = a;
      end
    endmodule";
    let got = bindings(src, "a");
    assert_eq!(got, ["none", "none", "Decl(top, Data)"], "{got:?}");
}

#[test]
fn many_locals_of_one_scope_each_hide_the_module_name() {
    let mut src = String::from("module top; int x;\n");
    for i in 0..400 {
        src.push_str(&format!("int v{i};\n"));
    }
    src.push_str("task automatic t();\n");
    for i in 0..400 {
        src.push_str(&format!("int v{i};\n"));
    }
    for i in 0..400 {
        src.push_str(&format!("x = v{i};\n"));
    }
    src.push_str("endtask\ninitial x = v399;\nendmodule\n");
    assert_eq!(bindings(&src, "v0"), ["none"]);
    assert_eq!(bindings(&src, "v399"), ["none", "Decl(top, Data)"]);
}
