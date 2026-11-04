//! IEEE 1800 §8.24 / §26.3: extern bodies belong to the class regardless
//! of whether it is reached through an imported or qualified spelling.
use xezim_core::ast::decl::ClassMethodKind;

#[test]
fn package_class_aliases_share_all_linked_bodies() {
    let source = r#"
package p;
 typedef class callback;
 class callback;
  string name;
  extern function new(string name="callback");
  extern function string get_name();
 endclass
 typedef callback callback_alias;
 function callback::new(string name="callback");this.name=name;endfunction
 function string callback::get_name();return name;endfunction
endpackage
module top;import p::*;callback_alias c;initial c=new();endmodule
"#;
    let (_, elab) = xezim_core::parse_and_elaborate_multi(
        &[source.to_string()], Some("top"), &[], &["alias.sv".to_string()], &[],
    ).expect("elaborate");
    for name in ["callback", "p::callback"] {
        let cls = &elab.classes[name];
        for method in ["new", "get_name"] {
            assert!(matches!(&cls.methods[method].kind, ClassMethodKind::Function(f) if !f.items.is_empty()),
                    "{name}::{method} must have its linked body");
        }
    }
}
