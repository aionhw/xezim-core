//! §8.7: class construction is declaration or assignment syntax.

const HEADER: &str = r#"
class item;
    int v;
    function new(int v);
        this.v = v;
    endfunction
endclass

module top;
    task take(item value);
    endtask
    initial begin
        item q[$];
"#;

#[test]
fn constructors_are_rejected_in_call_arguments() {
    for call in [
        "q.push_back(new(7));",
        "take(.value((new(7))));",
        "take(item::new(7));",
        "take(1 ? new(7) : null);",
    ] {
        let src = format!("{HEADER}{call}\nend\nendmodule");
        let result = sv_parser::parse(&src);
        assert!(
            result.errors.iter().any(|error| {
                error
                    .message
                    .contains("'new' is not permitted in a call argument")
            }),
            "{call}: {:?}",
            result.errors,
        );
    }
}

#[test]
fn constructor_assignments_and_handle_arguments_are_accepted() {
    let src = format!(
        "{HEADER}\nitem a = new(7);\nitem b;\nb = item::new(8);\nq.push_back(a);\ntake(.value(b));\nend\nendmodule"
    );
    let result = sv_parser::parse(&src);
    assert!(result.errors.is_empty(), "{:?}", result.errors);
}
