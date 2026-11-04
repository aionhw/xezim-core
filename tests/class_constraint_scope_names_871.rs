//! §18.3, §18.5.8.1: a constraint of a class declared in a module may read the
//! class's members and the variables and parameters of the module, and a
//! `foreach` constraint its loop variables, inside that constraint only. The
//! check looked these names up in a set it rebuilt for every class from every
//! signal and parameter of the design inlined so far, so elaboration grew with
//! the square of the instances (aionhw/xezim#871). The names it accepts are
//! unchanged; these designs pin both sides.

fn elaborate(src: &str) -> Result<(), String> {
    xezim_core::parse_and_elaborate_multi(&[src.to_string()], Some("top"), &[], &[], &[])
        .map(|_| ())
}

const WORKER: &str = "module worker #(parameter int MAX = 12) (output int ok);
  int limit = 5;
  class job;
    rand int cnt;
    rand int vals[4];
    constraint c_lim { cnt > 0; cnt < limit; cnt <= MAX; }
    constraint c_each { foreach (vals[i]) vals[i] inside {[0 : i + MAX]}; }
  endclass
  class plain; int x; endclass
  job j = new();
  initial ok = j.randomize();
endmodule
";

#[test]
fn instance_variables_parameters_and_loop_variables_are_legal() {
    let src = format!(
        "{WORKER}module mid; int ok; worker #(.MAX(9)) w (.ok(ok)); endmodule
module top;
  int ok [3];
  for (genvar i = 0; i < 3; i++) begin : g
    worker #(.MAX(i + 8)) u (.ok(ok[i]));
  end
  mid m ();
endmodule
"
    );
    elaborate(&src).expect("module variables, parameters and loop variables are legal");
}

#[test]
fn a_loop_variable_is_not_visible_outside_its_constraint() {
    let src = "module top;
  class job;
    rand int vals[4];
    rand int cnt;
    constraint c_each { foreach (vals[i]) vals[i] < 10; }
    constraint c_other { cnt == i; }
  endclass
  job j = new();
endmodule
";
    let err = elaborate(src).expect_err("a loop variable outside its foreach");
    assert!(
        err.contains("Undeclared identifier 'i' in class constraint"),
        "{err}"
    );
}

#[test]
fn undeclared_names_are_still_rejected_in_an_instance() {
    let src = "module worker (output int ok);
  int limit = 5;
  class job;
    rand int cnt;
    constraint c_lim { cnt < limit; cnt < nowhere; }
  endclass
  job j = new();
  initial ok = j.randomize();
endmodule
module top; int ok; worker u (.ok(ok)); endmodule
";
    let err = elaborate(src).expect_err("an undeclared name");
    assert!(
        err.contains("Undeclared identifier 'nowhere' in class constraint"),
        "{err}"
    );
    let src = src.replace("cnt < nowhere;", "foreach (cnt[k]) cnt < k + nowhere;");
    let err = elaborate(&src).expect_err("an undeclared name inside foreach");
    assert!(
        err.contains("Undeclared identifier 'nowhere' in class constraint"),
        "{err}"
    );
}
