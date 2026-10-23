//! SystemC sources (IEEE 1666-2023) lowered to SystemVerilog and elaborated
//! through the normal entry point: `systemc::configure` + `inject`.
//! Simulation results are checked in the xezim repo (`tests/systemc`),
//! against the SystemC 2.3.4 reference output.

use xezim_core::systemc;

fn write(dir: &std::path::Path, name: &str, text: &str) -> String {
    let p = dir.join(name);
    std::fs::write(&p, text).expect("write fixture");
    p.to_string_lossy().into_owned()
}

/// One test, because the SystemC configuration is process-global.
#[test]
fn lowers_elaborates_and_reports_unsupported() {
    let dir = std::env::temp_dir().join(format!("xezim_systemc_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");

    // §5.2 module with ports, a method, a thread and a child; §4.3 sc_main.
    let ok = write(
        &dir,
        "top.cpp",
        r#"#include <systemc.h>
SC_MODULE(inv) {
    sc_in<bool> a;
    sc_out<bool> y;
    void run() { y.write(!a.read()); }
    SC_CTOR(inv) { SC_METHOD(run); sensitive << a; }
};
SC_MODULE(top) {
    sc_signal<bool> s, t;
    inv* u;
    void stim() { s.write(true); wait(5, SC_NS); std::cout << t.read() << std::endl; }
    SC_CTOR(top) { u = new inv("u"); u->a(s); u->y(t); SC_THREAD(stim); }
};
int sc_main(int argc, char* argv[]) {
    top t("t");
    sc_start(10, SC_NS);
    return 0;
}
"#,
    );
    systemc::configure(vec![ok], Vec::new(), Vec::new());
    let (defs, elab) =
        xezim_core::parse_and_elaborate_multi(&[], None, &[], &[], &[]).expect("elaborates");
    assert_eq!(elab.name, "sc_main", "sc_main is the default top");
    for m in ["sc_main", "top", "inv"] {
        assert!(defs.contains_key(m), "module '{}' generated", m);
    }

    // Unsupported constructs are reported at their C++ location.
    let bad = write(
        &dir,
        "bad.cpp",
        r#"#include <systemc.h>
SC_MODULE(m) {
    void run() {
        try { wait(1, SC_NS); } catch (...) {}
    }
    SC_CTOR(m) { SC_THREAD(run); }
};
int sc_main(int, char*[]) { m x("x"); sc_start(); return 0; }
"#,
    );
    systemc::configure(vec![bad], Vec::new(), Vec::new());
    let err = xezim_core::parse_and_elaborate_multi(&[], None, &[], &[], &[])
        .expect_err("try/catch is unsupported");
    assert!(
        err.contains("bad.cpp:4:9: error: SystemC: exceptions are not supported in simulation"),
        "{}",
        err
    );
    assert!(err.contains("cannot be simulated"), "{}", err);

    systemc::configure(Vec::new(), Vec::new(), Vec::new());
    let _ = std::fs::remove_dir_all(&dir);
}
