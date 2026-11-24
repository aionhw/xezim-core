//! Streaming diagnostics preserve source context through errors and a hard kill.

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

fn directory(name: &str) -> PathBuf {
    let path = std::env::temp_dir().join(format!("xezim_oom_{name}_{}", std::process::id()));
    std::fs::create_dir_all(&path).unwrap();
    path
}

fn command(name: &str, path: &Path) -> Command {
    let mut command = Command::new(std::env::current_exe().unwrap());
    command
        .args(["--exact", name, "--nocapture"])
        .env("OOM_TRACE_TEST_WORKER", "1")
        .env("XEZIM_OOM_TRACE", path)
        .stdout(Stdio::null())
        .stderr(Stdio::null());
    command
}

fn records(path: &Path) -> Vec<serde_json::Value> {
    std::fs::read_to_string(path)
        .unwrap_or_default()
        .split_terminator('\n')
        .map(|line| serde_json::from_str(line).expect("complete JSON record"))
        .collect()
}

#[test]
fn nested_scopes_restore_context_and_sessions_append() {
    if std::env::var_os("OOM_TRACE_TEST_WORKER").is_some() {
        for _ in 0..2 {
            let _session = xezim_core::oom_trace::session();
            let _outer = xezim_core::oom_trace::scope("outer", "source\"é.sv:7", "top", "top");
            let _nested_session = xezim_core::oom_trace::session();
            let result: Result<(), ()> = (|| {
                let _inner = xezim_core::oom_trace::scope("inner", "inc.svh:12", "leaf", "top.u");
                xezim_core::oom_trace::checkpoint("grow", &[("signals", 42)]);
                Err(())
            })();
            assert!(result.is_err());
            xezim_core::oom_trace::checkpoint("after error", &[("signals", 42)]);
        }
        assert!(!xezim_core::oom_trace::enabled());
        return;
    }
    let dir = directory("scope");
    let path = dir.join("trace.jsonl");
    assert!(
        command("nested_scopes_restore_context_and_sessions_append", &path)
            .status()
            .unwrap()
            .success()
    );
    let records = records(&path);
    for event in ["start", "finish"] {
        assert_eq!(records.iter().filter(|r| r["event"] == event).count(), 2);
    }
    let after = records
        .iter()
        .find(|r| r["phase"] == "after error")
        .unwrap();
    assert_eq!(after["source"], "source\"é.sv:7");
    assert_eq!(after["instance"], "top");
    assert_eq!(after["counts"][0], serde_json::json!(["signals", 42]));
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn periodic_samples_survive_process_kill() {
    if std::env::var_os("OOM_TRACE_TEST_WORKER").is_some() {
        let _session = xezim_core::oom_trace::session();
        let _scope =
            xezim_core::oom_trace::scope("allocating", "large.sv:23", "leaf", "top.bank[7].u");
        xezim_core::oom_trace::checkpoint("allocate signals", &[("signals", 1234)]);
        loop {
            std::thread::park_timeout(Duration::from_secs(1));
        }
    }
    let dir = directory("kill");
    let path = dir.join("trace.jsonl");
    let mut child = command("periodic_samples_survive_process_kill", &path)
        .spawn()
        .unwrap();
    let deadline = Instant::now() + Duration::from_secs(15);
    // Ignore a trailing partial record while the child is still writing.
    let mut sampled = None;
    while Instant::now() < deadline {
        let text = std::fs::read_to_string(&path).unwrap_or_default();
        sampled = text
            .lines()
            .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
            .find(|r| r["event"] == "sample");
        if sampled.is_some() {
            break;
        }
        if child.try_wait().unwrap().is_some() {
            break;
        }
        std::thread::sleep(Duration::from_millis(20));
    }
    let _ = child.kill();
    child.wait().unwrap();
    let sample = sampled.expect("periodic sample before the kill");
    assert_eq!(sample["source"], "large.sv:23");
    assert_eq!(sample["instance"], "top.bank[7].u");
    assert_eq!(sample["phase"], "allocate signals");
    assert_eq!(sample["counts"][0], serde_json::json!(["signals", 1234]));
    #[cfg(target_os = "linux")]
    assert!(sample["rss_kib"].as_u64().unwrap() > 0);
    assert!(!records(&path).iter().any(|r| r["event"] == "finish"));
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn redacted_trace_strips_proprietary_paths_names_and_preserves_counts() {
    if std::env::var_os("OOM_TRACE_TEST_WORKER").is_some() {
        let artifact = std::env::var("OOM_TRACE_TEST_ARTIFACT").unwrap();
        let src = r#"
module SecretProprietaryLeafCell(input logic [7:0] secret_in, output logic [7:0] secret_out);
  logic [7:0] secret_reg;
  assign secret_out = secret_in ^ secret_reg;
  always @* secret_reg = secret_in;
endmodule
module SecretProprietaryTopMod;
  logic [7:0] secret_bus;
  genvar secret_idx;
  generate for (secret_idx = 0; secret_idx < 4; secret_idx = secret_idx + 1) begin : secret_gen_loop
    logic [7:0] secret_wire;
    SecretProprietaryLeafCell u_secret_bank(.secret_in(secret_bus), .secret_out(secret_wire));
  end endgenerate
endmodule
"#;
        let _session = xezim_core::oom_trace::session();
        let (_, elab) = xezim_core::parse_and_elaborate_multi(
            &[src.to_string()],
            Some("SecretProprietaryTopMod"),
            &[],
            &["/corp/confidential_proj/rtl/SecretProprietaryFile.sv".to_string()],
            &[],
        )
        .expect("elaborate");
        xezim_core::write_compiled(&elab, &artifact).expect("write artifact");
        return;
    }

    let dir = directory("redact");
    let trace_path = dir.join("trace.jsonl");
    let artifact_path = dir.join("secret_customer_design.xez");
    let mut cmd = command(
        "redacted_trace_strips_proprietary_paths_names_and_preserves_counts",
        &trace_path,
    );
    cmd.env("XEZIM_OOM_TRACE_REDACT", "1")
        .env("OOM_TRACE_TEST_ARTIFACT", &artifact_path);
    assert!(cmd.status().unwrap().success());

    let raw = std::fs::read_to_string(&trace_path).unwrap();
    let lower = raw.to_ascii_lowercase();
    for forbidden in [
        "secret",
        "proprietary",
        "confidential",
        "customer",
        "corp",
        ".sv",
        ".xez",
        "u_secret",
    ] {
        assert!(
            !lower.contains(forbidden),
            "redacted trace leaked '{forbidden}'"
        );
    }

    let recs = records(&trace_path);
    assert!(!recs.is_empty());
    assert!(recs.iter().all(|r| r["redacted"] == true));

    // All 4 instances of the same leaf module share one opaque `def#N` alias.
    let leaf_defs: std::collections::HashSet<&str> = recs
        .iter()
        .filter(|r| r["event"] == "enter" && r["phase"] == "inline instance")
        .filter_map(|r| r["definition"].as_str())
        .collect();
    assert_eq!(
        leaf_defs.len(),
        1,
        "expected 1 leaf def alias: {leaf_defs:?}"
    );
    let leaf_def = *leaf_defs.iter().next().unwrap();
    assert!(
        leaf_def.starts_with("def#"),
        "unexpected def alias: {leaf_def}"
    );

    // Enriched structural counts are preserved without proprietary names.
    assert!(
        recs.iter().any(|r| r["phase"] == "prepare.body.built"),
        "expected prepare.body.built checkpoint"
    );
    assert!(
        recs.iter().any(|r| r["phase"] == "write.artifact.done"),
        "expected write.artifact.done checkpoint"
    );
    let elab_done = recs
        .iter()
        .find(|r| r["phase"] == "elaboration complete")
        .expect("elaboration complete checkpoint");
    let count_names: std::collections::HashSet<&str> = elab_done["counts"]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(|pair| pair[0].as_str())
        .collect();
    for expected in [
        "signals",
        "signals_cap",
        "continuous_assigns",
        "continuous_assigns_cap",
        "pending_assigns",
        "var_decl_types",
        "property_decls",
        "packed_full_dims",
    ] {
        assert!(count_names.contains(expected), "missing count '{expected}'");
    }

    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn min_delta_kib_suppresses_noisy_instance_records_while_keeping_phases() {
    if std::env::var_os("OOM_TRACE_TEST_WORKER").is_some() {
        let src = r#"
module leaf(input logic a, output logic y);
  assign y = a;
endmodule
module top;
  logic a;
  genvar i;
  generate for (i = 0; i < 16; i = i + 1) begin : g
    logic y;
    leaf u(.a(a), .y(y));
  end endgenerate
endmodule
"#;
        let _session = xezim_core::oom_trace::session();
        let _ = xezim_core::parse_and_elaborate_multi(
            &[src.to_string()],
            Some("top"),
            &[],
            &["t.sv".to_string()],
            &[],
        )
        .expect("elaborate");
        return;
    }

    let dir = directory("delta");
    let trace_path = dir.join("trace.jsonl");
    let mut cmd = command(
        "min_delta_kib_suppresses_noisy_instance_records_while_keeping_phases",
        &trace_path,
    );
    cmd.env("XEZIM_OOM_TRACE_REDACT", "1")
        .env("XEZIM_OOM_TRACE_MIN_DELTA_KIB", "1048576");
    assert!(cmd.status().unwrap().success());

    let recs = records(&trace_path);
    let inst_records = recs
        .iter()
        .filter(|r| r["phase"] == "instance complete")
        .count();
    assert!(
        inst_records < 16,
        "expected delta filter to suppress per-instance records, got {inst_records}"
    );
    assert!(recs.iter().any(|r| r["event"] == "start"));
    assert!(recs.iter().any(|r| r["event"] == "finish"));
    assert!(recs.iter().any(|r| r["phase"] == "prepare.body.built"));
    assert!(recs.iter().any(|r| r["phase"] == "elaboration complete"));
    std::fs::remove_dir_all(dir).unwrap();
}
