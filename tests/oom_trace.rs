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
