//! Opt-in, streaming memory diagnostics. Records describe active work, not
//! allocator ownership: RSS includes the entire process and retained pages.

use std::cell::RefCell;
use std::fs::OpenOptions;
use std::io::Write;
use std::sync::{Arc, Mutex, mpsc};
use std::time::{Duration, Instant};

thread_local! {
    static ACTIVE: RefCell<Option<Arc<Trace>>> = const { RefCell::new(None) };
}

#[derive(Clone, Default, serde::Serialize)]
struct Context {
    phase: String,
    source: String,
    definition: String,
    instance: String,
}

struct State {
    sink: Box<dyn Write + Send>,
    buffer: Vec<u8>,
    context: Context,
    counts: Vec<(&'static str, usize)>,
    sequence: u64,
    previous_rss: Option<u64>,
    failed: bool,
}

struct Trace {
    start: Instant,
    state: Mutex<State>,
}

#[derive(serde::Serialize)]
struct Record<'a> {
    event: &'a str,
    pid: u32,
    sequence: u64,
    elapsed_ms: u128,
    #[serde(flatten)]
    context: &'a Context,
    rss_kib: Option<u64>,
    peak_rss_kib: Option<u64>,
    delta_rss_kib: Option<i128>,
    counts: &'a [(&'static str, usize)],
}

fn resident_memory() -> (Option<u64>, Option<u64>) {
    // Linux reports KiB directly; do not assume a page size. Unsupported
    // platforms keep the work trace, with null memory fields.
    let status = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
    let field = |key: &str| {
        status.lines().find_map(|line| {
            line.strip_prefix(key)?
                .split_whitespace()
                .next()?
                .parse()
                .ok()
        })
    };
    (field("VmRSS:"), field("VmHWM:"))
}

impl Trace {
    fn record(&self, state: &mut State, event: &str) {
        if state.failed {
            return;
        }
        let (rss_kib, peak_rss_kib) = resident_memory();
        let delta_rss_kib = rss_kib
            .zip(state.previous_rss)
            .map(|(now, old)| i128::from(now) - i128::from(old));
        state.previous_rss = rss_kib;
        state.sequence += 1;
        let record = Record {
            event,
            pid: std::process::id(),
            sequence: state.sequence,
            elapsed_ms: self.start.elapsed().as_millis(),
            context: &state.context,
            rss_kib,
            peak_rss_kib,
            delta_rss_kib,
            counts: &state.counts,
        };
        state.buffer.clear();
        let result = serde_json::to_writer(&mut state.buffer, &record)
            .map_err(std::io::Error::other)
            .and_then(|()| {
                state.buffer.push(b'\n');
                // One append per record keeps concurrent thread sessions'
                // JSON objects together, rather than interleaving fields.
                state.sink.write_all(&state.buffer)
            })
            .and_then(|()| state.sink.flush());
        if let Err(error) = result {
            state.failed = true;
            crate::log_eprintln(&format!(
                "[oom-trace] write failed; tracing disabled: {error}"
            ));
        }
    }
}

/// Owns a trace for this thread. Nested pipeline calls reuse the outer trace.
/// Dropping the owner stops and joins its sampler, including on error paths.
pub struct Session {
    owner: Option<(mpsc::Sender<()>, std::thread::JoinHandle<()>)>,
    _thread: std::marker::PhantomData<std::rc::Rc<()>>,
}

/// Start tracing when `XEZIM_OOM_TRACE` is `1` (stderr) or a JSONL file path.
/// File output appends, so repeated library calls do not discard evidence.
/// No environment mutation, background thread or file I/O occurs when off.
pub fn session() -> Session {
    let mut session = Session {
        owner: None,
        _thread: std::marker::PhantomData,
    };
    if enabled() {
        return session;
    }
    let Some(destination) = std::env::var_os("XEZIM_OOM_TRACE") else {
        return session;
    };
    if destination.is_empty() || destination == "0" {
        return session;
    }
    let sink: Box<dyn Write + Send> = if destination == "1" {
        Box::new(std::io::stderr())
    } else {
        match OpenOptions::new()
            .create(true)
            .append(true)
            .open(destination)
        {
            Ok(file) => Box::new(file),
            Err(error) => {
                crate::log_eprintln(&format!(
                    "[oom-trace] cannot open trace; tracing disabled: {error}"
                ));
                return session;
            }
        }
    };
    let trace = Arc::new(Trace {
        start: Instant::now(),
        state: Mutex::new(State {
            sink,
            buffer: Vec::with_capacity(2048),
            context: Context::default(),
            counts: Vec::new(),
            sequence: 0,
            previous_rss: None,
            failed: false,
        }),
    });
    let (stop, receiver) = mpsc::channel();
    let sampler = Arc::clone(&trace);
    let worker = std::thread::Builder::new()
        .name("oom-trace".into())
        .spawn(move || {
            while matches!(
                receiver.recv_timeout(Duration::from_secs(1)),
                Err(mpsc::RecvTimeoutError::Timeout)
            ) {
                if let Ok(mut state) = sampler.state.lock() {
                    sampler.record(&mut state, "sample");
                }
            }
        });
    match worker {
        Ok(worker) => {
            if let Ok(mut state) = trace.state.lock() {
                trace.record(&mut state, "start");
            }
            ACTIVE.with(|active| *active.borrow_mut() = Some(trace));
            session.owner = Some((stop, worker));
        }
        Err(error) => crate::log_eprintln(&format!("[oom-trace] cannot start sampler: {error}")),
    }
    session
}

impl Drop for Session {
    fn drop(&mut self) {
        if let Some((stop, worker)) = self.owner.take() {
            let _ = stop.send(());
            let _ = worker.join();
            ACTIVE.with(|active| {
                if let Some(trace) = active.borrow_mut().take()
                    && let Ok(mut state) = trace.state.lock()
                {
                    trace.record(&mut state, "finish");
                }
            });
        }
    }
}

/// Cheap guard for callers that would otherwise build diagnostic strings.
pub fn enabled() -> bool {
    ACTIVE.with(|active| active.borrow().is_some())
}

/// Restore the enclosing work context on all return paths.
pub struct Scope(
    Option<(Arc<Trace>, Context)>,
    std::marker::PhantomData<std::rc::Rc<()>>,
);

/// Enter source work. Only the active context is retained by the sampler;
/// no ASTs, per-instance history or snapshots are kept in memory.
pub fn scope(phase: &str, source: &str, definition: &str, instance: &str) -> Scope {
    let mut scope = Scope(None, std::marker::PhantomData);
    ACTIVE.with(|active| {
        if let Some(trace) = active.borrow().as_ref()
            && let Ok(mut state) = trace.state.lock()
        {
            let previous = std::mem::replace(
                &mut state.context,
                Context {
                    phase: phase.into(),
                    source: source.into(),
                    definition: definition.into(),
                    instance: instance.into(),
                },
            );
            trace.record(&mut state, "enter");
            scope.0 = Some((Arc::clone(trace), previous));
        }
    });
    scope
}

impl Drop for Scope {
    fn drop(&mut self) {
        if let Some((trace, previous)) = self.0.take()
            && let Ok(mut state) = trace.state.lock()
        {
            trace.record(&mut state, "leave");
            state.context = previous;
        }
    }
}

/// Mark a completed pipeline phase and replace the latest table counts.
/// Counts are O(1) lengths, never a recursive heap census or serialized AST.
pub fn checkpoint(phase: &str, counts: &[(&'static str, usize)]) {
    ACTIVE.with(|active| {
        if let Some(trace) = active.borrow().as_ref()
            && let Ok(mut state) = trace.state.lock()
        {
            state.context.phase = phase.into();
            state.counts.clear();
            state.counts.extend_from_slice(counts);
            trace.record(&mut state, "checkpoint");
        }
    });
}

use crate::elaborate::{Definition, ElaboratedModule};

/// Source context for opt-in memory diagnostics; never evaluate or copy ASTs.
pub(crate) fn definition(def: Definition, phase: &str, instance: &str) -> crate::oom_trace::Scope {
    if !crate::oom_trace::enabled() {
        return crate::oom_trace::scope(phase, "", "", "");
    }
    let span = match def {
        Definition::Module(d) => d.name.span,
        Definition::Interface(d) => d.name.span,
        Definition::Program(d) => d.name.span,
        Definition::Class(d) => d.name.span,
        Definition::Covergroup(d) => d.name.span,
        Definition::Package(d) => d.name.span,
        Definition::Typedef(d) => d.name.span,
        Definition::Udp(d) => d.name.span,
    };
    crate::oom_trace::scope(
        phase,
        &crate::elaborate::audit_location(def.name(), span),
        def.name(),
        instance,
    )
}

pub(crate) fn model(phase: &str, elab: &ElaboratedModule, prepared: Option<usize>) {
    if !enabled() {
        return;
    }
    let counts = [
        ("signals", elab.signals.len()),
        ("parameters", elab.parameters.len()),
        ("instances", elab.instances.len()),
        ("continuous_assigns", elab.continuous_assigns.len()),
        ("always_blocks", elab.always_blocks.len()),
        ("initial_blocks", elab.initial_blocks.len()),
        ("pending_always", elab.pending_always.len()),
        ("pending_initial", elab.pending_initial.len()),
        ("pending_assigns", elab.pending_cont_assign.len()),
        ("functions", elab.functions.len()),
        ("tasks", elab.tasks.len()),
        ("prepared_bodies", prepared.unwrap_or(0)),
    ];
    checkpoint(
        phase,
        if prepared.is_some() {
            &counts
        } else {
            &counts[..counts.len() - 1]
        },
    );
}
