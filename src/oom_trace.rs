//! Opt-in, streaming memory diagnostics. Records describe active work, not
//! allocator ownership: RSS includes the entire process and retained pages.
//!
//! Set `XEZIM_OOM_TRACE_REDACT=1` to replace all source paths, line numbers,
//! definition names, and instance hierarchy paths with opaque per-session
//! ordinal aliases (`file#N`, `def#N`, `inst#N(d=D,g=G)`) so traces from
//! proprietary designs can be shared safely without leaking identifiers or
//! directory layouts.
//!
//! Set `XEZIM_OOM_TRACE_MIN_DELTA_KIB=<N>` to suppress high-frequency
//! per-instance records unless resident memory changed by at least `N` KiB
//! since the previous emitted record (phase boundaries and 1 s samples are
//! always emitted, and live context/counts stay updated for the sampler).

use crate::hasher::HashMap;
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

/// Per-session sequential redactor. Maps distinct file paths and definition
/// names to order-of-first-appearance ordinals (never hashes of proprietary
/// strings) and summarizes instance paths in O(1) memory without retaining any
/// per-instance strings.
#[derive(Default)]
struct Redactor {
    files: HashMap<String, usize>,
    defs: HashMap<String, usize>,
    next_instance: u64,
}

impl Redactor {
    fn strip_location_suffix(raw: &str) -> &str {
        let mut s = raw;
        for _ in 0..2 {
            if let Some((head, tail)) = s.rsplit_once(':')
                && !tail.is_empty()
                && tail.bytes().all(|b| b.is_ascii_digit())
            {
                s = head;
            } else {
                break;
            }
        }
        s
    }

    fn source(&mut self, raw: &str) -> String {
        if raw.is_empty() {
            return String::new();
        }
        let base = Self::strip_location_suffix(raw);
        let next = self.files.len() + 1;
        let id = match self.files.get(base) {
            Some(&id) => id,
            None => {
                self.files.insert(base.to_string(), next);
                next
            }
        };
        format!("file#{id}")
    }

    fn definition(&mut self, raw: &str) -> String {
        if raw.is_empty() {
            return String::new();
        }
        let next = self.defs.len() + 1;
        let id = match self.defs.get(raw) {
            Some(&id) => id,
            None => {
                self.defs.insert(raw.to_string(), next);
                next
            }
        };
        format!("def#{id}")
    }

    fn instance(&mut self, raw: &str) -> String {
        if raw.is_empty() {
            return String::new();
        }
        self.next_instance += 1;
        let depth = raw.bytes().filter(|&b| b == b'.').count() + 1;
        let indexed = raw.bytes().filter(|&b| b == b'[').count();
        format!("inst#{}(d={},g={})", self.next_instance, depth, indexed)
    }
}

struct State {
    sink: Box<dyn Write + Send>,
    buffer: Vec<u8>,
    context: Context,
    counts: Vec<(&'static str, usize)>,
    sequence: u64,
    previous_rss: Option<u64>,
    last_emitted_rss: Option<u64>,
    redactor: Option<Redactor>,
    min_delta_kib: u64,
    failed: bool,
}

struct Trace {
    start: Instant,
    redacted: bool,
    state: Mutex<State>,
}

#[derive(serde::Serialize)]
struct Record<'a> {
    event: &'a str,
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    redacted: bool,
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

fn env_flag_enabled(name: &str) -> bool {
    std::env::var_os(name).is_some_and(|v| !v.is_empty() && v != "0")
}

fn env_u64(name: &str) -> u64 {
    std::env::var(name)
        .ok()
        .and_then(|v| v.trim().parse::<u64>().ok())
        .unwrap_or(0)
}

fn is_high_frequency_phase(phase: &str) -> bool {
    matches!(
        phase,
        "inline instance"
            | "prepare instance"
            | "retain instance context"
            | "prepare module body"
            | "instance complete"
    )
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
        if state.min_delta_kib > 0
            && !matches!(event, "start" | "finish" | "sample")
            && is_high_frequency_phase(&state.context.phase)
            && let (Some(now), Some(last)) = (rss_kib, state.last_emitted_rss)
            && now.abs_diff(last) < state.min_delta_kib
        {
            return;
        }
        let delta_rss_kib = rss_kib
            .zip(state.previous_rss)
            .map(|(now, old)| i128::from(now) - i128::from(old));
        state.previous_rss = rss_kib;
        state.last_emitted_rss = rss_kib;
        state.sequence += 1;
        let record = Record {
            event,
            redacted: self.redacted,
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
    let redacted = env_flag_enabled("XEZIM_OOM_TRACE_REDACT");
    let min_delta_kib = env_u64("XEZIM_OOM_TRACE_MIN_DELTA_KIB");
    let trace = Arc::new(Trace {
        start: Instant::now(),
        redacted,
        state: Mutex::new(State {
            sink,
            buffer: Vec::with_capacity(2048),
            context: Context::default(),
            counts: Vec::new(),
            sequence: 0,
            previous_rss: None,
            last_emitted_rss: None,
            redactor: redacted.then(Redactor::default),
            min_delta_kib,
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

/// Whether the active trace redacts proprietary source paths, definition names,
/// instance paths, and byte offsets (`XEZIM_OOM_TRACE_REDACT=1`).
pub fn redacted() -> bool {
    ACTIVE.with(|active| active.borrow().as_ref().is_some_and(|t| t.redacted))
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
            let next = match &mut state.redactor {
                Some(redactor) => Context {
                    phase: phase.into(),
                    source: redactor.source(source),
                    definition: redactor.definition(definition),
                    instance: redactor.instance(instance),
                },
                None => Context {
                    phase: phase.into(),
                    source: source.into(),
                    definition: definition.into(),
                    instance: instance.into(),
                },
            };
            let previous = std::mem::replace(&mut state.context, next);
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
    let source_texts_kib = elab.source_texts.iter().map(String::len).sum::<usize>() / 1024;
    let counts = [
        ("signals", elab.signals.len()),
        ("signals_cap", elab.signals.capacity()),
        ("parameters", elab.parameters.len()),
        ("instances", elab.instances.len()),
        ("instances_cap", elab.instances.capacity()),
        ("continuous_assigns", elab.continuous_assigns.len()),
        ("continuous_assigns_cap", elab.continuous_assigns.capacity()),
        ("always_blocks", elab.always_blocks.len()),
        ("initial_blocks", elab.initial_blocks.len()),
        ("pending_always", elab.pending_always.len()),
        ("pending_initial", elab.pending_initial.len()),
        ("pending_assigns", elab.pending_cont_assign.len()),
        ("pending_assigns_cap", elab.pending_cont_assign.capacity()),
        ("functions", elab.functions.len()),
        ("tasks", elab.tasks.len()),
        ("deferred_fns", elab.deferred_function_bodies.len()),
        ("deferred_tasks", elab.deferred_task_bodies.len()),
        ("var_decl_types", elab.var_decl_types.len()),
        ("typedefs", elab.typedefs.len()),
        ("typedef_types", elab.typedef_types.len()),
        ("classes", elab.classes.len()),
        ("nets", elab.nets.len()),
        ("vector_nets", elab.vector_nets.len()),
        ("two_state_signals", elab.two_state_signals.len()),
        ("port_aliases", elab.port_aliases.len()),
        ("input_port_actuals", elab.input_port_actuals.len()),
        ("elided_ports", elab.elided_port_count),
        ("arrays", elab.arrays.len()),
        ("arrays_2d", elab.arrays_2d.len()),
        ("arrays_nd", elab.arrays_nd.len()),
        ("unpacked_decl_dims", elab.unpacked_decl_dims.len()),
        ("packed_full_dims", elab.packed_full_dims.len()),
        ("packed_struct_fields", elab.packed_struct_fields.len()),
        ("packed_elem_widths", elab.packed_signal_elem_widths.len()),
        ("property_decls", elab.property_decls.len()),
        ("property_params", elab.property_params.len()),
        ("sequences", elab.sequences.len()),
        ("decl_sites", elab.decl_sites.len()),
        ("resolved_binds", elab.resolved_binds.len()),
        ("source_texts_kib", source_texts_kib),
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
