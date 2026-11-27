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
//!
//! Besides the per-step records, a session writes:
//! - `environment` (once, at start): machine memory and the memory limit and
//!   usage of the job's control group, which is what an out-of-memory kill is
//!   measured against;
//! - `include file access` (at finish, cumulative for the process): `include
//!   directives, path probes, header reads and the time they took;
//! - `bind.single_pass`, or `bind.discovery_pass` then `bind.rebuild`:
//!   whether bind directives forced a second elaboration of the design, with
//!   counts of the constructs that did;
//! - `error` (on failure): the failing step, with the message reduced to its
//!   class when redacting;
//! - `phase_summary` and `definition_summary` (at finish): for each phase and
//!   for the definitions that grew memory most, the number of scopes entered,
//!   the time, and the resident-memory growth of the scope itself, excluding
//!   nested scopes. These are small enough to share whole.

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

/// One open scope, for the exclusive time and memory of the summaries.
struct Frame {
    phase: String,
    definition: String,
    entered_us: u128,
    entered_rss: Option<u64>,
    nested_us: u128,
    nested_rss: i128,
}

#[derive(Default, Clone, Copy)]
struct Stat {
    scopes: usize,
    self_us: u128,
    grow_kib: u64,
    shrink_kib: u64,
}

impl Stat {
    fn add(&mut self, self_us: u128, self_rss: i128) {
        self.scopes += 1;
        self.self_us += self_us;
        if self_rss >= 0 {
            self.grow_kib += self_rss as u64;
        } else {
            self.shrink_kib += (-self_rss) as u64;
        }
    }

    fn counts(&self) -> [(&'static str, usize); 4] {
        [
            ("scopes", self.scopes),
            ("self_ms", (self.self_us / 1000) as usize),
            ("self_grow_kib", self.grow_kib as usize),
            ("self_shrink_kib", self.shrink_kib as usize),
        ]
    }
}

/// Definitions listed in the finish summary, largest growth first.
const SUMMARY_DEFINITIONS: usize = 40;

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
    last_rss: Option<u64>,
    /// The context of the first scope left since the last scope entry or
    /// checkpoint: where the work was when an error began to unwind.
    unwind_origin: Option<Context>,
    frames: Vec<Frame>,
    phase_stats: HashMap<String, Stat>,
    definition_stats: HashMap<String, Stat>,
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
        state.last_rss = rss_kib;
        if state.min_delta_kib > 0
            && matches!(event, "enter" | "leave" | "checkpoint")
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

impl Trace {
    /// Write the per-phase and per-definition totals gathered from the
    /// scopes. A definition's name is the alias its scopes already used.
    fn summaries(&self, state: &mut State) {
        let saved = std::mem::take(&mut state.context);
        let mut phases: Vec<(String, Stat)> = state.phase_stats.drain().collect();
        phases.sort_by(|a, b| b.1.grow_kib.cmp(&a.1.grow_kib).then_with(|| a.0.cmp(&b.0)));
        for (phase, stat) in phases {
            state.context = Context {
                phase,
                ..Context::default()
            };
            state.counts.clear();
            state.counts.extend_from_slice(&stat.counts());
            self.record(state, "phase_summary");
        }
        let mut definitions: Vec<(String, Stat)> = state.definition_stats.drain().collect();
        let total = definitions.len();
        definitions.sort_by(|a, b| b.1.grow_kib.cmp(&a.1.grow_kib).then_with(|| a.0.cmp(&b.0)));
        for (rank, (definition, stat)) in definitions
            .into_iter()
            .take(SUMMARY_DEFINITIONS)
            .enumerate()
        {
            state.context = Context {
                definition,
                ..Context::default()
            };
            state.counts.clear();
            state.counts.push(("rank", rank + 1));
            state.counts.push(("definitions", total));
            state.counts.extend_from_slice(&stat.counts());
            self.record(state, "definition_summary");
        }
        state.context = Context {
            phase: "include file access".into(),
            ..Context::default()
        };
        state.counts.clear();
        state
            .counts
            .extend_from_slice(&crate::sv_parser::preprocessor::include_stats::snapshot());
        self.record(state, "checkpoint");
        state.counts.clear();
        state.context = saved;
    }
}

/// Machine memory and the job's control-group memory limit and usage, in KiB.
/// A limit of 0 means none was found (no control group, or `max`).
fn environment_counts() -> Vec<(&'static str, usize)> {
    let read = |path: &str| std::fs::read_to_string(path).ok();
    let kib = |text: Option<String>| {
        text.and_then(|t| t.trim().parse::<u64>().ok())
            // An unlimited v1 group reports a value near `i64::MAX`.
            .filter(|&bytes| bytes < 1 << 60)
            .map_or(0, |bytes| (bytes / 1024) as usize)
    };
    let meminfo = read("/proc/meminfo").unwrap_or_default();
    let field = |key: &str| {
        meminfo
            .lines()
            .find_map(|line| line.strip_prefix(key)?.split_whitespace().next()?.parse().ok())
            .unwrap_or(0usize)
    };
    // v2: one line `0::/path`. v1: the line whose controller list has `memory`.
    let cgroups = read("/proc/self/cgroup").unwrap_or_default();
    let v2 = cgroups
        .lines()
        .find_map(|line| line.strip_prefix("0::"))
        .map(|path| format!("/sys/fs/cgroup{}", path.trim_end_matches('/')));
    let v1 = cgroups.lines().find_map(|line| {
        let mut parts = line.splitn(3, ':');
        let controllers = parts.nth(1)?;
        let path = parts.next()?;
        controllers
            .split(',')
            .any(|c| c == "memory")
            .then(|| format!("/sys/fs/cgroup/memory{}", path.trim_end_matches('/')))
    });
    let mut limit = 0;
    let mut usage = 0;
    let mut oom_kills = 0;
    if let Some(mut dir) = v2 {
        // The tightest limit may be on an ancestor group.
        usage = kib(read(&format!("{dir}/memory.current")));
        oom_kills = read(&format!("{dir}/memory.events"))
            .and_then(|t| {
                t.lines()
                    .find_map(|l| l.strip_prefix("oom_kill ")?.trim().parse().ok())
            })
            .unwrap_or(0usize);
        loop {
            let here = kib(read(&format!("{dir}/memory.max")));
            if here > 0 && (limit == 0 || here < limit) {
                limit = here;
            }
            match dir.rfind('/') {
                Some(cut) if dir.len() > "/sys/fs/cgroup".len() => dir.truncate(cut),
                _ => break,
            }
        }
    }
    if limit == 0
        && let Some(dir) = v1
    {
        limit = kib(read(&format!("{dir}/memory.limit_in_bytes")));
        usage = kib(read(&format!("{dir}/memory.usage_in_bytes")));
    }
    vec![
        ("mem_total_kib", field("MemTotal:")),
        ("mem_available_kib", field("MemAvailable:")),
        ("cgroup_limit_kib", limit),
        ("cgroup_usage_kib", usage),
        ("cgroup_oom_kills", oom_kills),
    ]
}

/// The class of an error message: the wording before the first quoted name.
/// With redaction on, anything that is not plain words is withheld, since a
/// message can carry a path or an identifier outside quotes.
fn error_class(message: &str, redacted: bool) -> String {
    let line = message.lines().next().unwrap_or_default();
    if !redacted {
        return line.chars().take(300).collect();
    }
    let Some(cut) = line.find(['\'', '"', '`']) else {
        return "unclassified".into();
    };
    let head = line[..cut].rsplit(": ").next().unwrap_or_default().trim();
    if head.is_empty()
        || head.split(' ').count() > 6
        || !head.chars().all(|c| c.is_ascii_alphabetic() || c == ' ')
    {
        return "unclassified".into();
    }
    head.into()
}

/// Record that the pipeline failed, in the phase the error left first. The counts are the
/// last ones a checkpoint published, so they describe the design at failure.
pub fn failure(message: &str) {
    ACTIVE.with(|active| {
        if let Some(trace) = active.borrow().as_ref()
            && let Ok(mut state) = trace.state.lock()
        {
            let class = error_class(message, trace.redacted);
            let saved = state.context.clone();
            if let Some(origin) = state.unwind_origin.take() {
                state.context = origin;
            }
            state.context.phase = format!("{}: {class}", state.context.phase);
            trace.record(&mut state, "error");
            state.context = saved;
        }
    });
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
            last_rss: None,
            unwind_origin: None,
            frames: Vec::new(),
            phase_stats: HashMap::default(),
            definition_stats: HashMap::default(),
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
                state.context.phase = "environment".into();
                state.counts = environment_counts();
                trace.record(&mut state, "checkpoint");
                state.context.phase.clear();
                state.counts.clear();
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
                    trace.summaries(&mut state);
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
            let definition = if next.definition.is_empty() {
                state
                    .frames
                    .last()
                    .map(|f| f.definition.clone())
                    .unwrap_or_default()
            } else {
                next.definition.clone()
            };
            let previous = std::mem::replace(&mut state.context, next);
            state.unwind_origin = None;
            trace.record(&mut state, "enter");
            let frame = Frame {
                phase: phase.into(),
                definition,
                entered_us: trace.start.elapsed().as_micros(),
                entered_rss: state.last_rss,
                nested_us: 0,
                nested_rss: 0,
            };
            state.frames.push(frame);
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
            let left = std::mem::replace(&mut state.context, previous);
            state.unwind_origin.get_or_insert(left);
            if let Some(frame) = state.frames.pop() {
                let us = trace
                    .start
                    .elapsed()
                    .as_micros()
                    .saturating_sub(frame.entered_us);
                let rss = state
                    .last_rss
                    .zip(frame.entered_rss)
                    .map_or(0, |(now, old)| i128::from(now) - i128::from(old));
                if let Some(parent) = state.frames.last_mut() {
                    parent.nested_us += us;
                    parent.nested_rss += rss;
                }
                let self_us = us.saturating_sub(frame.nested_us);
                let self_rss = rss - frame.nested_rss;
                state
                    .phase_stats
                    .entry(frame.phase)
                    .or_default()
                    .add(self_us, self_rss);
                if !frame.definition.is_empty() {
                    state
                        .definition_stats
                        .entry(frame.definition)
                        .or_default()
                        .add(self_us, self_rss);
                }
            }
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
            state.unwind_origin = None;
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

/// KiB held by `capacity` slots of `T` themselves, not by what they own.
fn slots_kib<T>(capacity: usize) -> usize {
    capacity.saturating_mul(std::mem::size_of::<T>()) / 1024
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
        (
            "instances_slots_kib",
            slots_kib::<crate::elaborate::ElabInstance>(elab.instances.capacity()),
        ),
        (
            "continuous_assigns_slots_kib",
            slots_kib::<crate::elaborate::ContinuousAssignment>(elab.continuous_assigns.capacity()),
        ),
        (
            "always_slots_kib",
            slots_kib::<crate::elaborate::AlwaysBlock>(elab.always_blocks.capacity()),
        ),
        (
            "pending_always_slots_kib",
            slots_kib::<crate::elaborate::PendingAlways>(elab.pending_always.capacity()),
        ),
        (
            "pending_assigns_slots_kib",
            slots_kib::<crate::elaborate::PendingContAssign>(elab.pending_cont_assign.capacity()),
        ),
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

#[cfg(test)]
mod summary_tests {
    use super::*;

    #[test]
    fn error_class_keeps_wording_and_withholds_names_when_redacted() {
        let message = "Undeclared identifier 'secret_sig' at dir/secret.sv:7:19";
        assert_eq!(error_class(message, true), "Undeclared identifier");
        assert_eq!(error_class(message, false), message);
        assert_eq!(
            error_class("dir/secret.sv:3: Unknown module 'secret_mod'", true),
            "Unknown module"
        );
        // No quoted name: the text may hold an identifier anywhere.
        assert_eq!(error_class("module secret_mod not found", true), "unclassified");
        assert_eq!(error_class("secret_mod.x 'y'", true), "unclassified");
        assert_eq!(error_class("", true), "unclassified");
    }

    #[test]
    fn stat_splits_growth_from_release() {
        let mut stat = Stat::default();
        stat.add(1500, 40);
        stat.add(2500, -10);
        assert_eq!(
            stat.counts(),
            [
                ("scopes", 2),
                ("self_ms", 4),
                ("self_grow_kib", 40),
                ("self_shrink_kib", 10),
            ]
        );
    }

    #[test]
    fn environment_reports_machine_memory_and_group_fields() {
        let counts = environment_counts();
        let names: Vec<&str> = counts.iter().map(|c| c.0).collect();
        assert_eq!(
            names,
            [
                "mem_total_kib",
                "mem_available_kib",
                "cgroup_limit_kib",
                "cgroup_usage_kib",
                "cgroup_oom_kills",
            ]
        );
        if cfg!(target_os = "linux") {
            assert!(counts[0].1 > 0);
        }
    }
}
