//! Output sink for VCD / XTrace dumps.
//!
//! Two modes:
//!   * Inline   — writes straight to a `BufWriter<File>` on the caller thread.
//!   * Threaded — hands work to a dedicated writer thread. Two message
//!                kinds are carried:
//!                  - `Chunk(Vec<u8>)`: pre-formatted bytes (used for VCD
//!                    headers and anything written via
//!                    `std::io::Write`).
//!                  - `VcdBatch(Vec<VcdTimestep>)`: structured per-timestep
//!                    value changes. The worker thread formats them with
//!                    `write_vcd_value`. This moves the bit-by-bit ASCII
//!                    conversion off the main simulation thread, which is
//!                    the actual CPU bottleneck for VCD dumps.
//!                Batches are flushed when `pending.len() >=
//!                `VCD_BATCH_FLUSH` or at `commit()` / `Drop`.
//!
//! `VcdSink` implements `std::io::Write` so existing `writeln!(w, ...)` call
//! sites keep working unchanged.
//!
//! The underlying byte stream is a boxed `Write` ([`DumpWriter`]). For plain
//! dumps that is the file itself; for `.zst` dumps it is a streaming zstd
//! encoder (`auto_finish`, so the frame footer is written on drop — whether
//! that drop happens on the caller thread (inline) or the writer thread).

use std::fs::File;
use std::io::{self, BufWriter, Write};
use std::sync::Arc;
use std::sync::mpsc::{self, Sender};
use std::thread::JoinHandle;

use super::value::{LogicBit, Value};

/// Owned byte sink behind a `VcdSink`. `Send` so the threaded writer can own it.
pub type DumpWriter = Box<dyn Write + Send>;

const CHUNK_CAPACITY: usize = 64 * 1024;
/// Minimum buffered bytes before `commit()` hands a byte chunk to the worker.
const COMMIT_THRESHOLD: usize = 32 * 1024;
/// Number of per-timestep VCD change records to accumulate before dispatch.
const VCD_BATCH_FLUSH: usize = 256;

pub struct VcdTimestep {
    /// `Some(t)` → emit `#t` header before the changes.
    pub time: Option<u64>,
    /// (VCD identifier code, value). The code is an `Arc<str>` so the caller's
    /// per-change clone (millions of times on large dumps) is a refcount bump
    /// instead of a fresh heap allocation of the short code string.
    pub changes: Vec<(Arc<str>, Value)>,
}

/// One XTrace time slot's records, still in VALUE form. The worker renders the
/// `T,` / `D,` / `P,` / `X,` records — the ASCII conversion is the expensive
/// part of an XTrace dump and does not belong on the simulation thread.
pub struct XtraceTimestep {
    /// `Some(d)` → emit a `T,+d` time-advance record before the changes.
    pub time_delta: Option<u64>,
    /// (XTrace dictionary id, value, is_real, is_string).
    pub changes: Vec<(Arc<str>, Value, bool, bool)>,
    /// Dictionary ids of §19.5 events that fired in this slot (`X,event,sig=`).
    pub events: Vec<Arc<str>>,
}

enum WorkerMsg {
    Chunk(Vec<u8>),
    VcdBatch(Vec<VcdTimestep>),
    XtraceBatch(Vec<XtraceTimestep>),
    /// Force the worker's `BufWriter` (and any streaming zstd encoder) to
    /// flush accumulated bytes to the OS file, so a later crash/SIGKILL of
    /// the main process leaves a readable partial dump.
    Flush,
    Shutdown,
}

enum Mode {
    Inline(BufWriter<DumpWriter>),
    Threaded {
        buf: Vec<u8>,
        pending: Vec<VcdTimestep>,
        pending_xt: Vec<XtraceTimestep>,
        tx: Option<Sender<WorkerMsg>>,
        handle: Option<JoinHandle<()>>,
    },
}

pub struct VcdSink {
    mode: Mode,
}

impl VcdSink {
    pub fn inline(w: DumpWriter) -> Self {
        VcdSink {
            mode: Mode::Inline(BufWriter::new(w)),
        }
    }

    pub fn threaded(w: DumpWriter) -> Self {
        let (tx, rx) = mpsc::channel::<WorkerMsg>();
        let handle = std::thread::Builder::new()
            .name("xezim-vcd".to_string())
            .spawn(move || {
                let mut bw = BufWriter::with_capacity(256 * 1024, w);
                while let Ok(msg) = rx.recv() {
                    match msg {
                        WorkerMsg::Chunk(bytes) => {
                            let _ = bw.write_all(&bytes);
                        }
                        WorkerMsg::VcdBatch(batch) => {
                            for ts in &batch {
                                if let Some(t) = ts.time {
                                    let _ = writeln!(bw, "#{}", t);
                                }
                                for (id, val) in &ts.changes {
                                    write_vcd_value(&mut bw, val, id);
                                }
                            }
                        }
                        WorkerMsg::XtraceBatch(batch) => {
                            for ts in &batch {
                                write_xtrace_timestep(&mut bw, ts);
                            }
                        }
                        WorkerMsg::Flush => {
                            let _ = bw.flush();
                        }
                        WorkerMsg::Shutdown => break,
                    }
                }
                let _ = bw.flush();
                // `bw` drops here → flushes, then drops the inner `DumpWriter`.
                // For a zstd `auto_finish` encoder that drop writes the frame footer.
            })
            .expect("spawn xezim-vcd writer thread");
        VcdSink {
            mode: Mode::Threaded {
                buf: Vec::with_capacity(CHUNK_CAPACITY),
                pending: Vec::with_capacity(VCD_BATCH_FLUSH),
                pending_xt: Vec::new(),
                tx: Some(tx),
                handle: Some(handle),
            },
        }
    }

    /// Open a dump sink writing to `file`.
    ///
    /// * `threaded` — route formatting/IO through a background writer thread.
    /// * `zstd_level` — `Some(level)` to zstd-compress the byte stream (the
    ///   produced file is a single `.zst` frame); `None` for a plain stream.
    pub fn open_file(file: File, threaded: bool, zstd_level: Option<i32>) -> io::Result<Self> {
        let w: DumpWriter = match zstd_level {
            Some(level) => Box::new(zstd::stream::Encoder::new(file, level)?.auto_finish()),
            None => Box::new(file),
        };
        Ok(if threaded {
            Self::threaded(w)
        } else {
            Self::inline(w)
        })
    }

    /// In threaded mode: push a timestep's value changes into the pending
    /// batch (dispatched when the batch is full). In inline mode: format
    /// immediately on the caller thread.
    pub fn post_vcd_changes(&mut self, time: Option<u64>, changes: Vec<(Arc<str>, Value)>) {
        match &mut self.mode {
            Mode::Inline(w) => {
                if let Some(t) = time {
                    let _ = writeln!(w, "#{}", t);
                }
                for (id, val) in &changes {
                    write_vcd_value(w, val, id);
                }
            }
            Mode::Threaded {
                buf,
                pending,
                tx: Some(tx),
                ..
            } => {
                if !buf.is_empty() {
                    let chunk = std::mem::replace(buf, Vec::with_capacity(CHUNK_CAPACITY));
                    let _ = tx.send(WorkerMsg::Chunk(chunk));
                }
                pending.push(VcdTimestep { time, changes });
                if pending.len() >= VCD_BATCH_FLUSH {
                    let batch = std::mem::replace(pending, Vec::with_capacity(VCD_BATCH_FLUSH));
                    let _ = tx.send(WorkerMsg::VcdBatch(batch));
                }
            }
            _ => {}
        }
    }

    /// XTrace counterpart of `post_vcd_changes`: hand one time slot's records to
    /// the worker in VALUE form so the `D`/`P`/`X` record rendering — which
    /// walks every bit of every changed value — happens off the simulation
    /// thread. In inline mode it is rendered here, as before.
    ///
    /// A `VcdSink` instance carries either VCD batches or XTrace batches (the
    /// simulator holds separate sinks for the two dumps), so only the byte
    /// buffer has to be ordered against this one.
    pub fn post_xtrace_changes(&mut self, ts: XtraceTimestep) {
        match &mut self.mode {
            Mode::Inline(w) => write_xtrace_timestep(w, &ts),
            Mode::Threaded {
                buf,
                pending_xt,
                tx: Some(tx),
                ..
            } => {
                if !buf.is_empty() {
                    let chunk = std::mem::replace(buf, Vec::with_capacity(CHUNK_CAPACITY));
                    let _ = tx.send(WorkerMsg::Chunk(chunk));
                }
                pending_xt.push(ts);
                if pending_xt.len() >= VCD_BATCH_FLUSH {
                    let batch = std::mem::take(pending_xt);
                    let _ = tx.send(WorkerMsg::XtraceBatch(batch));
                }
            }
            _ => {}
        }
    }

    /// Hand any pending bytes and VCD batches to the worker. In inline
    /// mode this is a no-op; `BufWriter` handles batching. Called at
    /// natural boundaries; `Drop` flushes whatever is left.
    pub fn commit(&mut self) {
        if let Mode::Threaded {
            buf,
            pending,
            pending_xt,
            tx: Some(tx),
            ..
        } = &mut self.mode
        {
            if buf.len() >= COMMIT_THRESHOLD {
                let chunk = std::mem::replace(buf, Vec::with_capacity(CHUNK_CAPACITY));
                let _ = tx.send(WorkerMsg::Chunk(chunk));
            }
            if pending.len() >= VCD_BATCH_FLUSH {
                let batch = std::mem::replace(pending, Vec::with_capacity(VCD_BATCH_FLUSH));
                let _ = tx.send(WorkerMsg::VcdBatch(batch));
            }
            if pending_xt.len() >= VCD_BATCH_FLUSH {
                let batch = std::mem::take(pending_xt);
                let _ = tx.send(WorkerMsg::XtraceBatch(batch));
            }
        }
    }
}

/// Render an XTrace value token (§15).
///
/// * `string` (`is_string`): a §15.4 quoted, escaped literal, not a bit blob.
/// * `real` (`is_real`): a DECIMAL number — the same spelling the VCD path uses.
///   §9.3's type list is *recommended*, not exhaustive, so a `real` signal
///   carrying a decimal value is a legitimate producer choice; §15.1 explicitly
///   allows decimal "where semantically better".
/// * fully-known: `0x<hex>`.
/// * all-x / all-z: the compact `X` / `Z` forms of §15.3. A 128-bit all-z net
///   then costs 1 byte on the line instead of 130; 4-state designs sit at x/z
///   for most of reset, and full-width binary made XTrace several times LARGER
///   than the equivalent VCD.
/// * mixed x/z: FULL-WIDTH `0b<bits>`, every bit spelled out. VCD's leading-run
///   suppression is deliberately NOT copied: it is legal there only because
///   §21.7.2.1 defines a left-EXTENSION rule for a value shorter than its `$var`
///   width. XTrace defines no such rule, so a partially collapsed vector would
///   be unparseable.
///
/// Lives here, next to `write_xtrace_timestep`, because the writer thread calls
/// it: value→ASCII conversion is the bulk of an XTrace dump's cost and is what
/// the background writer exists to absorb.
pub fn xtrace_format_value(val: &Value, is_real: bool, is_string: bool) -> String {
    if is_string {
        // §9.3 `str` type + §15.4: a string signal is emitted as a quoted,
        // escaped literal, not a 1024-bit hex blob. §8.5 escapes only.
        let mut s = String::with_capacity(val.width as usize / 8 + 2);
        s.push('"');
        for b in val.sv_string_bytes() {
            match b {
                b'\\' => s.push_str("\\\\"),
                b'"' => s.push_str("\\\""),
                b'\n' => s.push_str("\\n"),
                b'\t' => s.push_str("\\t"),
                // A raw comma inside a quoted value is spec-legal (a parser that
                // honours quotes handles it), but XTrace records are
                // comma-delimited and design goal #1 is "easy to parse", so
                // escape it via §8.5 `\xHH` to stay safe for naive splitters.
                b',' => s.push_str("\\x2c"),
                0x20..=0x7e => s.push(b as char),
                other => s.push_str(&format!("\\x{:02x}", other)),
            }
        }
        s.push('"');
        return s;
    }
    if is_real || val.is_real {
        return vcd_real_string(val.to_f64());
    }
    if val.has_xz() {
        let w = val.width as usize;
        // §15.3 compact unknowns: `X` iff EVERY bit is x, `Z` iff every bit is
        // z. A mixed vector (or one with known bits) keeps full width.
        let (mut all_x, mut all_z) = (true, true);
        for i in 0..w {
            match val.get_bit(i) {
                LogicBit::X => all_z = false,
                LogicBit::Z => all_x = false,
                _ => {
                    all_x = false;
                    all_z = false;
                    break;
                }
            }
        }
        if w > 0 && all_x {
            return "X".to_string();
        }
        if w > 0 && all_z {
            return "Z".to_string();
        }
        // Per-bit binary representation preserves X/Z exactly.
        let mut s = String::with_capacity(w + 2);
        s.push_str("0b");
        for i in (0..w).rev() {
            s.push(match val.get_bit(i) {
                LogicBit::Zero => '0',
                LogicBit::One => '1',
                LogicBit::X => 'X',
                LogicBit::Z => 'Z',
            });
        }
        s
    } else if val.width <= 64 {
        format!("0x{:x}", val.to_u64().unwrap_or(0))
    } else {
        // Wide all-known: emit as hex, MSB first.
        let mut s = String::with_capacity((val.width as usize).div_ceil(4) + 2);
        s.push_str("0x");
        let mut started = false;
        let nibble_count = (val.width as usize).div_ceil(4);
        for n in (0..nibble_count).rev() {
            let mut nib: u32 = 0;
            for b in 0..4 {
                let bit_idx = n * 4 + b;
                if bit_idx < val.width as usize {
                    if let LogicBit::One = val.get_bit(bit_idx) {
                        nib |= 1 << b;
                    }
                }
            }
            if nib != 0 || started || n == 0 {
                s.push(char::from_digit(nib, 16).unwrap());
                started = true;
            }
        }
        s
    }
}

/// Render one XTrace time slot (§18 trace records). Shared by the inline path
/// and the writer thread so the two can never diverge.
///
/// `T,+delta` advances time; a single change is a `D,<id>,<val>` record, several
/// are packed 16-per-`P` record, and each fired event adds `X,event,sig=<id>`.
fn write_xtrace_timestep<W: Write>(w: &mut W, ts: &XtraceTimestep) {
    if let Some(delta) = ts.time_delta {
        let _ = writeln!(w, "T,+{}", delta);
    }
    if ts.changes.len() == 1 {
        let (id, val, is_real, is_string) = &ts.changes[0];
        let _ = writeln!(
            w,
            "D,{},{}",
            id,
            xtrace_format_value(val, *is_real, *is_string)
        );
    } else if !ts.changes.is_empty() {
        for chunk in ts.changes.chunks(16) {
            let _ = write!(w, "P");
            for (id, val, is_real, is_string) in chunk {
                let _ = write!(
                    w,
                    ",{}={}",
                    id,
                    xtrace_format_value(val, *is_real, *is_string)
                );
            }
            let _ = writeln!(w);
        }
    }
    // §10.4 `X,<event_type>[,k=v]*`. The event_type names the record family
    // (`event` — an SV event object fired); the `sig=` attribute points at the
    // object's own dictionary id, which is why an event keeps an `S` record even
    // though it carries no value. `X` inherits the current time from the T
    // record above (§19.3), so no timestamp is repeated.
    for id in &ts.events {
        let _ = writeln!(w, "X,event,sig={}", id);
    }
}

/// Hand every buffered RECORD batch (VCD and XTrace) to the worker. Must run
/// before any raw byte chunk is enqueued, or a header/footer written through
/// `std::io::Write` would overtake records that were produced earlier — which
/// silently truncates the tail of a dump when the closing `@section end` is
/// written while a partial batch is still buffered here.
fn dispatch_batches(
    pending: &mut Vec<VcdTimestep>,
    pending_xt: &mut Vec<XtraceTimestep>,
    tx: &Sender<WorkerMsg>,
) {
    if !pending.is_empty() {
        let batch = std::mem::replace(pending, Vec::with_capacity(VCD_BATCH_FLUSH));
        let _ = tx.send(WorkerMsg::VcdBatch(batch));
    }
    if !pending_xt.is_empty() {
        let batch = std::mem::take(pending_xt);
        let _ = tx.send(WorkerMsg::XtraceBatch(batch));
    }
}

impl Write for VcdSink {
    fn write(&mut self, data: &[u8]) -> io::Result<usize> {
        match &mut self.mode {
            Mode::Inline(w) => w.write(data),
            Mode::Threaded {
                buf,
                pending,
                pending_xt,
                tx: Some(tx),
                ..
            } => {
                dispatch_batches(pending, pending_xt, tx);
                buf.extend_from_slice(data);
                Ok(data.len())
            }
            Mode::Threaded { buf, .. } => {
                buf.extend_from_slice(data);
                Ok(data.len())
            }
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        match &mut self.mode {
            Mode::Inline(w) => w.flush(),
            // Unlike `commit()` (threshold-gated), a flush must force ALL
            // buffered work to the worker AND have the worker flush its own
            // BufWriter to disk — otherwise a crash loses the tail of the dump.
            Mode::Threaded {
                buf,
                pending,
                pending_xt,
                tx: Some(tx),
                ..
            } => {
                if !buf.is_empty() {
                    let chunk = std::mem::replace(buf, Vec::with_capacity(CHUNK_CAPACITY));
                    let _ = tx.send(WorkerMsg::Chunk(chunk));
                }
                dispatch_batches(pending, pending_xt, tx);
                let _ = tx.send(WorkerMsg::Flush);
                Ok(())
            }
            Mode::Threaded { .. } => Ok(()),
        }
    }
}

impl Drop for VcdSink {
    fn drop(&mut self) {
        if let Mode::Threaded {
            buf,
            pending,
            pending_xt,
            tx,
            handle,
        } = &mut self.mode
        {
            if let Some(tx_ref) = tx.as_ref() {
                if !buf.is_empty() {
                    let chunk = std::mem::take(buf);
                    let _ = tx_ref.send(WorkerMsg::Chunk(chunk));
                }
                dispatch_batches(pending, pending_xt, tx_ref);
            }
            if let Some(tx) = tx.take() {
                let _ = tx.send(WorkerMsg::Shutdown);
                drop(tx);
            }
            if let Some(h) = handle.take() {
                let _ = h.join();
            }
        }
    }
}

/// Render a `real` value as a VCD decimal number (IEEE 1800-2017 §21.7.2.1:
/// the value of a `real` variable is written as `r<decimal_number>`).
/// Rust's `{}` for `f64` is the shortest round-trip form, which is exactly
/// what a VCD reader needs; NaN/±inf have no VCD spelling, so they degrade
/// to `0` rather than emitting an unparsable token.
pub fn vcd_real_string(v: f64) -> String {
    if v.is_finite() {
        format!("{}", v)
    } else {
        "0".to_string()
    }
}

/// The binary digit string of a vector value, MSB first, with §21.7.2.1-legal
/// leading-run suppression — the same spelling a reference simulator Verilog emits.
///
/// A reader LEFT-EXTENDS a value shorter than the `$var` width using the
/// leftmost emitted character: `x` extends with x, `z` with z, and anything else
/// (`0`/`1`) with `0`. So:
///
///   * a leading run of `x` collapses to ONE `x` (`8'bxxxx0011` → `bx0011`), and
///     likewise a leading run of `z` (`8'bzzzz0011` → `bz0011`) — the reader
///     re-extends with that same character.
///   * a leading run of `0` collapses only while the first RETAINED character is
///     `1` (`8'b00001111` → `b1111`). `8'b000000x1` may NOT collapse to `bx1` —
///     that reads back as `8'bxxxxxxx1` — so one explicit `0` is kept: `b0x1`.
///   * a leading `1` extends with `0`, so nothing may be dropped in front of it.
pub fn vcd_vector_bits(val: &Value) -> String {
    let w = val.width as usize;
    let mut s = String::with_capacity(w + 1);
    for i in (0..w).rev() {
        s.push(match val.get_bit(i) {
            LogicBit::Zero => '0',
            LogicBit::One => '1',
            LogicBit::X => 'x',
            LogicBit::Z => 'z',
        });
    }
    let lead = match s.as_bytes().first() {
        Some(&c) => c,
        None => return "0".to_string(),
    };
    // `1` left-extends as `0`: the leading run is significant, keep it all.
    if lead == b'1' {
        return s;
    }
    // Index of the first character that differs from the leading one.
    let end = match s.bytes().position(|c| c != lead) {
        // Uniform vector: one character stands for all of it (`bx`, `bz`, `b0`).
        None => return (lead as char).to_string(),
        Some(i) => i,
    };
    if lead == b'0' {
        if s.as_bytes()[end] == b'1' {
            // 0-extension restores the dropped zeros.
            return s.split_off(end);
        }
        // First significant bit is x/z: keep ONE `0` so the reader 0-extends
        // instead of x/z-extending.
        let mut out = String::with_capacity(w - end + 1);
        out.push('0');
        out.push_str(&s[end..]);
        return out;
    }
    // Leading run of x (or z): the reader re-extends with that same character,
    // so one instance carries the whole run.
    let mut out = String::with_capacity(w - end + 1);
    out.push(lead as char);
    out.push_str(&s[end..]);
    out
}

/// Format a single `Value` as a VCD value-change record (real, scalar or
/// vector) — IEEE 1800-2017 §21.7.2.1. Shared by the inline path, the
/// background writer thread AND `Simulator`'s header/checkpoint paths, which
/// used to carry a second, divergent copy of this logic.
pub fn write_vcd_value<W: Write>(w: &mut W, val: &Value, id: &str) {
    if val.is_real {
        // `real` is a `$var real 64` and its changes are `r<decimal> <id>`.
        // Emitting the raw IEEE-754 bit pattern as a 64-bit binary vector
        // (the old behaviour) makes every real read back as a nonsense integer.
        let _ = writeln!(w, "r{} {}", vcd_real_string(val.to_f64()), id);
    } else if val.width == 1 {
        let ch = match val.bits_first() {
            LogicBit::Zero => '0',
            LogicBit::One => '1',
            LogicBit::X => 'x',
            LogicBit::Z => 'z',
        };
        let _ = writeln!(w, "{}{}", ch, id);
    } else {
        let _ = writeln!(w, "b{} {}", vcd_vector_bits(val), id);
    }
}
