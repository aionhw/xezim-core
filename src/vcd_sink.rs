//! Output sink for VCD / AITRACE dumps.
//!
//! Two modes:
//!   * Inline   — writes straight to a `BufWriter<File>` on the caller thread.
//!   * Threaded — hands work to a dedicated writer thread. Two message
//!                kinds are carried:
//!                  - `Chunk(Vec<u8>)`: pre-formatted bytes (used for VCD
//!                    headers, AITRACE records, and anything written via
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
    pub changes: Vec<(String, Value)>,
}

enum WorkerMsg {
    Chunk(Vec<u8>),
    VcdBatch(Vec<VcdTimestep>),
    Shutdown,
}

enum Mode {
    Inline(BufWriter<DumpWriter>),
    Threaded {
        buf: Vec<u8>,
        pending: Vec<VcdTimestep>,
        tx: Option<Sender<WorkerMsg>>,
        handle: Option<JoinHandle<()>>,
    },
}

pub struct VcdSink {
    mode: Mode,
}

impl VcdSink {
    pub fn inline(w: DumpWriter) -> Self {
        VcdSink { mode: Mode::Inline(BufWriter::new(w)) }
    }

    pub fn threaded(w: DumpWriter) -> Self {
        let (tx, rx) = mpsc::channel::<WorkerMsg>();
        let handle = std::thread::Builder::new()
            .name("xezim-vcd".to_string())
            .spawn(move || {
                let mut bw = BufWriter::with_capacity(256 * 1024, w);
                while let Ok(msg) = rx.recv() {
                    match msg {
                        WorkerMsg::Chunk(bytes) => { let _ = bw.write_all(&bytes); }
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
        Ok(if threaded { Self::threaded(w) } else { Self::inline(w) })
    }

    /// In threaded mode: push a timestep's value changes into the pending
    /// batch (dispatched when the batch is full). In inline mode: format
    /// immediately on the caller thread.
    pub fn post_vcd_changes(&mut self, time: Option<u64>, changes: Vec<(String, Value)>) {
        match &mut self.mode {
            Mode::Inline(w) => {
                if let Some(t) = time {
                    let _ = writeln!(w, "#{}", t);
                }
                for (id, val) in &changes {
                    write_vcd_value(w, val, id);
                }
            }
            Mode::Threaded { buf, pending, tx: Some(tx), .. } => {
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

    /// Hand any pending bytes and VCD batches to the worker. In inline
    /// mode this is a no-op; `BufWriter` handles batching. Called at
    /// natural boundaries; `Drop` flushes whatever is left.
    pub fn commit(&mut self) {
        if let Mode::Threaded { buf, pending, tx: Some(tx), .. } = &mut self.mode {
            if buf.len() >= COMMIT_THRESHOLD {
                let chunk = std::mem::replace(buf, Vec::with_capacity(CHUNK_CAPACITY));
                let _ = tx.send(WorkerMsg::Chunk(chunk));
            }
            if pending.len() >= VCD_BATCH_FLUSH {
                let batch = std::mem::replace(pending, Vec::with_capacity(VCD_BATCH_FLUSH));
                let _ = tx.send(WorkerMsg::VcdBatch(batch));
            }
        }
    }
}

impl Write for VcdSink {
    fn write(&mut self, data: &[u8]) -> io::Result<usize> {
        match &mut self.mode {
            Mode::Inline(w) => w.write(data),
            Mode::Threaded { buf, pending, tx: Some(tx), .. } => {
                if !pending.is_empty() {
                    let batch = std::mem::replace(pending, Vec::with_capacity(VCD_BATCH_FLUSH));
                    let _ = tx.send(WorkerMsg::VcdBatch(batch));
                }
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
            Mode::Threaded { .. } => {
                self.commit();
                Ok(())
            }
        }
    }
}

impl Drop for VcdSink {
    fn drop(&mut self) {
        if let Mode::Threaded { buf, pending, tx, handle, .. } = &mut self.mode {
            if let Some(tx_ref) = tx.as_ref() {
                if !buf.is_empty() {
                    let chunk = std::mem::take(buf);
                    let _ = tx_ref.send(WorkerMsg::Chunk(chunk));
                }
                if !pending.is_empty() {
                    let batch = std::mem::take(pending);
                    let _ = tx_ref.send(WorkerMsg::VcdBatch(batch));
                }
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

/// Format a single `Value` as a VCD value-change record (scalar or vector).
/// Shared by the inline path and the background writer thread.
pub fn write_vcd_value<W: Write>(w: &mut W, val: &Value, id: &str) {
    let payload = format_vcd_value_bytes(val);
    if val.width == 1 {
        let _ = w.write_all(&payload);
        let _ = writeln!(w, "{}", id);
    } else {
        let _ = w.write_all(&payload);
        let _ = writeln!(w, " {}", id);
    }
}

/// Format a `Value` as the VCD value payload only.
///
/// This intentionally omits the VCD identifier and trailing newline. Surfer's
/// simulator protocol expects exactly this payload inside `SignalValue::VCDValue`.
pub fn format_vcd_value_bytes(val: &Value) -> Vec<u8> {
    if val.width == 1 {
        let ch = match val.bits_first() {
            LogicBit::Zero => b'0',
            LogicBit::One => b'1',
            LogicBit::X => b'x',
            LogicBit::Z => b'z',
        };
        vec![ch]
    } else {
        let mut bytes = Vec::with_capacity(val.width as usize + 1);
        bytes.push(b'b');
        let mut all_zero = true;
        for i in (0..val.width as usize).rev() {
            match val.get_bit(i) {
                LogicBit::Zero => {
                    if !all_zero { bytes.push(b'0'); }
                }
                LogicBit::One => { all_zero = false; bytes.push(b'1'); }
                LogicBit::X => { all_zero = false; bytes.push(b'x'); }
                LogicBit::Z => { all_zero = false; bytes.push(b'z'); }
            }
        }
        if all_zero { bytes.push(b'0'); }
        bytes
    }
}
