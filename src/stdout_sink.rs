//! Buffered stdout sink for `$display`/`$write` output.
//!
//! Two modes:
//!   * Inline   — buffered `BufWriter<Stdout>` on the caller thread. Still a
//!                win over bare `print!`, which goes through a `LineWriter`
//!                and syscalls on every `\n` — picorv32 emits ~8k single-byte
//!                writes via `$write("%c",...)` and each was its own lock
//!                acquisition on the global stdout.
//!   * Threaded — hands filled buffers to a dedicated writer thread via an
//!                mpsc channel. Single-producer FIFO → output ordering is
//!                preserved.

use std::io::{self, BufWriter, Stdout, Write};
use std::sync::mpsc::{self, Receiver, Sender, TryRecvError};
use std::thread::JoinHandle;

const BUF_CAPACITY: usize = 16 * 1024;
const FLUSH_THRESHOLD: usize = 8 * 1024;

/// Lines buffered between clock reads in the line-flush path. Reading the clock
/// is cheap (vDSO) but not free, and 1-in-64 bounds the check's cost to noise
/// while still catching the "simulation went quiet" case within 64 lines.
const LINE_FLUSH_CHECK_EVERY: u32 = 64;
/// Longest a completed line may sit in the producer buffer before it is handed
/// to the writer thread. Bounds how stale a `$display` can look on a terminal;
/// far below human perception, and long enough that a burst of output coalesces
/// into whole-buffer dispatches instead of one channel send per line.
const LINE_FLUSH_MAX_DELAY: std::time::Duration = std::time::Duration::from_millis(5);

enum Mode {
    Inline(BufWriter<Stdout>),
    Threaded {
        buf: Vec<u8>,
        tx: Option<Sender<Msg>>,
        /// Emptied buffers handed back by the worker, so a dispatch does not
        /// allocate a fresh `Vec` and grow it from zero every time.
        recycle: Receiver<Vec<u8>>,
        /// Lines written since the last clock read (see `LINE_FLUSH_CHECK_EVERY`).
        lines_since_check: u32,
        /// When the buffer was last handed to the worker.
        last_dispatch: std::time::Instant,
        handle: Option<JoinHandle<()>>,
    },
}

enum Msg {
    Chunk(Vec<u8>),
    /// Barrier: the worker writes and flushes everything queued ahead of this
    /// message, then signals. See `StdoutSink::sync`.
    Sync(Sender<()>),
    Shutdown,
}

/// Writer loop.
///
/// The flush POLICY lives here rather than at the producer, and that is the
/// whole point of the threaded mode. `$display` has to stay visible during a
/// long or stalled run, so a line may not sit in a buffer indefinitely — but
/// making the producer force a flush per line just moves a write syscall per
/// line onto the simulation thread, which measured 12% SLOWER than writing
/// inline (the channel hop is pure added cost when nothing is batched).
///
/// Instead the worker drains everything already queued, then flushes once. When
/// the simulation is producing faster than the terminal accepts, thousands of
/// lines coalesce into one syscall; when it goes quiet, the queue drains and the
/// flush happens immediately, so the last line is visible right away. Both
/// properties come from the same rule.
fn run_threaded_writer<W: Write>(
    rx: Receiver<Msg>,
    mut writer: W,
    recycle_tx: Option<Sender<Vec<u8>>>,
) {
    // Hand a drained buffer back to the producer for reuse. A disconnected
    // return channel just drops it — recycling is an optimization, never a
    // correctness requirement.
    let give_back = |bytes: &mut Vec<u8>| {
        if let Some(tx) = recycle_tx.as_ref() {
            let mut b = std::mem::take(bytes);
            b.clear();
            let _ = tx.send(b);
        }
    };
    let mut stop = false;
    let mut acks: Vec<Sender<()>> = Vec::new();
    while let Ok(msg) = rx.recv() {
        match msg {
            Msg::Chunk(mut bytes) => {
                let _ = writer.write_all(&bytes);
                give_back(&mut bytes);
            }
            Msg::Sync(ack) => acks.push(ack),
            Msg::Shutdown => break,
        }
        // Absorb whatever else is already queued before paying for a flush.
        loop {
            match rx.try_recv() {
                Ok(Msg::Chunk(mut bytes)) => {
                    let _ = writer.write_all(&bytes);
                    give_back(&mut bytes);
                }
                Ok(Msg::Sync(ack)) => acks.push(ack),
                Ok(Msg::Shutdown) => {
                    stop = true;
                    break;
                }
                Err(TryRecvError::Empty) | Err(TryRecvError::Disconnected) => break,
            }
        }
        // Caught up: make everything written so far visible, then release any
        // waiting barrier — only after the flush, so the caller can rely on the
        // bytes being in the file when `sync()` returns.
        let _ = writer.flush();
        for ack in acks.drain(..) {
            let _ = ack.send(());
        }
        if stop {
            break;
        }
    }
    let _ = writer.flush();
    for ack in acks.drain(..) {
        let _ = ack.send(());
    }
}

pub struct StdoutSink {
    mode: Mode,
}

/// Encode simulation text for output: SystemVerilog strings are BYTE
/// strings carried through Rust `String`s as one Latin-1 char per byte
/// (see the parser's escape decoder / `Value::to_sv_string`), so chars
/// U+0080..U+00FF must leave as their single raw byte — `"\xab"` prints
/// byte 0xAB, not the two-byte UTF-8 of U+00AB. Chars above U+00FF (not
/// producible from SV string data) fall back to UTF-8. ASCII text — the
/// overwhelming common case — is borrowed unchanged.
fn encode_sim_bytes(s: &str) -> std::borrow::Cow<'_, [u8]> {
    if s.is_ascii() {
        return std::borrow::Cow::Borrowed(s.as_bytes());
    }
    let mut out = Vec::with_capacity(s.len());
    for c in s.chars() {
        let u = c as u32;
        if u <= 0xFF {
            out.push(u as u8);
        } else {
            let mut b = [0u8; 4];
            out.extend_from_slice(c.encode_utf8(&mut b).as_bytes());
        }
    }
    std::borrow::Cow::Owned(out)
}

impl StdoutSink {
    pub fn inline() -> Self {
        StdoutSink {
            mode: Mode::Inline(BufWriter::with_capacity(BUF_CAPACITY, io::stdout())),
        }
    }

    pub fn threaded() -> Self {
        let (tx, rx) = mpsc::channel::<Msg>();
        let (recycle_tx, recycle) = mpsc::channel::<Vec<u8>>();
        let handle = std::thread::Builder::new()
            .name("xezim-stdout".to_string())
            .spawn(move || {
                // Do NOT hold an exclusive `stdout.lock()` on the worker —
                // it would deadlock anything on the main thread that
                // touches stdout (e.g. `println!` after sim.run() returns).
                // The unlocked `Stdout` handle acquires the lock per write
                // and releases it between calls.
                let w = BufWriter::with_capacity(BUF_CAPACITY, io::stdout());
                run_threaded_writer(rx, w, Some(recycle_tx));
            })
            .expect("spawn xezim-stdout writer thread");
        StdoutSink {
            mode: Mode::Threaded {
                buf: Vec::with_capacity(BUF_CAPACITY),
                tx: Some(tx),
                recycle,
                lines_since_check: 0,
                last_dispatch: std::time::Instant::now(),
                handle: Some(handle),
            },
        }
    }

    /// Take a recycled buffer if the worker has returned one, else allocate.
    fn fresh_buf(recycle: &Receiver<Vec<u8>>) -> Vec<u8> {
        match recycle.try_recv() {
            Ok(mut b) => {
                b.clear();
                b
            }
            Err(TryRecvError::Empty) | Err(TryRecvError::Disconnected) => {
                Vec::with_capacity(BUF_CAPACITY)
            }
        }
    }

    #[inline]
    pub fn write_str(&mut self, s: &str) {
        self.write_bytes(&encode_sim_bytes(s));
    }

    #[inline]
    pub fn writeln_str(&mut self, s: &str) {
        // Append the message AND its newline before any dispatch check, so a
        // chunk boundary can never fall inside a line. It could before: the
        // threshold was tested after the message and again after the `\n`, so a
        // line that happened to fill the buffer went to the writer thread
        // WITHOUT its terminator — and with `--log` (stdout and stderr dup2'd to
        // one file) a diagnostic written meanwhile landed inside it, producing
        // `...status=running[PROF] settle=...`.
        let bytes = encode_sim_bytes(s);
        match &mut self.mode {
            Mode::Inline(w) => {
                let _ = w.write_all(&bytes);
                let _ = w.write_all(b"\n");
            }
            Mode::Threaded { buf, .. } => {
                buf.extend_from_slice(&bytes);
                buf.push(b'\n');
            }
        }
        // Line-buffered: a complete line must not sit here indefinitely, or a
        // long-running sim (e.g. c910 hello_world) churns for 30+ minutes with
        // no visible output because the 16 KB buffer never fills before a
        // SIGTERM from `timeout`. `$write`-without-newline still batches in the
        // buffer (picorv32's per-char UART pattern isn't regressed — the `\n`
        // from the surrounding message releases it).
        //
        // In THREADED mode the line is released on a TIME bound, not per line:
        // handing every line over individually costs a channel send + buffer
        // swap per `$display`, which measured 12-20% SLOWER than writing inline
        // because nothing is batched. Inline mode flushes for real, as before.
        self.line_flush();
    }

    /// Release completed lines if they have waited long enough. Threaded mode
    /// only; inline mode flushes immediately as it always has.
    fn line_flush(&mut self) {
        match &mut self.mode {
            Mode::Inline(w) => {
                let _ = w.flush();
            }
            Mode::Threaded {
                buf,
                tx: Some(tx),
                recycle,
                lines_since_check,
                last_dispatch,
                ..
            } => {
                if buf.is_empty() {
                    return;
                }
                // A full buffer goes now regardless — `write_bytes` already
                // dispatches at the threshold, so reaching here with a full
                // buffer means this line completed it.
                if buf.len() < FLUSH_THRESHOLD {
                    *lines_since_check += 1;
                    if *lines_since_check < LINE_FLUSH_CHECK_EVERY {
                        return;
                    }
                    *lines_since_check = 0;
                    if last_dispatch.elapsed() < LINE_FLUSH_MAX_DELAY {
                        return;
                    }
                }
                let chunk = std::mem::replace(buf, Self::fresh_buf(recycle));
                let _ = tx.send(Msg::Chunk(chunk));
                *lines_since_check = 0;
                *last_dispatch = std::time::Instant::now();
            }
            _ => {}
        }
    }

    fn write_bytes(&mut self, data: &[u8]) {
        match &mut self.mode {
            Mode::Inline(w) => {
                let _ = w.write_all(data);
            }
            Mode::Threaded {
                buf,
                tx: Some(tx),
                recycle,
                lines_since_check,
                last_dispatch,
                ..
            } => {
                buf.extend_from_slice(data);
                if buf.len() >= FLUSH_THRESHOLD {
                    let chunk = std::mem::replace(buf, Self::fresh_buf(recycle));
                    let _ = tx.send(Msg::Chunk(chunk));
                    *lines_since_check = 0;
                    *last_dispatch = std::time::Instant::now();
                }
            }
            _ => {}
        }
    }

    /// Hand everything buffered to the writer unconditionally. This is the
    /// caller-visible flush (`flush_stdout`, `Drop`); `writeln_str` uses the
    /// time-bounded `line_flush` instead.
    pub fn flush(&mut self) {
        match &mut self.mode {
            Mode::Inline(w) => {
                let _ = w.flush();
            }
            Mode::Threaded {
                buf,
                tx: Some(tx),
                recycle,
                lines_since_check,
                last_dispatch,
                ..
            } if !buf.is_empty() => {
                let chunk = std::mem::replace(buf, Self::fresh_buf(recycle));
                let _ = tx.send(Msg::Chunk(chunk));
                *lines_since_check = 0;
                *last_dispatch = std::time::Instant::now();
            }
            _ => {}
        }
    }

    /// Flush, then BLOCK until the writer thread has put every queued byte in
    /// the file.
    ///
    /// Needed wherever simulation output has to be ordered against something
    /// this sink does not carry — chiefly `--log`, which dup2's stdout AND
    /// stderr onto one file, so a diagnostic written directly to stderr would
    /// otherwise be able to overtake `$display` output still sitting in the
    /// queue. Call it before handing the stream to another writer.
    pub fn sync(&mut self) {
        self.flush();
        if let Mode::Threaded { tx: Some(tx), .. } = &mut self.mode {
            let (ack_tx, ack_rx) = mpsc::channel::<()>();
            if tx.send(Msg::Sync(ack_tx)).is_ok() {
                let _ = ack_rx.recv();
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{Arc, Mutex};

    #[derive(Clone)]
    struct RecordingWriter(Arc<Mutex<Vec<&'static str>>>);

    impl Write for RecordingWriter {
        fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
            self.0.lock().unwrap().push("write");
            Ok(buf.len())
        }

        fn flush(&mut self) -> io::Result<()> {
            self.0.lock().unwrap().push("flush");
            Ok(())
        }
    }

    /// Queued chunks coalesce into ONE flush, and that flush happens before
    /// shutdown — i.e. output is visible without a syscall per chunk.
    #[test]
    fn threaded_chunks_coalesce_into_one_flush() {
        let events = Arc::new(Mutex::new(Vec::new()));
        let writer = RecordingWriter(Arc::clone(&events));
        let (tx, rx) = mpsc::channel();
        tx.send(Msg::Chunk(b"buffered ".to_vec())).unwrap();
        tx.send(Msg::Chunk(b"line\n".to_vec())).unwrap();
        tx.send(Msg::Shutdown).unwrap();

        run_threaded_writer(rx, writer, None);

        // Both chunks are drained in one pass, then flushed once; the final
        // flush on loop exit is the second.
        assert_eq!(
            *events.lock().unwrap(),
            ["write", "write", "flush", "flush"]
        );
    }

    /// A chunk that arrives with nothing behind it is flushed immediately, so a
    /// `$display` in an otherwise-idle simulation is visible right away.
    #[test]
    fn lone_chunk_is_flushed_immediately() {
        let events = Arc::new(Mutex::new(Vec::new()));
        let writer = RecordingWriter(Arc::clone(&events));
        let (tx, rx) = mpsc::channel();
        tx.send(Msg::Chunk(b"line\n".to_vec())).unwrap();
        drop(tx);

        run_threaded_writer(rx, writer, None);

        assert_eq!(*events.lock().unwrap(), ["write", "flush", "flush"]);
    }
}

impl Drop for StdoutSink {
    fn drop(&mut self) {
        self.flush();
        if let Mode::Threaded { tx, handle, .. } = &mut self.mode {
            if let Some(tx) = tx.take() {
                let _ = tx.send(Msg::Shutdown);
                drop(tx);
            }
            if let Some(h) = handle.take() {
                let _ = h.join();
            }
        }
    }
}
