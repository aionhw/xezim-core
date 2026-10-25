//! xezim-core: shared SystemVerilog elaboration, runtime primitives, and
//! artifact format used by both the `xezim` bytecode interpreter and the
//! `xezim-b` native compiler.

// Rust permits exactly ONE `#[global_allocator]` per binary, so this lives here
// rather than in the `xezim` bin: declaring it in the shared library means the
// xezim binary, xezim-b, AND every test binary get it, whereas a declaration in
// `xezim/src/main.rs` covered only the CLI and left `cargo test` on glibc
// malloc. Measured on UVM examples: -33% to -45%; c910 memcpy -16%,
// counter-identical.
//
// Default-on but gated: a library that declares a global allocator imposes it
// on every consumer, so a downstream crate wanting its own (or the system one)
// opts out with `default-features = false`.
#[cfg(feature = "mimalloc-allocator")]
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

#[cfg(feature = "mimalloc-allocator")]
unsafe extern "C" {
    fn mi_collect(force: bool);
}

/// Hand memory that was just freed back to the OS NOW. mimalloc keeps freed
/// pages resident for its purge delay (1 s by default) so that a quick
/// re-allocation finds them warm; after a phase drops a large structure (the
/// parsed AST, the elaboration-time signal map) the next phase's big fresh
/// allocations then land on top of it, and peak RSS carries both (c906
/// CoreMark: 750 MB peak without, 599 MB with). Call it at such phase
/// boundaries only — it walks every heap.
///
/// Only a large process purges. For a small one the saving is a few MB, and
/// purging splits the huge pages later allocations would have reused: the
/// axi4 AVIP ran 2.3% more cycles with it.
pub fn release_free_memory() {
    const MIN_RESIDENT_BYTES: u64 = 256 << 20;
    let resident = std::fs::read_to_string("/proc/self/statm")
        .ok()
        .and_then(|s| {
            s.split_whitespace()
                .nth(1)
                .and_then(|v| v.parse::<u64>().ok())
        })
        .map(|pages| pages * 4096)
        .unwrap_or(0);
    if resident < MIN_RESIDENT_BYTES {
        return;
    }
    #[cfg(feature = "mimalloc-allocator")]
    // SAFETY: `mi_collect` only reorganizes the allocator's own free lists
    // and is safe to call at any time from any thread.
    unsafe {
        mi_collect(true);
    }
}

/// `XEZIM_COMPILE_PHASES`: print the wall time of one elaboration pass,
/// measured from `since`, and restart the clock.
pub(crate) fn elab_phase(label: &str, since: &mut std::time::Instant) {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    if *ON.get_or_init(|| std::env::var_os("XEZIM_COMPILE_PHASES").is_some()) {
        eprintln!(
            "[ELAB-PHASE] {}: {:.1}ms",
            label,
            since.elapsed().as_secs_f64() * 1000.0
        );
        *since = std::time::Instant::now();
    }
}

pub mod bits2;
mod body_type_params;
pub mod elaborate;
pub mod packed_value;
pub mod pkg_scope;
pub mod sdf;
pub mod stdout_sink;
pub mod upf;
pub mod value;
pub mod vcd_sink;
pub mod vhdl;

/// Deterministic hasher for `HashMap`/`HashSet` so iteration order is
/// reproducible across runs. Both `crate::hasher::HashMap` (default `RandomState`)
/// and `std::collections::HashMap` use OS-random seeds, which causes
/// non-deterministic iteration. For simulator correctness debugging
/// (and to make c910 memcpy reproducible at the same cycle each run),
/// we use a fixed-seeded ahash state.
pub mod hasher {
    #[derive(Clone, Debug)]
    pub struct DeterministicState(ahash::RandomState);

    impl Default for DeterministicState {
        fn default() -> Self {
            DeterministicState(ahash::RandomState::with_seeds(
                0xdead_beef_cafe_babe,
                0xfeed_face_0123_4567,
                0xbada_55_b01d_face,
                0x0123_4567_89ab_cdef,
            ))
        }
    }

    impl std::hash::BuildHasher for DeterministicState {
        type Hasher = ahash::AHasher;
        fn build_hasher(&self) -> Self::Hasher {
            <ahash::RandomState as std::hash::BuildHasher>::build_hasher(&self.0)
        }
    }

    pub type HashMap<K, V> = std::collections::HashMap<K, V, DeterministicState>;
    pub type HashSet<T> = std::collections::HashSet<T, DeterministicState>;
}

pub use elaborate::{ElaboratedModule, elaborate_module};
pub use sv_parser::{self, ParseResult, ast, diagnostics, lexer, parse, preprocessor};
pub use value::Value;

/// Magic bytes identifying a xezim compiled artifact.
/// Version byte: \x20 = \x1f + ContinuousAssignment.origin (source span
/// and scope of an `assign` or net declaration assignment, for code
/// coverage); \x1f = \x1e + PackageItem::Covergroup (package and
/// file-scope covergroups, §19.3), CoverBin.array_size, TransStep transitions,
/// Cross.options and CrossBin selects (§19.5-§19.6),
/// AssertionStatement.is_sequence (§16.14.3 `cover sequence`);
/// \x1e = \x1d + `local::` kept as HierarchicalIdentifier.root
/// and the parity round's parser/elaboration semantics changes (cached
/// parses from \x1d or earlier carry the old results);
/// \x1d = \x1c + AssertionStatement.label and
/// ElaboratedModule.class_decl_pkg (§21.2.1.7 `%m` scopes);
/// \x1c = \x1b + AssertionStatement.deferred (§16.4 deferred
/// assertions);
/// \x1b = \x1a + SpecifyPath terminal lists/condition/delay
/// list and ElaboratedModule.module_paths (§30.4 module paths);
/// \x1a = \x19 + ElabInstance.src_pos (time-0 process order);
/// \x13 = \x12 + ExprKind::ShallowCopy, ForeachTail.key_type,
/// ElaboratedClass.assoc_index_props, ElaboratedModule.assoc_index_widths
/// (PR #112/#24 integration);
/// \x12 = \x11 + PackageItem::Export (§26.6);
/// \x11 = \x10 + AliasDecl + ElaboratedModule.alias_pairs
/// (§10.11); \x10 = \x0f + ElaboratedClass.assoc_key_types (§6.19.6);
/// \x0f = \x0e + ModuleItem::NestedModule (§23.4);
/// \x0e = \x0d + ResolvedNetKind::ChargeStorage (§6.6.4
/// trireg); \x0d = \x0c + EventTrigger target expression (§15.5
/// runtime-select receivers);
/// \x0a = \x09 + ElaboratedModule.elab_diagnostics (warm-cache
/// diagnostic replay); \x14 = \x13 + reference-verified elaboration
/// semantics changes (untyped-param sizing through unary minus, explicit
/// signing precedence, signed genvars, tf-port implicit-name unpacked dims)
/// — cached parses/elaborations from \x13 carry the old results;
/// \x09 = \x08 + ForeverTail StatementKind variant;
/// \x19 = \x18 + SpecifyBlock.timing_checks and
/// ElaboratedModule.timing_checks (§31 timing checks);
/// \x18 = \x17 + DataType::Interface type_args (virtual-interface
/// parameterization, §25.9); \x17 = \x16 + elab interconnect_nets set (§6.6.8);
/// \x08 = \x07 + genblk branch labels + elab implicit_nets set;
/// \x07 = \x06 + Value is_fill field (§5.7.1 unbased-unsized);
/// \x06 = \x05 + serialized source_files/src_file_of_module
/// (cache-hit file:line diagnostics); \x05 = \x04 + const-NBA and branch fusion opcodes; \x04 = \x03 encoding + fused load-select opcodes
/// (LoadSignalRange/LoadSignalBit) in cached bytecode; \x03 =
/// zstd-compressed varint bincode body (\x02 = uncompressed varint,
/// \x01 = uncompressed fixint).
/// \x21 = \x20 + chained TypeName scopes and per-scope type arguments.
/// \x22 = \x21 + ClassExtends.scopes, and package type names declared in
/// more than one place renamed to `pkg::name` (§26.3).
/// \x23 = \x22 + dynamic-outer associative class property dimensions (§7.4.5).
/// \x24 = \x23 + constant selects in bind target paths (§23.11).
/// \x25 = \x24 + resolved instance binds and bind declaration generate scope (§23.11),
/// and class queue declaration kinds (§7.10).
/// \\x26 = \\x25 + compilation-unit net declarations in the serialized AST (§6.7).
/// \\x27 = \\x26 + assertion clocking event lists (§16.5 / §9.4.2).
/// \x28 = \x27 + hierarchical interface-port aliases (§25.3 / §23.8).
/// \x29 = \x28 + retained specify-parameter declaration kind (§6.20.5).
pub const XEZIM_BYTECODE_MAGIC: &[u8; 8] = b"XEZIMBC\x29";

/// Name of the synthetic root that instantiates every top of a multi-top
/// design (§23.3.3), each instance named after its module. It is not part of
/// the user's hierarchy: printed paths start at the top below it.
pub const MULTI_TOP_WRAPPER: &str = "__xezim_multi_top";

/// zstd compression level used for `.xez` artifacts. Level 3 is zstd's own
/// default — strong compression at high throughput. Empirically shrinks
/// the elaborated-bincode stream ~27×, which more than pays for the
/// compute via reduced disk I/O.
///
/// Can be overridden at runtime via `set_zstd_level()`. Default is 3.
const XEZIM_ZSTD_LEVEL_DEFAULT: i32 = 3;

/// Thread-local compression level setting. Defaults to XEZIM_ZSTD_LEVEL_DEFAULT.
/// Use `set_zstd_level()` to change it before calling `write_compiled`.
static ZSTD_LEVEL: std::sync::OnceLock<std::sync::RwLock<i32>> = std::sync::OnceLock::new();

/// Flag to enable compression statistics output. When enabled, `write_compiled`
/// and `read_compiled` will print statistics about compression ratios.
static COMPRESSION_STATS: std::sync::OnceLock<std::sync::atomic::AtomicBool> =
    std::sync::OnceLock::new();

/// Set the zstd compression level (1-22). Must be called before `write_compiled`.
/// Higher levels = better compression but slower. Level 3 is the default.
/// `--artifact-compression none`: write `-o` artifacts as raw bincode (no
/// zstd). The read side sniffs the zstd frame magic after the XEZIM header,
/// so both kinds load transparently.
static ARTIFACT_UNCOMPRESSED: std::sync::atomic::AtomicBool =
    std::sync::atomic::AtomicBool::new(false);

pub fn set_artifact_uncompressed(on: bool) {
    ARTIFACT_UNCOMPRESSED.store(on, std::sync::atomic::Ordering::Relaxed);
}

pub fn artifact_uncompressed() -> bool {
    ARTIFACT_UNCOMPRESSED.load(std::sync::atomic::Ordering::Relaxed)
}

pub fn set_zstd_level(level: i32) {
    let cell = ZSTD_LEVEL.get_or_init(|| std::sync::RwLock::new(XEZIM_ZSTD_LEVEL_DEFAULT));
    if let Ok(mut guard) = cell.write() {
        *guard = level.clamp(1, 22);
    }
}

/// Get the current zstd compression level.
pub fn get_zstd_level() -> i32 {
    ZSTD_LEVEL
        .get_or_init(|| std::sync::RwLock::new(XEZIM_ZSTD_LEVEL_DEFAULT))
        .read()
        .map(|g| *g)
        .unwrap_or(XEZIM_ZSTD_LEVEL_DEFAULT)
}

/// Enable or disable compression statistics output.
pub fn set_compression_stats(enabled: bool) {
    let cell = COMPRESSION_STATS.get_or_init(|| std::sync::atomic::AtomicBool::new(false));
    cell.store(enabled, std::sync::atomic::Ordering::Relaxed);
}

/// Check if compression statistics are enabled.
fn compression_stats_enabled() -> bool {
    COMPRESSION_STATS
        .get()
        .map(|c| c.load(std::sync::atomic::Ordering::Relaxed))
        .unwrap_or(false)
}

/// Bincode configuration for xezim compiled artifacts. Variable-int encoding
/// shrinks length tags, enum discriminants, and small integers; the wire
/// format is incompatible with the top-level `bincode::serialize` defaults
/// (which use fixed 8-byte ints), so this is the single source of truth used
/// by both writer and reader.
pub fn xez_bincode_options() -> impl bincode::Options + Copy {
    use bincode::Options;
    bincode::DefaultOptions::new()
        .with_varint_encoding()
        .with_little_endian()
}

fn artifact_version_error(file_magic: &[u8; 8]) -> Option<String> {
    if file_magic[..7] == XEZIM_BYTECODE_MAGIC[..7] && file_magic[7] != XEZIM_BYTECODE_MAGIC[7] {
        Some(format!(
            "incompatible xezim artifact version (file v{}, expected v{}); recompile with current xezim",
            file_magic[7], XEZIM_BYTECODE_MAGIC[7]
        ))
    } else {
        None
    }
}

/// Serialize a compiled ElaboratedModule to a file. Streams bincode through
/// a zstd encoder into the file; never holds the full serialized blob in
/// memory, and writes ~27× less to disk than the raw bincode stream.
///
/// Uses the compression level set via `set_zstd_level()` (default: 3).
/// If compression statistics are enabled via `set_compression_stats(true)`,
/// prints the compression ratio after writing.
pub fn write_compiled(elab: &elaborate::ElaboratedModule, path: &str) -> Result<(), String> {
    use bincode::Options;
    use std::io::Write;

    if artifact_uncompressed() {
        let f = std::fs::File::create(path).map_err(|e| format!("create '{}': {}", path, e))?;
        let mut w = std::io::BufWriter::with_capacity(1 << 20, f);
        w.write_all(XEZIM_BYTECODE_MAGIC)
            .map_err(|e| format!("write '{}': {}", path, e))?;
        xez_bincode_options()
            .serialize_into(&mut w, elab)
            .map_err(|e| format!("serialize: {}", e))?;
        return w.flush().map_err(|e| format!("flush '{}': {}", path, e));
    }

    let level = get_zstd_level();
    let stats_enabled = compression_stats_enabled();

    let f = std::fs::File::create(path).map_err(|e| format!("create '{}': {}", path, e))?;
    let mut w = std::io::BufWriter::with_capacity(1 << 20, f);
    w.write_all(XEZIM_BYTECODE_MAGIC)
        .map_err(|e| format!("write '{}': {}", path, e))?;

    // Create a wrapper to count bytes written
    let enc = zstd::stream::Encoder::new(w, level).map_err(|e| format!("zstd init: {}", e))?;

    // We need to measure uncompressed size for statistics
    // Unfortunately zstd::Encoder doesn't expose this directly, so we'll
    // serialize to a separate buffer first to measure, then compress
    if stats_enabled {
        // First, serialize to measure uncompressed size
        let mut uncompressed = Vec::new();
        xez_bincode_options()
            .serialize_into(&mut uncompressed, elab)
            .map_err(|e| format!("serialize: {}", e))?;
        let uncompressed_size = uncompressed.len();

        // Now compress and write
        let f2 = std::fs::File::create(path).map_err(|e| format!("create '{}': {}", path, e))?;
        let mut w2 = std::io::BufWriter::with_capacity(1 << 20, f2);
        w2.write_all(XEZIM_BYTECODE_MAGIC)
            .map_err(|e| format!("write '{}': {}", path, e))?;
        let mut enc2 =
            zstd::stream::Encoder::new(w2, level).map_err(|e| format!("zstd init: {}", e))?;
        enc2.write_all(&uncompressed)
            .map_err(|e| format!("zstd write: {}", e))?;
        let mut w2 = enc2.finish().map_err(|e| format!("zstd finish: {}", e))?;
        w2.flush().map_err(|e| format!("flush '{}': {}", path, e))?;

        // Get compressed size
        let compressed_size = std::fs::metadata(path).map(|m| m.len()).unwrap_or(0);

        let ratio = if uncompressed_size > 0 {
            compressed_size as f64 / uncompressed_size as f64
        } else {
            1.0
        };

        eprintln!(
            "[CACHE][COMPRESS] {}: {} bytes -> {} bytes ({:.2}× ratio, level {})",
            path,
            uncompressed_size,
            compressed_size,
            1.0 / ratio,
            level
        );

        Ok(())
    } else {
        // Standard path without statistics. bincode writes field by field;
        // batch those writes before they reach the compressor.
        let mut buffered = std::io::BufWriter::with_capacity(1 << 20, enc);
        xez_bincode_options()
            .serialize_into(&mut buffered, elab)
            .map_err(|e| format!("serialize: {}", e))?;
        let enc = buffered
            .into_inner()
            .map_err(|e| format!("flush '{}': {}", path, e))?;
        let mut w = enc.finish().map_err(|e| format!("zstd finish: {}", e))?;
        w.flush().map_err(|e| format!("flush '{}': {}", path, e))
    }
}

/// Read a compiled artifact from a file. Returns Ok(Some(elab)) if the file is
/// a valid artifact, Ok(None) if it lacks the magic header, Err on I/O,
/// version-mismatch, or deserialization failure.
///
/// If compression statistics are enabled via `set_compression_stats(true)`,
/// prints the file size and decompression info.
pub fn read_compiled(path: &str) -> Result<Option<elaborate::ElaboratedModule>, String> {
    use bincode::Options;
    use std::io::Read;

    let stats_enabled = compression_stats_enabled();

    if stats_enabled {
        let file_size = std::fs::metadata(path).map(|m| m.len()).unwrap_or(0);
        eprintln!(
            "[CACHE][COMPRESS] reading {}: {} bytes (compressed)",
            path, file_size
        );
    }

    let f = std::fs::File::open(path).map_err(|e| format!("read '{}': {}", path, e))?;
    let mut r = std::io::BufReader::with_capacity(1 << 20, f);
    let mut magic = [0u8; 8];
    if r.read_exact(&mut magic).is_err() {
        return Ok(None);
    }
    if &magic != XEZIM_BYTECODE_MAGIC {
        if let Some(err) = artifact_version_error(&magic) {
            return Err(err);
        }
        return Ok(None);
    }
    // Sniff: a zstd frame starts 28 B5 2F FD; an uncompressed artifact's
    // first payload bytes are a bincode string length (low bytes small), so
    // the two cannot collide. Chain the peeked bytes back in front.
    let mut head = [0u8; 4];
    let got = r
        .read(&mut head)
        .map_err(|e| format!("read '{}': {}", path, e))?;
    let chained = std::io::Read::chain(std::io::Cursor::new(head[..got].to_vec()), r);
    // bincode pulls every field through `read_exact`; buffer the decoder's
    // output so those are memory copies, not one decompression call each.
    let elab = if got == 4 && head == [0x28, 0xB5, 0x2F, 0xFD] {
        let dec = zstd::stream::Decoder::new(chained).map_err(|e| format!("zstd init: {}", e))?;
        xez_bincode_options()
            .deserialize_from(std::io::BufReader::with_capacity(1 << 20, dec))
            .map_err(|e| format!("deserialize: {}", e))?
    } else {
        xez_bincode_options()
            .deserialize_from(std::io::BufReader::with_capacity(1 << 16, chained))
            .map_err(|e| format!("deserialize: {}", e))?
    };
    Ok(Some(elab))
}

/// Like `read_compiled` but reads from an in-memory slice (e.g. an embedded
/// `include_bytes!()` payload in a binary produced by `--emit-native`).
pub fn read_compiled_bytes(bytes: &[u8]) -> Result<elaborate::ElaboratedModule, String> {
    use bincode::Options;
    if bytes.len() < 8 {
        return Err("xezim artifact: payload shorter than magic header".to_string());
    }
    let (magic, body) = bytes.split_at(8);
    if magic != XEZIM_BYTECODE_MAGIC {
        let mut m = [0u8; 8];
        m.copy_from_slice(magic);
        if let Some(err) = artifact_version_error(&m) {
            return Err(err);
        }
        return Err("xezim artifact: missing magic header".to_string());
    }
    // Same compressed/uncompressed sniff as `read_compiled`.
    if body.len() >= 4 && body[..4] == [0x28, 0xB5, 0x2F, 0xFD] {
        let dec = zstd::stream::Decoder::new(body).map_err(|e| format!("zstd init: {}", e))?;
        xez_bincode_options()
            .deserialize_from(std::io::BufReader::with_capacity(1 << 20, dec))
            .map_err(|e| format!("deserialize: {}", e))
    } else {
        xez_bincode_options()
            .deserialize(body)
            .map_err(|e| format!("deserialize: {}", e))
    }
}

use std::rc::Rc;

/// Implementation-defined `--module-timescale` command-line extension.
/// `global` applies to every module with no explicit source-level timescale;
/// `named` applies to the listed modules likewise. Exponents are powers of ten
/// in seconds (e.g. `1ns` = -9). Never overrides an explicit timescale.
///
/// `force` (`-override_timescale`) is the exception: when set, it is the
/// timescale of EVERY design element, package and compilation-unit scope.
/// `\`timescale` directives, `timeunit`/`timeprecision` declarations and the
/// other fields are ignored. Time literals with a unit (`#3ns`) keep their
/// absolute value.
#[derive(Clone, Default)]
pub struct ModuleTimescaleCli {
    pub global: Option<(i32, i32)>,
    pub named: std::collections::HashMap<String, (i32, i32)>,
    pub force: Option<(i32, i32)>,
}

/// Library-search configuration from the CLI (`-v <file>`, `-y <dir>`,
/// `+libext+<ext>`),
/// consumed by `resolve_library_modules`. Commercial semantics: a `-v` file's
/// definitions are adopted only to satisfy unresolved instantiations (never
/// top candidates); `+libext+` REPLACES the default `-y` extension list.
#[derive(Default, Clone)]
pub struct LibraryCli {
    pub lib_files: Vec<String>,
    pub lib_dirs: Vec<String>,
    /// `None` = default extensions (v, sv, V); `Some(list)` = exactly `list`.
    pub lib_exts: Option<Vec<String>>,
    /// Emit detailed parse and adoption diagnostics for explicit `-v` files.
    pub primitive_verbose: bool,
}

static LIBRARY_CLI: std::sync::OnceLock<std::sync::Mutex<LibraryCli>> = std::sync::OnceLock::new();

/// Whether `--primitive-verbose` is active — read by the simulator's UDP
/// lowering to print per-terminal resolution detail.
pub fn primitive_verbose() -> bool {
    library_cli_cell()
        .lock()
        .map(|g| g.primitive_verbose)
        .unwrap_or(false)
}

fn library_cli_cell() -> &'static std::sync::Mutex<LibraryCli> {
    LIBRARY_CLI.get_or_init(|| std::sync::Mutex::new(LibraryCli::default()))
}

/// `-xenowarn`: suppress the §6.10 "implicit 1-bit net created" warnings.
/// Gate-level customer designs with thousands of vendor-cell pins can emit
/// thousands of these; the flag silences the WARNING while keeping the
/// implicit-net behavior itself (and the `default_nettype none error).
static IMPLICIT_NET_WARN: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(true);

pub fn set_implicit_net_warn(on: bool) {
    IMPLICIT_NET_WARN.store(on, std::sync::atomic::Ordering::Relaxed);
}

/// `--strict-top`: a `-s <name>` that names no known module is an ERROR
/// instead of a warning plus auto-detection of the hierarchy root.
///
/// The lenient default exists to recover from wrong `:top_module:` values in
/// generated corpora (sv-tests' veer-el2 names a module that does not exist),
/// and there is no way to tell that case apart from a plain typo — both are
/// "named top absent, other modules present".
///
/// Strict is now the DEFAULT (xezim#107): `-s name` is an explicit user
/// assertion about the design, and silently simulating a DIFFERENT root on a
/// typo is exactly the CI failure mode reported — a warning line is the
/// easiest thing to lose in a CI log. The tolerance worth keeping is "you
/// didn't say" (no `-s` still auto-detects), not "you said wrong". A
/// generated corpus that knowingly carries stale `:top_module:` names (the
/// sv-tests case above) opts back out with `--no-strict-top`.
static STRICT_TOP: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(true);

pub fn set_strict_top(on: bool) {
    STRICT_TOP.store(on, std::sync::atomic::Ordering::Relaxed);
}

pub fn strict_top() -> bool {
    STRICT_TOP.load(std::sync::atomic::Ordering::Relaxed)
}

/// One command-line parameter override: `-gNAME=VALUE`, or `-GNAME=VALUE`
/// (`force`).
#[derive(Clone, Debug)]
pub struct ParamOverride {
    /// The module a `/<top>/NAME` path names; None: every module.
    pub module: Option<String>,
    pub name: String,
    /// Value text: a constant expression, or plain text for a `string`
    /// parameter.
    pub value: String,
    /// Also beats a value given at an instantiation or by `defparam`.
    pub force: bool,
}

static PARAM_OVERRIDES: std::sync::Mutex<Vec<ParamOverride>> = std::sync::Mutex::new(Vec::new());
static FORCED_PARAM_NAMES: std::sync::Mutex<Vec<String>> = std::sync::Mutex::new(Vec::new());
static ANY_FORCED_PARAM: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// Install the command-line parameter overrides, in command-line order;
/// replaces any earlier set. Each value becomes the parameter's declared
/// default, so a value given at an instantiation or by `defparam` still wins
/// unless the override is forced.
pub fn set_param_overrides(overrides: Vec<ParamOverride>) {
    let forced: Vec<String> = overrides
        .iter()
        .filter(|o| o.force && o.module.is_none())
        .map(|o| o.name.clone())
        .collect();
    ANY_FORCED_PARAM.store(!forced.is_empty(), std::sync::atomic::Ordering::Relaxed);
    *FORCED_PARAM_NAMES.lock().unwrap() = forced;
    *PARAM_OVERRIDES.lock().unwrap() = overrides;
}

/// Parameters a forced override (`-GNAME=VALUE`) set in every module: an
/// instance's own value for one of them is dropped so the default applies.
pub(crate) fn forced_param_names() -> Vec<String> {
    if !ANY_FORCED_PARAM.load(std::sync::atomic::Ordering::Relaxed) {
        return Vec::new();
    }
    FORCED_PARAM_NAMES.lock().unwrap().clone()
}

/// `--verbose`: per-file compile progress — which file is being parsed and
/// which definitions it contributed to the working library. The point is
/// debuggability of big `-f` builds ("did my testbench actually get compiled,
/// and what came out of it?"), so the output names every module/interface/
/// package/program/class rather than just counting them.
static COMPILE_VERBOSE: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

pub fn set_compile_verbose(on: bool) {
    COMPILE_VERBOSE.store(on, std::sync::atomic::Ordering::Relaxed);
}

pub fn compile_verbose() -> bool {
    COMPILE_VERBOSE.load(std::sync::atomic::Ordering::Relaxed)
}

/// Single-line build progress on stderr: rewrites itself with `\r` so a long
/// parse/elaboration shows a live indicator instead of silence. Active only
/// when stderr is a terminal — piped output and `-l` logs never see control
/// characters — and callers skip it under `--verbose`, which already prints a
/// full line per file.
pub fn progress_status(msg: &str) {
    use std::io::{IsTerminal, Write};
    let err = std::io::stderr();
    if !err.is_terminal() {
        return;
    }
    // Truncate to one line: a long path must not wrap, or the \r rewrite
    // leaves stale fragments behind.
    let msg: String = if msg.len() > 100 {
        format!("...{}", &msg[msg.len() - 97..])
    } else {
        msg.to_string()
    };
    let mut h = err.lock();
    let _ = write!(h, "\r\x1b[K{}", msg);
    let _ = h.flush();
}

/// Erase the progress line (call before printing normal output).
pub fn progress_clear() {
    use std::io::{IsTerminal, Write};
    let err = std::io::stderr();
    if !err.is_terminal() {
        return;
    }
    let mut h = err.lock();
    let _ = write!(h, "\r\x1b[K");
    let _ = h.flush();
}

pub(crate) fn implicit_net_warn() -> bool {
    IMPLICIT_NET_WARN.load(std::sync::atomic::Ordering::Relaxed)
}

// --- Elaboration diagnostic capture (for warm-cache replay) ---------------
//
// Elaboration emits diagnostics (implicit-net warnings, port-width lint,
// unresolved-module notes, width-underflow) as a side effect. A warm design-
// cache HIT skips elaboration, so those messages would silently vanish. When
// capture is active, `elab_diag` records each message so the caller can store
// it in the artifact and replay it on a hit. Messages are ALWAYS printed live.
thread_local! {
    static ELAB_DIAG_SINK: std::cell::RefCell<Option<Vec<String>>> =
        const { std::cell::RefCell::new(None) };
}

/// Start capturing elaboration diagnostics (single-threaded elaboration).
pub fn elab_diag_capture_begin() {
    ELAB_DIAG_SINK.with(|c| *c.borrow_mut() = Some(Vec::new()));
}

/// Stop capturing and return the captured messages (empty if not capturing).
pub fn elab_diag_capture_take() -> Vec<String> {
    ELAB_DIAG_SINK.with(|c| c.borrow_mut().take().unwrap_or_default())
}

/// How many times one KIND of elaboration diagnostic is reported before the
/// rest are summarized away. A design with hundreds of implicit nets (or
/// width-mismatched ports) otherwise buries every other message.
const DIAG_KIND_LIMIT_DEFAULT: u32 = 5;

/// The active cap, from `XEZIM_DIAG_LIMIT` (`0` = unlimited).
///
/// The default keeps a noisy design readable, but it hides exactly the
/// messages you reach for when a whole CLASS of things is wrong: five port
/// width mismatches followed by "further messages suppressed" reads as "there
/// were five", and the count that would have told you it was systemic is gone.
/// Raise it when a diagnostic is the thing you are chasing rather than noise.
///
/// Read once — the cap must not change mid-elaboration, or a warm-cache replay
/// would not reproduce the same output. An unparseable value keeps the default
/// rather than failing a run over a diagnostic setting.
fn diag_kind_limit() -> u32 {
    static LIMIT: std::sync::OnceLock<u32> = std::sync::OnceLock::new();
    *LIMIT.get_or_init(|| match std::env::var("XEZIM_DIAG_LIMIT") {
        Ok(v) => match v.trim().parse::<u32>() {
            Ok(0) => u32::MAX,
            Ok(n) => n,
            Err(_) => DIAG_KIND_LIMIT_DEFAULT,
        },
        Err(_) => DIAG_KIND_LIMIT_DEFAULT,
    })
}

/// Group key for the duplicate cap: the message up to the first quoted name.
/// "…undeclared identifier 'a'" and "…undeclared identifier 'b'" share a key,
/// so the cap counts one KIND rather than one exact string.
fn diag_kind_key(msg: &str) -> &str {
    match msg.find('\'') {
        Some(i) => &msg[..i],
        None => msg,
    }
}

thread_local! {
    static ELAB_DIAG_COUNTS: std::cell::RefCell<crate::hasher::HashMap<String, u32>> =
        std::cell::RefCell::new(crate::hasher::HashMap::default());
}

/// Reset the per-kind diagnostic counters (start of an elaboration run).
pub fn elab_diag_reset_counts() {
    ELAB_DIAG_COUNTS.with(|c| c.borrow_mut().clear());
}

/// Emit an elaboration diagnostic: printed live, and recorded when capture is
/// active so a warm cache hit can replay it.
///
/// At most `diag_kind_limit()` messages of a given kind are emitted; the last
/// one carries a note that the rest are suppressed, and names the env var so
/// the reader can see the rest. Suppressed messages are dropped from the
/// capture sink too, so a warm-cache replay reproduces the same output.
pub(crate) fn elab_diag(msg: String) {
    let n = ELAB_DIAG_COUNTS.with(|c| {
        let mut m = c.borrow_mut();
        let e = m.entry(diag_kind_key(&msg).to_string()).or_insert(0);
        *e += 1;
        *e
    });
    let limit = diag_kind_limit();
    if n > limit {
        return;
    }
    // `u32::MAX` is the unlimited sentinel: no cap, and no suppression note.
    let msg = if n == limit && limit != u32::MAX {
        format!(
            "{}\n[xezim][warning] further messages of this kind are suppressed \
             (limit {}; set XEZIM_DIAG_LIMIT=N, or 0 for unlimited, to see them).",
            msg, limit
        )
    } else {
        msg
    };
    eprintln!("{}", msg);
    ELAB_DIAG_SINK.with(|c| {
        if let Some(v) = c.borrow_mut().as_mut() {
            v.push(msg);
        }
    });
}

pub fn set_library_cli(cfg: LibraryCli) {
    *library_cli_cell().lock().unwrap() = cfg;
}

/// Library files whose definitions were ADOPTED during elaboration (module
/// name list per file, insertion-ordered). Consumed by `--dump-merged-sv` to
/// append the needed `-v`/`-y` sources so the merged artifact rebuilds
/// standalone.
static ADOPTED_LIB_FILES: std::sync::OnceLock<
    std::sync::Mutex<Vec<(std::path::PathBuf, Vec<String>)>>,
> = std::sync::OnceLock::new();

fn adopted_lib_files_cell() -> &'static std::sync::Mutex<Vec<(std::path::PathBuf, Vec<String>)>> {
    ADOPTED_LIB_FILES.get_or_init(|| std::sync::Mutex::new(Vec::new()))
}

pub(crate) fn record_adopted_lib_file(path: std::path::PathBuf, module: &str) {
    if let Ok(mut v) = adopted_lib_files_cell().lock() {
        if let Some((_, mods)) = v.iter_mut().find(|(p, _)| *p == path) {
            if !mods.iter().any(|m| m == module) {
                mods.push(module.to_string());
            }
        } else {
            v.push((path, vec![module.to_string()]));
        }
    }
}

/// The adopted-library record, in adoption order. Does not clear — a single
/// CLI run elaborates once.
pub fn adopted_lib_files() -> Vec<(std::path::PathBuf, Vec<String>)> {
    adopted_lib_files_cell()
        .lock()
        .map(|v| v.clone())
        .unwrap_or_default()
}

/// The preprocessing context `-v`/`-y` indexing ran under: the include dirs
/// and the macro snapshot taken AFTER the primary sources (so a library file
/// sees defines from the design, exactly as `index_library_file` did).
/// Recorded once per run by `resolve_library_modules`; consumed by
/// `preprocess_adopted_lib` so `--dump-merged-sv` can append library text
/// with includes/macros resolved instead of raw bytes (raw text broke
/// standalone re-compiles of the merged file the moment it left the original
/// directory).
static ADOPTED_LIB_PP_CONTEXT: std::sync::OnceLock<
    std::sync::Mutex<Option<(Vec<String>, Vec<(String, preprocessor::MacroDef)>)>>,
> = std::sync::OnceLock::new();

fn adopted_lib_pp_context_cell()
-> &'static std::sync::Mutex<Option<(Vec<String>, Vec<(String, preprocessor::MacroDef)>)>> {
    ADOPTED_LIB_PP_CONTEXT.get_or_init(|| std::sync::Mutex::new(None))
}

pub(crate) fn record_adopted_lib_pp_context(
    include_dirs: &[String],
    lib_defines: &std::collections::HashMap<String, preprocessor::MacroDef>,
) {
    if let Ok(mut g) = adopted_lib_pp_context_cell().lock() {
        *g = Some((
            include_dirs.to_vec(),
            lib_defines
                .iter()
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect(),
        ));
    }
}

/// Preprocess one adopted library file exactly as the `-v`/`-y` indexing pass
/// did: a FRESH preprocessor per file with the recorded include dirs and the
/// post-primary-source macro snapshot, resolving includes relative to the
/// file itself. Returns None when no context was recorded (no library pass
/// ran) or when preprocessing reports errors — callers fall back to the raw
/// bytes so the merged dump still contains the file either way.
pub fn preprocess_adopted_lib(path: &std::path::Path) -> Option<String> {
    let ctx = adopted_lib_pp_context_cell().lock().ok()?.clone()?;
    let source = std::fs::read_to_string(path).ok()?;
    let mut pp = preprocessor::Preprocessor::new();
    for dir in &ctx.0 {
        pp.add_include_dir(std::path::PathBuf::from(dir));
    }
    for (name, def) in &ctx.1 {
        pp.define(name.clone(), def.clone());
    }
    let text = pp.preprocess_file(&source, Some(path));
    if !pp.errors().is_empty() {
        return None;
    }
    Some(text)
}

static MODULE_TIMESCALE_CLI: std::sync::OnceLock<std::sync::Mutex<ModuleTimescaleCli>> =
    std::sync::OnceLock::new();

fn module_timescale_cli_cell() -> &'static std::sync::Mutex<ModuleTimescaleCli> {
    MODULE_TIMESCALE_CLI.get_or_init(|| std::sync::Mutex::new(ModuleTimescaleCli::default()))
}

/// Install the parsed `--module-timescale` configuration before elaboration.
pub fn set_module_timescale_cli(cli: ModuleTimescaleCli) {
    if let Ok(mut g) = module_timescale_cli_cell().lock() {
        *g = cli;
    }
}

fn module_timescale_cli() -> ModuleTimescaleCli {
    module_timescale_cli_cell()
        .lock()
        .map(|g| g.clone())
        .unwrap_or_default()
}

#[derive(Debug, Clone)]
pub enum SourceDefinition {
    Module(Rc<ast::module::ModuleDeclaration>),
    Interface(Rc<ast::module::InterfaceDeclaration>),
    Program(Rc<ast::module::ProgramDeclaration>),
    Class(Rc<ast::decl::ClassDeclaration>),
    Package(Rc<ast::module::PackageDeclaration>),
    Typedef(Rc<ast::decl::TypedefDeclaration>),
    /// IEEE 1800-2017 §29 User-Defined Primitive.
    Udp(Rc<ast::decl::UdpDecl>),
}

impl SourceDefinition {
    pub fn name(&self) -> String {
        match self {
            SourceDefinition::Module(m) => m.name.name.clone(),
            SourceDefinition::Interface(i) => i.name.name.clone(),
            SourceDefinition::Program(p) => p.name.name.clone(),
            SourceDefinition::Class(c) => c.name.name.clone(),
            SourceDefinition::Package(p) => p.name.name.clone(),
            SourceDefinition::Typedef(t) => t.name.name.clone(),
            SourceDefinition::Udp(u) => u.name.name.clone(),
        }
    }

    pub fn items(&self) -> &[ast::decl::ModuleItem] {
        match self {
            SourceDefinition::Module(m) => &m.items,
            SourceDefinition::Interface(i) => &i.items,
            SourceDefinition::Program(p) => &p.items,
            SourceDefinition::Class(_)
            | SourceDefinition::Package(_)
            | SourceDefinition::Typedef(_)
            | SourceDefinition::Udp(_) => &[],
        }
    }
}

/// Tokenize a source string.
pub fn tokenize_file(source: &str, _path: Option<&std::path::Path>) -> Vec<lexer::Token> {
    lexer::Lexer::new(source).tokenize()
}

/// Parse a source string into an AST.
pub fn parse_str(source: &str) -> Result<ParseResult, Vec<diagnostics::Diagnostic>> {
    let result = sv_parser::parse(source);
    if !result.errors.is_empty() {
        Err(result.errors)
    } else {
        Ok(result)
    }
}

/// `--verbose` compile reporting: what a source file contributed to the
/// working library, by name. An empty result is called out explicitly — a
/// file whose entire body sits behind a false `ifdef` is the classic
/// "my testbench never compiled" failure and deserves a loud line.
fn report_file_definitions(label: &str, descriptions: &[ast::Description]) {
    let mut named: Vec<(&'static str, &str)> = Vec::new();
    let mut other = 0usize;
    for d in descriptions {
        match d {
            ast::Description::Module(m) => named.push(("module", &m.name.name)),
            ast::Description::Interface(x) => named.push(("interface", &x.name.name)),
            ast::Description::Program(p) => named.push(("program", &p.name.name)),
            ast::Description::Package(p) => named.push(("package", &p.name.name)),
            ast::Description::Class(c) => named.push(("class", &c.name.name)),
            ast::Description::Udp(u) => named.push(("primitive", &u.name.name)),
            ast::Description::TypedefDecl(t) => named.push(("typedef", &t.name.name)),
            _ => other += 1,
        }
    }
    if named.is_empty() && other == 0 {
        eprintln!(
            "[compile]   {}: NO definitions — if unexpected, check `ifdef guards and defines",
            label
        );
        return;
    }
    let list = named
        .iter()
        .map(|(k, n)| format!("{} {}", k, n))
        .collect::<Vec<_>>()
        .join(", ");
    if other > 0 {
        eprintln!("[compile]   {}: {} (+{} other item(s))", label, list, other);
    } else {
        eprintln!("[compile]   {}: {}", label, list);
    }
}

/// Render the `severity` diagnostics of one parsed file, each located
/// through `map` (spans index `text`, the file's preprocessed text). The
/// parser's error recovery can report one problem twice at the same place;
/// identical repeats are dropped, and past the first 20 (by then mostly
/// recovery cascades) only a count is given.
pub fn render_parse_diagnostics(
    diags: &[diagnostics::Diagnostic],
    severity: diagnostics::Severity,
    text: &str,
    map: Option<&sv_parser::source_map::LineMap>,
    file: &str,
) -> Vec<String> {
    const SHOWN: usize = 20;
    let mut seen: std::collections::HashSet<(usize, usize, &str)> =
        std::collections::HashSet::new();
    let unique: Vec<&diagnostics::Diagnostic> = diags
        .iter()
        .filter(|d| d.severity == severity)
        .filter(|d| seen.insert((d.span.start, d.span.end, d.message.as_str())))
        .collect();
    let mut out: Vec<String> = unique
        .iter()
        .take(SHOWN)
        .map(|d| diagnostics::render_diagnostic(d, text, map, file))
        .collect();
    if unique.len() > SHOWN {
        out.push(format!(
            "... {} more {}(s) in '{}' not shown",
            unique.len() - SHOWN,
            severity.as_str(),
            file
        ));
    }
    out
}

/// A design's sources preprocessed once, in parse order, together with the
/// preprocessor state elaboration reads afterwards. Produced by
/// `preprocess_design` so a driver that already preprocessed the sources
/// (for its own diagnostics) can hand the result to
/// `parse_and_elaborate_multi_preprocessed` instead of paying for a second,
/// identical pass.
pub struct PreprocessedSources {
    /// The inputs the texts were produced from; a consumer checks these
    /// before reusing the texts.
    pub sources: Vec<String>,
    pub source_files: Vec<String>,
    pub include_dirs: Vec<String>,
    pub defines: Vec<(String, Option<String>)>,
    /// Per-file preprocessed text and line map.
    pub texts: Vec<String>,
    pub line_maps: Vec<Option<sv_parser::source_map::LineMap>>,
    /// Preprocessor errors over all files (empty on success).
    pub errors: Vec<String>,
    /// End-of-pass preprocessor state.
    pub macro_defines: std::collections::HashMap<String, preprocessor::MacroDef>,
    pub module_timescales: std::collections::HashMap<String, (f64, f64)>,
    pub module_ts_own_file: std::collections::HashSet<String>,
    /// Thread-local directive state the pass recorded (`default_nettype
    /// none`, `unconnected_drive`), replayed on the elaborating thread.
    pub default_nettype_none: bool,
    pub unconnected_drive: Vec<(String, bool)>,
}

fn new_design_preprocessor(
    include_dirs: &[String],
    defines: &[(String, Option<String>)],
) -> preprocessor::Preprocessor {
    let mut pp = preprocessor::Preprocessor::new();
    for dir in include_dirs {
        pp.add_include_dir(std::path::PathBuf::from(dir));
    }
    for (name, val) in defines {
        pp.define(
            name.clone(),
            preprocessor::MacroDef {
                name: name.clone(),
                params: None,
                body: val.clone().unwrap_or_default(),
            },
        );
    }
    pp
}

/// Preprocess every source with one preprocessor, exactly as
/// `parse_and_elaborate_multi` does file by file, but over all files even
/// when one reports errors (the caller decides what to do with `errors`).
pub fn preprocess_design(
    sources: &[String],
    source_files: &[String],
    include_dirs: &[String],
    defines: &[(String, Option<String>)],
) -> PreprocessedSources {
    let mut pp = new_design_preprocessor(include_dirs, defines);
    let mut texts = Vec::with_capacity(sources.len());
    let mut line_maps = Vec::with_capacity(sources.len());
    for (i, source) in sources.iter().enumerate() {
        let source_path = source_files.get(i).map(std::path::PathBuf::from);
        pp.begin_top_level_file();
        texts.push(pp.preprocess_file(source, source_path.as_deref()));
        line_maps.push(pp.take_line_map());
    }
    PreprocessedSources {
        sources: sources.to_vec(),
        source_files: source_files.to_vec(),
        include_dirs: include_dirs.to_vec(),
        defines: defines.to_vec(),
        texts,
        line_maps,
        errors: pp.errors().to_vec(),
        macro_defines: pp.snapshot_defines(),
        module_timescales: pp.module_timescales.clone(),
        module_ts_own_file: pp.module_ts_own_file.clone(),
        default_nettype_none: sv_parser::default_nettype_none_seen(),
        unconnected_drive: sv_parser::unconnected_drive_snapshot(),
    }
}

impl PreprocessedSources {
    /// True when this pass was produced from exactly these inputs and
    /// finished without errors, so its texts are what a fresh pass would
    /// produce.
    pub fn matches(
        &self,
        sources: &[String],
        source_files: &[String],
        include_dirs: &[String],
        defines: &[(String, Option<String>)],
    ) -> bool {
        self.errors.is_empty()
            && self.texts.len() == sources.len()
            && self.source_files == source_files
            && self.include_dirs == include_dirs
            && self.defines == defines
            && self.sources == sources
    }
}

pub fn parse_and_elaborate_multi(
    sources: &[String],
    top_module_name: Option<&str>,
    include_dirs: &[String],
    source_files: &[String],
    defines: &[(String, Option<String>)],
) -> Result<
    (
        crate::hasher::HashMap<String, SourceDefinition>,
        elaborate::ElaboratedModule,
    ),
    String,
> {
    parse_and_elaborate_multi_preprocessed(
        sources,
        top_module_name,
        include_dirs,
        source_files,
        defines,
        None,
    )
}

/// `parse_and_elaborate_multi` reusing an earlier `preprocess_design` pass
/// over the same inputs (checked with `PreprocessedSources::matches`; a
/// mismatch preprocesses afresh).
pub fn parse_and_elaborate_multi_preprocessed(
    sources: &[String],
    top_module_name: Option<&str>,
    include_dirs: &[String],
    source_files: &[String],
    defines: &[(String, Option<String>)],
    pre: Option<PreprocessedSources>,
) -> Result<
    (
        crate::hasher::HashMap<String, SourceDefinition>,
        elaborate::ElaboratedModule,
    ),
    String,
> {
    let mut pre = pre.filter(|p| p.matches(sources, source_files, include_dirs, defines));
    if let Some(p) = pre.as_ref() {
        if p.default_nettype_none {
            sv_parser::set_default_nettype_none_seen(true);
        }
        for (name, pull1) in &p.unconnected_drive {
            sv_parser::record_unconnected_drive(name, *pull1);
        }
    }
    let mut pre_files = pre.as_mut().map(|p| {
        (
            std::mem::take(&mut p.texts).into_iter(),
            std::mem::take(&mut p.line_maps).into_iter(),
        )
    });
    let mut phase_t = std::time::Instant::now();
    let mut all_descriptions = Vec::new();
    // Preprocessed text of each source, kept in parse order. Every AST
    // `Span` is a byte offset into ITS file's preprocessed text, so these
    // are what runtime diagnostics need to turn a span into `file:line`
    // (see `ElaboratedModule::source_texts`).
    let mut preprocessed_texts: Vec<String> = Vec::with_capacity(sources.len());
    // Line map of each preprocessed text back to the original files, for
    // `file:line:col` diagnostics through `include`s and macros.
    let mut line_maps: Vec<Option<sv_parser::source_map::LineMap>> =
        Vec::with_capacity(sources.len());
    // Which file defined each module/interface/program, by name. Captured
    // HERE — the only point where a description's originating file is still
    // known — and handed to runtime diagnostics via
    // `ElaboratedModule::src_file_of_module` (see that field's doc).
    let mut src_file_of_module: crate::hasher::HashMap<String, u32> =
        crate::hasher::HashMap::default();
    let mut pp = new_design_preprocessor(include_dirs, defines);

    for (i, source) in sources.iter().enumerate() {
        let source_path = source_files.get(i).map(std::path::PathBuf::from);
        let label = source_files
            .get(i)
            .map(|s| s.as_str())
            .unwrap_or("<unnamed>");
        if compile_verbose() {
            eprintln!("[compile] ({}/{}) parsing {}", i + 1, sources.len(), label);
        } else {
            progress_status(&format!(
                "[compile] parsing {}/{}: {}",
                i + 1,
                sources.len(),
                label.rsplit('/').next().unwrap_or(label)
            ));
        }
        // Mark a new compilation file so a `timescale that stuck across from a
        // prior file is treated as inherited (overridable by --module-timescale)
        // rather than declared here.
        let (preprocessed, line_map) = match pre_files.as_mut() {
            Some((texts, maps)) => (
                texts.next().unwrap_or_default(),
                maps.next().unwrap_or_default(),
            ),
            None => {
                pp.begin_top_level_file();
                let text = pp.preprocess_file(source, source_path.as_deref());
                (text, pp.take_line_map())
            }
        };
        // Preprocessor-fatal conditions (missing/unreadable `include, include
        // recursion, strict directive violations): fail the run at the first
        // affected file. Continuing used to silently drop the include's
        // declarations, and the damage surfaced far away as implicit nets and
        // width mismatches.
        if !pp.errors().is_empty() {
            progress_clear();
            return Err(format!(
                "Preprocessing failed in '{}' (file {} of {}):\n{}",
                label,
                i + 1,
                sources.len(),
                pp.errors().join("\n")
            ));
        }

        let tokens = lexer::Lexer::new(&preprocessed).tokenize();
        let mut parser = sv_parser::parse::Parser::new(tokens);
        let source_ast = parser.parse_source_text();
        let diags = parser.diagnostics().to_vec();

        if diags
            .iter()
            .any(|d| d.severity == diagnostics::Severity::Error)
        {
            progress_clear();
            let errs = render_parse_diagnostics(
                &diags,
                diagnostics::Severity::Error,
                &preprocessed,
                line_map.as_ref(),
                label,
            );
            return Err(format!(
                "Parse errors in '{}' (file {} of {}):\n{}",
                label,
                i + 1,
                sources.len(),
                errs.join("\n")
            ));
        }
        // Parser warnings (an unsupported UDP table, a nonstandard
        // construct accepted for compatibility), located like the errors;
        // informational notes only under --verbose.
        let mut shown = vec![diagnostics::Severity::Warning];
        if compile_verbose() {
            shown.push(diagnostics::Severity::Info);
        }
        for sev in shown {
            for w in render_parse_diagnostics(&diags, sev, &preprocessed, line_map.as_ref(), label)
            {
                progress_clear();
                eprintln!("{}", w);
            }
        }
        if compile_verbose() {
            report_file_definitions(label, &source_ast.descriptions);
        }
        // Second, AST-level strict pass (runs alongside the permissive parser;
        // gated by --strict, on by default). Rejects LRM violations the main
        // parser accepts. See sv_parser::strict_check.
        let strict_viol = sv_parser::strict_check::strict_diagnostics(&source_ast.descriptions);
        if !strict_viol.is_empty() {
            progress_clear();
            let errs = render_parse_diagnostics(
                &strict_viol,
                diagnostics::Severity::Error,
                &preprocessed,
                line_map.as_ref(),
                label,
            );
            return Err(format!(
                "Strict check failed in '{}' (file {} of {}):\n{}",
                label,
                i + 1,
                sources.len(),
                errs.join("\n")
            ));
        }
        for d in &source_ast.descriptions {
            let name = match d {
                ast::Description::Module(m) => Some(&m.name.name),
                ast::Description::Interface(iface) => Some(&iface.name.name),
                ast::Description::Program(p) => Some(&p.name.name),
                ast::Description::PackageItem(ast::decl::PackageItem::Checker(c)) => {
                    Some(&c.name.name)
                }
                // Packages too: a diagnostic about a package subroutine
                // resolves its file:line by hinting with the PACKAGE name
                // (see `span_location_of`); without this entry a package
                // span is ambiguous across files and reports no location.
                ast::Description::Package(p) => Some(&p.name.name),
                // File-scope classes, for the file:line of their methods in
                // code coverage.
                ast::Description::Class(c)
                | ast::Description::PackageItem(ast::decl::PackageItem::Class(c)) => {
                    Some(&c.name.name)
                }
                _ => None,
            };
            if let Some(name) = name {
                src_file_of_module.entry(name.clone()).or_insert(i as u32);
            }
        }
        all_descriptions.extend(source_ast.descriptions);
        preprocessed_texts.push(preprocessed);
        line_maps.push(line_map);
    }

    // IEEE 1801 power intent: splice the generated UPF package and glue
    // processes into the parsed design before elaboration.
    // VHDL (IEEE 1076): the lowered VHDL design joins the SV descriptions.
    let vhdl_top = vhdl::inject(&mut all_descriptions, top_module_name)?;
    let top_module_name = top_module_name.or(vhdl_top.as_deref());
    upf::inject(&mut all_descriptions, top_module_name)?;
    let (lib_defines, module_timescales, module_ts_own_file) = match pre {
        Some(p) => (p.macro_defines, p.module_timescales, p.module_ts_own_file),
        None => (
            pp.snapshot_defines(),
            pp.module_timescales.clone(),
            pp.module_ts_own_file.clone(),
        ),
    };
    // Publish the sources BEFORE elaborating so an error raised during
    // elaboration (e.g. a duplicate declaration) can report `file:line`;
    // `elab.source_texts` below is assigned too late for that. Moved, not
    // cloned, then moved back out.
    elaborate::set_elab_sources(preprocessed_texts, source_files.to_vec());
    elaborate::set_elab_line_maps(line_maps);
    elaborate::set_elab_module_files(src_file_of_module.clone());
    if !compile_verbose() {
        progress_status(&format!(
            "[compile] elaborating design ({} files parsed, {} definitions)...",
            sources.len(),
            all_descriptions.len()
        ));
    }
    elab_phase("parse", &mut phase_t);
    let elaborated = parse_and_elaborate(
        all_descriptions,
        top_module_name,
        include_dirs,
        &lib_defines,
        &module_timescales,
        &module_ts_own_file,
    );
    progress_clear();
    let (texts, files) = elaborate::take_elab_sources();
    let maps = elaborate::take_elab_line_maps();
    let (defs, mut elab) = elaborated?;
    elab.source_texts = texts;
    elab.source_files = files;
    elab.source_line_maps = maps;
    elab.src_file_of_module = src_file_of_module;
    // Captured from the RAW sources — the only place the pre-preprocessing
    // line counts are still known.
    elab.source_orig_lines = sources.iter().map(|s| s.lines().count() as u32).collect();
    Ok((defs, elab))
}

/// Where the overridable value parameter `name` of a module, interface or
/// program is declared: a non-local parameter-port-list entry, or a body
/// `parameter` of a definition without a port list (§6.20.1: with one, a
/// body `parameter` is local). Parameters in generate blocks are local too
/// and are never looked at. Returns (in the port list, declaration index,
/// assignment index, declared `string`).
fn find_overridable_param(
    params: &[ast::decl::ParameterDeclaration],
    items: &[ast::decl::ModuleItem],
    name: &str,
) -> Option<(bool, usize, usize, bool)> {
    use ast::decl::{ModuleItem, ParameterKind};
    let body_overridable = params.is_empty();
    let decls = params
        .iter()
        .enumerate()
        .map(|(i, pd)| (true, i, pd))
        .chain(items.iter().enumerate().filter_map(|(i, it)| match it {
            ModuleItem::ParameterDeclaration(pd) if body_overridable => Some((false, i, pd)),
            _ => None,
        }));
    for (in_header, di, pd) in decls {
        let ParameterKind::Data {
            data_type,
            assignments,
        } = &pd.kind
        else {
            continue;
        };
        if pd.local {
            continue;
        }
        if let Some(ai) = assignments.iter().position(|a| a.name.name == name) {
            let is_string = matches!(
                data_type,
                ast::types::DataType::Simple {
                    kind: ast::types::SimpleType::String,
                    ..
                }
            );
            return Some((in_header, di, ai, is_string));
        }
    }
    None
}

/// Set the default of the parameter `find_overridable_param` located.
fn set_param_default(
    params: &mut [ast::decl::ParameterDeclaration],
    items: &mut [ast::decl::ModuleItem],
    (in_header, di, ai): (bool, usize, usize),
    value: ast::expr::Expression,
) {
    let pd = if in_header {
        Some(&mut params[di])
    } else {
        match &mut items[di] {
            ast::decl::ModuleItem::ParameterDeclaration(pd) => Some(pd),
            _ => None,
        }
    };
    if let Some(ast::decl::ParameterDeclaration {
        kind: ast::decl::ParameterKind::Data { assignments, .. },
        ..
    }) = pd
    {
        assignments[ai].init = Some(value);
    }
}

/// Parse a `-g` value as a constant expression; None when it is not one.
pub(crate) fn parse_override_value(text: &str) -> Option<ast::expr::Expression> {
    use ast::decl::{ModuleItem, ParameterKind};
    let src = format!(
        "module __xezim_param_value; localparam __xezim_v = {};\nendmodule\n",
        text
    );
    let mut parser = sv_parser::parse::Parser::new(lexer::Lexer::new(&src).tokenize());
    let parsed = parser.parse_source_text();
    if parser
        .diagnostics()
        .iter()
        .any(|d| d.severity == diagnostics::Severity::Error)
    {
        return None;
    }
    let Some(ast::Description::Module(m)) = parsed.descriptions.into_iter().next() else {
        return None;
    };
    m.items.into_iter().find_map(|it| match it {
        ModuleItem::LocalparamDeclaration(pd) | ModuleItem::ParameterDeclaration(pd) => {
            match pd.kind {
                ParameterKind::Data { assignments, .. } => {
                    assignments.into_iter().next().and_then(|a| a.init)
                }
                _ => None,
            }
        }
        _ => None,
    })
}

/// Apply the command-line overrides (see `set_param_overrides`) to the
/// parsed definitions, except those named in `skip`. Returns how many
/// definitions each override changed. A `string` parameter takes an
/// unquoted value as its text.
fn apply_param_overrides(
    definitions: &mut crate::hasher::HashMap<String, SourceDefinition>,
    skip: Option<&std::collections::HashSet<String>>,
) -> Result<Vec<usize>, String> {
    let overrides = PARAM_OVERRIDES.lock().unwrap().clone();
    let mut hits = vec![0usize; overrides.len()];
    for (o, hit) in overrides.iter().zip(hits.iter_mut()) {
        let expr = parse_override_value(&o.value);
        for (dname, def) in definitions.iter_mut() {
            if o.module.as_ref().is_some_and(|m| m != dname)
                || skip.is_some_and(|s| s.contains(dname))
            {
                continue;
            }
            let found = match def {
                SourceDefinition::Module(m) => find_overridable_param(&m.params, &m.items, &o.name),
                SourceDefinition::Interface(m) => {
                    find_overridable_param(&m.params, &m.items, &o.name)
                }
                SourceDefinition::Program(m) => {
                    find_overridable_param(&m.params, &m.items, &o.name)
                }
                _ => None,
            };
            let Some((in_header, di, ai, is_string)) = found else {
                continue;
            };
            let value = match &expr {
                Some(e)
                    if !is_string || matches!(e.kind, ast::expr::ExprKind::StringLiteral(_)) =>
                {
                    e.clone()
                }
                _ if is_string => ast::expr::Expression::new(
                    ast::expr::ExprKind::StringLiteral(o.value.clone()),
                    ast::Span::dummy(),
                ),
                _ => {
                    return Err(format!(
                        "-{}{}={}: '{}' is not a valid parameter value",
                        if o.force { 'G' } else { 'g' },
                        o.name,
                        o.value,
                        o.value
                    ));
                }
            };
            let at = (in_header, di, ai);
            match def {
                SourceDefinition::Module(m) => {
                    let m = Rc::make_mut(m);
                    set_param_default(&mut m.params, &mut m.items, at, value);
                }
                SourceDefinition::Interface(m) => {
                    let m = Rc::make_mut(m);
                    set_param_default(&mut m.params, &mut m.items, at, value);
                }
                SourceDefinition::Program(m) => {
                    let m = Rc::make_mut(m);
                    set_param_default(&mut m.params, &mut m.items, at, value);
                }
                _ => {}
            }
            *hit += 1;
        }
    }
    Ok(hits)
}

/// Warn about each command-line override no definition declared.
fn warn_unapplied_param_overrides(hits: &[usize]) {
    let overrides = PARAM_OVERRIDES.lock().unwrap().clone();
    for (o, _) in overrides.iter().zip(hits).filter(|(_, h)| **h == 0) {
        let path = o
            .module
            .as_ref()
            .map(|m| format!("/{}/", m))
            .unwrap_or_default();
        let owner = o
            .module
            .as_ref()
            .map(|m| format!("module '{}'", m))
            .unwrap_or_else(|| "module".to_string());
        eprintln!(
            "[xezim][warning] -{}{}{}={}: no {} declares an overridable parameter '{}'; ignored",
            if o.force { 'G' } else { 'g' },
            path,
            o.name,
            o.value,
            owner,
            o.name
        );
    }
}

/// Every name a module declares in its OWN scope: ports, nets, variables,
/// parameters and genvars. Used to decide whether a compilation-unit (`$unit`)
/// declaration is shadowed here (§3.12.1) — items nested in a generate region
/// or a subroutine belong to an inner scope and are deliberately not counted.
fn design_declared_names(
    ports: &ast::module::PortList,
    params: &[ast::decl::ParameterDeclaration],
    items: &[ast::decl::ModuleItem],
) -> std::collections::HashSet<String> {
    use ast::decl::{ModuleItem, ParameterKind};
    let mut names: std::collections::HashSet<String> = std::collections::HashSet::new();
    match ports {
        ast::module::PortList::Ansi(ports) => {
            names.extend(ports.iter().map(|p| p.name.name.clone()));
        }
        ast::module::PortList::NonAnsi(ids) => {
            names.extend(ids.iter().map(|i| i.name.clone()));
        }
        ast::module::PortList::Empty => {}
    }
    for p in params {
        if let ParameterKind::Data { assignments, .. } = &p.kind {
            names.extend(assignments.iter().map(|a| a.name.name.clone()));
        }
    }
    for it in items {
        match it {
            ModuleItem::PortDeclaration(pd) => {
                names.extend(pd.declarators.iter().map(|d| d.name.name.clone()));
            }
            ModuleItem::NetDeclaration(nd) => {
                names.extend(nd.declarators.iter().map(|d| d.name.name.clone()));
            }
            ModuleItem::DataDeclaration(dd) => {
                names.extend(dd.declarators.iter().map(|d| d.name.name.clone()));
            }
            ModuleItem::ParameterDeclaration(pd) | ModuleItem::LocalparamDeclaration(pd) => {
                if let ParameterKind::Data { assignments, .. } = &pd.kind {
                    names.extend(assignments.iter().map(|a| a.name.name.clone()));
                }
            }
            ModuleItem::GenvarDeclaration(gd) => {
                names.extend(gd.names.iter().map(|n| n.name.clone()));
            }
            _ => {}
        }
    }
    names
}

fn parse_and_elaborate(
    mut all_descriptions: Vec<ast::Description>,
    top_module_name: Option<&str>,
    include_dirs: &[String],
    lib_defines: &std::collections::HashMap<String, preprocessor::MacroDef>,
    module_timescales: &std::collections::HashMap<String, (f64, f64)>,
    module_ts_own_file: &std::collections::HashSet<String>,
) -> Result<
    (
        crate::hasher::HashMap<String, SourceDefinition>,
        elaborate::ElaboratedModule,
    ),
    String,
> {
    // Array defaults are needed through the final bind/parameter passes,
    // including elaboration of the compilation-unit and top scopes.
    let _array_param_scope = elaborate::array_params::scope();
    // Effective per-module timescale, unifying `\`timescale` directives (from
    // the preprocessor) with in-body `timeunit`/`timeprecision` declarations
    // (§3.14.2). A `timeunit` decl was previously ignored here, so its module's
    // delays were never scaled — `#5` in a `timeunit 1us` module ran as 5 ns.
    // Precedence, highest first (implementation-defined --module-timescale
    // extension): local timeunit/timeprecision decl > active `\`timescale`
    // directive > named --module-timescale > global --module-timescale >
    // 1 ns / 1 ns default. The command-line forms never override an explicit
    // source-level timescale (a local decl OR an active directive).
    // §26.3: a type name declared by two packages (or a package and $unit / a
    // module) gets its package-qualified spelling before anything keys the
    // flat per-design type tables by it (#300).
    body_type_params::normalize(&mut all_descriptions);
    pkg_scope::qualify_colliding_package_types(&mut all_descriptions)?;
    pkg_scope::stamp_automatic_subroutines(&mut all_descriptions);
    let cli = module_timescale_cli();
    // `-override_timescale`: one timescale for everything, in seconds.
    let forced_secs: Option<(f64, f64)> = cli
        .force
        .map(|(u, p)| (elaborate::exp_to_secs(u), elaborate::exp_to_secs(p)));
    let mut eff_ts: std::collections::HashMap<String, (f64, f64)> =
        std::collections::HashMap::new();
    let mut named_matched: std::collections::HashSet<String> = std::collections::HashSet::new();
    // §3.14.2.2 — track modules that carry NO `timescale (no source-level
    // decl, no preceding directive, no CLI override) so a mixed design (some
    // modules timed, some not) can be warned about after the pass.
    let mut any_explicit_ts = false;
    let mut modules_without_ts: Vec<String> = Vec::new();
    // §3.14.2.3: `timeunit`/`timeprecision` at COMPILATION-UNIT scope — parsed
    // as Description::TimeunitsDecl but previously dropped entirely, so
    // `timeunit 1ns; timeprecision 10ps;` before a module left the design on
    // the 1 ns default tick and `#78.1ps` collapsed to 0. Track it sticky, in
    // source order, as the fallback for modules with no timescale of their
    // own.
    let mut unit_scope_ts: (Option<i32>, Option<i32>) = (None, None);
    for desc in &all_descriptions {
        if let ast::Description::TimeunitsDecl(td) = desc {
            if let Some(u) = &td.unit {
                unit_scope_ts.0 = Some(elaborate::time_literal_to_exp(u));
            }
            if let Some(p) = &td.precision {
                unit_scope_ts.1 = Some(elaborate::time_literal_to_exp(p));
            }
        }
        // §3.14.2: a `timescale governs every design element it precedes, not
        // just modules. An INTERFACE's tasks (a BFM's drive/sample routines)
        // and a PROGRAM's blocks carry `#` delays and read `$realtime` exactly
        // like module items do, but only modules were ever entered into the
        // effective-timescale map — so an interface's delays stayed raw ticks
        // and its `$realtime` reported the wrong unit. The preprocessor already
        // records interfaces and programs in `module_timescales`
        // (`design_element_name` covers module/interface/program/package), so
        // they only had to be walked here.
        let ts_target: Option<(&String, &Vec<ast::decl::ModuleItem>)> = match desc {
            ast::Description::Module(m) => Some((&m.name.name, &m.items)),
            ast::Description::Interface(i) => Some((&i.name.name, &i.items)),
            ast::Description::Program(p) => Some((&p.name.name, &p.items)),
            _ => None,
        };
        if let Some((name, ts_items)) = ts_target {
            // Explicit source-level declarations.
            let mut local_u: Option<i32> = None;
            let mut local_p: Option<i32> = None;
            for it in ts_items {
                if let ast::decl::ModuleItem::TimeunitsDecl(td) = it {
                    if let Some(u) = &td.unit {
                        local_u = Some(elaborate::time_literal_to_exp(u));
                    }
                    if let Some(p) = &td.precision {
                        local_p = Some(elaborate::time_literal_to_exp(p));
                    }
                }
            }
            let directive = module_timescales
                .get(name)
                .map(|&(u, p)| (elaborate::secs_to_exp(u), elaborate::secs_to_exp(p)));
            // A `\`timescale` that STUCK across from a prior file (inherited) is
            // NOT the module's own source-level timescale. `--module-timescale`
            // may override such an inheritance; only a local `timeunit` decl or a
            // directive in the module's OWN file is truly "explicit source-level"
            // and wins over the CLI.
            let directive_own_file = directive.is_some() && module_ts_own_file.contains(name);
            let own_explicit = local_u.is_some() || local_p.is_some() || directive_own_file;
            let named = cli.named.get(name).copied();
            let cli_ts = named.or(cli.global);
            if named.is_some() {
                named_matched.insert(name.clone());
            }
            if cli.force.is_some() {
                // Uniform by construction: nothing to warn about.
            } else if own_explicit {
                any_explicit_ts = true;
            } else if directive.is_none() && cli_ts.is_none() {
                // Genuinely no timescale anywhere (own or inherited) and no CLI.
                modules_without_ts.push(name.clone());
            }

            let eff_exp: Option<(i32, i32)> = if let Some(f) = cli.force {
                // `-override_timescale` replaces every source-level and
                // command-line timescale.
                Some(f)
            } else if own_explicit {
                // A local decl overrides the (own-file) directive field by field;
                // a missing field falls back to the directive, then to 1 ns.
                let (du, dp) = directive.unwrap_or((-9, -9));
                let u = local_u.unwrap_or(du);
                let p = local_p.unwrap_or(dp);
                if named.is_some() && cli.force.is_none() {
                    eprintln!(
                        "[warn] --module-timescale for module '{}' ignored; it has an explicit source-level timescale",
                        name
                    );
                }
                Some((u, p))
            } else if unit_scope_ts.0.is_some() || unit_scope_ts.1.is_some() {
                // §3.14.2.3 compilation-unit-scope decl: source-explicit, so
                // it outranks the CLI and inherited directives.
                let u = unit_scope_ts.0.unwrap_or(-9);
                let p = unit_scope_ts.1.unwrap_or(unit_scope_ts.0.unwrap_or(-9));
                any_explicit_ts = true;
                Some((u, p))
            } else if let Some(ts) = cli_ts {
                // --module-timescale supplies the timescale, OVERRIDING any
                // directive merely inherited (sticky) from a prior file.
                Some(ts)
            } else {
                // No CLI: keep a cross-file-inherited directive (single-compilation-
                // unit sticky behavior) when present; else the tool default
                // (§3.14.2.2 leaves it tool-defined): 1ns/1ns, the unit the
                // reference simulator applies, so an untimed module's `#1` and
                // `$realtime` both count nanoseconds. (1ps/1ps was tried on
                // 2026-09-04: testbenches that mix bare `#10` clocks with
                // absolute `3000ns` literals then ran 1000x more clock cycles,
                // 10x slower, and no longer matched the reference.)
                directive.or(Some((-9, -9)))
            };
            if let Some((u, p)) = eff_exp {
                eff_ts.insert(
                    name.clone(),
                    (elaborate::exp_to_secs(u), elaborate::exp_to_secs(p)),
                );
            }
        }
    }
    // §3.14.2.2 — a design that MIXES timed and untimed modules is a common
    // source of surprise (the untimed module falls back to the default unit).
    // Warn once per untimed module, but only in the mixed case (a fully
    // untimed design has a uniform default and needs no warning).
    if any_explicit_ts {
        for name in &modules_without_ts {
            eprintln!(
                "[warn] module '{}' has no timescale directive; defaulting its timescale to 1ns/1ns",
                name
            );
        }
    }
    // §10: warn on a named assignment that matched no module definition.
    for name in cli.named.keys() {
        if !named_matched.contains(name) {
            eprintln!("[warn] --module-timescale did not match module '{}'", name);
        }
    }

    // Global simulation tick = the finest precision across the design
    // (default 1 ns). All module delays are then pre-scaled to this unit.
    let tick_s = eff_ts.values().map(|&(_, p)| p).fold(1e-9_f64, f64::min);
    let mut module_timescale_exp: crate::hasher::HashMap<String, (i32, i32)> =
        crate::hasher::HashMap::default();
    for (n, &(u, p)) in &eff_ts {
        module_timescale_exp.insert(
            n.clone(),
            (elaborate::secs_to_exp(u), elaborate::secs_to_exp(p)),
        );
    }
    let mut definitions: crate::hasher::HashMap<String, SourceDefinition> =
        crate::hasher::HashMap::default();
    // §3.13/§23.2: a module and a CLASS may legally share a name — they live in
    // different namespaces (hierarchy vs data type), as the reference
    // simulator accepts (`class test` + `module test`). The single
    // name-keyed `definitions` map cannot hold both, and the module (needed
    // for top-module detection/instantiation) overwrites the class, silently
    // dropping its factory/type registration. Keep every top-level (compilation
    // unit scope) class in a separate registry keyed by its class name so it
    // can always be re-registered into `elab.classes` regardless of a
    // same-named module.
    let mut class_defs: crate::hasher::HashMap<String, Rc<ast::decl::ClassDeclaration>> =
        crate::hasher::HashMap::default();
    // §3.13/§6.18: the same collision applies to TYPEDEFs — a typedef is a
    // compilation-unit-scope DATA type and legally coexists with a same-named
    // hierarchy kind (module/interface/program/package/UDP), but the single
    // name-keyed `definitions` map gives the slot to the hierarchy kind.
    // Keep every top-level typedef in its own registry so it can always be
    // re-registered into `elab.typedef_types` regardless of a same-named
    // hierarchy declaration (the reference resolves `typedef base shared;`
    // + `module shared;` to the typedef for a `shared h;` handle value).
    let mut typedef_defs: crate::hasher::HashMap<String, Rc<ast::decl::TypedefDeclaration>> =
        crate::hasher::HashMap::default();
    let mut top_module = None;
    // Source position of each module/interface/program declaration: several
    // auto-detected tops elaborate in this order, as the reference does.
    let mut def_source_pos: crate::hasher::HashMap<String, usize> =
        crate::hasher::HashMap::default();
    // When the design has multiple uninstantiated top-level modules, this
    // holds their names so that — after elaboration of the synthetic
    // `__xezim_multi_top` wrapper — each one's module-local static
    // declarations (classes/typedefs) can be hoisted into the global table
    // exactly as they would be if that module alone were the root. Empty for
    // single-top designs (no hoisting needed, no behaviour change).
    let mut multi_top_modules: Vec<String> = Vec::new();
    let mut top_level_imports = Vec::new();
    let mut top_level_lets = Vec::new();
    let mut top_level_functions: Vec<ast::decl::FunctionDeclaration> = Vec::new();
    let mut top_level_tasks: Vec<ast::decl::TaskDeclaration> = Vec::new();
    let mut top_level_nettypes: Vec<ast::decl::NettypeDeclaration> = Vec::new();
    // §35.5.4: a compilation-unit `import "DPI-C"` is visible in every
    // module of the unit, exactly like a $unit function — it was the one
    // $unit declaration kind never injected, so `add(1, 2)` was undeclared.
    let mut top_level_dpi_imports: Vec<ast::decl::DPIImport> = Vec::new();
    // Likewise `export "DPI-C" function f;` at $unit: the exported
    // subroutine is injected as a $unit function already; the export
    // directive must follow it so the symbol is published.
    let mut top_level_dpi_exports: Vec<ast::decl::DPIExport> = Vec::new();
    let mut top_level_params: Vec<ast::decl::ParameterDeclaration> = Vec::new();
    let mut top_level_vars: Vec<ast::decl::DataDeclaration> = Vec::new();
    let mut top_level_nets: Vec<ast::decl::NetDeclaration> = Vec::new();
    // §19.3 $unit-scope covergroups, injected into every module like the
    // $unit subroutines.
    let mut top_level_covergroups: Vec<ast::decl::CovergroupDeclaration> = Vec::new();
    let mut top_level_binds: Vec<ast::decl::BindDirective> = Vec::new();
    // §18.5.1 $unit-scope out-of-class constraint definitions (class, name).
    let mut top_level_ooc_constraints: Vec<(String, String, Vec<ast::decl::ConstraintItem>)> =
        Vec::new();
    // §3.14.2.3: sticky compilation-unit timeunit/timeprecision, tracked in
    // source order through THIS loop so classes / $unit subroutines /
    // packages pick up the scope timescale in force at their declaration
    // (ivtest br1003a-d). Mirrors the eff_ts walk above.
    let mut cu_ts_defs: (Option<i32>, Option<i32>) = (None, None);
    for desc in all_descriptions {
        if let ast::Description::TimeunitsDecl(td) = &desc {
            if let Some(u) = &td.unit {
                cu_ts_defs.0 = Some(elaborate::time_literal_to_exp(u));
            }
            if let Some(p) = &td.precision {
                cu_ts_defs.1 = Some(elaborate::time_literal_to_exp(p));
            }
        }
        let cu_scope_ts: Option<(i32, i32)> = if let Some(f) = cli.force {
            Some(f)
        } else if cu_ts_defs.0.is_some() || cu_ts_defs.1.is_some() {
            let u = cu_ts_defs.0.unwrap_or(-9);
            let p = cu_ts_defs.1.unwrap_or(u);
            Some((u, p))
        } else {
            None
        };
        let decl_name = match &desc {
            ast::Description::Module(m) => Some(&m.name.name),
            ast::Description::Interface(i) => Some(&i.name.name),
            ast::Description::Program(p) => Some(&p.name.name),
            _ => None,
        };
        if let Some(n) = decl_name {
            let pos = def_source_pos.len();
            def_source_pos.entry(n.clone()).or_insert(pos);
        }
        match desc {
            ast::Description::Module(mut m) => {
                // §23.4: hoist NESTED module declarations (recursively) into
                // the definitions map; the enclosing body keeps everything
                // else. Scope access into the enclosing module is not modeled.
                fn hoist_nested(
                    m: &mut ast::module::ModuleDeclaration,
                    out: &mut Vec<ast::module::ModuleDeclaration>,
                ) {
                    let mut kept = Vec::with_capacity(m.items.len());
                    for item in m.items.drain(..) {
                        if let ast::decl::ModuleItem::NestedModule(inner) = item {
                            let mut inner = *inner;
                            hoist_nested(&mut inner, out);
                            out.push(inner);
                        } else {
                            kept.push(item);
                        }
                    }
                    m.items = kept;
                }
                let mut nested: Vec<ast::module::ModuleDeclaration> = Vec::new();
                hoist_nested(&mut m, &mut nested);
                for n in nested {
                    let nname = n.name.name.clone();
                    if definitions.contains_key(&nname) {
                        log_eprintln(&format!(
                            "[xezim][warning] module '{}' redefined; the later definition overwrites the earlier one (IEEE 1800-2017 \u{00a7}3.3)",
                            nname
                        ));
                    }
                    let (unit_s, prec_s) = eff_ts.get(&nname).copied().unwrap_or((tick_s, tick_s));
                    let mut n = n;
                    elaborate::rewrite_module_delays_pub(&mut n.items, unit_s, prec_s, tick_s);
                    elaborate::scope_time_param_ports_pub(&mut n.params, unit_s, prec_s);
                    definitions.insert(nname, SourceDefinition::Module(Rc::new(n)));
                }
                let name = m.name.name.clone();
                // Only a same-kind collision (module overwriting module) is a
                // genuine §3.3 redefinition worth warning about — and the module
                // then legitimately wins. A module with the SAME name as an
                // existing class/interface/package is legal (§3.13: hierarchy
                // and data namespaces are separate); `class_defs` preserves the
                // class, so no warning and no data loss.
                if matches!(definitions.get(&name), Some(SourceDefinition::Module(_))) {
                    // The reference simulator ACCEPTS a redefinition with a
                    // warning and the LAST definition wins (measured:
                    // "Existing module 'm' ... will be overwritten", the
                    // second body's output appears). Rejecting broke multi-
                    // file flows that deliberately override a module.
                    log_eprintln(&format!(
                        "[xezim][warning] module '{}' redefined; the later definition overwrites the earlier one (IEEE 1800-2017 \u{00a7}3.3)",
                        name
                    ));
                }
                // Pre-scale this module's delays from its own timeunit to the
                // global tick (no-op when both are 1 ns).
                // Every module's delays are pre-scaled to the global tick, even
                // those with no explicit or CLI timescale — the simulator
                // consumes tick-denominated delays. A module with no effective
                // timescale uses the tick unit, making the rewrite a numeric
                // no-op but still converting the delay form.
                let (unit_s, prec_s) = eff_ts.get(&name).copied().unwrap_or((tick_s, tick_s));
                elaborate::rewrite_module_delays_pub(&mut m.items, unit_s, prec_s, tick_s);
                elaborate::scope_time_param_ports_pub(&mut m.params, unit_s, prec_s);
                top_module = Some(name.clone());
                definitions.insert(name, SourceDefinition::Module(Rc::new(m)));
            }
            ast::Description::Interface(i) => {
                let name = i.name.name.clone();
                // Interface items ARE `ModuleItem`s, so the module walker
                // applies unchanged; the effective timescale now exists for
                // interfaces too (see the ts_target walk above).
                let (unit_s, prec_s) = eff_ts.get(&name).copied().unwrap_or((tick_s, tick_s));
                let mut i = i;
                elaborate::rewrite_module_delays_pub(&mut i.items, unit_s, prec_s, tick_s);
                elaborate::scope_time_param_ports_pub(&mut i.params, unit_s, prec_s);
                definitions.insert(name, SourceDefinition::Interface(Rc::new(i)));
            }
            ast::Description::Program(mut p) => {
                let name = p.name.name.clone();
                // A program's delays scale like a module's; the pass never
                // visited programs, so `#7` in one ran at zero time.
                let (unit_s, prec_s) = eff_ts.get(&name).copied().unwrap_or((tick_s, tick_s));
                elaborate::rewrite_module_delays_pub(&mut p.items, unit_s, prec_s, tick_s);
                elaborate::scope_time_param_ports_pub(&mut p.params, unit_s, prec_s);
                top_module = Some(name.clone());
                definitions.insert(name, SourceDefinition::Program(Rc::new(p)));
            }
            ast::Description::Class(mut c) => {
                if let Some((u, p)) = cu_scope_ts {
                    elaborate::rewrite_class_time_semantics(&mut c, u, p, tick_s);
                }
                // A compilation-unit class scales its method delays by the
                // unit's `timescale, like a package's classes.
                let (unit_s, prec_s) = forced_secs.unwrap_or_else(|| {
                    module_timescales
                        .get("$unit")
                        .copied()
                        .unwrap_or((tick_s, tick_s))
                });
                elaborate::rewrite_class_delays_pub(&mut c, unit_s, prec_s, tick_s);
                let name = c.name.name.clone();
                let rc = Rc::new(c);
                // Always keep the class in its own registry so a same-named
                // module cannot clobber it (see `class_defs`). Into
                // `definitions` it goes ONLY when the name is free of a
                // hierarchy kind (module/interface/program) — a class and a
                // module may share a name (§3.13), and if the module came
                // first we must not evict it from the name-keyed slot the
                // top-module/instantiation walkers rely on. In that case the
                // registration below restores the class into `elab.classes`.
                class_defs.insert(name.clone(), rc.clone());
                match definitions.get(&name) {
                    Some(SourceDefinition::Module(_))
                    | Some(SourceDefinition::Interface(_))
                    | Some(SourceDefinition::Program(_)) => {}
                    _ => {
                        definitions.insert(name, SourceDefinition::Class(rc));
                    }
                }
            }
            ast::Description::Package(mut p) => {
                if let Some((u, pr)) = cu_scope_ts {
                    for item in &mut p.items {
                        match item {
                            ast::decl::PackageItem::Function(f) => {
                                elaborate::rewrite_scope_time_semantics(&mut f.items, u, pr, tick_s)
                            }
                            ast::decl::PackageItem::Task(t) => {
                                elaborate::rewrite_scope_time_semantics(&mut t.items, u, pr, tick_s)
                            }
                            ast::decl::PackageItem::Class(c) => {
                                elaborate::rewrite_class_time_semantics(c, u, pr, tick_s)
                            }
                            _ => {}
                        }
                    }
                }
                let name = p.name.name.clone();
                // Delays inside the package scale by ITS timescale, exactly
                // as a module's items do above; without this a `#200` in a
                // package class method stayed 200 raw ticks.
                // Packages are not in `eff_ts` (that walk covers instantiable
                // elements); the preprocessor records the directive in effect
                // at the package, else the compilation unit's first one.
                let (mut unit_s, mut prec_s) = forced_secs.unwrap_or_else(|| {
                    module_timescales
                        .get(&name)
                        .or_else(|| module_timescales.get("$unit"))
                        .copied()
                        .unwrap_or((tick_s, tick_s))
                });
                // A `timeunit`/`timeprecision` declared IN the package wins
                // over the directive (LRM §3.14.2.2), but not over
                // `-override_timescale`.
                for item in p.items.iter().filter(|_| forced_secs.is_none()) {
                    if let ast::decl::PackageItem::TimeunitsDecl(td) = item {
                        if let Some(u) = &td.unit {
                            unit_s = elaborate::exp_to_secs(elaborate::time_literal_to_exp(u));
                        }
                        if let Some(pr) = &td.precision {
                            prec_s = elaborate::exp_to_secs(elaborate::time_literal_to_exp(pr));
                        }
                    }
                }
                elaborate::rewrite_package_delays_pub(&mut p.items, unit_s, prec_s, tick_s);
                definitions.insert(name, SourceDefinition::Package(Rc::new(p)));
            }
            ast::Description::TypedefDecl(t) => {
                let name = t.name.name.clone();
                // §6.18: a bare forward typedef (`typedef name;`) must not
                // displace a real definition of the same name — `typedef_test_0`
                // restates the forward name after the full `typedef int name;`.
                // Forward → insert only if absent; real → always (replaces a
                // prior forward placeholder).
                if t.forward {
                    // A bare forward typedef (`typedef name;`) is a placeholder;
                    // it must not displace a real definition of the same name —
                    // `definitions.entry().or_insert` leaves a prior real entry
                    // in place. A placeholder has no entity to preserve across a
                    // hierarchy-name clash (only REAL typedefs do — they are
                    // recorded in `typedef_defs` below).
                    definitions
                        .entry(name)
                        .or_insert_with(|| SourceDefinition::Typedef(Rc::new(t)));
                } else {
                    // Real typedef: keep it in the dedicated registry so a
                    // same-named hierarchy kind (module/interface/program/
                    // package/UDP) that later takes the `definitions` slot
                    // can't erase it (see `typedef_defs`). Mirrors the class
                    // guard: into the name-keyed `definitions` map it goes
                    // ONLY when the name is free of a hierarchy-kind slot the
                    // instantiation/type walkers rely on (§3.13 data vs
                    // hierarchy namespaces are separate).
                    typedef_defs.insert(name.clone(), Rc::new(t.clone()));
                    match definitions.get(&name) {
                        Some(SourceDefinition::Module(_))
                        | Some(SourceDefinition::Interface(_))
                        | Some(SourceDefinition::Program(_)) => {}
                        _ => {
                            definitions.insert(name, SourceDefinition::Typedef(Rc::new(t)));
                        }
                    }
                }
            }
            ast::Description::ImportDecl(id) => {
                top_level_imports.push(id);
            }
            ast::Description::PackageItem(ast::decl::PackageItem::Checker(c)) => {
                let m = ast::module::ModuleDeclaration {
                    attrs: Vec::new(),
                    kind: ast::module::ModuleKind::Module,
                    lifetime: None,
                    name: c.name,
                    params: Vec::new(),
                    ports: c.ports,
                    items: c.items,
                    endlabel: c.endlabel,
                    span: c.span,
                };
                let name = m.name.name.clone();
                definitions.insert(name, SourceDefinition::Module(Rc::new(m)));
            }
            ast::Description::PackageItem(ast::decl::PackageItem::Let(l)) => {
                top_level_lets.push(l);
            }
            ast::Description::PackageItem(ast::decl::PackageItem::Function(mut f)) => {
                if let Some((u, p)) = cu_scope_ts {
                    elaborate::rewrite_scope_time_semantics(&mut f.items, u, p, tick_s);
                }
                // A `$unit` subroutine's delays scale by the compilation
                // unit's `timescale (recorded as "$unit"), like a module's.
                let (unit_s, prec_s) = forced_secs.unwrap_or_else(|| {
                    module_timescales
                        .get("$unit")
                        .copied()
                        .unwrap_or((tick_s, tick_s))
                });
                for st in f.items.iter_mut() {
                    elaborate::rewrite_stmt_delays_pub(st, unit_s, prec_s, tick_s);
                }
                top_level_functions.push(f);
            }
            ast::Description::PackageItem(ast::decl::PackageItem::Task(mut t)) => {
                if let Some((u, p)) = cu_scope_ts {
                    elaborate::rewrite_scope_time_semantics(&mut t.items, u, p, tick_s);
                }
                let (unit_s, prec_s) = forced_secs.unwrap_or_else(|| {
                    module_timescales
                        .get("$unit")
                        .copied()
                        .unwrap_or((tick_s, tick_s))
                });
                for st in t.items.iter_mut() {
                    elaborate::rewrite_stmt_delays_pub(st, unit_s, prec_s, tick_s);
                }
                top_level_tasks.push(t);
            }
            ast::Description::PackageItem(ast::decl::PackageItem::Nettype(n)) => {
                top_level_nettypes.push(n);
            }
            ast::Description::PackageItem(ast::decl::PackageItem::DPIImport(di)) => {
                top_level_dpi_imports.push(di);
            }
            ast::Description::DPIImport(di) => {
                top_level_dpi_imports.push(di);
            }
            ast::Description::DPIExport(e) => {
                top_level_dpi_exports.push(e);
            }
            ast::Description::PackageItem(ast::decl::PackageItem::DPIExport(e)) => {
                top_level_dpi_exports.push(e);
            }
            ast::Description::PackageItem(ast::decl::PackageItem::Parameter(p)) => {
                top_level_params.push(p);
            }
            ast::Description::PackageItem(ast::decl::PackageItem::Data(d)) => {
                top_level_vars.push(d);
            }
            // §6.7 / §10.3.1: keep net kind, strengths, delays and continuous
            // declaration assignments when hoisting compilation-unit storage.
            ast::Description::PackageItem(ast::decl::PackageItem::Net(n)) => {
                top_level_nets.push(n);
            }
            ast::Description::PackageItem(ast::decl::PackageItem::Covergroup(cg)) => {
                top_level_covergroups.push(cg);
            }
            ast::Description::Bind(b) => {
                top_level_binds.push(b);
            }
            ast::Description::OutOfClassConstraint {
                class_name,
                constraint_name,
                items,
            } => {
                top_level_ooc_constraints.push((class_name, constraint_name, items));
            }
            ast::Description::Udp(u) => {
                // IEEE 1800-2017 §29: register the UDP in the definition map so
                // instantiations resolve to it (elaboration lowers each
                // instance into a runtime truth-table evaluator).
                let name = u.name.name.clone();
                // Mirror the historical behavior where a UDP parsed as an empty
                // `Description::Module` advanced the source-order `top_module`
                // cursor. A UDP is never a real hierarchy root, but keeping this
                // cursor identical preserves auto-top-detection: a following
                // heuristic re-selects a proper module/program candidate, and
                // leaving the cursor on a trailing UDP (an instantiated,
                // non-candidate name) correctly forces that heuristic instead of
                // pinning a trivial trailing program/package.
                top_module = Some(name.clone());
                definitions.insert(name, SourceDefinition::Udp(Rc::new(u)));
            }
            _ => {}
        }
    }

    // Before binds clone any definition, so a specialized clone carries the
    // overridden default too.
    let mut param_override_hits = apply_param_overrides(&mut definitions, None)?;

    // §23.11: retain module/generate bind declarations in their lexical
    // scopes. Targets are resolved after the ordinary hierarchy is elaborated.
    if !top_level_functions.is_empty()
        || !top_level_tasks.is_empty()
        || !top_level_nettypes.is_empty()
        || !top_level_params.is_empty()
        || !top_level_vars.is_empty()
        || !top_level_nets.is_empty()
        || !top_level_covergroups.is_empty()
        || !top_level_dpi_imports.is_empty()
        || !top_level_dpi_exports.is_empty()
    {
        for def in definitions.values_mut() {
            // §3.12.1 / §13.4.3: programs and interfaces share compilation-
            // unit declarations with modules, including constant functions.
            if let Some((ports, params, items)) = match def {
                SourceDefinition::Module(m) => {
                    let m = Rc::make_mut(m);
                    Some((&m.ports, &m.params, &mut m.items))
                }
                SourceDefinition::Program(p) => {
                    let p = Rc::make_mut(p);
                    Some((&p.ports, &p.params, &mut p.items))
                }
                SourceDefinition::Interface(i) => {
                    let i = Rc::make_mut(i);
                    Some((&i.ports, &i.params, &mut i.items))
                }
                _ => None,
            } {
                // What this module declares ITSELF, captured before anything is
                // injected — a name in here shadows the $unit declaration of
                // the same name (§3.12.1), see the variable injection below.
                let local_decl_names: std::collections::HashSet<String> =
                    design_declared_names(ports, params, items);
                // §3.12.1: a $unit subroutine's body resolves its free names
                // in $UNIT scope. When this module SHADOWS a $unit variable,
                // the shadowed copy is injected under the reserved
                // `$unit::<name>` (see the variable injection below) — rewrite
                // the injected body to reference THAT, or the subroutine would
                // silently read/write the module's shadow instead.
                let mut shadowed_unit_vars: std::collections::HashMap<String, String> =
                    top_level_vars
                        .iter()
                        .flat_map(|d| d.declarators.iter())
                        .filter(|v| local_decl_names.contains(&v.name.name))
                        .map(|v| {
                            (
                                v.name.name.clone(),
                                sv_parser::unit_scope_name(&v.name.name),
                            )
                        })
                        .collect();
                shadowed_unit_vars.extend(
                    top_level_nets
                        .iter()
                        .flat_map(|d| &d.declarators)
                        .filter(|v| local_decl_names.contains(&v.name.name))
                        .map(|v| {
                            (
                                v.name.name.clone(),
                                sv_parser::unit_scope_name(&v.name.name),
                            )
                        }),
                );
                let subst_body = |items: &[ast::stmt::Statement],
                                  ports: &[ast::decl::FunctionPort]|
                 -> Option<Vec<ast::stmt::Statement>> {
                    if shadowed_unit_vars.is_empty() {
                        return None;
                    }
                    // A formal or body-local of the same name re-shadows —
                    // drop those from the substitution for this subroutine.
                    let mut map = shadowed_unit_vars.clone();
                    for p in ports {
                        map.remove(&p.name.name);
                    }
                    for it in items {
                        if let ast::stmt::StatementKind::VarDecl { declarators, .. } = &it.kind {
                            for d in declarators {
                                map.remove(&d.name.name);
                            }
                        }
                    }
                    if map.is_empty() {
                        return None;
                    }
                    Some(
                        items
                            .iter()
                            .map(|s| elaborate::substitute_bare_idents_stmt(s, &map))
                            .collect(),
                    )
                };
                for f in top_level_functions.iter().rev() {
                    let mut f = f.clone();
                    if let Some(items) = subst_body(&f.items, &f.ports) {
                        f.items = items;
                    }
                    items.insert(0, ast::decl::ModuleItem::FunctionDeclaration(f));
                }
                for t in top_level_tasks.iter().rev() {
                    let mut t = t.clone();
                    if let Some(items) = subst_body(&t.items, &t.ports) {
                        t.items = items;
                    }
                    items.insert(0, ast::decl::ModuleItem::TaskDeclaration(t));
                }
                for n in top_level_nettypes.iter().rev() {
                    items.insert(0, ast::decl::ModuleItem::NettypeDeclaration(n.clone()));
                }
                for di in top_level_dpi_imports.iter().rev() {
                    // A module's own import of the same name shadows the
                    // $unit one (§3.12.1); do not inject a duplicate.
                    let name = match &di.proto {
                        ast::decl::DPIProto::Function(fd) => fd.name.name.name.clone(),
                        ast::decl::DPIProto::Task(td) => td.name.name.name.clone(),
                    };
                    let own = items.iter().any(|it| {
                        matches!(it, ast::decl::ModuleItem::DPIImport(x)
                        if match &x.proto {
                            ast::decl::DPIProto::Function(fd) => fd.name.name.name == name,
                            ast::decl::DPIProto::Task(td) => td.name.name.name == name,
                        })
                    });
                    if !own {
                        items.insert(0, ast::decl::ModuleItem::DPIImport(di.clone()));
                    }
                }
                for e in top_level_dpi_exports.iter() {
                    items.push(ast::decl::ModuleItem::DPIExport(e.clone()));
                }
                // A module's own covergroup of the same name shadows the
                // $unit one.
                for cg in top_level_covergroups.iter().rev() {
                    let own = items.iter().any(|it| {
                        matches!(it, ast::decl::ModuleItem::CovergroupDeclaration(x)
                            if x.name.name == cg.name.name)
                    });
                    if !own {
                        items.insert(0, ast::decl::ModuleItem::CovergroupDeclaration(cg.clone()));
                    }
                }
                // $unit-scope parameters become body localparams (constants):
                // visible inside the module, not part of its override interface.
                // A module-local declaration of the same name SHADOWS the $unit
                // one (LRM §3.12.1 name resolution) — skip injecting any $unit
                // param the module already declares, else the two collide as a
                // "Duplicate declaration". The skip is per DECLARATOR: with
                // `localparam int A = 1, B = 2;` at $unit scope and a module
                // declaring only `B`, dropping the whole declaration would have
                // lost `A` and keeping it re-declared `B`.
                for p in top_level_params.iter().rev() {
                    let mut p = p.clone();
                    if let ast::decl::ParameterKind::Data { assignments, .. } = &mut p.kind {
                        assignments.retain(|a| !local_decl_names.contains(&a.name.name));
                        if assignments.is_empty() {
                            continue;
                        }
                    }
                    items.insert(0, ast::decl::ModuleItem::LocalparamDeclaration(p));
                }
                // $unit-scope variables (`string label = "X";`) become module
                // signals so references — including from class methods
                // validated against this module — resolve.
                //
                // §3.12.1: a module-local declaration of the same name SHADOWS
                // the $unit variable — they are two DISTINCT objects. Injecting
                // the $unit copy verbatim collided with the module's own
                // declaration ("duplicate declaration of 'gv'"). A shadowed
                // $unit variable is instead injected under the reserved name
                // `$unit::<name>`, which is what a qualified `$unit::gv`
                // reference resolves to; the module's own `gv` keeps the bare
                // name, so the two no longer share one storage slot.
                for d in top_level_vars.iter().rev() {
                    if !d
                        .declarators
                        .iter()
                        .any(|v| local_decl_names.contains(&v.name.name))
                    {
                        items.insert(0, ast::decl::ModuleItem::DataDeclaration(d.clone()));
                        continue;
                    }
                    // `int a, b;` where only `b` is shadowed: split the
                    // declaration so each declarator lands under the right name.
                    let (shadowed, plain): (Vec<_>, Vec<_>) = d
                        .declarators
                        .iter()
                        .cloned()
                        .partition(|v| local_decl_names.contains(&v.name.name));
                    if !shadowed.is_empty() {
                        let mut dd = d.clone();
                        dd.declarators = shadowed;
                        for v in dd.declarators.iter_mut() {
                            v.name.name = sv_parser::unit_scope_name(&v.name.name);
                        }
                        items.insert(0, ast::decl::ModuleItem::DataDeclaration(dd));
                    }
                    if !plain.is_empty() {
                        let mut dd = d.clone();
                        dd.declarators = plain;
                        items.insert(0, ast::decl::ModuleItem::DataDeclaration(dd));
                    }
                }
                // §3.12.1: unit nets remain distinct from module-local
                // declarations, and their driver expressions use unit scope.
                for net in top_level_nets.iter().rev() {
                    let mut net = net.clone();
                    for decl in &mut net.declarators {
                        if local_decl_names.contains(&decl.name.name) {
                            decl.name.name = sv_parser::unit_scope_name(&decl.name.name);
                        }
                        if let Some(init) = &mut decl.init {
                            let stmt = ast::stmt::Statement::new(
                                ast::stmt::StatementKind::Expr(init.clone()),
                                init.span,
                            );
                            if let ast::stmt::StatementKind::Expr(expr) =
                                elaborate::substitute_bare_idents_stmt(&stmt, &shadowed_unit_vars)
                                    .kind
                            {
                                *init = expr;
                            }
                        }
                    }
                    items.insert(0, ast::decl::ModuleItem::NetDeclaration(net));
                }
            }
        }
    }
    // Capture the definitions that came from the explicitly-provided source
    // files BEFORE pulling in `-y` / `-v` library modules. Library
    // modules satisfy instantiations but must NEVER be candidates for the
    // implicit top: otherwise compiling a self-contained file (e.g. a lone
    // `class`) that shares an include dir with sibling testbenches would let
    // one of those testbenches (`module tb; initial run_test(); …`) get picked
    // as the top and run. An include dir is a search path, not a compile list.
    let explicit_def_names: std::collections::HashSet<String> =
        definitions.keys().cloned().collect();
    let lib_cli = library_cli_cell().lock().unwrap().clone();
    if !lib_cli.lib_dirs.is_empty() || !lib_cli.lib_files.is_empty() {
        resolve_library_modules(
            &mut definitions,
            include_dirs,
            lib_defines,
            &lib_cli,
            &top_level_binds,
        )?;
        let lib_hits = apply_param_overrides(&mut definitions, Some(&explicit_def_names))?;
        for (h, n) in param_override_hits.iter_mut().zip(lib_hits) {
            *h += n;
        }

        // A `-v`/`-y` library module is adopted AFTER the primary-source delay
        // rewrite (above), so it never received a timescale — its `#delay`s
        // stayed raw tick-unit values while the same module compiled as a
        // primary source would be scaled. Apply `--module-timescale` (named,
        // else global) to each newly-adopted library module so its delays scale
        // consistently. Library modules with no CLI timescale keep tick units
        // (their own `` `timescale `` directive is a separate, not-yet-captured
        // path).
        if cli.global.is_some() || !cli.named.is_empty() {
            let lib_names: Vec<String> = definitions
                .keys()
                .filter(|n| !explicit_def_names.contains(*n))
                .cloned()
                .collect();
            for name in lib_names {
                let ts = cli.named.get(&name).copied().or(cli.global);
                let Some((u, p)) = ts else { continue };
                let unit_s = elaborate::exp_to_secs(u);
                let prec_s = elaborate::exp_to_secs(p);
                if let Some(SourceDefinition::Module(rc)) = definitions.get_mut(&name) {
                    let m = Rc::make_mut(rc);
                    elaborate::rewrite_module_delays_pub(&mut m.items, unit_s, prec_s, tick_s);
                    elaborate::scope_time_param_ports_pub(&mut m.params, unit_s, prec_s);
                    module_timescale_exp.insert(
                        name.clone(),
                        (
                            elaborate::secs_to_exp(unit_s),
                            elaborate::secs_to_exp(elaborate::exp_to_secs(p)),
                        ),
                    );
                }
            }
        }
    }

    warn_unapplied_param_overrides(&param_override_hits);

    // §6.18 + §3.12.1: a $unit typedef's DIMENSIONS are evaluated in the
    // scope where the typedef is DECLARED — the compilation unit — not where
    // the type is later used. The $unit localparams themselves are injected
    // into each module body (and skipped entirely when the module shadows the
    // name), so by elaboration time the typedef would resolve its dims against
    // the MODULE's table: `localparam A=8; typedef logic [A-1:0] T[1:0];` in
    // a module declaring `localparam A=4` produced 4-bit (or, shadowed, 1-bit)
    // elements. Fold the dims to literals here, against the $unit environment,
    // while both are still in hand. Anything that doesn't const-evaluate in
    // that environment (e.g. `pkg::W`) is left untouched for the existing
    // late resolution.
    {
        let mut unit_params: std::collections::HashMap<
            String,
            Value,
            crate::hasher::DeterministicState,
        > = Default::default();
        for pd in &top_level_params {
            if let ast::decl::ParameterKind::Data { assignments, .. } = &pd.kind {
                for a in assignments {
                    if let Some(init) = &a.init {
                        if let Some(v) =
                            elaborate::const_eval_i64_with_params(init, Some(&unit_params))
                        {
                            let mut val = Value::from_u64(v as u64, 32);
                            val.is_signed = true;
                            unit_params.insert(a.name.name.clone(), val);
                        }
                    }
                }
            }
        }
        {
            type PTable =
                std::collections::HashMap<String, Value, crate::hasher::DeterministicState>;
            fn fold_expr(e: &mut ast::expr::Expression, table: &PTable) {
                if table.is_empty() || matches!(e.kind, ast::expr::ExprKind::Number(_)) {
                    return;
                }
                if let Some(v) = elaborate::const_eval_i64_with_params(e, Some(table)) {
                    if v >= 0 {
                        *e = ast::expr::Expression::new(
                            // UNSIZED literal — a sized one would trip the
                            // §6.19 enum-member width check against narrow
                            // base types.
                            ast::expr::ExprKind::Number(ast::expr::NumberLiteral::Integer {
                                size: None,
                                signed: true,
                                base: ast::expr::NumberBase::Decimal,
                                value: v.to_string(),
                                cached_val: std::cell::Cell::new(None),
                            }),
                            e.span,
                        );
                    }
                }
            }
            fn fold_packed(dims: &mut [ast::types::PackedDimension], table: &PTable) {
                for d in dims.iter_mut() {
                    if let ast::types::PackedDimension::Range { left, right, .. } = d {
                        fold_expr(left, table);
                        fold_expr(right, table);
                    }
                }
            }
            fn fold_unpacked(d: &mut ast::types::UnpackedDimension, table: &PTable) {
                match d {
                    ast::types::UnpackedDimension::Range { left, right, .. } => {
                        fold_expr(left, table);
                        fold_expr(right, table);
                    }
                    ast::types::UnpackedDimension::Expression { expr, .. } => {
                        fold_expr(expr, table)
                    }
                    // `[B]` with B a parameter parses as an ASSOCIATIVE dim
                    // keyed by "type B" — rewrite to a literal size in the
                    // declaring scope, exactly like normalize_unpacked_dims
                    // does later with the (wrong-scope) module table.
                    ast::types::UnpackedDimension::Associative {
                        data_type: Some(dt),
                        span,
                    } => {
                        if let ast::types::DataType::TypeReference { name, .. } = dt.as_ref() {
                            if let Some(v) = table.get(&name.name.name) {
                                if let Some(n) = v.to_u64() {
                                    *d = ast::types::UnpackedDimension::Expression {
                                        expr: Box::new(ast::expr::Expression::new(
                                            ast::expr::ExprKind::Number(
                                                ast::expr::NumberLiteral::Integer {
                                                    size: None,
                                                    signed: true,
                                                    base: ast::expr::NumberBase::Decimal,
                                                    value: n.to_string(),
                                                    cached_val: std::cell::Cell::new(None),
                                                },
                                            ),
                                            *span,
                                        )),
                                        span: *span,
                                    };
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
            fn fold_dt(dt: &mut ast::types::DataType, table: &PTable, depth: usize) {
                if depth > 8 {
                    return;
                }
                match dt {
                    ast::types::DataType::IntegerVector { dimensions, .. }
                    | ast::types::DataType::Implicit { dimensions, .. }
                    // `typedef l [A-1:0] T[$];` — packed dims ON a type
                    // reference base.
                    | ast::types::DataType::TypeReference { dimensions, .. } => {
                        fold_packed(dimensions, table)
                    }
                    ast::types::DataType::Enum(et) => {
                        if let Some(bt) = et.base_type.as_mut() {
                            fold_dt(bt.as_mut(), table, depth + 1);
                        }
                        // Member initializers (`B = X`) evaluate in the
                        // DECLARING scope too.
                        for m in et.members.iter_mut() {
                            if let Some(init) = m.init.as_mut() {
                                fold_expr(init, table);
                            }
                        }
                    }
                    // A struct/union base (`typedef struct packed { logic
                    // [A-1:0] x; } T[1:0];`) carries the scope references in
                    // its MEMBER types — recurse.
                    ast::types::DataType::Struct(su) => {
                        for m in su.members.iter_mut() {
                            fold_dt(&mut m.data_type, table, depth + 1);
                            for mdecl in m.declarators.iter_mut() {
                                for d in mdecl.dimensions.iter_mut() {
                                    fold_unpacked(d, table);
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
            fn eval_params_into(pd: &ast::decl::ParameterDeclaration, table: &mut PTable) {
                if let ast::decl::ParameterKind::Data { assignments, .. } = &pd.kind {
                    for a in assignments {
                        if let Some(init) = &a.init {
                            if let Some(v) =
                                elaborate::const_eval_i64_with_params(init, Some(table))
                            {
                                let mut val = Value::from_u64(v as u64, 32);
                                val.is_signed = true;
                                table.insert(a.name.name.clone(), val);
                            }
                        }
                    }
                }
            }
            // $unit typedefs fold against the $unit params.
            for def in definitions.values_mut() {
                let SourceDefinition::Typedef(t) = def else {
                    continue;
                };
                let td = Rc::make_mut(t);
                fold_dt(&mut td.data_type, &unit_params, 0);
                for d in td.dimensions.iter_mut() {
                    fold_unpacked(d, &unit_params);
                }
            }
            // PACKAGE typedefs fold against ($unit params + that package's own
            // params, in item order) — each package is its own scope, so
            // same-named localparams in different packages (`P1.A=8`,
            // `P2.A=4`) must not bleed into each other the way the flat
            // elaboration table lets them. With the dims already literal, the
            // later flat-table walk stores the right width no matter which
            // package's `A` currently occupies the slot — and a QUALIFIED
            // `P1::T` reference works without any import.
            for def in definitions.values_mut() {
                let SourceDefinition::Package(pkg) = def else {
                    continue;
                };
                let pkg = Rc::make_mut(pkg);
                let mut table = unit_params.clone();
                for item in pkg.items.iter_mut() {
                    match item {
                        ast::decl::PackageItem::Parameter(pd) => eval_params_into(pd, &mut table),
                        ast::decl::PackageItem::Typedef(td) => {
                            fold_dt(&mut td.data_type, &table, 0);
                            for d in td.dimensions.iter_mut() {
                                fold_unpacked(d, &table);
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    let named_top_found = top_module_name.is_some_and(|n| definitions.contains_key(n));
    if let (Some(name), true) = (top_module_name, named_top_found) {
        top_module = Some(name.to_string());
        // Several tops named on the command line arrive as a wrapper the
        // driver wrote; hoist their module-local declarations as below.
        if name == MULTI_TOP_WRAPPER {
            let mut tops = std::collections::HashSet::new();
            if let Some(w) = definitions.get(name) {
                collect_instantiated_modules(w.items(), &mut tops);
            }
            multi_top_modules = tops.into_iter().collect();
            multi_top_modules.sort();
        }
    } else {
        // No top named, OR the named top wasn't found — auto-detect the
        // hierarchy root (a module instantiated by no other). This recovers
        // from a wrong `:top_module:` in a generated test (e.g. sv-tests'
        // veer-el2 specifies `veer-el2_wrapper`, but the module is
        // `el2_veer_wrapper`).
        if let Some(name) = top_module_name {
            if strict_top() {
                let mut known: Vec<&str> = definitions
                    .iter()
                    .filter(|(n, d)| {
                        explicit_def_names.contains(n.as_str())
                            && !matches!(d, SourceDefinition::Typedef(_) | SourceDefinition::Udp(_))
                    })
                    .map(|(n, _)| n.as_str())
                    .collect();
                known.sort_unstable();
                return Err(format!(
                    "top module '{}' not found; known top-level definitions: {} \
                     (use --no-strict-top to auto-detect the design root instead)",
                    name,
                    if known.is_empty() {
                        "(none)".to_string()
                    } else {
                        known.join(", ")
                    }
                ));
            }
            eprintln!(
                "[xezim][warning] top module '{}' not found; auto-detecting the design root",
                name
            );
        }
        let mut instantiated: std::collections::HashSet<String> = std::collections::HashSet::new();
        for m in definitions.values() {
            collect_instantiated_modules(m.items(), &mut instantiated);
        }
        for bind in &top_level_binds {
            instantiated.insert(bind.instantiation.module_name.name.clone());
        }
        let mut candidates: Vec<String> = definitions
            .keys()
            .filter(|n| {
                !instantiated.contains(n.as_str())
                && explicit_def_names.contains(n.as_str())
                // A top-level (`$unit`-scope) typedef is never a hierarchy
                // root. Without this a file like `typedef enum {...} T;
                // module test; ...` wrongly picked `T`, which then fails
                // elaboration ("not a module or program"). Packages stay
                // eligible: a package-only design (e.g. uvm_pkg) legitimately
                // elaborates the package as the root.
                && !matches!(definitions.get(n.as_str()), Some(SourceDefinition::Typedef(_)))
                // §29: a UDP is never a hierarchy root — exclude it so a
                // trailing/unused primitive can't pin auto-top-detection.
                && !matches!(definitions.get(n.as_str()), Some(SourceDefinition::Udp(_)))
            })
            .cloned()
            .collect();
        // Sort to make top-module selection deterministic when more than one
        // module is uninstantiated. Without this, ahash's random seed picks
        // arbitrarily between, e.g., openc910's `tb` and `top` testbenches —
        // each iteration runs a different testbench's initial blocks, so the
        // sim either fires up clk/rst correctly or silently picks the
        // verilator variant whose forever-counter logic xezim doesn't model.
        candidates.sort();
        // If the source-order parse already picked a top that's a valid
        // candidate (uninstantiated by anything else), prefer it over the
        // candidate-based heuristic. Otherwise fall through to the heuristic
        // and rely on `candidates.sort()` for determinism.
        let parse_pick_valid = top_module
            .as_ref()
            .is_some_and(|n| candidates.iter().any(|c| c == n));
        // IEEE 1800-2017 §23.3.3: every uninstantiated
        // module/interface/program is a top-level instance and its
        // initial/always/continuous-assign blocks ALL execute concurrently.
        // xezim elaborates a single root, so when MORE than one module-like
        // candidate is uninstantiated, wrap them all in a synthetic module and
        // let `inline_instantiations` flatten each as a namespaced child
        // instance (signal/block names are prefixed per instance, avoiding
        // collisions). Packages/classes/typedefs/UDPs are excluded: packages
        // are consumed globally regardless of root choice, and the rest are
        // not hierarchy roots. This fixes multi-top testbenches (e.g. UVM's
        // 35objections/03basic/04module) where the previous heuristic ran only
        // one module's initial blocks.
        let mut module_candidates: Vec<String> = candidates
            .iter()
            .filter(|c| {
                matches!(
                    definitions.get(c.as_str()),
                    Some(SourceDefinition::Module(_))
                        | Some(SourceDefinition::Interface(_))
                        | Some(SourceDefinition::Program(_))
                )
            })
            .cloned()
            .collect();
        // §23.3.3: the tops elaborate (and their time-0 processes start) in
        // source order, not name order; library-adopted ones go last.
        module_candidates.sort_by_key(|c| def_source_pos.get(c).copied().unwrap_or(usize::MAX));
        if module_candidates.len() > 1 {
            // Multi-top design: synthesize `__xezim_multi_top` instantiating
            // every top-level module and elaborate that as the root.
            let wrapper = make_multi_top_wrapper(&module_candidates);
            let wrapper_name = wrapper.name.name.clone();
            definitions.insert(
                wrapper_name.clone(),
                SourceDefinition::Module(std::rc::Rc::new(wrapper)),
            );
            top_module = Some(wrapper_name);
            multi_top_modules = module_candidates.clone();
        } else if parse_pick_valid {
            // Keep top_module as-is — deterministic via source order.
        } else if candidates.len() == 1 {
            top_module = Some(candidates[0].clone());
        } else if candidates.len() > 1 {
            for c in &candidates {
                if definitions
                    .get(c)
                    .unwrap()
                    .items()
                    .iter()
                    .any(|item| matches!(item, ast::decl::ModuleItem::InitialConstruct(_)))
                {
                    top_module = Some(c.clone());
                    break;
                }
            }
        }
        // No candidate carried an `initial` (e.g. a file of several `class`
        // declarations with no module — common in §18 constrained-random
        // tests). Rather than failing with "No module found", fall back to the
        // first candidate so the design still elaborates: a single-class file
        // already behaved this way, and a multi-class file should too.
        if top_module.is_none() && !candidates.is_empty() {
            top_module = Some(candidates[0].clone());
        }
    }

    elaborate::relaxed_static::normalize(&mut definitions);
    let top_name = top_module.ok_or("No module found")?;
    let top_def = definitions
        .get(&top_name)
        .ok_or_else(|| format!("Module '{}' not found", top_name))?;
    let params = crate::hasher::HashMap::default();

    let def_refs: crate::hasher::HashMap<String, elaborate::Definition> = definitions
        .iter()
        .filter_map(|(k, v)| {
            let def = match v {
                SourceDefinition::Module(m) => elaborate::Definition::Module(m),
                SourceDefinition::Interface(i) => elaborate::Definition::Interface(i),
                SourceDefinition::Program(p) => elaborate::Definition::Program(p),
                SourceDefinition::Class(c) => elaborate::Definition::Class(c),
                SourceDefinition::Package(p) => elaborate::Definition::Package(p),
                SourceDefinition::Typedef(t) => elaborate::Definition::Typedef(t),
                SourceDefinition::Udp(u) => elaborate::Definition::Udp(u),
            };
            Some((k.clone(), def))
        })
        .collect();

    let elab_def = match top_def {
        SourceDefinition::Module(m) => elaborate::Definition::Module(m),
        SourceDefinition::Interface(i) => elaborate::Definition::Interface(i),
        SourceDefinition::Program(p) => elaborate::Definition::Program(p),
        SourceDefinition::Class(c) => elaborate::Definition::Class(c),
        SourceDefinition::Package(p) => elaborate::Definition::Package(p),
        _ => {
            return Err(format!(
                "Top-level element '{}' is not a module or program",
                top_name
            ));
        }
    };
    // §3.12.1/§6.20/§23.11: evaluate the compilation unit's bind
    // constants with ordinary typed parameter elaboration, before a top's
    // declarations can shadow them.
    let unit_bind_params = if top_level_binds.is_empty() {
        crate::hasher::HashMap::default()
    } else {
        let mut unit = make_multi_top_wrapper(&[]);
        unit.name.name = "__xezim_bind_unit".into();
        unit.items.extend(
            top_level_params
                .iter()
                .cloned()
                .map(ast::decl::ModuleItem::ParameterDeclaration),
        );
        unit.items.extend(
            top_level_functions
                .iter()
                .cloned()
                .map(ast::decl::ModuleItem::FunctionDeclaration),
        );
        elaborate::elaborate_module_with_defs(
            elaborate::Definition::Module(&unit),
            &params,
            Some(&def_refs),
            &top_level_imports,
            &top_level_lets,
            &[],
        )?
        .parameters
    };
    let mut phase_t = std::time::Instant::now();
    let mut elab = elaborate::elaborate_module_with_defs(
        elab_def,
        &params,
        Some(&def_refs),
        &top_level_imports,
        &top_level_lets,
        &top_level_ooc_constraints,
    )?;
    elab_phase("elaborate top", &mut phase_t);
    elab.tick_s = tick_s;
    elab.module_timescale_exp = module_timescale_exp;
    elab.modules_without_timescale = modules_without_ts;
    // The top module's own unit/precision drives the default $time scaling and
    // $printtimescale when no per-scope entry is found.
    if let Some(&(u, p)) = elab.module_timescale_exp.get(&elab.name) {
        elab.timeunit_exp = u;
        elab.timeprecision_exp = p;
    }
    // `-override_timescale` also covers a synthetic multi-top wrapper, which
    // has no entry of its own.
    if let Some((u, p)) = module_timescale_cli().force {
        elab.timeunit_exp = u;
        elab.timeprecision_exp = p;
    }

    // §23.11: bind selection uses the finished hierarchy and declaration
    // scope. Re-elaborate only designs with newly resolved bindings; ordinary
    // designs retain their single elaboration pass. This also permits binds
    // into hierarchy introduced by an earlier bind.
    for pass in 0..64 {
        elaborate::inline_instantiations(&mut elab, &def_refs)?;
        if !resolve_instance_binds(&mut elab, &top_level_binds, &unit_bind_params)? {
            break;
        }
        if pass == 63 {
            return Err("bind hierarchy does not converge (§23.11)".into());
        }
        let binds = std::mem::take(&mut elab.resolved_binds);
        let timescales = std::mem::take(&mut elab.module_timescale_exp);
        let without_timescale = std::mem::take(&mut elab.modules_without_timescale);
        let unit = elab.timeunit_exp;
        let precision = elab.timeprecision_exp;
        elab = elaborate::elaborate_module_with_defs(
            elab_def,
            &params,
            Some(&def_refs),
            &top_level_imports,
            &top_level_lets,
            &top_level_ooc_constraints,
        )?;
        elab.resolved_binds = binds;
        elab.tick_s = tick_s;
        elab.module_timescale_exp = timescales;
        elab.modules_without_timescale = without_timescale;
        elab.timeunit_exp = unit;
        elab.timeprecision_exp = precision;
    }
    elab_phase("inline instantiations", &mut phase_t);
    // Re-register any compilation-unit-scope CLASS whose name a module
    // clobbered in `definitions`/`def_refs` (§3.13 class/module name-space
    // coexistence). `inline_instantiations` could not see it because the
    // module won the name-keyed slot; restore it into `elab.classes` under
    // its real class name so factory/type creation still resolves. Same
    // registration shape as the multi-top hoist below.
    for (cname, cd) in class_defs.iter() {
        if elab.classes.contains_key(cname) {
            continue;
        }
        elaborate::register_class_enum_members(cd, &mut elab);
        elab.classes.insert(
            cname.clone(),
            std::sync::Arc::new(elaborate::elaborate_class_with_params(
                cd,
                Some(&elab.parameters),
            )),
        );
    }
    // Re-register any compilation-unit-scope TYPEDEF whose name a hierarchy
    // kind clobbered in `definitions`/`def_refs` (§3.13/§6.18 data namespace).
    // `ordered_typedefs` never saw it because the module/interface/program/
    // package/UDP won the name-keyed slot; run it through the same
    // `process_typedef` path the normal elaboration uses so a `shared h;`
    // (handle typed via a clobbered typedef) still resolves at runtime.
    for (tname, td) in typedef_defs.iter() {
        if elab.typedef_types.contains_key(tname)
            && !matches!(
                elab.typedef_types.get(tname),
                Some(ast::types::DataType::Void(_))
            )
        {
            continue;
        }
        elaborate::process_typedef(td, &mut elab);
    }
    // §7.2/§23.3: port CONNECTIONS are emitted as continuous assigns during
    // inlining — after the in-module expansion pass — so an unpacked-struct
    // port connection (`assign s = u1.o;`) arrives here whole. Expand those
    // member-wise too, or the parent never sees any member of the value.
    elab_phase("class/typedef re-registration", &mut phase_t);
    elaborate::expand_whole_struct_continuous_assigns(&mut elab);
    elab_phase("whole-struct assign expansion", &mut phase_t);
    // §28.8: bidirectional switches need every terminal's drivers in hand.
    elaborate::resolve_bidirectional_switches(&mut elab);
    // §6.6.7: fold user-defined nettype drivers — after inlining, so drivers
    // arriving from several instances through ports resolve together with any
    // written in the parent. Must precede the bitwise fold below.
    elaborate::resolve_user_nettype_drivers(&mut elab)?;
    elab_phase("switches and nettype drivers", &mut phase_t);
    // §7.2.2: a whole-struct continuous assign that arrived through inlining
    // still needs splitting into per-member assigns.
    elaborate::expand_unpacked_struct_assigns(&mut elab);
    elab_phase("unpacked-struct assign expansion", &mut phase_t);
    // §6.7.1: a net delay delays every driver of the net. Before the fold
    // below, which then resolves the drivers it moves onto a driver-side net.
    elaborate::apply_net_delays(&mut elab);
    // §6.6.1: a net with several continuous drivers resolves them all.
    elaborate::resolve_multi_driver_nets(&mut elab);
    elab_phase("net delays and multi-driver nets", &mut phase_t);
    // Link `function ClassName::m(); ...` out-of-class bodies into their
    // classes — must run after inline_instantiations repopulates classes.
    elaborate::link_extern_methods(&mut elab, &def_refs);
    // Multi-top hoist: a synthetic `__xezim_multi_top` wrapper flattens each
    // top-level module as a child instance (so its signals/initials are
    // namespaced and run), but the child-inline path drops module-LOCAL static
    // declarations (classes/typedefs). When a module is the sole root these
    // are registered globally; to keep multi-top behaviour identical, hoist
    // each top module's classes and typedefs here, exactly as root
    // elaboration does. This is what lets UVM's `class test` + factory
    // (`uvm_component_utils`) resolve when the testbench module is one of
    // several tops.
    if !multi_top_modules.is_empty() {
        for mname in &multi_top_modules {
            let Some(elaborate::Definition::Module(mdef)) = def_refs.get(mname) else {
                continue;
            };
            for item in &mdef.items {
                match item {
                    ast::decl::ModuleItem::ClassDeclaration(cd) => {
                        elaborate::register_class_enum_members(cd, &mut elab);
                        elab.classes.insert(
                            cd.name.name.clone(),
                            std::sync::Arc::new(elaborate::elaborate_class_with_params(
                                cd,
                                Some(&elab.parameters),
                            )),
                        );
                    }
                    ast::decl::ModuleItem::TypedefDeclaration(td) => {
                        elaborate::process_typedef(td, &mut elab);
                    }
                    _ => {}
                }
            }
        }
    }
    // Instance-scoped class handles (an interface's `proxy` handle) are only
    // known after inlining; the root pass above never saw them.
    elaborate::null_init_class_handles(&mut elab);
    if std::env::var("XEZIM_ELAB_STATS").is_ok() {
        eprintln!(
            "[elab-stats] always_blocks={} initial_blocks={} cont_assigns={} pending_always={} pending_initial={} pending_cont_assign={} signals={} parameters={} arrays={} arrays_2d={} arrays_nd={} packed_struct_fields={}",
            elab.always_blocks.len(),
            elab.initial_blocks.len(),
            elab.continuous_assigns.len(),
            elab.pending_always.len(),
            elab.pending_initial.len(),
            elab.pending_cont_assign.len(),
            elab.signals.len(),
            elab.parameters.len(),
            elab.arrays.len(),
            elab.arrays_2d.len(),
            elab.arrays_nd.len(),
            elab.packed_struct_fields.len(),
        );
        // Bytewise breakdown via bincode serialize. Approximation only —
        // bincode is more compact than in-memory layout (no Vec capacity
        // slack, no padding, no String header) but the per-section relative
        // sizes correctly identify hot spots. On c910 hello this revealed
        // continuous_assigns at 394 MB, always_blocks at 193 MB, signals at
        // 173 MB — the three to target for memory work.
        use bincode::Options;
        let opts = xez_bincode_options();
        let try_size = |label: &str, bytes: Result<Vec<u8>, _>| match bytes {
            Ok(b) => eprintln!("[elab-bytes-bincode] {}: {:>10} bytes", label, b.len()),
            Err(_) => eprintln!("[elab-bytes-bincode] {}: <serialize failed>", label),
        };
        try_size("always_blocks    ", opts.serialize(&elab.always_blocks));
        try_size("initial_blocks   ", opts.serialize(&elab.initial_blocks));
        try_size(
            "continuous_assigns",
            opts.serialize(&elab.continuous_assigns),
        );
        try_size("signals          ", opts.serialize(&elab.signals));
        try_size("parameters       ", opts.serialize(&elab.parameters));
        try_size("arrays           ", opts.serialize(&elab.arrays));
        try_size("arrays_2d        ", opts.serialize(&elab.arrays_2d));
        try_size("arrays_nd        ", opts.serialize(&elab.arrays_nd));
        try_size("functions        ", opts.serialize(&elab.functions));
        try_size("tasks            ", opts.serialize(&elab.tasks));
        try_size("typedefs         ", opts.serialize(&elab.typedefs));
        try_size("typedef_types    ", opts.serialize(&elab.typedef_types));
        try_size("classes          ", opts.serialize(&elab.classes));
        try_size("specify_delays   ", opts.serialize(&elab.specify_delays));
    }
    elab_phase("post-inline passes", &mut phase_t);
    Ok((definitions, elab))
}

/// Decode one suffix from legacy §23.11 specialization names. New binds
/// retain their source definitions and use `resolved_binds` instead.
/// Callers must first check for a real declaration with the complete name.
pub fn bind_spec_base(name: &str) -> &str {
    if let Some(pos) = name.rfind("__bind") {
        let tail = &name[pos + 6..];
        if !tail.is_empty() && tail.bytes().all(|b| b.is_ascii_digit()) {
            return &name[..pos];
        }
    }
    name
}

/// §23.11: select targets using effective hierarchy and lexical constants.
fn resolve_instance_binds(
    elab: &mut elaborate::ElaboratedModule,
    unit_binds: &[ast::decl::BindDirective],
    unit_params: &crate::hasher::HashMap<String, Value>,
) -> Result<bool, String> {
    let mut sites: Vec<_> = elab
        .bind_sites
        .iter()
        .cloned()
        .map(|(scope, b)| (scope, b, false))
        .collect();
    sites.extend(unit_binds.iter().cloned().map(|b| (String::new(), b, true)));
    if sites.is_empty() {
        return Ok(false);
    }
    let mut hosts = vec![(String::new(), elab.name.clone())];
    hosts.extend(
        elab.instances
            .iter()
            .map(|i| (i.path.clone(), i.def_name.clone())),
    );
    let mut changed = false;
    let mut unresolved = Vec::new();
    for (scope, b, unit_scope) in sites {
        let mut constants = elab.parameters.clone();
        if unit_scope {
            // §3.12.1/§23.11: $unit declarations cannot inherit a top's
            // same-named localparam when selecting their bind targets.
            constants.retain(|name, _| name.contains('.') || name.contains("::"));
            constants.extend(
                unit_params
                    .iter()
                    .map(|(name, value)| (name.clone(), value.clone())),
            );
        }
        // Qualified constants remain available; nearer lexical declarations
        // replace bare names from enclosing scopes, never from the target.
        for (key, value) in &elab.parameters {
            constants.insert(format!("{}.{}", elab.name, key), value.clone());
        }
        let mut ancestors = vec![scope.as_str()];
        let mut ancestor = scope.as_str();
        while let Some((parent, _)) = ancestor.rsplit_once('.') {
            ancestors.push(parent);
            ancestor = parent;
        }
        for parent in ancestors.iter().rev() {
            let prefix = format!("{parent}.");
            for (key, value) in &elab.parameters {
                if let Some(local) = key.strip_prefix(&prefix) {
                    constants.insert(local.to_string(), value.clone());
                }
            }
        }
        let mut targets = Vec::new();
        if b.target_path.is_empty() {
            // §23.11: a single identifier can name an instance as well as a
            // module/interface type. Lexical instance lookup takes priority,
            // including when an unrelated type has the same spelling.
            let instance = ancestors
                .iter()
                .filter(|parent| !parent.is_empty())
                .map(|parent| format!("{parent}.{}", b.target_module.name))
                .chain(std::iter::once(b.target_module.name.clone()))
                .find(|candidate| hosts.iter().any(|(host, _)| host == candidate));
            if let Some(instance) = instance {
                targets.push(instance);
            } else {
                targets.extend(
                    hosts
                        .iter()
                        .filter(|(_, def)| *def == b.target_module.name)
                        .map(|(p, _)| p.clone()),
                );
            }
        } else {
            for path in std::iter::once(&b.target_path).chain(b.extra_paths.iter()) {
                let mut joined = String::new();
                for segment in path {
                    if !joined.is_empty() {
                        joined.push('.');
                    }
                    joined.push_str(&segment.name.name);
                    for select in &segment.selects {
                        let value = elaborate::const_eval_i64_with_params(select, Some(&constants))
                            .ok_or_else(|| {
                                format!(
                                    "nonconstant bind target index in '{}' (§23.11)",
                                    b.target_module.name
                                )
                            })?;
                        use std::fmt::Write as _;
                        let _ = write!(joined, "[{value}]");
                    }
                }
                let absolute = joined.strip_prefix("$root.").unwrap_or(&joined);
                let rooted = absolute.strip_prefix(&format!("{}.", elab.name));
                let mut candidates = Vec::new();
                if absolute == elab.name {
                    candidates.push(String::new());
                }
                if let Some(p) = rooted {
                    candidates.push(p.to_string());
                }
                if joined.starts_with("$root.") {
                    candidates.push(absolute.to_string());
                } else {
                    for parent in &ancestors {
                        if !parent.is_empty() {
                            candidates.push(format!("{parent}.{joined}"));
                        }
                    }
                    candidates.push(joined.clone());
                }
                if let Some(target) = candidates
                    .into_iter()
                    .find(|p| hosts.iter().any(|(host, _)| host == p))
                {
                    targets.push(target);
                }
            }
        }
        if targets.is_empty() && !b.target_path.is_empty() {
            unresolved.push(
                b.target_path
                    .iter()
                    .map(|s| s.name.name.as_str())
                    .collect::<Vec<_>>()
                    .join("."),
            );
        }
        targets.sort();
        targets.dedup();
        for target in targets {
            let bound = elab.resolved_binds.entry(target).or_default();
            if !bound.iter().any(|previous| {
                previous.span == b.span
                    && previous.instantiation.module_name.name == b.instantiation.module_name.name
                    && previous.gen_scope == b.gen_scope
                    && previous
                        .instantiation
                        .instances
                        .iter()
                        .map(|i| &i.name.name)
                        .eq(b.instantiation.instances.iter().map(|i| &i.name.name))
            }) {
                bound.push(b.clone());
                changed = true;
            }
        }
    }
    if !changed {
        unresolved.sort();
        unresolved.dedup();
        for target in unresolved {
            log_eprintln(&format!(
                "[elab] no bind target instance '{}'; bind ignored",
                target
            ));
        }
    }
    Ok(changed)
}

pub(crate) fn collect_instantiated_modules(
    items: &[ast::decl::ModuleItem],
    set: &mut std::collections::HashSet<String>,
) {
    for item in items {
        match item {
            ast::decl::ModuleItem::Bind(b) => {
                set.insert(b.instantiation.module_name.name.clone());
            }
            ast::decl::ModuleItem::ModuleInstantiation(mi) => {
                set.insert(mi.module_name.name.clone());
            }
            ast::decl::ModuleItem::GenerateIf(gi) => {
                for (_cond, items) in &gi.branches {
                    collect_instantiated_modules(items, set);
                }
            }
            ast::decl::ModuleItem::GenerateFor(gf) => collect_instantiated_modules(&gf.items, set),
            // A stdcell netlist routinely instantiates cells inside generate
            // regions, named generate blocks, and generate-case arms — these
            // were invisible to the library resolver, so `-v`/`-y` never
            // adopted the cell and elaboration failed with
            // "Module 'X' instantiated but not found".
            ast::decl::ModuleItem::GenerateRegion(gr) => {
                collect_instantiated_modules(&gr.items, set)
            }
            ast::decl::ModuleItem::GenerateCase(gc) => {
                for arm in &gc.arms {
                    collect_instantiated_modules(&arm.items, set);
                }
            }
            _ => {}
        }
    }
}

/// Build a synthetic wrapper module that instantiates each uninstantiated
/// top-level module once, with no port connections (top-level ports are left
/// unconnected, matching how simulators elaborate a module with unused ports).
/// Used as the single elaboration root for multi-top designs
/// (IEEE 1800-2017 §23.3.3). Each instance is named after its module so `%m`
/// reads `__xezim_multi_top.<module>`.
fn make_multi_top_wrapper(modules: &[String]) -> ast::module::ModuleDeclaration {
    use ast::decl::{HierarchicalInstance, ModuleInstantiation};
    let items: Vec<ast::decl::ModuleItem> = modules
        .iter()
        .map(|name| {
            ast::decl::ModuleItem::ModuleInstantiation(ModuleInstantiation {
                module_name: ast::Identifier {
                    name: name.clone(),
                    span: ast::Span::dummy(),
                },
                params: None,
                instances: vec![HierarchicalInstance {
                    name: ast::Identifier {
                        name: name.clone(),
                        span: ast::Span::dummy(),
                    },
                    dimensions: vec![],
                    connections: vec![],
                    span: ast::Span::dummy(),
                }],
                span: ast::Span::dummy(),
            })
        })
        .collect();
    ast::module::ModuleDeclaration {
        attrs: vec![],
        kind: ast::module::ModuleKind::Module,
        lifetime: None,
        name: ast::Identifier {
            name: MULTI_TOP_WRAPPER.to_string(),
            span: ast::Span::dummy(),
        },
        params: vec![],
        ports: ast::module::PortList::Empty,
        items,
        endlabel: None,
        span: ast::Span::dummy(),
    }
}

fn resolve_library_modules(
    definitions: &mut crate::hasher::HashMap<String, SourceDefinition>,
    include_dirs: &[String],
    lib_defines: &std::collections::HashMap<String, preprocessor::MacroDef>,
    lib_cli: &LibraryCli,
    unit_binds: &[ast::decl::BindDirective],
) -> Result<(), String> {
    // Remember this pass's preprocessing context so --dump-merged-sv can
    // re-preprocess ADOPTED files identically (see preprocess_adopted_lib).
    record_adopted_lib_pp_context(include_dirs, lib_defines);
    fn collect_sv_files(
        dir: &std::path::Path,
        exts: &[String],
        out: &mut Vec<std::path::PathBuf>,
    ) -> Result<(), String> {
        let entries =
            std::fs::read_dir(dir).map_err(|e| format!("read_dir '{}': {}", dir.display(), e))?;
        for entry in entries {
            let entry = entry.map_err(|e| format!("read_dir '{}': {}", dir.display(), e))?;
            let path = entry.path();
            if path.is_dir() {
                collect_sv_files(&path, exts, out)?;
                continue;
            }
            let Some(ext) = path.extension().and_then(|s| s.to_str()) else {
                continue;
            };
            if exts.iter().any(|e| e == ext) {
                out.push(path);
            }
        }
        Ok(())
    }

    // `+libext+<ext>` REPLACES the default extension list (commercial
    // semantics); without it, `-y` searches .v/.sv/.V as before.
    let exts: Vec<String> = match &lib_cli.lib_exts {
        Some(list) => list.clone(),
        None => vec!["v".into(), "sv".into(), "V".into()],
    };

    let mut files: Vec<(std::path::PathBuf, bool)> = Vec::new();
    // `-y` semantics are ON-DEMAND (§33.3 / every commercial tool and
    // iverilog): a directory supplies `<module>.<ext>` when `module` is
    // unresolved — nothing else in it is ever read. Eager-parsing the whole
    // directory both poisoned runs with unrelated files' parse errors
    // (Verilator's test_regress `t/` holds ~9400 files, many deliberately
    // broken) and cost multi-GB RSS on big trees. Collect candidates only;
    // parsing happens lazily in the adoption loop below, with a one-time
    // full-scan fallback for libraries whose file names do not match their
    // module names (the historical xezim behavior).
    let mut pending: Vec<std::path::PathBuf> = Vec::new();
    for dir in &lib_cli.lib_dirs {
        let path = std::path::Path::new(dir);
        if path.is_dir() {
            let mut found = Vec::new();
            collect_sv_files(path, &exts, &mut found)?;
            pending.extend(found);
        }
    }
    // `-v <file>`: an explicit library FILE (any extension). Indexed like a
    // `-y` hit — its modules are adopted only when needed, never tops.
    for f in &lib_cli.lib_files {
        let path = std::path::PathBuf::from(f);
        if !path.is_file() {
            return Err(format!("-v library file not found: {}", f));
        }
        files.push((path, true));
    }

    // Index every library file's module/interface/program definitions (and
    // non-forward typedefs) by name WITHOUT adopting them yet. §23.3.2: a
    // library directory supplies definitions only to satisfy *unresolved*
    // instantiations. Adopting everything poisons the primary design's global
    // scope — sv-tests points `-I` at ivltests/ (~1000 unrelated single-file
    // tests), whose modules carry internal typedefs/enums (e.g. an unrelated
    // `typedef word word_darray[];`) that then fail the §6.18 base-type check
    // in a test that never mentions them.
    let mut lib: crate::hasher::HashMap<String, SourceDefinition> = Default::default();
    let mut lib_typedefs: Vec<Rc<ast::decl::TypedefDeclaration>> = Vec::new();
    let mut scanned_paths: Vec<std::path::PathBuf> = Vec::new();
    let mut parse_issue_files: Vec<std::path::PathBuf> = Vec::new();
    let mut lib_origins: crate::hasher::HashMap<String, (std::path::PathBuf, bool, &'static str)> =
        Default::default();
    #[allow(clippy::too_many_arguments)]
    fn index_library_file(
        path: std::path::PathBuf,
        explicit_v: bool,
        include_dirs: &[String],
        lib_defines: &std::collections::HashMap<String, preprocessor::MacroDef>,
        lib_cli: &LibraryCli,
        lib: &mut crate::hasher::HashMap<String, SourceDefinition>,
        lib_typedefs: &mut Vec<Rc<ast::decl::TypedefDeclaration>>,
        scanned_paths: &mut Vec<std::path::PathBuf>,
        parse_issue_files: &mut Vec<std::path::PathBuf>,
        lib_origins: &mut crate::hasher::HashMap<String, (std::path::PathBuf, bool, &'static str)>,
    ) {
        let source = match std::fs::read_to_string(&path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!(
                    "Warning: library file '{}' unreadable: {}",
                    path.display(),
                    e
                );
                return;
            }
        };
        scanned_paths.push(path.clone());
        let mut pp = preprocessor::Preprocessor::new();
        for dir in include_dirs {
            pp.add_include_dir(std::path::PathBuf::from(dir));
        }
        for (name, def) in lib_defines {
            pp.define(name.clone(), def.clone());
        }
        let preprocessed = pp.preprocess_file(&source, Some(&path));
        let line_map = pp.take_line_map();
        // A missing `include or illegal directive in a library file: nothing
        // else reports the preprocessor's list on this path.
        for e in pp.errors() {
            eprintln!("{}", e);
        }
        let result = sv_parser::parse(&preprocessed);
        // Spans index the re-parsed text; it is the preprocessed text again
        // (nothing is left to expand), so the map applies to it.
        let line_map = line_map.filter(|_| result.source_text == preprocessed);
        let file_label = path.display().to_string();
        let render = |d: &diagnostics::Diagnostic| {
            diagnostics::render_diagnostic(d, &result.source_text, line_map.as_ref(), &file_label)
        };
        if explicit_v && lib_cli.primitive_verbose {
            let mut modules = 0usize;
            let mut primitives = 0usize;
            for desc in &result.source.descriptions {
                match desc {
                    ast::Description::Module(m) => {
                        modules += 1;
                        eprintln!(
                            "[primitive-verbose] parsed module '{}' from -v '{}'",
                            m.name.name,
                            path.display()
                        );
                    }
                    ast::Description::Udp(u) => {
                        primitives += 1;
                        eprintln!(
                            "[primitive-verbose] parsed UDP '{}' from -v '{}': ports={} rows={} sequential={} init={:?}",
                            u.name.name,
                            path.display(),
                            u.ports.len(),
                            u.rows.len(),
                            u.is_sequential,
                            u.init
                        );
                    }
                    ast::Description::Interface(i) => eprintln!(
                        "[primitive-verbose] parsed interface '{}' from -v '{}'",
                        i.name.name,
                        path.display()
                    ),
                    ast::Description::Program(p) => eprintln!(
                        "[primitive-verbose] parsed program '{}' from -v '{}'",
                        p.name.name,
                        path.display()
                    ),
                    _ => {}
                }
            }
            eprintln!(
                "[primitive-verbose] -v parse summary '{}': bytes={} descriptions={} modules={} primitives={} errors={} warnings={}",
                path.display(),
                source.len(),
                result.source.descriptions.len(),
                modules,
                primitives,
                result.errors.len(),
                result.warnings.len()
            );
            if !result.errors.is_empty() || !result.warnings.is_empty() {
                eprintln!(
                    "[primitive-verbose] detailed parser diagnostics for -v '{}':",
                    path.display()
                );
                for diagnostic in result.errors.iter().chain(result.warnings.iter()).take(16) {
                    eprintln!("{}", render(diagnostic));
                }
            }
        }
        // A half-parsed library file silently loses every definition after the
        // point of failure — the classic "-v vendor.v then Module 'X' not
        // found". Surface it: file:line:col per error (first three), located
        // through the line map in the original (possibly `include`d) file.
        if !result.errors.is_empty() {
            eprintln!(
                "Warning: library file '{}': {} parse error(s) — definitions after the first error may be lost:",
                path.display(),
                result.errors.len()
            );
            for e in result.errors.iter().take(3) {
                eprintln!("{}", render(e));
            }
            if result.errors.len() > 3 {
                eprintln!("  ... and {} more", result.errors.len() - 3);
            }
            parse_issue_files.push(path.clone());
        }
        // §3.12.1 / §33.3: a library file is its own compilation unit, so a
        // subroutine declared at ITS top level (typically an `include`d
        // simulation-helper header) is visible, unqualified, to every module
        // in that file. The primary-file path injects `$unit` subroutines into
        // every module; mirror that here for the file's own modules — before
        // this they were dropped on adoption, and a call to one was reported
        // as an undeclared identifier.
        let unit_subs: Vec<ast::decl::ModuleItem> = result
            .source
            .descriptions
            .iter()
            .filter_map(|d| match d {
                ast::Description::PackageItem(ast::decl::PackageItem::Function(f)) => {
                    Some(ast::decl::ModuleItem::FunctionDeclaration(f.clone()))
                }
                ast::Description::PackageItem(ast::decl::PackageItem::Task(t)) => {
                    Some(ast::decl::ModuleItem::TaskDeclaration(t.clone()))
                }
                _ => None,
            })
            .collect();
        for desc in result.source.descriptions {
            match desc {
                ast::Description::Module(mut m) => {
                    let name = m.name.name.clone();
                    if !lib.contains_key(&name) {
                        for sub in unit_subs.iter().rev() {
                            m.items.insert(0, sub.clone());
                        }
                        lib.insert(name.clone(), SourceDefinition::Module(Rc::new(m)));
                        lib_origins.insert(name, (path.clone(), explicit_v, "module"));
                    }
                }
                ast::Description::Interface(i) => {
                    let name = i.name.name.clone();
                    if !lib.contains_key(&name) {
                        lib.insert(name.clone(), SourceDefinition::Interface(Rc::new(i)));
                        lib_origins.insert(name, (path.clone(), explicit_v, "interface"));
                    }
                }
                ast::Description::Program(p) => {
                    let name = p.name.name.clone();
                    if !lib.contains_key(&name) {
                        lib.insert(name.clone(), SourceDefinition::Program(Rc::new(p)));
                        lib_origins.insert(name, (path.clone(), explicit_v, "program"));
                    }
                }
                // A non-forward typedef may fill a forward typedef the primary
                // design actually declared; adopted below, never blanket. A
                // forward typedef, class or package is never pulled from a
                // library dir (that is the scope-poisoning we avoid).
                ast::Description::TypedefDecl(t) if !t.forward => {
                    lib_typedefs.push(Rc::new(t));
                }
                // §29: a UDP defined in a `-v`/`-y` library file (vendor
                // stdcell). Adopted on demand like a library module.
                ast::Description::Udp(u) => {
                    let name = u.name.name.clone();
                    if !lib.contains_key(&name) {
                        lib.insert(name.clone(), SourceDefinition::Udp(Rc::new(u)));
                        lib_origins.insert(name, (path.clone(), explicit_v, "UDP"));
                    }
                }
                _ => {}
            }
        }
    }

    for (path, explicit_v) in files {
        index_library_file(
            path,
            explicit_v,
            include_dirs,
            lib_defines,
            lib_cli,
            &mut lib,
            &mut lib_typedefs,
            &mut scanned_paths,
            &mut parse_issue_files,
            &mut lib_origins,
        );
    }

    // Instantiated module/interface/program names inside a definition's body.    // Instantiated module/interface/program names inside a definition's body.
    fn instantiations(def: &SourceDefinition, out: &mut std::collections::HashSet<String>) {
        let items = match def {
            SourceDefinition::Module(m) => &m.items,
            SourceDefinition::Interface(i) => &i.items,
            SourceDefinition::Program(p) => &p.items,
            _ => return,
        };
        collect_instantiated_modules(items, out);
    }

    // Adopt only library modules that satisfy an unresolved instantiation
    // reachable from the explicitly-compiled design, transitively (a pulled-in
    // library module may itself instantiate further library modules).
    let mut seed = std::collections::HashSet::new();
    seed.extend(
        unit_binds
            .iter()
            .map(|b| b.instantiation.module_name.name.clone()),
    );
    // Instantiated-name -> referring definition names. This is what turns an
    // opaque "module 'X' not found" into an actionable note: it names WHICH
    // module's body references X, so a user can check whether that reference
    // even elaborates (a reference inside a dead `generate`/parameter branch
    // is collected by this TEXTUAL scan but never needed at runtime — a
    // commercial elaborator would report nothing for it).
    let mut referrers: std::collections::HashMap<String, std::collections::BTreeSet<String>> =
        std::collections::HashMap::new();
    for (def_name, def) in definitions.iter() {
        let mut names = std::collections::HashSet::new();
        instantiations(def, &mut names);
        for n in &names {
            referrers
                .entry(n.clone())
                .or_default()
                .insert(def_name.clone());
        }
        seed.extend(names);
    }
    let mut work: Vec<String> = seed.into_iter().collect();
    let mut unresolved: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    let mut adopted_from_v = 0usize;
    let mut full_scan_done = false;
    while let Some(name) = work.pop() {
        if definitions.contains_key(&name) {
            continue;
        }
        // Lazy `-y` resolution: try `<dir>/<name>.<ext>` first — the one
        // file the flag's contract says may define this module. Only when
        // that misses does the (one-time) full directory scan run, which
        // keeps name-mismatched libraries working at the old cost.
        if !lib.contains_key(&name) && !pending.is_empty() {
            let mut hit: Vec<std::path::PathBuf> = Vec::new();
            for dir in &lib_cli.lib_dirs {
                for ext in &exts {
                    let cand = std::path::Path::new(dir).join(format!("{name}.{ext}"));
                    if let Some(pos) = pending.iter().position(|p| p == &cand) {
                        hit.push(pending.remove(pos));
                    }
                }
            }
            for path in hit {
                index_library_file(
                    path,
                    false,
                    include_dirs,
                    lib_defines,
                    lib_cli,
                    &mut lib,
                    &mut lib_typedefs,
                    &mut scanned_paths,
                    &mut parse_issue_files,
                    &mut lib_origins,
                );
            }
            if !lib.contains_key(&name) && !full_scan_done {
                full_scan_done = true;
                for path in std::mem::take(&mut pending) {
                    index_library_file(
                        path,
                        false,
                        include_dirs,
                        lib_defines,
                        lib_cli,
                        &mut lib,
                        &mut lib_typedefs,
                        &mut scanned_paths,
                        &mut parse_issue_files,
                        &mut lib_origins,
                    );
                }
            }
        }
        if let Some(def) = lib.get(&name) {
            if let Some((path, from_v, kind)) = lib_origins.get(&name) {
                // Record every adoption (both -v and -y) so `--dump-merged-sv`
                // can append the library files the design actually needed and
                // produce a standalone-rebuildable artifact.
                record_adopted_lib_file(path.clone(), &name);
                if *from_v {
                    adopted_from_v += 1;
                    if lib_cli.primitive_verbose {
                        eprintln!(
                            "[primitive-verbose] adopting {} '{}' from -v '{}' to resolve an instantiation",
                            kind,
                            name,
                            path.display()
                        );
                    }
                }
            }
            let mut more = std::collections::HashSet::new();
            instantiations(def, &mut more);
            definitions.insert(name.clone(), def.clone());
            for n in more {
                referrers.entry(n.clone()).or_default().insert(name.clone());
                if !definitions.contains_key(&n) {
                    work.push(n);
                }
            }
        } else {
            unresolved.insert(name);
        }
    }
    if lib_cli.primitive_verbose && !lib_cli.lib_files.is_empty() {
        let indexed_from_v = lib_origins
            .values()
            .filter(|(_, from_v, _)| *from_v)
            .count();
        eprintln!(
            "[primitive-verbose] -v resolution summary: files={} indexed_definitions={} adopted={} unresolved={}",
            lib_cli.lib_files.len(),
            indexed_from_v,
            adopted_from_v,
            unresolved.len()
        );
        for name in &unresolved {
            eprintln!(
                "[primitive-verbose] unresolved definition '{}' after scanning explicit -v files",
                name
            );
        }
    }
    // Detailed context for names the libraries could not supply — printed here,
    // where the library scan is in scope, so the eventual "instantiated but not
    // found" elaboration error arrives with its cause already on the terminal.
    if !unresolved.is_empty() && (!lib.is_empty() || !lib_cli.lib_files.is_empty()) {
        // Print EVERY unresolved name — a truncated list once hid 2 of a
        // customer design's 10 missing vendor cells.
        for name in unresolved.iter() {
            let mut line = format!(
                "note: module '{}' not defined in the design and not found among {} definition(s) indexed from {} library file(s)",
                name,
                lib.len(),
                scanned_paths.len()
            );
            // WHO references it — so the user can judge whether the reference
            // is live (a real missing cell) or sits in a branch elaboration
            // never enters (in which case this note is advisory only; the
            // textual scan cannot evaluate generate/parameter conditions).
            if let Some(refs) = referrers.get(name) {
                let shown: Vec<String> = refs
                    .iter()
                    .take(4)
                    .map(|r| match lib_origins.get(r) {
                        Some((path, _, _)) => format!("'{}' ({})", r, path.display()),
                        None => format!("'{}'", r),
                    })
                    .collect();
                line.push_str(&format!(" — instantiated in: {}", shown.join(", ")));
                if refs.len() > 4 {
                    line.push_str(&format!(" and {} more", refs.len() - 4));
                }
                line.push_str(
                    "; if that reference sits in a generate/`ifdef branch that never elaborates, this note is advisory and no model is needed",
                );
            }
            // Case mismatch is a classic netlist/lib mismatch.
            if let Some(close) = lib
                .keys()
                .find(|k| k.eq_ignore_ascii_case(name) && k.as_str() != name.as_str())
            {
                line.push_str(&format!(
                    " — did you mean '{}'? (module names are case-sensitive)",
                    close
                ));
            }
            // Primitive-looking text without an indexed UDP usually means the
            // parser lost the declaration after an earlier syntax error.
            let prim_pat = format!("primitive {}", name);
            let prim_pat2 = format!("primitive  {}", name);
            if let Some(f) = scanned_paths.iter().find(|p| {
                std::fs::read_to_string(p)
                    .map(|s| s.contains(&prim_pat) || s.contains(&prim_pat2))
                    .unwrap_or(false)
            }) {
                line.push_str(&format!(
                    " — '{}' contains a UDP `primitive` with this name, but parsing did not recover its definition; rerun with --primitive-verbose",
                    f.display()
                ));
            }
            elab_diag(line);
        }
        for f in parse_issue_files.iter().take(3) {
            eprintln!(
                "note: '{}' had parse errors (see warnings above) — its definitions may be incomplete",
                f.display()
            );
        }
    }

    // §6.18: fill a forward typedef the primary design declared (`typedef
    // name;`) from a library file's real typedef — only those, never blanket.
    // A forward typedef in the design may be filled by a `-y` file that no
    // unresolved module ever pulled in. If any remain unfilled and unscanned
    // candidates exist, do the full scan now — old behavior, but only paid
    // when this actually matters.
    if !pending.is_empty()
        && definitions
            .values()
            .any(|d| matches!(d, SourceDefinition::Typedef(e) if e.forward))
    {
        for path in std::mem::take(&mut pending) {
            index_library_file(
                path,
                false,
                include_dirs,
                lib_defines,
                lib_cli,
                &mut lib,
                &mut lib_typedefs,
                &mut scanned_paths,
                &mut parse_issue_files,
                &mut lib_origins,
            );
        }
    }
    for t in lib_typedefs {
        let name = t.name.name.clone();
        let replace_forward = matches!(
            definitions.get(&name),
            Some(SourceDefinition::Typedef(e)) if e.forward);
        if replace_forward {
            definitions.insert(name, SourceDefinition::Typedef(t));
        }
    }
    Ok(())
}

/// Set the log file for simulation output. Placeholder.
pub fn log_println(s: &str) {
    println!("{}", s);
}
pub fn log_eprintln(s: &str) {
    eprintln!("{}", s);
}
