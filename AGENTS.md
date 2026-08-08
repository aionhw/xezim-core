# xezim-core — Development Guide for AI Coding Agents

This file is read by coding agents (Claude Code, OpenAI Codex, Cursor, Copilot) at
the start of every session. It is **operational**: what to build, how to build it,
what must never break. It covers only this repository — the sibling `xezim` repo
(bytecode interpreter + simulator) is where behavior is validated; read its
`AGENTS.md` before editing code that this library feeds. If a fact here conflicts
with the code, the code (and the test suite) is the source of truth; fix this file.

## What this is

`xezim-core` is the **shared SystemVerilog library** consumed by two binaries:
`xezim` (bytecode interpreter/simulator) and `xezim-b` (ahead-of-time native
compiler). It owns parsing, elaboration, the 4-state value model, the compiled-
artifact format, and small runtime sinks (stdout, VCD).

Two crates in one repo:

- **`xezim-core`** (this crate, `src/`, lib name `xezim_core`) — elaboration,
  values, artifact serialization, deterministic hasher, SDF, VCD/stdout sinks.
- **`sv-parser`** (subcrate at `xezim-parser/`, lib name `sv_parser`, bin
  `sv-parse`) — lexer, preprocessor, parser, strict-checks. Parse-only; no
  simulation or elaboration.

`xezim` depends on this repo via `path = "../xezim-core"` (clone both repos into
the same parent). It is **not** a submodule. The simulators run **elaborated**
designs, so most wrong-result bugs live in `xezim`'s VM — a change here only helps
when the symptom is parse/elaboration/formatting.

## Repository map

```
src/lib.rs                lib name xezim_core; hasher module (deterministic HashMap/
                          HashSet), XEZIM_BYTECODE_MAGIC + artifact (de)serialization,
                          mimalloc global allocator, parse+elaborate orchestration, re-exports
src/elaborate.rs          Elaborator: AST → flat simulation model. The repo's largest file.
                          Resolves decls, continuous assigns, always blocks, classes, params,
                          port binding; produces ElaboratedModule
src/value.rs              4-state Value (0/1/X/Z), width + signedness; ≤64-bit inline u64,
                          wider → Vec<LogicBit>; BitsRef/BitsIter views
src/packed_value.rs       Packed storage for wide signals (2 bits/bit, 4× less memory) —
                          the perf workhorse; not yet wired into Value everywhere
src/bits2.rs              2-state arbitrary-width value (Verilator-style, no X/Z mask);
                          the compute-core type for the cycle-based path
src/sdf/                  SDF parser + annotator (IEEE 1497-2001): IOPATH/INTERCONNECT delays
src/vcd_sink.rs           VCD waveform dump
src/stdout_sink.rs        Locked stdout/stderr sink — feeds xezim's `-l` fd-level redirect
xezim-parser/src/lexer/   Tokenizer (scanner.rs, token.rs)
xezim-parser/src/preprocessor/  `include/`defines/`ifdef handling
xezim-parser/src/parse/   Recursive-descent parser → AST (declarations, expressions, items,
                          statements, types, helpers)
xezim-parser/src/ast/     Typed AST (decl, expr, module, stmt, types)
xezim-parser/src/diagnostics/  Diagnostic type + rendering
xezim-parser/src/strict_check.rs  Additive negative-case lint (gated by --strict)
```

## Build & test

Toolchain: Rust **1.92** MSRV (`rust-version` in `Cargo.toml`), edition 2024.
CI (`test.yml`) runs `cargo test`; `msrv.yml` runs `cargo msrv verify`.

```bash
cargo build                          # debug
cargo build --release                # optimized (lto=true, codegen-units=1)
cargo test                           # unit tests in src/ + xezim-parser/src/tests.rs
cargo test -p sv-parser              # just the parser subcrate
cargo run -p sv-parser -- --check design.sv    # sv-parse CLI: parse-only, report errors
cargo run -p sv-parser -- --dump-ast design.sv  # dump the AST (Rust Debug format)
cargo run -p sv-parser -- --dump-json design.sv # one JSON object per file
```

Tests live next to code (`#[cfg(test)] mod tests` in `src/value.rs`,
`src/packed_value.rs`, `src/sdf/mod.rs`, `src/stdout_sink.rs`, `src/bits2.rs`,
`xezim-parser/src/tests.rs`). Because behavior is only observable through the
`xezim` simulator, most parser/elaborator work is validated from the `xezim`
suite (`cargo test --test <group> <name>` there) even when the fix lands here.

## Architecture

Pipeline: source → preprocessor → parse/AST (`sv-parser`) → elaboration
(`elaborate.rs`) → `ElaboratedModule` → (in `xezim`) bytecode compile → execute.
Key types: `Value`/`LogicBit` (4-state), `Bits2` (2-state), `ElaboratedModule`,
`Signal`, `ElaboratedClass`, `ElabInstance`.

| Symptom | Owner |
|---|---|
| Parse/preprocessor errors, AST shape | `xezim-parser` (lexer, preprocessor, parse/, ast/) |
| Type/width/signedness, parameters, classes, port binding, legality | `src/elaborate.rs` |
| Value arithmetic/representation, `$bits`, X/Z propagation | `src/value.rs`, `src/bits2.rs` |
| `$display`/formatting output | `src/stdout_sink.rs` |
| SDF annotation | `src/sdf/` |
| VCD dumping | `src/vcd_sink.rs` |

`src/lib.rs` re-exports the surface `xezim` relies on:
`pub use sv_parser::{self, parse, lexer, preprocessor, diagnostics, ParseResult, ast};`
and `pub use value::Value;` / `pub use elaborate::{elaborate_module, ElaboratedModule};`.
Keep that surface stable — `xezim` and `xezim-b` both depend on it.

## Critical invariants — do not break these

- **Determinism is a hard requirement.** The `hasher` module
  (`crate::hasher::{HashMap, HashSet}`, fixed ahash seeds in
  `DeterministicState`) exists so iteration order is reproducible run-to-run.
  **Never** use `std::collections::HashMap/HashSet` where iteration order can
  affect observable behavior — `elaborate.rs` deliberately uses
  `crate::hasher::HashMap` everywhere a traversal could leak into output.
- **Global allocator**: mimalloc is installed here (`mimalloc-allocator` default
  feature) because Rust permits exactly ONE `#[global_allocator]` per binary and
  this is the shared lib — declaring it here covers xezim, xezim-b, and every
  test binary. **Never add another `#[global_allocator]`.** A consumer opting
  out uses `xezim-core = { path = "../xezim-core", default-features = false }`.
- **Artifact format versioning**: `XEZIM_BYTECODE_MAGIC = b"XEZIMBC\x0c"`
  (`src/lib.rs`). The last byte is the serialized-format version. When you add
  or change a serialized field in `ElaboratedModule` (or any bincode-serialized
  type), **bump `\x0c` to `\x0d`** and add one line to the version-ladder
  comment above it, so stale `.xez` artifacts fail with a clear "recompile with
  current xezim" error instead of deserializing garbage.
- **Artifacts are zstd-compressed bincode.** Default level 3 (overridable via
  `set_zstd_level`). The magic/version check runs before decompression.
- **Logging routing**: output goes through `log_println`/`log_eprintln`
  (`src/lib.rs`) so the caller's `-l` fd-level redirect works — it captures
  DPI/VPI C output too. Bare `println!`/`eprintln!` bypasses `--log`.
- **Wide-value storage**: `Value` keeps ≤64-bit values inline (a `u64` value/mask
  pair, no heap); wider values fall back to `Vec<LogicBit>`. `packed_value.rs`
  is the memory-lean wide representation (2 bits/bit, 4× smaller) being rolled
  in for perf — when extending it, keep the 4-state semantics identical to
  `Value`.
- **`sv-parser` stays parse-only.** No simulation, no elaboration, no value
  model. Prefer a precise error/diagnostic over silently accepting garbage; the
  parser is deliberately permissive on legal-but-rare LRM forms, and
  `strict_check.rs` adds a separate second pass for negative cases (must be
  precise — a false positive rejects a valid design).

## Coding conventions

snake_case; Rust 2024 edition; MSRV 1.92 (`rust-version` in `Cargo.toml`);
clippy-clean. Modules carry `//!` doc comments. Hard fixes get explanatory
comments with **LRM § citations** (e.g. `§6.6.7`) and regression tests
referencing the same section. User-facing errors are `Result<_, String>` /
diagnostic strings; do not panic on user input. Prefer the smallest correct
change and match the surrounding style.

## Workflows

**Fix a parse/elaboration bug**
1. Reproduce in the `xezim` repo: write the minimal `.sv`, confirm the wrong
   behavior (`./target/release/xezim repro.sv --no-cache`).
2. Add a failing regression test in `xezim`'s suite (`tests/<group>/<name>.rs`
   + group-root mod line) so the fix is pinned there too.
3. Fix it here in `src/elaborate.rs` or `xezim-parser`; keep it localized.
4. `cargo test` here, then run the focused test in `xezim`
   (`cargo test --test <group> <name>`), then `cargo test --no-fail-fast` and
   `cargo test --features jit --no-fail-fast` there (exactly what xezim's CI
   runs).
5. Re-verify determinism (`+seed=1` twice, diff output) for anything touching
   hash/RNG order.

**Add a language feature**: parse it in `xezim-parser` → elaborate/type it in
`elaborate.rs` → (in `xezim`) execute it in `simulator.rs` → add a test there
citing the LRM § → document any new flag/env knob in the `xezim` README.

## Before you open a PR

- Regression test added (here for unit-level, in the `xezim` repo for anything
  observable through the simulator) **with an LRM § citation** in its doc
  comment.
- `cargo test` green here; the corresponding `xezim` suite green
  (`cargo test --no-fail-fast` **and** `cargo test --features jit --no-fail-fast`).
- Serialized-format fields changed? Bump `XEZIM_BYTECODE_MAGIC`'s version byte
  and the version-ladder comment.
- Determinism preserved; no `std` hash/RNG order leaks.
- Minimal diff: no unrelated refactors, no dead code added.
- If this guide becomes wrong (paths, commands, conventions), fix it in the same PR.

## Resources

- `../xezim/AGENTS.md` — the interpreter/simulator repo this library feeds
- `../xezim/docs/dev/*` — architecture, debugging, testing, gotchas
- `xezim-parser/` crate docs (`cargo doc -p sv-parser`) — lexer/parser/AST
