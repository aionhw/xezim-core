# xezim-parser

SystemVerilog parser — the front-end of [xezim](../).

Performs lexing, preprocessing, and parsing of SystemVerilog source (IEEE 1800-2017/2023) into a typed AST. No simulation or elaboration — just parsing.

---

## Project Layout

```
src/
├── lexer/          — tokenizer (scanner, keywords, literals)
├── preprocessor/   — `include, `define, `ifdef, ... directive expansion
├── parse/          — recursive-descent parser over the token stream
│   ├── declarations.rs
│   ├── expressions.rs
│   ├── items.rs
│   ├── statements.rs
│   └── types.rs
├── ast/            — pure-data AST types (one file per IEEE 1800 chapter)
│   ├── decl.rs     — declarations (§A.2)
│   ├── expr.rs     — expressions (§A.8)
│   ├── stmt.rs     — statements (§A.6)
│   ├── module.rs   — module / program / interface shells
│   └── types.rs    — data types, nets, packed/unpacked dimensions
├── serde/          — optional serialization support (see below)
├── diagnostics/    — diagnostics & error reporting
├── lib.rs          — crate root, public API
├── main.rs         — `sv-parse` binary (smoke-test runner)
└── tests.rs
```

---

## Quick start

```rust
use sv_parser::parse;

let result = parse("module top; endmodule");
assert!(result.errors.is_empty());
assert_eq!(result.source.descriptions.len(), 1);
```

Parse a file with preprocessor settings:

```rust
use sv_parser::parse_file;

let result = parse_file(
    "design.sv",
    &["./includes"],            // -I include dirs
    &[("SYNTHESIS", "1")],      // -D defines
);
```

---

## Cargo features

| Feature | Default | Effect |
|---|---|---|
| `serde` | ✅ on | Enables `Serialize` / `Deserialize` on every AST type via gated `cfg_attr(feature="serde", ...)` derives. Code lives in `src/serde/`. |

Disable serde to build the AST as pure data with no serialization trait impls:

```bash
cargo build --no-default-features
```

---

## Build & test

```bash
cargo build            # debug
cargo build --release
cargo test
cargo build --no-default-features   # without serde
```

The `sv-parse` binary does a quick parse-only smoke test of a file:

```bash
cargo run --bin sv-parse -- path/to/source.sv
```

---

## Scope

This crate is deliberately parse-only. Everything downstream — elaboration, simulation, bytecode compilation, VCD / SDF handling — lives in the parent [xezim](../) crate, which consumes the AST produced here.

---

## License

MIT OR Apache-2.0 (see `../LICENSE`).
