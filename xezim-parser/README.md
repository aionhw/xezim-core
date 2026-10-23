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
├── systemc/        — SystemC (C++) front end with its own AST — see below
│   ├── lexer.rs, token.rs, preprocess.rs  — C++ tokens and #include/#define/#if
│   ├── parser/     — declarations, statements, expressions
│   ├── ast.rs      — SystemC AST
│   └── classify.rs — ports/channels/sockets/processes of a module
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

## SystemC front end

`sv_parser::systemc` parses SystemC designs — the RTL subset and TLM-2.0
(IEEE 1666-2023) — into a separate SystemC AST. The input is C++: classes,
templates, operator overloads, lambdas and the usual statements, with the
SystemC macros (`SC_MODULE`, `SC_CTOR`, `SC_HAS_PROCESS`, `SC_METHOD` /
`SC_THREAD` / `SC_CTHREAD`, `sensitive`, `dont_initialize`,
`reset_signal_is`, `SC_NAMED`, `SC_FORK`/`SC_JOIN`, and the SystemC 3.0
`SC_*_IMP` / `SC_INIT` / `SC_NAMED_WITH_INIT`) recognized as syntax. The
SystemC/TLM library headers are not read (`#include <systemc>` is skipped);
a design's own headers are included and macro-expanded normally.

```rust
use sv_parser::systemc;

let r = systemc::parse_file("top.cpp", &["./include"], &[("NDEBUG", "1")]).unwrap();
for d in &r.errors {
    eprintln!("{}", r.render(d)); // file:line:col: error: … + source line + caret
}
for m in r.unit.modules() {
    println!("{}: {} ports, {} processes", m.name_str().unwrap_or("?"),
             m.ports().len(), r.unit.processes(m).len());
}
```

`sv-parse` sends files with a C++ extension (`.cpp`, `.cc`, `.cxx`, `.h`,
`.hpp`, `.hh`, …) through this front end; `--systemc` forces it for any file.
`--dump-ast` / `--dump-json` print the SystemC AST.

Not supported (diagnosed, never silently accepted): function-pointer and
pointer-to-member declarators, template template parameters, `goto`,
function-try-blocks. Names are not resolved: a `<` after an unknown name is a
template argument list only when it parses as one in a type position (or
before `(`/`::` in an expression), and library types are recognized by
spelling (see `parser/mod.rs` for the built-in name tables).

---

## Scope

This crate is deliberately parse-only. Everything downstream — elaboration, simulation, bytecode compilation, VCD / SDF handling — lives in the parent [xezim](../) crate, which consumes the AST produced here.

---

## License

MIT OR Apache-2.0 (see `../LICENSE`).
