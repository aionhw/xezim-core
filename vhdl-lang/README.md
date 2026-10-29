# vhdl_lang (vendored)

The VHDL parser of xezim-core's VHDL front end (`src/vhdl/cst/`): the crates
`vhdl_lang` 0.88.0 and `vhdl_lang_macros` 0.88.0 of the rust_hdl project
(<https://github.com/VHDL-LS/rust_hdl>, the VHDL-LS language server), copied
from crates.io. Only the parser (`VHDLParser`, the `ast` module) is used; the
analysis, completion and formatting parts are compiled but not called.

`vhdl_libraries/` holds the four library sources upstream's unit tests read
(`src/analysis/tests/util.rs`), from the rust_hdl repository at tag v0.88.0:
`std/*.vhd` are rust_hdl's (MPL-2.0); `ieee2008/std_logic_1164.vhdl` is the
IEEE P1076 source (Apache-2.0, as in `../src/vhdl/libraries/LICENSE`). They
are only used by `cargo test --manifest-path vhdl-lang/vhdl_lang/Cargo.toml`.

License: Mozilla Public License 2.0 (`LICENSE`), as published upstream. The
files here stay under the MPL-2.0; changes are marked with a comment starting
`xezim:` and listed below, so they can be offered upstream.

## Changes from 0.88.0

- `vhdl_lang/Cargo.toml`: `vhdl_lang_macros` taken from `../vhdl_lang_macros`;
  the benchmark and integration-test targets (not vendored) removed.
- `vhdl_lang/Cargo.toml`: `enum-map` 2.7.3 instead of 3.1.0, which needs rustc
  1.95 (xezim-core's MSRV is 1.92); the crate uses only `enum_map!`, `Enum` and
  `EnumMap`, which are the same in both.
- `syntax/type_declaration.rs`: `range implementation_defined` (as the IEEE
  P1076 sources of STD.STANDARD write INTEGER, REAL and TIME) is accepted and
  carried as the range attribute `implementation_defined'range`.
- `ast.rs`, `syntax/object_declaration.rs`: the signal kind of a guarded
  signal (`register`, `bus`), `ObjectDeclaration::signal_kind` (LRM 6.4.2.3).
- `ast.rs`, `syntax/declarative_part.rs`: disconnection specifications,
  `Declaration::Disconnection` (LRM 7.4); the matches over `Declaration` in
  `ast/search.rs`, `analysis/declarative.rs`, `analysis/names.rs` and
  `formatting/declaration.rs` gained the variant.
- `syntax/concurrent_statement.rs`: guarded concurrent signal assignments
  (`s <= guarded v`, LRM 11.6) and postponed signal assignments (upstream left
  both as TODOs).
- `syntax/type_declaration.rs`: `pure function` declarations in protected
  types.
- `syntax/design_unit.rs`: a token that cannot start a design unit is
  reported and skipped to the next design unit; it used to discard the whole
  file.
- `syntax/interface_declaration.rs`: error recovery in an interface list stops
  at `end` (a missing `)`), instead of consuming the rest of the file.
- `syntax/tokens/tokenizer.rs`: the `-- vhdl_ls off` comment pragma (the
  language server's way of leaving code out) is not honoured: a simulator
  analyses every line.
- `syntax/xezim_tests.rs` (in `syntax.rs`): a test of each change above.
  Upstream tests adjusted to the changes: the expected-keyword lists of
  `syntax/declarative_part.rs` include `disconnect`; the two `vhdl_ls off`
  tests of `syntax/tokens/tokenizer.rs` are ignored. Run them with
  `cargo test --manifest-path vhdl-lang/vhdl_lang/Cargo.toml --lib`.
