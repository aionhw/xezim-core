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
- VHDL-2019 generic type classes (LRM 6.5.3, `type t is range <>`, `(<>)`,
  `private`, `array (...) of ...`, ...): `ast.rs`
  `InterfaceDeclaration::TypeClass`, `IncompleteTypeDefinition`;
  `syntax/interface_declaration.rs`.
- VHDL-2019 return statements (LRM 10.13): `return when c;` and
  `return a when c else b [else unaffected];`, the `condition` and
  `conditionals` fields of `ast.rs` `ReturnStatement`;
  `syntax/sequential_statement.rs`.
- VHDL-2019 sequential block statements: `ast.rs`
  `SequentialStatement::Block`, `syntax/sequential_statement.rs` (an error
  before VHDL-2019).
- Protected type declarations (LRM 5.6.2): the VHDL-2019 generic clause and
  map (`ProtectedTypeDeclaration::generic_clause`, `generic_map`) and
  `private variable` declarations, and the subprogram instantiations, use
  clauses, alias declarations and attribute specifications 2008 already
  allows (`ProtectedTypeDeclarativeItem::Other`, `Private`);
  `syntax/type_declaration.rs`.
- VHDL-2019 protected type instantiations (LRM 5.6.4), `type t is new
  generic_protected_type [generic map (...)]`: `ast.rs`
  `TypeDefinition::ProtectedInstance`, `syntax/type_declaration.rs` (an error
  before VHDL-2019).
- `syntax/names.rs` `parse_type_mark_starting_with_name`: the attributes
  that denote a subtype besides `'subtype` and `'element` are type marks too:
  `t'base` and VHDL-2019's `p'designated_subtype` and `a'index[(n)]`
  (`AttributeDesignator::Ident`, with the dimension as the expression).
- The matches over the new variants in `ast/display.rs`, `ast/search.rs`,
  `ast/util.rs`, `analysis/*.rs`, `lint/sensitivity_list.rs` and
  `formatting/*.rs` (the formatter writes the new forms as in the source;
  the analysis skips them: xezim uses the parser only).
- `syntax/xezim_tests.rs` (in `syntax.rs`): a test of each change above.
  Upstream tests adjusted to the changes: the expected-keyword lists of
  `syntax/declarative_part.rs` include `disconnect`; the two `vhdl_ls off`
  tests of `syntax/tokens/tokenizer.rs` are ignored. Run them with
  `cargo test --manifest-path vhdl-lang/vhdl_lang/Cargo.toml --lib`.
