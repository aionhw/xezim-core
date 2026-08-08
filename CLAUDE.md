@AGENTS.md

## Claude Code

- Use plan mode for significant or multi-file changes.
- After a change, run `cargo test` here, then the focused test group in the
  sibling `xezim` repo (`cargo test --test <group> <name>` from `../xezim`).
- If a sim result looks wrong, reproduce it with a minimal SV case in `../xezim`
  before editing this repo.
- Re-verify determinism (`+seed=1` twice, diff the output) for RNG/hash/solver
  changes.
- When behavior is ambiguous, treat the existing test suite as the source of
  truth.
