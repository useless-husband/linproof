# Changelog

## 0.1.0 (unreleased)

First version.

### Proved (Lean 4.34.1, core and Std only)

- `Spec.lean`: histories with operations that may never return, real-time order,
  completions, legality, linearizability; register, compare-and-set register and string
  key-value store specifications.
- `check_iff`: the checker is sound and complete for every deterministic specification, on
  well-formed histories.
- `fsearch_eq` / `check_eq_checkUnmemoised`: the fast search (sorted event lists, memo of
  failed configurations, Zobrist hashing, pending operations kept apart) computes the same
  function as the plain Wing–Gong–Lowe search.
- `exists_kept_move`, `ext_drop`: moves that apply a timed-out operation without changing the
  state are never needed, and neither are timed-out read-only operations.
- `locality`: Herlihy and Wing's locality theorem for a store of independent keys;
  `checkKeyed_iff` for the per-key checker, `groupByKey_getD` for the one-pass grouping.
- Only `propext`, `Classical.choice` and `Quot.sound` are used; no `sorry`, `native_decide`,
  `partial` or `unsafe` in the library.

### Tool

- `linproof check` for the `register`, `cas-register` and `kv` models, with keys, several
  files, standard input, explanations of violations, parallel key checks (`--jobs`) with early
  exit (`--all-keys` to disable), a time limit (`--timeout`, exit status 3), and the plain
  search (`--no-memo`).
- JSON-lines history format; `tools/jepsen2jsonl.py` converts Jepsen logs and EDN histories.

### Evidence

- Differential testing against Porcupine v1.3.1 on seeded random histories (30,000 run
  locally, 6,000 in CI) and on the 108 histories in Porcupine's test data.
- Lean runtime tests, command-line tests, converter tests; benchmarks in `bench/results.md`.
