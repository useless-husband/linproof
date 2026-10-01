# linproof

**A linearizability checker whose verdict comes with a machine-checked proof.**

Distributed databases are tested by recording what concurrent clients asked and what they were
told, then asking a *linearizability checker* whether some sequential order of the operations
explains every answer. Jepsen's Knossos and Porcupine do this job, and their verdicts are what
people trust when they report a consistency bug, or report none. linproof does the same job and
is written in Lean 4, with a proof, checked by Lean, that it answers "linearizable" exactly when
the history is linearizable according to a short definition you can read in one sitting. It
compiles to an ordinary 3 MB command-line program and checks real Jepsen histories in
milliseconds.

[繁體中文說明](README.zh-TW.md) · [Design](docs/DESIGN.md) · [Benchmark results](bench/results.md) · [導讀（給初學者）](docs/導讀.zh-TW.md)

```console
$ linproof check etcd_000.jsonl
etcd_000.jsonl: 85 operations (16 never returned), model cas-register
NOT LINEARIZABLE (0.14 ms, 282 configurations ruled out)

The longest partial linearization found places 38 of the 69 operations that returned.
Its last 8 steps (--verbose shows all 41):
  line 35 process 0: read -> 3 [66, 67]   => 3
  line 28 process 4: write 1 [53, -] (never returned; takes effect here)   => 1
  line 36 process 3: cas 3 -> 4: fail [69, 70]   => 1
  line 38 process 0: write 1 [73, 74]   => 1
  line 39 process 2: cas 0 -> 0: fail [75, 76]   => 1
  line 40 process 3: cas 2 -> 2: fail [77, 79]   => 1
  line 42 process 0: cas 4 -> 3: fail [81, 82]   => 1
  line 43 process 2: write 0 [83, 86]   => 0
Then the register holds 0, and no operation that real-time order allows next can follow:
  line 44 process 11: read -> 2 [84, 85]: it read 2, but the register holds 0
$ echo $?
1
```

`etcd_000` is one of the 102 Jepsen etcd histories that ship with Porcupine, converted with
`tools/jepsen2jsonl.py`. The verdict is proved; the explanation under it is diagnostics (see
[what is trusted](#what-is-proved-and-what-is-trusted)).

## What is proved, and what is trusted

The whole specification is [`Linproof/Spec.lean`](Linproof/Spec.lean). The part that defines
linearizability is this (comments trimmed):

```lean
structure Model (State Input Output : Type) where
  init : State
  step : State → Input → Output → Option State     -- deterministic sequential specification

structure Op (Input Output : Type) where
  call : Nat                        -- invocation time
  input : Input
  ret : Option (Nat × Output)       -- response time and output; none = never returned

def precedes (a b : Op Input Output) : Prop :=       -- a returned before b was invoked
  match a.ret with
  | some (t, _) => t < b.call
  | none => False

def WellFormed (h : List (Op Input Output)) : Prop :=
  ∀ op ∈ h, ∀ t o, op.ret = some (t, o) → op.call ≤ t

inductive Completion : List (Op Input Output) → List (Op Input Output × Output) → Prop
  | nil : Completion [] []
  | returned {op h c t o} : op.ret = some (t, o) → Completion h c →
      Completion (op :: h) ((op, o) :: c)                  -- kept with its observed output
  | tookEffect {op h c} (o : Output) : op.ret = none → Completion h c →
      Completion (op :: h) ((op, o) :: c)                  -- never returned, took effect
  | noEffect {op h c} : op.ret = none → Completion h c →
      Completion (op :: h) c                               -- never returned, no effect

def Legal (M : Model State Input Output) : State → List (Input × Output) → Prop
  | _, [] => True
  | s, (i, o) :: rest => ∃ s', M.step s i o = some s' ∧ Legal M s' rest

def Linearizable (M : Model State Input Output) (h : List (Op Input Output)) : Prop :=
  ∃ (c l : List (Op Input Output × Output)), Completion h c ∧ l.Perm c ∧
    l.Pairwise (fun a b => ¬ precedes b.1 a.1) ∧
    Legal M M.init (l.map fun p => (p.1.input, p.2))
```

This is Herlihy and Wing's definition: extend the history with responses for some operations
that never returned and drop the others (`Completion`), then find an order of what is left
(`Perm`) that keeps real-time order (`Pairwise`) and that the sequential specification accepts
(`Legal`). Process identifiers are not needed because each process's operations are already
ordered in real time. [docs/DESIGN.md](docs/DESIGN.md#the-definition) explains the
correspondence in detail, including how timestamps stand in for event positions. The same file
defines the three specifications the tool checks against: a read/write register, a
compare-and-set register, and a string key-value store (`Keyed String kvCell`, one independent
cell per key, with get/put/append as in Porcupine's key-value tests).

The main results, in [`Linproof/Theorems.lean`](Linproof/Theorems.lean) (instance arguments
omitted):

```lean
-- the generic checker, for any deterministic specification M
theorem checker_correct (M : Model σ ι ο) (P : PendingSteps M) (h : List (Op ι ο))
    (hwf : WellFormed h) : check M P h = true ↔ Linearizable M h

-- the fast memoised search computes the same function as the plain Wing–Gong–Lowe search
theorem memo_correct (M : Model σ ι ο) (P : PendingSteps M) (h : List (Op ι ο)) :
    check M P h = checkUnmemoised M P h

-- Herlihy and Wing's locality theorem for a store of independent keys
theorem keyed_locality (M : Model σ ι ο) (h : List (Op (K × ι) ο)) (hwf : WellFormed h) :
    Linearizable (Keyed K M) h ↔ ∀ k, Linearizable M (project k h)

-- what `linproof check --model kv` runs: keys checked one by one, decided exactly
theorem kvStore_correct (h : List (Op (String × KVInput) KVOutput)) (hwf : WellFormed h) :
    checkKeyed kvCell kvCellSteps h = true ↔ Linearizable kvStore h
```

plus the same statement for each register model, keyed and unkeyed, and
`isWellFormed h = true ↔ WellFormed h` for the check the tool runs first. There is no `sorry`,
`admit`, `native_decide` or added axiom, and no `partial` or `unsafe` definition anywhere in the
library; every function the theorems mention is total, with termination proved. CI runs
[`scripts/check-proofs.sh`](scripts/check-proofs.sh), which enforces this and prints the axioms
behind each theorem; they are Lean's three standard ones:

```console
$ lake env lean scripts/axioms.lean
'Linproof.Theorems.checker_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'Linproof.Theorems.memo_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'Linproof.Theorems.keyed_locality' depends on axioms: [propext, Classical.choice, Quot.sound]
'Linproof.Theorems.register_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'Linproof.Theorems.casRegister_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'Linproof.Theorems.keyedRegister_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'Linproof.Theorems.keyedCasRegister_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'Linproof.Theorems.kvStore_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'Linproof.Theorems.wellFormed_decided' depends on axioms: [propext, Quot.sound]
```

**Covered by the theorems:** the function that turns a list of operations into a verdict, i.e.
`isWellFormed`, `check`, `checkKeyed` and everything they call: the search, the memo, the event
lists, the hashing, the per-key grouping.

**Trusted, not proved:** reading the file (`Linproof/Json.lean`, `Linproof/History.lean`);
`Main.lean`, which calls the verified functions, combines per-key verdicts computed in parallel
(a `List.all` written with tasks) and prints; the explanation printed for violations
(`Linproof/Explain.lean`); the Lean kernel, compiler and runtime, including the runtime
implementations of `Array`, `Nat`, `Std.HashSet`, `Std.HashMap` and `withPtrEq`; and, if you use
it, the converter `tools/jepsen2jsonl.py`, which decides how Jepsen's `:fail` and `:info` are
read. These parts are covered by the tests below instead.

## Install and use

You need [elan](https://github.com/leanprover/elan); it installs the Lean version named in
`lean-toolchain` (4.34.1). There are no other dependencies.

```sh
git clone https://github.com/useless-husband/linproof && cd linproof
lake build                 # library, proofs and the linproof executable (about 15 s)
.lake/build/bin/linproof check --model cas-register history.jsonl
```

```
linproof check [--model M] [--verbose] [--quiet] [--jobs N] [--all-keys] [--timeout S]
               [--no-memo] FILE...

  --model        register | cas-register (default) | kv
  --verbose, -v  print the whole partial linearization of a violation, not its end
  --quiet, -q    one line per file: "FILE: linearizable", "not linearizable" or "unknown"
                 (no explanation, so no second search)
  --jobs N, -j N check up to N keys in parallel (default 4)
  --all-keys     check every key; by default a keyed history stops at the first violating key
  --timeout S    give up on a file after S seconds and report it as unknown
  --no-memo      the plain search (also verified; exponential, for testing)

exit status: 0 all linearizable, 1 some history not linearizable, 2 usage/input error,
             3 some history unknown (time limit reached, no violation found)
```

### History format

One JSON object per line; blank lines are ignored. `FILE` may be `-` for standard input.

```json
{"process": 0, "call": 0, "return": 5, "op": "write", "input": 1}
{"process": 1, "call": 2, "return": 7, "op": "read", "output": 1}
{"process": 2, "call": 3, "op": "cas", "input": [1, 2]}
{"process": 0, "call": 8, "return": 9, "op": "cas", "input": [1, 3], "output": false}
```

| field | meaning |
|---|---|
| `call` | invocation time, a non-negative integer (required) |
| `return` | response time; omit it or use `null` if the operation never returned (crashed, timed out): it may or may not have taken effect, and its `output` is ignored |
| `op`, `input`, `output` | the operation, below |
| `key` | optional string or integer: operations on different keys are independent objects, checked separately (an integer key is read as its decimal string, so `1` and `"1"` are the same key) |
| `process` | optional integer, only used in messages |

Two operations are ordered in real time only if one's `return` is strictly less than the
other's `call`; equal timestamps mean concurrent, as in Porcupine. This also applies to one
process's consecutive operations, so give distinct timestamps (event positions, as the
converter does) if a process's response and its next invocation could otherwise tie. Numbers
must be integers.

| model | `op` | `input` | `output` (when it returned) |
|---|---|---|---|
| `register`, `cas-register` | `read` | | the value read |
| | `write` | the value written | |
| `cas-register` | `cas` | `[expected, new]` | `true` (swapped) or `false` (did not match) |
| `kv` (needs `key`) | `get` | | the string read (`""` for a key never written) |
| | `put` | the string written | |
| | `append` | the string appended | |

Register values are `null` (the initial value), integers or strings.

Jepsen histories (`jepsen.util` log lines or EDN maps such as `history.edn`) convert with
`python3 tools/jepsen2jsonl.py history.edn > history.jsonl`. Event positions become
timestamps; `:info` and unfinished operations become operations that never returned; `:fail`
on `:cas` means the compare-and-set returned false (as in Jepsen's etcd test and Porcupine) and
on any other operation that it did not happen.

## How it works

The checker is the search of Wing and Gong as improved by Lowe: from a configuration (the
operations not yet placed, and the model state), place any *minimal* operation (no remaining
operation returned before it was invoked), apply it to the model, and continue; backtrack on
failure; succeed when every operation that returned is placed. Configurations from which the
search failed are remembered and never explored again. The executable version keeps the
remaining events sorted by time, so the candidates are the invocations before the first
pending response, hashes configurations incrementally, skips moves that cannot help (an
operation that never returned and leaves the state unchanged), and checks keys separately and in
parallel. Each of these is proved to give the same answer as the plain search, which is proved
to decide the definition; the proof for keys is Herlihy and Wing's locality theorem.
[docs/DESIGN.md](docs/DESIGN.md) describes the proof layers, the hard parts, and the
alternatives that were rejected.

## Evidence beyond the proofs

The proofs cover the checking function. These tests cover the rest: the parser, the glue, the
compiled code, and whether the definition says what a reader expects.

* **Differential testing against Porcupine** ([`test/porcupine`](test/porcupine), a Go module
  that fetches Porcupine v1.3.1). Random histories with fixed seeds: half are linearizable by
  construction (each operation gets a linearization point inside its interval and outputs come
  from running the specification in that order, including operations that crash and take
  effect or not), half have one operation corrupted. On 30,000 histories (10,000 per model,
  seeds 1–10000, 5,478 of them not linearizable) the two checkers agree on every verdict:
  `make diff DIFF_N=10000`. CI runs 2,000 per model.
* **Real histories.** The 102 Jepsen etcd histories and 6 key-value histories in Porcupine's test
  data, converted with `tools/jepsen2jsonl.py`: linproof, Porcupine on the converted files, and
  the verdicts recorded in Porcupine's own test suite agree on all 108 (`go test` in
  `test/porcupine`).
* **Lean runtime tests** ([`test/LinproofTests.lean`](test/LinproofTests.lean), 12,066 checks):
  hand-worked histories for every model (stale reads, touching intervals, operations that never
  returned, compare-and-set, duplicates, keys), JSON and history parser cases, and 6,000 random
  histories on which the fast search, the plain search and the explanation must agree.
* **Command-line tests** ([`test/cli-tests.sh`](test/cli-tests.sh), 60 checks): exit codes,
  messages with line numbers, standard input, several files, time limits, `--no-memo`
  agreement.

```sh
make test     # all of the above except the 30,000-history run (Go and Python 3 needed)
make proofs   # sorry/axiom checks and the axiom report
```

## Benchmarks

Apple M5 (10 cores), macOS 27, Lean 4.34.1, Go 1.27.1, on a machine shared with other jobs;
median of 5 runs. Porcupine's time is measured in-process around `porcupine.CheckOperations`;
linproof's *check* time is what the tool reports (after parsing); *process* is the wall time of
the whole `linproof` invocation, including process start and parsing. Both tools receive the
same files. Reproduce with `make bench`; full output in [bench/results.md](bench/results.md).

| histories | Porcupine | linproof check | linproof process |
|---|---:|---:|---:|
| 102 Jepsen etcd histories (total) | 306 ms | 117 ms | 561 ms |
| slowest of them, `etcd_002` (77 ops, 19 never returned) | 94 ms | 61 ms | 65 ms |
| 6 key-value histories from Porcupine's tests (total) | 35 ms | 82 ms | 146 ms |
| register, 100,000 ops | 731 ms | 172 ms | 360 ms |
| compare-and-set register, 100,000 ops, 1% never returned | 564 ms | 401 ms | 612 ms |
| compare-and-set register, 10,000 ops, one corrupted (a violation) | 77 ms | 78 ms | 207 ms |
| key-value store, 100,000 ops, 100 keys, 1% never returned | 37 ms | 114 ms | 381 ms |
| a violation among 10,000 ops with 1% never returned | > 30 s | > 30 s | > 30 s |

The search is exponential in the worst case (the problem is NP-complete), and the last row is
such a case for both tools. Porcupine is faster on many small keys, where it checks partitions
on every core and its per-history overhead is lower; linproof is faster on long single-object
histories and on the etcd histories with many timed-out operations. Which candidate order the
search tries first changes these numbers in both directions; the measurements behind the
current choice are in [docs/DESIGN.md](docs/DESIGN.md#operations-that-never-returned).

## Limitations

* **Deterministic specifications only.** `step` returns at most one next state. Sets or queues
  whose operations may return any of several values need a different definition.
* **Three built-in models.** A new model is a `Model` value plus a `PendingSteps` value whose
  laws must be proved (about 50 lines for the compare-and-set register), and a parser case.
* **The input path is trusted.** A parser bug could make the tool check a different history than
  the one in the file; the theorems say nothing about that. The same holds for the Lean compiler.
* **Worst-case exponential**, like every exact checker: histories with many concurrent
  operations that never returned, and a violation that only shows late, may not finish
  (see the benchmark table), and memory grows with every configuration ruled out (4.5 GB
  after 30 seconds on the last benchmark row). Use `--timeout`; the answer is then
  "unknown", never a guess.
* **The explanation repeats the search.** For a violation the tool searches a second time to
  explain it, so a violation that took long to find takes about twice as long to report;
  `--quiet` skips the explanation.
* **Key checks cannot be cancelled.** After the first violating key the tool prints and exits,
  which stops the other checks; with several files on one command line, checks left over from
  one file keep running while the next file is checked.
* **The explanation is not verified**, only tested against the verdict. Porcupine's interactive
  HTML visualization has no equivalent here.
* **Single-object histories are checked as one search**; there is no P-compositionality
  (Horn and Kroening) beyond splitting by key.

## Related work

To my knowledge, no other checker for register or key-value histories comes with a
machine-checked proof of its verdict. The closest projects:

* **[Knossos](https://github.com/jepsen-io/knossos)** (Clojure) and
  **[Porcupine](https://github.com/anishathalye/porcupine)** (Go) are the checkers used with
  Jepsen and in many test suites. They implement the same family of algorithms and are much more
  featureful (Knossos has several search strategies and a large model library; Porcupine has
  visualization and partitioned, parallel checking). They are not verified. linproof's real
  history data and its differential tests come from Porcupine.
* **[ahorn/linearizability-checker](https://github.com/ahorn/linearizability-checker)** (C++,
  Horn and Kroening, *Faster linearizability checking via P-compositionality*, FORTE 2015)
  introduced P-compositionality and produced the etcd histories used here. Not verified.
* **[grahnen/LinearizabilityTheory](https://github.com/grahnen/LinearizabilityTheory)** is a
  Lean 4 + Mathlib proof of the stack monitoring algorithm of Abdulla et al., *Efficient
  Linearizability Monitoring* (PLDI 2025), with the theorem
  `algorithm_correct : H.linearizable ↔ ∃ s, algorithm H = some s`. It covers the stack data
  type only, has no generic specification, register or key-value model, executable tool or
  history format, and was last updated in November 2025.
* **[Provenance-Works/Radix](https://github.com/Provenance-Works/Radix)** defines
  `Trace.isLinearizable` over memory events for its Lean model of atomics; it has no checker.
* Proof systems such as **[LHL](https://github.com/ehatti/LHL)** (Linearizability Hoare Logic,
  Rocq) prove that *implementations* are linearizable. linproof proves a *history checker*
  correct, which is what testing tools rely on.
* The definitions follow Herlihy and Wing, *Linearizability: A Correctness Condition for
  Concurrent Objects* (ACM TOPLAS, 1990), and the search follows Wing and Gong, *Testing and
  verifying concurrent objects* (JPDC, 1993) with Lowe's memoisation, *Testing for
  linearizability* (CCPE, 2017).

## Development

```sh
make build           # lake build
make proofs          # forbidden-keyword scan, build, axiom report
make test            # Lean, CLI, converter and Porcupine tests
make diff DIFF_N=N   # N random histories per model against Porcupine
make bench           # benchmark against Porcupine (writes bench/results.md)
```

Layout: `Linproof/Spec.lean` (the trusted definitions), `Search.lean` (plain search),
`Memo.lean` (fast search), `Bridge.lean` (search ↔ definition), `Checker.lean`,
`Models.lean`, `Keyed.lean`, `Locality.lean`, `Theorems.lean`, `Explain.lean`, `Json.lean`,
`History.lean`; `Main.lean` (the tool); `test/`, `tools/`, `bench/`, `scripts/`.

## License

[MIT](LICENSE)
