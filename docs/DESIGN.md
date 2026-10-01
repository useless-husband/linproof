# Design

This document explains how linproof is built: what is proved, how the proofs are layered,
the problems that took the most work, and the alternatives that were rejected.

## Architecture

```
              trusted                         proved                        not proved, not trusted
 ┌──────────────────────────┐   ┌────────────────────────────────────┐   ┌──────────────────────┐
 │ Spec.lean                │   │ Search.lean   plain search, Ext    │   │ Explain.lean         │
 │  Model, Op, precedes,    │◀──│ Memo.lean     fast search = plain  │   │  why a history is    │
 │  WellFormed, Completion, │   │ Bridge.lean   Ext = Linearizable   │   │  not linearizable    │
 │  Legal, Linearizable,    │   │ Checker.lean  check_iff            │   └──────────────────────┘
 │  Keyed, the 3 models     │   │ Models.lean   pending-step laws    │
 └──────────────────────────┘   │ Keyed.lean    one pass per key     │
 ┌──────────────────────────┐   │ Locality.lean locality,            │
 │ Json.lean, History.lean  │   │               checkKeyed_iff       │
 │ Main.lean (I/O, glue)    │──▶│ Theorems.lean headline statements  │
 │ Lean compiler + runtime  │   └────────────────────────────────────┘
 └──────────────────────────┘
```

`Main.lean` parses a file into a `List (Op ι ο)` (or a keyed one), decides well-formedness with
the verified `isWellFormed`, and calls `check` or `checkKeyed`. The verdict printed is the
`Bool` those functions return. Everything that computes that `Bool` is covered by
`check_iff` / `checkKeyed_iff`; the parser that produced the input and the printing are not.

## The definition

`Spec.lean` is short on purpose. A history is a list of operations with an invocation time, an
input and an optional response (time and output). `Linearizable M h` holds when there are lists
`c` and `l` such that

1. `Completion h c`: `c` keeps every operation that returned, with its observed output, and
   keeps any subset of the operations that never returned, with any output;
2. `l.Perm c`: `l` is an order on exactly those operations;
3. `l.Pairwise (fun a b => ¬ precedes b.1 a.1)`: no operation comes after one it precedes in
   real time (`precedes a b` means `a` returned strictly before `b` was invoked);
4. `Legal M M.init (...)`: the model accepts the sequence from its initial state.

This is Herlihy and Wing's definition (ACM TOPLAS, 1990) restated for a single object.
Their history `H` is extended to `H'` by appending responses to some pending invocations
(clause 1, `tookEffect` with the chosen output), `complete(H')` drops the other pending
invocations (clause 1, `noEffect`), `complete(H')` must be equivalent to a legal sequential
history `S` (clauses 2 and 4) and `<_H ⊆ <_S` (clause 3). Equivalence in Herlihy and Wing
compares per-process subsequences; since each process is sequential, its operations are
ordered by `<_H`, so clause 3 already forces the same per-process order and process
identifiers can be left out of the definition (they are kept in the file format for messages).
Timestamps replace the position of events in `H`: a history given as an event sequence becomes
timestamps by numbering the events (`tools/jepsen2jsonl.py` does this), and ties, which an event
sequence cannot have, are read as concurrency, the same choice Porcupine makes.

A sequential specification is a deterministic state machine
`step : State → Input → Output → Option State`. Nondeterministic objects (a set whose `remove`
may return any element) are out of scope; the three models shipped (register,
compare-and-set register, key-value store) are deterministic.

## Proof layers

The main theorem is assembled from four results, each about one function or one relation.

**`Search.search_iff`** (plain search decides `Ext`). A *configuration* is a list `rem` of
operation indices not yet placed and a model state `s`. `Ext rem s` says the configuration can be
finished: there is a list `R` of distinct indices from `rem`, each with an output, covering every
operation of `rem` that returned, respecting real-time order and accepted by the model from `s`.
The one-step lemma `ext_iff` says `Ext rem s` holds iff nothing that returned remains, or some
*minimal* operation `x` (no operation still in `rem` returned before `x` was invoked) can move the
model to a state `s'` with `Ext (rem.erase x) s'`. `search` is that recursion, so `search_iff`
follows by strong induction on `rem.length`. The minimal operations are computed through the
earliest pending response (`minimal_iff`).

**`Search.fsearch_eq`** (fast search = plain search). See below; this is where most of the
engineering went.

**`Bridge.ext_iff_linearizable`** (`Ext` at the start = the definition). One direction maps
indices to operations. The other has to recover indices from a completion of a history that may
contain identical operations: `completion_indices` reconstructs which positions the completion
kept, and `perm_map_lift` transports the order of the linearization back to those positions.

**`Locality.locality`** (keys are independent). See below.

## The fast search and its proof

The plain search is correct but slow: every step rescans all remaining operations, so a
50,000-operation history took 49.6 seconds. The executable search `fsearch` keeps more structure
and is proved to return the same `Bool` as `search` on every input (`fsearch_eq`); nothing about
the fast path is trusted.

* **Events.** The invocations and responses of the remaining operations that returned are kept
  in a list sorted by time, invocations first at equal times. The candidates are the
  invocations before the first response, and that response's time is the earliest pending
  response. `scan_minRet` and `scan_cands` prove this from an invariant (`EvInv`: the list is
  sorted, has no duplicates and contains exactly the events of the remaining operations), and
  `evInv_remove` proves that removing one operation's two events preserves it.
* **Memoisation.** Configurations from which the search failed are stored in a `Std.HashSet`.
  The invariant `MemoOK` says every stored configuration is one where the plain search returns
  `false`; successes need no memo because the first one ends the search. The memo key contains
  the whole configuration (remaining operations and state), so the proof needs nothing about the
  hash function except that equal keys hash equally.
* **Incremental hashing.** The hash of a configuration is the XOR of a fixed SplitMix64 value per
  placed operation (Zobrist hashing), updated in constant time. It appears in the key only as a
  hint and plays no part in the proofs.
* **Shared tails.** Comparing two keys compares their lists of remaining operations. Two
  configurations reached in different orders share their tails in memory, because
  `List.erase` keeps the tail after the erased element. `listEqS` compares with core Lean's
  `withPtrEq`, which is logically plain equality (`withPtrEq a b k h` is defined as `k ()`) and
  is implemented by a pointer check, so a memo hit costs as much as the part of the lists that
  differs. Without this, memo hits were the quadratic bottleneck.

With these the 50,000-operation history takes about 50 ms.

## Operations that never returned

Operations whose client crashed or timed out (`:info` in Jepsen) are the classic difficulty for
linearizability checkers, because such an operation may take effect at any later time or never.
Three proved reductions handle them:

1. **Moves that change nothing are skipped** (`keep`, `exists_kept_move`). Placing an operation
   that never returned without changing the state can always be left out of a linearization,
   so the search never tries it. The proof is an induction on the witness: removing such a step
   from a witness leaves a witness. On the 102 Jepsen etcd histories this cut the total time from
   646 ms to 141 ms (single runs during development).
2. **Read-only operations that never returned are dropped at the start** (`ext_drop`). A model
   may declare inputs read-only (`PendingSteps.readOnly`, with a law); a pending read can never
   be needed.
3. **Pending operations live outside the event list** (`FInv`). Skipped operations would
   otherwise stay at the front of the event list forever and be rescanned at every step. The
   configuration is split into operations that returned (`remR`, with the event list) and those
   that did not (`remP`). Erasing from `remR ++ remP` splits exactly
   (`List.erase_append_left/right`), so `fsearch_eq` still relates the split configuration to the
   plain search by list equality.

**Candidate order** does not affect the answer, only how soon it is found, and the proofs only
use which candidates exist. Two orders were measured during development (milliseconds of
`check` time, single runs on the shared machine; `bench/results.md` has medians for the
current version):

| order                      | 102 etcd histories | kv, 100k ops, 100 keys, 1% crashes | cas, 100k ops, 1% crashes |
|----------------------------|-------------------:|-----------------------------------:|--------------------------:|
| returned operations first  | 38                 | 443                                | 320                       |
| pending operations first   | 114                | 83                                 | 381                       |
| Porcupine (for reference)  | 297                | 24                                 | 549                       |

Returned-first explores 1.25 million configurations on the key-value history, where reads often
observe an append whose client crashed. Pending-first stays within a small factor of Porcupine
everywhere and is the default.

## Locality

`Locality.lean` proves Herlihy and Wing's locality theorem for `Keyed K M`, a store whose keys
hold independent objects: a well-formed history is linearizable iff each key's sub-history is.

* *Only if*: restrict the linearization to one key. Filtering keeps real-time order, and
  `legal_keyed` shows the model of the store accepts a sequence iff each key's model accepts its
  restriction.
* *If*: the per-key linearizations have to be merged into one sequence that respects real-time
  order across keys. Each operation of a per-key linearization gets a *point*, the latest
  invocation time among it and the operations before it (`annotate`). Points never decrease along
  a linearization and lie inside the operation's interval: `call ≤ point` by construction, and
  `point ≤ return` because the linearization respects real-time order and the history is well
  formed (`annotate_ret`). Sorting all operations by point with `List.mergeSort`, which is stable
  (`List.sublist_mergeSort`), keeps each key's order, and an operation that returned before
  another was invoked has a strictly smaller point, so it comes first. Completions are lifted
  from the keys to the whole history by `completion_lift`.

The executable groups the history by key in one pass (`groupByKey`, a `Std.HashMap` fold) and
`groupByKey_getD` proves each group is the projection. `checkKeyed_iff` combines this with
`check_iff` and locality. The command-line tool runs the per-key `check` calls in parallel tasks
(at most `--jobs` at a time) and stops at the first key that is not linearizable, which already
decides the verdict; Porcupine does the same.

## Termination and totality

Every definition under `Linproof/` that a theorem mentions is total: the searches use
well-founded recursion on the number of remaining events (plus pending operations), with the
decrease proved in `decreasing_by`. `scripts/check-proofs.sh` rejects `sorry`, `admit`,
`native_decide`, `axiom`, `partial`, `unsafe`, `implemented_by` and `extern` anywhere in the
library and fails unless the main theorems depend only on `propext`, `Classical.choice` and
`Quot.sound`. The JSON parser is also total (fuel bounded by the input length) even though it is
trusted rather than proved.

## Trusted computing base

* `Spec.lean`: the definitions and the three models.
* `Json.lean`, `History.lean`: turning text into operations. Covered by tests
  (`test/LinproofTests.lean`, `test/cli-tests.sh`), not by proofs.
* `Main.lean`: argument handling, the parallel combination of per-key verdicts (a `List.all`
  written with tasks), the time limit (a timer task raced against the check; when it wins the
  answer is "unknown"), printing.
* The Lean kernel (for the proofs) and the Lean compiler and runtime (for the executable),
  including core and Std code with runtime implementations: `Array`, `Nat`, `String`,
  `Std.HashSet`/`HashMap`, `withPtrEq`.
* `tools/jepsen2jsonl.py` if you use it: it decides how Jepsen's `:fail` and `:info` are read.

## Alternatives rejected

* **Mathlib.** It would have supplied `Finset` and order lemmas, but a fresh build or cache
  download is gigabytes. Core Lean 4.34 has enough list theory (`Perm`, `Pairwise`, `Sublist`,
  `mergeSort` stability, `min?`); the few missing lemmas are proved locally.
* **`Lean.Json`.** Importing it links the compiler's libraries into the executable: 104 MB
  instead of 3 MB. A 200-line total parser is easier to audit than to trust a large dependency
  for a trusted component anyway.
* **Bitset memo keys** (as in Porcupine). A bitset needs bit-level lemmas to relate it to the
  remaining operations and costs `n/64` words per key; the list of remaining operations is
  already part of the configuration, and with shared tails its comparison is cheap.
* **Fuel instead of well-founded recursion.** Structural recursion on a fuel argument is easier
  to unfold in proofs but needs a separate argument that the fuel suffices; `termination_by`
  with explicit decrease proofs keeps the functions honest.
* **Verifying the explanation.** The explanation (longest partial linearization and why the next
  operations fail) is diagnostics. Proving it would add little: the verdict is proved, and the
  explanation is checked against the verdict on 6,000 random histories.
* **Parsing Jepsen's EDN in Lean.** EDN is a richer format than the tool needs and its
  semantics (`:fail` on a compare-and-set) are a modelling choice; it lives in a small converter
  script where that choice is visible.
