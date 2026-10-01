import Linproof.Memo
import Linproof.Bridge

/-!
# The checker and its correctness theorem

`check M P h` runs the fast memoised search (`Memo.lean`) on the history `h`. `check_iff` states that, on a
well-formed history, it returns `true` exactly when `h` is linearizable with respect to `M`:
the "if" direction is completeness (no linearizable history is rejected), the "only if"
direction is soundness (no violation is missed).

The proof chains the three layers:

* `Search.fsearch_eq`: the fast memoised search computes the same function as
  `Search.search`;
* `Search.search_iff`: `Search.search` decides `Search.Ext`;
* `Bridge.ext_iff_linearizable`: `Search.Ext` at the start configuration is `Linearizable`.
-/

namespace Linproof

variable {σ ι ο : Type}

/-- Decide whether a history is well formed (no response before its invocation). -/
def isWellFormed (h : List (Op ι ο)) : Bool :=
  h.all fun op =>
    match op.ret with
    | some (t, _) => decide (op.call ≤ t)
    | none => true

theorem isWellFormed_iff (h : List (Op ι ο)) : isWellFormed h = true ↔ WellFormed h := by
  simp only [isWellFormed, List.all_eq_true, WellFormed]
  constructor
  · intro H op hop t o hr
    have := H op hop
    simp only [hr, decide_eq_true_eq] at this
    exact this
  · intro H op hop
    rcases hr : op.ret with _ | ⟨t, o⟩
    · rfl
    · simpa using H op hop t o hr

variable (M : Model σ ι ο) (P : PendingSteps M)

/-- The operations, ordered by invocation time. The order does not matter for correctness
(`Search.ext_congr`); it makes removing a linearized operation cheap, since candidates are
always among the earliest invocations. -/
def startRem (ops : Array (Op ι ο)) : List (Fin ops.size) :=
  (List.finRange ops.size).mergeSort fun a b => decide ((Search.op ops a).call ≤ (Search.op ops b).call)

theorem startRem_nodup (ops : Array (Op ι ο)) : (startRem ops).Nodup :=
  (List.mergeSort_perm _ _).symm.nodup (List.nodup_finRange _)

theorem mem_startRem (ops : Array (Op ι ο)) (i : Fin ops.size) : i ∈ startRem ops := by
  simp [startRem, List.mem_mergeSort]

/-- The search without memoisation. Exponential on hard histories, and quadratic even on
easy ones; kept as the reference the fast search is proved equal to. -/
def checkUnmemoised (h : List (Op ι ο)) : Bool :=
  Search.search M P h.toArray (startRem h.toArray) M.init

theorem checkUnmemoised_iff (h : List (Op ι ο)) (hwf : WellFormed h) :
    checkUnmemoised M P h = true ↔ Linearizable M h := by
  have hwf' : Search.WF h.toArray := (Bridge.wf_iff h.toArray).2 (by simpa using hwf)
  rw [checkUnmemoised, Search.search_iff M P h.toArray hwf' _ _ _ rfl (startRem_nodup _),
    Search.ext_congr M h.toArray (rem' := List.finRange h.toArray.size)
      (fun i => by simp [mem_startRem]),
    Bridge.ext_iff_linearizable, List.toList_toArray]

variable [DecidableEq σ] [Hashable σ]

/-- Run the fast search on a history; returns the verdict and the final memo. -/
def runSearch (h : List (Op ι ο)) : Bool × Search.Memo h.toArray (σ := σ) :=
  let rem := startRem h.toArray
  Search.fsearch M P h.toArray rem (Search.events h.toArray rem) 0 M.init ∅

/-- **The checker.** -/
def check (h : List (Op ι ο)) : Bool :=
  (runSearch M P h).1

/-- The fast memoised checker computes the same function as the plain search. -/
theorem check_eq_checkUnmemoised (h : List (Op ι ο)) : check M P h = checkUnmemoised M P h :=
  (Search.fsearch_eq M P h.toArray _ _ _ _ _ _ rfl
    (Search.evInv_events h.toArray (startRem_nodup _)) (Search.memoOK_empty M P h.toArray)).1

/-- The checker's verdict together with the number of configurations it ruled out (the size
of the memo), for reporting. The verdict is `check` by definition. -/
def checkWithStats (h : List (Op ι ο)) : Bool × Nat :=
  let r := runSearch M P h
  (r.1, r.2.size)

theorem checkWithStats_fst (h : List (Op ι ο)) : (checkWithStats M P h).1 = check M P h := rfl

/-- **Soundness and completeness.** On a well-formed history, the checker answers `true`
exactly when the history is linearizable. -/
theorem check_iff (h : List (Op ι ο)) (hwf : WellFormed h) :
    check M P h = true ↔ Linearizable M h := by
  rw [check_eq_checkUnmemoised]
  exact checkUnmemoised_iff M P h hwf

end Linproof
