import Linproof.Memo
import Linproof.Bridge

/-!
# The checker and its correctness theorem

`check M P h` runs the memoised search on the history `h`. `check_iff` states that, on a
well-formed history, it returns `true` exactly when `h` is linearizable with respect to `M`:
the "if" direction is completeness (no linearizable history is rejected), the "only if"
direction is soundness (no violation is missed).

The proof chains the three layers:

* `Search.msearch_eq`: the memoised search computes the same function as `Search.search`;
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

/-- The search without memoisation. Exponential on hard histories; kept as the reference
implementation and for tests. -/
def checkUnmemoised (h : List (Op ι ο)) : Bool :=
  Search.search M P h.toArray (List.finRange h.toArray.size) M.init

theorem checkUnmemoised_iff (h : List (Op ι ο)) (hwf : WellFormed h) :
    checkUnmemoised M P h = true ↔ Linearizable M h := by
  have hwf' : Search.WF h.toArray := (Bridge.wf_iff h.toArray).2 (by simpa using hwf)
  rw [checkUnmemoised, Search.search_iff M P h.toArray hwf' _ _ _ rfl (List.nodup_finRange _),
    Bridge.ext_iff_linearizable, List.toList_toArray]

variable [DecidableEq σ] [Hashable σ]

/-- **The checker.** -/
def check (h : List (Op ι ο)) : Bool :=
  (Search.msearch M P h.toArray (List.finRange h.toArray.size) M.init ∅).1

/-- The memoised checker computes the same function as the unmemoised one. -/
theorem check_eq_checkUnmemoised (h : List (Op ι ο)) : check M P h = checkUnmemoised M P h :=
  (Search.msearch_eq M P h.toArray _ _ _ _ rfl (Search.memoOK_empty M P h.toArray)).1

/-- The checker's verdict together with the number of configurations it ruled out (the size
of the memo), for reporting. The verdict is `check` by definition. -/
def checkWithStats (h : List (Op ι ο)) : Bool × Nat :=
  let r := Search.msearch M P h.toArray (List.finRange h.toArray.size) M.init ∅
  (r.1, r.2.size)

theorem checkWithStats_fst (h : List (Op ι ο)) : (checkWithStats M P h).1 = check M P h := rfl

/-- **Soundness and completeness.** On a well-formed history, the checker answers `true`
exactly when the history is linearizable. -/
theorem check_iff (h : List (Op ι ο)) (hwf : WellFormed h) :
    check M P h = true ↔ Linearizable M h := by
  rw [check_eq_checkUnmemoised]
  exact checkUnmemoised_iff M P h hwf

end Linproof
