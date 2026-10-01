import Linproof.Checker

/-!
# Keyed histories: checking each key on its own

`Keyed K M` (in `Spec.lean`) is a store whose keys hold independent objects specified by
`M`. A history of it is linearizable exactly when, for every key, the operations on that
key form a linearizable history of `M` (`Locality.lean`). The executable relies on this to
check keys one at a time, which is what makes large key-value histories tractable: the
search space of the whole history is roughly the product of the per-key search spaces.
-/

namespace Linproof

variable {σ ι ο : Type} {K : Type} [DecidableEq K]

/-- The operation with its key removed. -/
def Op.unkey (op : Op (K × ι) ο) : Op ι ο := { call := op.call, input := op.input.2, ret := op.ret }

/-- The operations on key `k`, as a history of the per-key object. -/
def project (k : K) (h : List (Op (K × ι) ο)) : List (Op ι ο) :=
  (h.filter fun op => op.input.1 = k).map Op.unkey

/-- The keys that occur in a history, each once, in order of first occurrence. -/
def keysOf (h : List (Op (K × ι) ο)) : List K :=
  (h.map fun op => op.input.1).eraseDups

theorem mem_keysOf {h : List (Op (K × ι) ο)} {k : K} :
    k ∈ keysOf h ↔ ∃ op ∈ h, op.input.1 = k := by
  simp [keysOf, List.mem_eraseDups]

variable (M : Model σ ι ο) (P : PendingSteps M) [DecidableEq σ] [Hashable σ]

/-- For each key that occurs in the history: the verdict on its operations and the number of
configurations ruled out. -/
def checkKeyedResults (h : List (Op (K × ι) ο)) : List (K × Bool × Nat) :=
  (keysOf h).map fun k => (k, checkWithStats M P (project k h))

/-- **The keyed checker**: every key's history is linearizable. -/
def checkKeyed (h : List (Op (K × ι) ο)) : Bool :=
  (checkKeyedResults M P h).all (·.2.1)

end Linproof
