import Linproof.Locality
import Linproof.Models

/-!
# The main results, in one place

These are the statements the README quotes and CI prints the axioms of. Each is a corollary
of the general theorems (`check_iff`, `checkKeyed_iff`, `Locality.locality`) instantiated
with the specifications of `Spec.lean`, which are exactly the functions the command-line
tool runs.
-/

namespace Linproof.Theorems

/-- The generic checker is sound and complete for every deterministic specification. -/
theorem checker_correct {σ ι ο : Type} [DecidableEq σ] [Hashable σ]
    (M : Model σ ι ο) (P : PendingSteps M) (h : List (Op ι ο)) (hwf : WellFormed h) :
    check M P h = true ↔ Linearizable M h :=
  check_iff M P h hwf

/-- The memoised checker computes the same function as the plain search. -/
theorem memo_correct {σ ι ο : Type} [DecidableEq σ] [Hashable σ]
    (M : Model σ ι ο) (P : PendingSteps M) (h : List (Op ι ο)) :
    check M P h = checkUnmemoised M P h :=
  check_eq_checkUnmemoised M P h

/-- Locality: a keyed history is linearizable iff each key's history is. -/
theorem keyed_locality {σ ι ο K : Type} [DecidableEq K] (M : Model σ ι ο)
    (h : List (Op (K × ι) ο)) (hwf : WellFormed h) :
    Linearizable (Keyed K M) h ↔ ∀ k, Linearizable M (project k h) :=
  Locality.locality M h hwf

/-- `linproof check --model register`, on a history without keys. -/
theorem register_correct (h : List (Op RegInput RegOutput)) (hwf : WellFormed h) :
    check (register .null) (registerSteps .null) h = true ↔ Linearizable (register .null) h :=
  check_iff _ _ h hwf

/-- `linproof check --model cas-register`, on a history without keys. -/
theorem casRegister_correct (h : List (Op RegInput RegOutput)) (hwf : WellFormed h) :
    check (casRegister .null) (casRegisterSteps .null) h = true ↔
      Linearizable (casRegister .null) h :=
  check_iff _ _ h hwf

/-- `linproof check --model cas-register`, on a history whose operations carry keys
(independent registers, as in Jepsen's `independent` tests). -/
theorem keyedCasRegister_correct (h : List (Op (String × RegInput) RegOutput))
    (hwf : WellFormed h) :
    checkKeyed (casRegister .null) (casRegisterSteps .null) h = true ↔
      Linearizable (Keyed String (casRegister .null)) h :=
  checkKeyed_iff _ _ h hwf

/-- `linproof check --model register`, on a history whose operations carry keys. -/
theorem keyedRegister_correct (h : List (Op (String × RegInput) RegOutput))
    (hwf : WellFormed h) :
    checkKeyed (register .null) (registerSteps .null) h = true ↔
      Linearizable (Keyed String (register .null)) h :=
  checkKeyed_iff _ _ h hwf

/-- `linproof check --model kv`: the string key-value store, checked key by key. -/
theorem kvStore_correct (h : List (Op (String × KVInput) KVOutput)) (hwf : WellFormed h) :
    checkKeyed kvCell kvCellSteps h = true ↔ Linearizable kvStore h :=
  checkKeyed_iff _ _ h hwf

/-- Well-formedness, which the tool checks before running the checker, is decided exactly. -/
theorem wellFormed_decided {ι ο : Type} (h : List (Op ι ο)) :
    isWellFormed h = true ↔ WellFormed h :=
  isWellFormed_iff h

end Linproof.Theorems
