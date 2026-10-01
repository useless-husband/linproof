import Linproof.Search

/-!
# Pending steps of the concrete models

For each specification in `Spec.lean`, the states an operation that never returned can lead
to, with a proof that this list is exactly the set of states reachable with *some* output.
These proofs are what lets `check_iff` apply to the concrete models.
-/

namespace Linproof

/-- Pending steps of the compare-and-set register. -/
def casRegisterSteps (init : Val) : PendingSteps (casRegister init) where
  next s i :=
    match i with
    | .read => [s]
    | .write v => [v]
    | .cas e n => if s = e then [n] else [s]
  next_iff := by
    intro s i s'
    cases i with
    | read =>
      simp only [List.mem_singleton, casRegister]
      constructor
      · intro h; exact ⟨.value s, by simp [h]⟩
      · rintro ⟨o, ho⟩
        cases o <;> simp at ho
        exact ho.2.symm
    | write v =>
      simp only [List.mem_singleton, casRegister]
      constructor
      · intro h; exact ⟨.ok, by simp [h]⟩
      · rintro ⟨o, ho⟩
        cases o <;> simp at ho
        exact ho.symm
    | cas e n =>
      show s' ∈ (if s = e then [n] else [s]) ↔ _
      by_cases hse : s = e
      · simp only [hse, ↓reduceIte, List.mem_singleton]
        constructor
        · intro h; exact ⟨.ok, by simp [casRegister, h]⟩
        · rintro ⟨o, ho⟩
          cases o <;> simp [casRegister] at ho
          exact ho.symm
      · simp only [hse, ↓reduceIte, List.mem_singleton]
        constructor
        · intro h; exact ⟨.fail, by simp [casRegister, hse, h]⟩
        · rintro ⟨o, ho⟩
          cases o <;> simp [casRegister, hse] at ho
          exact ho.symm

/-- Pending steps of the read/write register. A `cas` is not an operation of this object,
so it can never take effect. -/
def registerSteps (init : Val) : PendingSteps (register init) where
  next s i :=
    match i with
    | .read => [s]
    | .write v => [v]
    | .cas _ _ => []
  next_iff := by
    intro s i s'
    cases i with
    | read =>
      simp only [List.mem_singleton, register]
      constructor
      · intro h; exact ⟨.value s, by simp [h]⟩
      · rintro ⟨o, ho⟩
        cases o <;> simp at ho
        exact ho.2.symm
    | write v =>
      simp only [List.mem_singleton, register]
      constructor
      · intro h; exact ⟨.ok, by simp [h]⟩
      · rintro ⟨o, ho⟩
        cases o <;> simp at ho
        exact ho.symm
    | cas e n =>
      simp only [List.not_mem_nil, false_iff, not_exists, register]
      intro o
      cases o <;> simp

/-- Pending steps of one key of the string key-value store. -/
def kvCellSteps : PendingSteps kvCell where
  next s i :=
    match i with
    | .get => [s]
    | .put v => [v]
    | .append v => [s ++ v]
  next_iff := by
    intro s i s'
    cases i with
    | get =>
      simp only [List.mem_singleton, kvCell]
      constructor
      · intro h; exact ⟨.value s, by simp [h]⟩
      · rintro ⟨o, ho⟩
        cases o <;> simp at ho
        exact ho.2.symm
    | put v =>
      simp only [List.mem_singleton, kvCell]
      constructor
      · intro h; exact ⟨.ok, by simp [h]⟩
      · rintro ⟨o, ho⟩
        cases o <;> simp at ho
        exact ho.symm
    | append v =>
      simp only [List.mem_singleton, kvCell]
      constructor
      · intro h; exact ⟨.ok, by simp [h]⟩
      · rintro ⟨o, ho⟩
        cases o <;> simp at ho
        exact ho.symm

end Linproof
