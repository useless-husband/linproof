import Linproof.Spec

/-!
# The Wing–Gong–Lowe search, without memoisation

The checker explores *configurations* `(rem, s)`: `rem` lists the operations that have not
been linearized yet and `s` is the model state reached by the ones that have. From a
configuration it may linearize any operation `x` of `rem` that is *minimal* — no operation
still in `rem` returned before `x` was invoked — provided the model accepts it from `s`.
It succeeds once every remaining operation is one that never returned (those may be
dropped).

`Ext rem s` says that the remaining operations can be finished from `s`. The main result of
this file, `search_iff`, is that the executable `search` decides `Ext`. `Bridge.lean` then
shows that `Ext` at the start configuration is exactly `Linearizable`.

Operations are referred to by their position in an array `ops`, so `rem` is a list of
indices; `rem` never contains duplicates.
-/

namespace Linproof

variable {σ ι ο : Type}

/-- The checker needs, besides the model, the states that an operation which never returned
may lead to: all `s'` such that *some* output is legal. -/
structure PendingSteps (M : Model σ ι ο) where
  next : σ → ι → List σ
  next_iff : ∀ s i s', s' ∈ next s i ↔ ∃ o, M.step s i o = some s'

namespace Search

variable (M : Model σ ι ο) (P : PendingSteps M) (ops : Array (Op ι ο))

/-- The operation at index `i`. (A named accessor keeps `simp` from rewriting the index.) -/
def op (i : Fin ops.size) : Op ι ο := ops[i]

/-- Response times are no earlier than invocation times. -/
def WF : Prop := ∀ (i : Fin ops.size) t o, (op ops i).ret = some (t, o) → (op ops i).call ≤ t

/-- The model states reached by linearizing operation `x` in state `s`. -/
def succs (s : σ) (x : Fin ops.size) : List σ :=
  match (op ops x).ret with
  | some (_, o) => (M.step s (op ops x).input o).toList
  | none => P.next s (op ops x).input

/-- The earliest response time among the operations of `rem` that returned. -/
def minRet (rem : List (Fin ops.size)) : Option Nat :=
  (rem.filterMap fun j => (op ops j).ret.map Prod.fst).min?

/-- Candidate moves: minimal operations (invoked no later than `m`, the earliest pending
response) paired with each state they can lead to. -/
def cands (rem : List (Fin ops.size)) (s : σ) (m : Nat) : List (Fin ops.size × σ) :=
  (rem.filter fun x => decide ((op ops x).call ≤ m)).flatMap
    fun x => (succs M P ops s x).map (x, ·)

theorem mem_cands {rem : List (Fin ops.size)} {s : σ} {m : Nat} {x : Fin ops.size} {s' : σ} :
    (x, s') ∈ cands M P ops rem s m ↔ x ∈ rem ∧ (op ops x).call ≤ m ∧ s' ∈ succs M P ops s x := by
  simp only [cands, List.mem_flatMap, List.mem_filter, List.mem_map, decide_eq_true_eq,
    Prod.mk.injEq]
  constructor
  · rintro ⟨y, ⟨hy, hc⟩, s'', hs, rfl, rfl⟩
    exact ⟨hy, hc, hs⟩
  · rintro ⟨hy, hc, hs⟩
    exact ⟨x, ⟨hy, hc⟩, s', hs, rfl, rfl⟩

theorem length_erase_lt {α : Type} [DecidableEq α] {l : List α} {a : α} (h : a ∈ l) :
    (l.erase a).length < l.length := by
  rw [List.length_erase_of_mem h]
  have := List.length_pos_of_mem h
  omega

/-- The unmemoised search. -/
def search (rem : List (Fin ops.size)) (s : σ) : Bool :=
  match minRet ops rem with
  | none => true
  | some m => (cands M P ops rem s m).attach.any fun c => search (rem.erase c.1.1) c.1.2
termination_by rem.length
decreasing_by
  exact length_erase_lt ((mem_cands M P ops).1 c.2).1

/-- The remaining operations `rem` can be finished from state `s`: there is a sequence `R`
of distinct operations of `rem`, each with an output, that contains every operation of `rem`
that returned (with its observed output), respects real-time order and is accepted by the
model from `s`. -/
def Ext (rem : List (Fin ops.size)) (s : σ) : Prop :=
  ∃ R : List (Fin ops.size × ο),
    (R.map Prod.fst).Nodup ∧
    (∀ p ∈ R, p.1 ∈ rem) ∧
    (∀ i ∈ rem, ∀ t o, (op ops i).ret = some (t, o) → i ∈ R.map Prod.fst) ∧
    (∀ p ∈ R, ∀ t o, (op ops p.1).ret = some (t, o) → p.2 = o) ∧
    R.Pairwise (fun a b => ¬ precedes (op ops b.1) (op ops a.1)) ∧
    Legal M s (R.map fun p => ((op ops p.1).input, p.2))

/-! ### Facts about `minRet` -/

theorem minRet_eq_none {rem : List (Fin ops.size)} :
    minRet ops rem = none ↔ ∀ i ∈ rem, (op ops i).ret = none := by
  simp only [minRet, List.min?_eq_none_iff, List.filterMap_eq_nil_iff, Option.map_eq_none_iff]

theorem minRet_eq_some {rem : List (Fin ops.size)} {m : Nat} (h : minRet ops rem = some m) :
    (∃ i ∈ rem, ∃ o, (op ops i).ret = some (m, o)) ∧
    (∀ i ∈ rem, ∀ t o, (op ops i).ret = some (t, o) → m ≤ t) := by
  rw [minRet, List.min?_eq_some_iff] at h
  obtain ⟨hmem, hle⟩ := h
  refine ⟨?_, ?_⟩
  · obtain ⟨i, hi, he⟩ := List.mem_filterMap.1 hmem
    rcases hr : (op ops i).ret with _ | ⟨t, o⟩
    · simp [hr] at he
    · simp [hr] at he
      exact ⟨i, hi, o, by rw [hr, he]⟩
  · intro i hi t o hr
    apply hle
    exact List.mem_filterMap.2 ⟨i, hi, by simp [hr]⟩

/-- With `m` the earliest response among `rem`, an operation is minimal exactly when it was
invoked no later than `m`. -/
theorem minimal_iff {rem : List (Fin ops.size)} {m : Nat} (h : minRet ops rem = some m)
    (x : Fin ops.size) :
    (∀ j ∈ rem, ¬ precedes (op ops j) (op ops x)) ↔ (op ops x).call ≤ m := by
  obtain ⟨⟨i, hi, o, hio⟩, hle⟩ := minRet_eq_some ops h
  constructor
  · intro hmin
    have := hmin i hi
    simp only [precedes, hio] at this
    omega
  · intro hc j hj hp
    unfold precedes at hp
    rcases hr : (op ops j).ret with _ | ⟨t, o'⟩
    · simp [hr] at hp
    · simp only [hr] at hp
      have := hle j hj t o' hr
      omega

/-! ### The one-step characterisation of `Ext` -/

theorem succs_iff {s s' : σ} {x : Fin ops.size} :
    s' ∈ succs M P ops s x ↔
      ∃ o, (∀ t o', (op ops x).ret = some (t, o') → o = o') ∧ M.step s (op ops x).input o = some s' := by
  unfold succs
  rcases hr : (op ops x).ret with _ | ⟨t, o⟩
  · simp only [P.next_iff]
    constructor
    · rintro ⟨o, ho⟩; exact ⟨o, by simp, ho⟩
    · rintro ⟨o, -, ho⟩; exact ⟨o, ho⟩
  · simp only [Option.mem_toList, Option.some.injEq, Prod.mk.injEq]
    constructor
    · intro h; exact ⟨o, by rintro _ _ ⟨-, rfl⟩; rfl, h⟩
    · rintro ⟨o', ho', h⟩
      rw [ho' t o ⟨rfl, rfl⟩] at h
      exact h

theorem ext_of_done {rem : List (Fin ops.size)} {s : σ} (h : ∀ i ∈ rem, (op ops i).ret = none) :
    Ext M ops rem s := by
  refine ⟨[], by simp, by simp, ?_, by simp, by simp, by simp [Legal]⟩
  intro i hi t o hr
  simp [h i hi] at hr

theorem ext_cons {rem : List (Fin ops.size)} {s s' : σ} {x : Fin ops.size}
    (hnd : rem.Nodup) (hx : x ∈ rem) (hmin : ∀ j ∈ rem, ¬ precedes (op ops j) (op ops x))
    (hs : s' ∈ succs M P ops s x) (hext : Ext M ops (rem.erase x) s') : Ext M ops rem s := by
  obtain ⟨o, ho, hstep⟩ := (succs_iff M P ops).1 hs
  obtain ⟨R, hnd', hsub, hcov, hout, hpw, hleg⟩ := hext
  have hxR : x ∉ R.map Prod.fst := by
    intro hm
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
    exact List.Nodup.not_mem_erase hnd (hsub p hp)
  refine ⟨(x, o) :: R, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (x :: R.map Prod.fst).Nodup
    exact List.nodup_cons.2 ⟨hxR, hnd'⟩
  · intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact hx
    · exact List.mem_of_mem_erase (hsub p hp)
  · intro i hi t o' hr
    by_cases hix : i = x
    · subst hix; simp
    · have := hcov i ((List.mem_erase_of_ne hix).2 hi) t o' hr
      simp [this]
  · intro p hp t o' hr
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ho t o' hr
    · exact hout p hp t o' hr
  · refine List.Pairwise.cons ?_ hpw
    intro p hp
    exact hmin p.1 (List.mem_of_mem_erase (hsub p hp))
  · exact ⟨s', hstep, hleg⟩

theorem ext_iff (hwf : WF ops) {rem : List (Fin ops.size)} {s : σ} (hnd : rem.Nodup) :
    Ext M ops rem s ↔ (∀ i ∈ rem, (op ops i).ret = none) ∨
      ∃ x ∈ rem, (∀ j ∈ rem, ¬ precedes (op ops j) (op ops x)) ∧
        ∃ s' ∈ succs M P ops s x, Ext M ops (rem.erase x) s' := by
  constructor
  · rintro ⟨R, hnd', hsub, hcov, hout, hpw, hleg⟩
    cases R with
    | nil =>
      left
      intro i hi
      rcases hr : (op ops i).ret with _ | ⟨t, o⟩
      · rfl
      · simpa using hcov i hi t o hr
    | cons p R =>
      obtain ⟨x, o⟩ := p
      right
      have hx : x ∈ rem := hsub (x, o) (by simp)
      simp only [List.map_cons, List.nodup_cons] at hnd'
      obtain ⟨hxR, hnd'⟩ := hnd'
      obtain ⟨s', hstep, hleg⟩ := hleg
      rw [List.pairwise_cons] at hpw
      refine ⟨x, hx, ?_, s', ?_, R, hnd', ?_, ?_, ?_, hpw.2, hleg⟩
      · -- `x` is minimal: a predecessor in `rem` returned, so it is in `R`, hence after `x`.
        intro j hj hp
        rcases hr : (op ops j).ret with _ | ⟨t, o'⟩
        · simp [precedes, hr] at hp
        · have hjR := hcov j hj t o' hr
          rcases List.mem_cons.1 hjR with hjx | hjR
          · subst hjx
            have := hwf j t o' hr
            simp only [precedes, hr] at hp
            omega
          · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hjR
            exact hpw.1 q hq hp
      · exact (succs_iff M P ops).2 ⟨o, hout (x, o) (by simp), hstep⟩
      · intro q hq
        have hq1 : q.1 ≠ x := fun h => hxR (h ▸ List.mem_map_of_mem hq)
        exact (List.mem_erase_of_ne hq1).2 (hsub q (List.mem_cons_of_mem _ hq))
      · intro i hi t o' hr
        have hix : i ≠ x := fun h => List.Nodup.not_mem_erase hnd (h ▸ hi)
        rcases List.mem_cons.1 (hcov i (List.mem_of_mem_erase hi) t o' hr) with h | h
        · exact absurd h hix
        · exact h
      · intro q hq t o' hr
        exact hout q (List.mem_cons_of_mem _ hq) t o' hr
  · rintro (hdone | ⟨x, hx, hmin, s', hs, hext⟩)
    · exact ext_of_done M ops hdone
    · exact ext_cons M P ops hnd hx hmin hs hext

/-- `Ext` depends only on which operations remain, not on their order in `rem`. -/
theorem ext_congr {rem rem' : List (Fin ops.size)} {s : σ} (h : ∀ i, i ∈ rem ↔ i ∈ rem') :
    Ext M ops rem s ↔ Ext M ops rem' s := by
  unfold Ext
  simp only [h]

/-! ### Correctness of the search -/

theorem search_eq (rem : List (Fin ops.size)) (s : σ) :
    search M P ops rem s = match minRet ops rem with
      | none => true
      | some m => (cands M P ops rem s m).attach.any
          fun c => search M P ops (rem.erase c.1.1) c.1.2 := by
  rw [search]

theorem search_iff (hwf : WF ops) :
    ∀ (n : Nat) (rem : List (Fin ops.size)) (s : σ), rem.length = n → rem.Nodup →
      (search M P ops rem s = true ↔ Ext M ops rem s) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro rem s hlen hnd
    rw [search_eq, ext_iff M P ops hwf hnd]
    rcases hm : minRet ops rem with _ | m
    · simp only [true_iff]
      exact Or.inl ((minRet_eq_none ops).1 hm)
    · simp only [List.any_eq_true, List.mem_attach, true_and]
      have hnot : ¬ ∀ i ∈ rem, (op ops i).ret = none := by
        intro h
        rw [(minRet_eq_none ops).2 h] at hm
        cases hm
      simp only [hnot, false_or]
      constructor
      · rintro ⟨⟨⟨x, s'⟩, hc⟩, hrec⟩
        obtain ⟨hx, hcall, hs⟩ := (mem_cands M P ops).1 hc
        have hlt : (rem.erase x).length < n := hlen ▸ length_erase_lt hx
        refine ⟨x, hx, (minimal_iff ops hm x).2 hcall, s', hs, ?_⟩
        exact (ih _ hlt (rem.erase x) s' rfl (hnd.erase x)).1 hrec
      · rintro ⟨x, hx, hmin, s', hs, hext⟩
        have hc : (x, s') ∈ cands M P ops rem s m :=
          (mem_cands M P ops).2 ⟨hx, (minimal_iff ops hm x).1 hmin, hs⟩
        have hlt : (rem.erase x).length < n := hlen ▸ length_erase_lt hx
        exact ⟨⟨(x, s'), hc⟩, (ih _ hlt (rem.erase x) s' rfl (hnd.erase x)).2 hext⟩

end Search

end Linproof
