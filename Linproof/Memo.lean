import Linproof.Search
import Std.Data.HashSet

/-!
# Memoisation

The executable search remembers every configuration `(rem, s)` from which it has already
failed, in a hash set, and gives up immediately when it meets one again. Configurations that
succeed never need to be remembered: the first success ends the whole search.

`msearch_eq` proves that the memoised search returns the same answer as `search`, as long as
every remembered configuration really is a failure of `search` (`MemoOK`), and that it keeps
the memo in that state. The proof is an induction on the number of remaining operations;
nothing depends on how the hash set is implemented beyond the `Std.HashSet` lemma
`contains_insert`.
-/

namespace Linproof

namespace Search

variable {σ ι ο : Type} (M : Model σ ι ο) (P : PendingSteps M) (ops : Array (Op ι ο))

/-- Run `f` over the list, threading a state, and stop at the first `true`. -/
def anyThread {α τ : Type} : List α → τ → (α → τ → Bool × τ) → Bool × τ
  | [], t, _ => (false, t)
  | a :: as, t, f =>
    match f a t with
    | (true, t') => (true, t')
    | (false, t') => anyThread as t' f

theorem anyThread_spec {α τ : Type} (g : α → Bool) (I : τ → Prop) (f : α → τ → Bool × τ) :
    ∀ (l : List α), (∀ a ∈ l, ∀ t, I t → (f a t).1 = g a ∧ I (f a t).2) →
      ∀ t, I t → (anyThread l t f).1 = l.any g ∧ I (anyThread l t f).2 := by
  intro l
  induction l with
  | nil => intro _ t ht; exact ⟨rfl, ht⟩
  | cons a as ih =>
    intro hf t ht
    obtain ⟨h1, h2⟩ := hf a (by simp) t ht
    unfold anyThread
    rcases hfa : f a t with ⟨b, t'⟩
    rw [hfa] at h1 h2
    cases b with
    | true => exact ⟨by simp [List.any_cons, ← h1], h2⟩
    | false =>
      obtain ⟨ih1, ih2⟩ := ih (fun a' ha' => hf a' (List.mem_cons_of_mem _ ha')) t' h2
      exact ⟨by simp [List.any_cons, ← h1, ih1], ih2⟩

variable [DecidableEq σ] [Hashable σ]

/-- The set of configurations known to fail. -/
abbrev Memo := Std.HashSet (List (Fin ops.size) × σ)

/-- The memoised search. It returns the verdict and the enlarged memo. -/
def msearch (rem : List (Fin ops.size)) (s : σ) (V : Memo ops (σ := σ)) :
    Bool × Memo ops (σ := σ) :=
  if V.contains (rem, s) then (false, V)
  else
    match minRet ops rem with
    | none => (true, V)
    | some m =>
      match anyThread (cands M P ops rem s m).attach V
          (fun c V => msearch (rem.erase c.1.1) c.1.2 V) with
      | (true, V') => (true, V')
      | (false, V') => (false, V'.insert (rem, s))
termination_by rem.length
decreasing_by exact length_erase_lt ((mem_cands M P ops).1 c.2).1

/-- Every configuration in the memo is one from which `search` fails. -/
def MemoOK (V : Memo ops (σ := σ)) : Prop :=
  ∀ rem s, V.contains (rem, s) = true → search M P ops rem s = false

theorem memoOK_empty : MemoOK M P ops ∅ := by
  intro rem s h
  simp at h

theorem msearch_eq :
    ∀ (n : Nat) (rem : List (Fin ops.size)) (s : σ) (V : Memo ops (σ := σ)),
      rem.length = n → MemoOK M P ops V →
      (msearch M P ops rem s V).1 = search M P ops rem s ∧
        MemoOK M P ops (msearch M P ops rem s V).2 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro rem s V hlen hV
    rw [msearch]
    by_cases hc : V.contains (rem, s) = true
    · simp only [hc, ite_true]
      exact ⟨(hV rem s hc).symm, hV⟩
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      rw [search_eq]
      rcases hm : minRet ops rem with _ | m
      · exact ⟨rfl, hV⟩
      · simp only
        -- every recursive call is correct and keeps the memo sound
        have hrec : ∀ c ∈ (cands M P ops rem s m).attach, ∀ V', MemoOK M P ops V' →
            (msearch M P ops (rem.erase c.1.1) c.1.2 V').1 =
                search M P ops (rem.erase c.1.1) c.1.2 ∧
              MemoOK M P ops (msearch M P ops (rem.erase c.1.1) c.1.2 V').2 := by
          intro c _ V' hV'
          have hlt : (rem.erase c.1.1).length < n :=
            hlen ▸ length_erase_lt ((mem_cands M P ops).1 c.2).1
          exact ih _ hlt _ _ _ rfl hV'
        obtain ⟨h1, h2⟩ := anyThread_spec
          (fun (c : {x // x ∈ cands M P ops rem s m}) => search M P ops (rem.erase c.1.1) c.1.2)
          (MemoOK M P ops)
          (fun (c : {x // x ∈ cands M P ops rem s m}) V => msearch M P ops (rem.erase c.1.1) c.1.2 V)
          _ hrec V hV
        rcases hat : anyThread (cands M P ops rem s m).attach V
            (fun c V => msearch M P ops (rem.erase c.1.1) c.1.2 V) with ⟨b, V'⟩
        rw [hat] at h1 h2
        simp only at h1 h2
        cases b with
        | true => exact ⟨h1, h2⟩
        | false =>
          dsimp only
          refine ⟨h1, ?_⟩
          intro rem' s' hin
          rw [Std.HashSet.contains_insert] at hin
          rcases Bool.or_eq_true_iff.1 hin with heq | hin
          · have heq : (rem, s) = (rem', s') := LawfulBEq.eq_of_beq heq
            cases heq
            rw [search_eq, hm]
            exact h1.symm
          · exact h2 rem' s' hin

end Search

end Linproof
