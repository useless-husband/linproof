import Linproof.Keyed

/-!
# Locality

Herlihy and Wing's locality theorem for the keyed store: a well-formed history of
`Keyed K M` is linearizable if and only if, for every key `k`, the operations on `k` form a
linearizable history of `M`.

* "Only if" restricts a linearization of the whole history to one key: filtering keeps the
  real-time order, and `legal_keyed` shows the restriction is accepted by `M`.
* "If" has to merge one linearization per key into a single sequence that still respects
  real-time order across keys. Each operation of a per-key linearization is given a *point*:
  the latest invocation time among it and the operations before it. Points never decrease
  along a linearization, and lie between the operation's invocation and its response (this
  is where real-time order and well-formedness are used). Sorting all operations by point
  with a stable sort (`List.mergeSort`) gives a sequence in which no operation comes before
  one that returned before it was invoked, and in which each key's operations appear in
  their original order (`List.sublist_mergeSort`).
-/

namespace Linproof

namespace Locality

/-! ### List lemmas -/

theorem perm_flatMap_left {α β : Type} :
    ∀ {l : List α} {f g : α → List β}, (∀ a ∈ l, (f a).Perm (g a)) →
      (l.flatMap f).Perm (l.flatMap g) := by
  intro l
  induction l with
  | nil => intro _ _ _; simp
  | cons a l ih =>
    intro f g h
    simp only [List.flatMap_cons]
    exact (h a (by simp)).append (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem sublist_flatMap_of_mem {α β : Type} (f : α → List β) :
    ∀ {l : List α} {a : α}, a ∈ l → (f a).Sublist (l.flatMap f) := by
  intro l
  induction l with
  | nil => intro _ h; simp at h
  | cons b l ih =>
    intro a h
    simp only [List.flatMap_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact List.sublist_append_left _ _
    · exact (ih h).trans (List.sublist_append_right _ _)

theorem flatMap_congr' {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (by simp), ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-- Remove duplicates (used only inside proofs). -/
def dedup {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a :: l => if a ∈ dedup l then dedup l else a :: dedup l

theorem mem_dedup {α : Type} [DecidableEq α] : ∀ {l : List α} {a : α}, a ∈ dedup l ↔ a ∈ l := by
  intro l
  induction l with
  | nil => simp [dedup]
  | cons b l ih =>
    intro a
    unfold dedup
    split
    · rw [ih, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | h)
        · exact ih.1 ‹_›
        · exact h
    · rw [List.mem_cons, List.mem_cons, ih]

theorem nodup_dedup {α : Type} [DecidableEq α] : ∀ (l : List α), (dedup l).Nodup := by
  intro l
  induction l with
  | nil => exact List.nodup_nil
  | cons b l ih =>
    unfold dedup
    split
    · exact ih
    · exact List.nodup_cons.2 ⟨‹_›, ih⟩

section blocks

variable {α κ : Type} [DecidableEq κ] (key : α → κ)

/-- Grouping a list by key, over a duplicate-free list of keys that covers every element,
is a reordering of it. -/
theorem perm_flatMap_filter :
    ∀ (ks : List κ) (C : List α), ks.Nodup → (∀ x ∈ C, key x ∈ ks) →
      (ks.flatMap fun k => C.filter fun x => key x = k).Perm C := by
  intro ks
  induction ks with
  | nil =>
    intro C _ hcov
    cases C with
    | nil => simp
    | cons x C => simpa using hcov x (by simp)
  | cons k ks ih =>
    intro C hnd hcov
    rw [List.nodup_cons] at hnd
    simp only [List.flatMap_cons]
    have hrest : (ks.flatMap fun k' => C.filter fun x => key x = k').Perm
        (C.filter fun x => !decide (key x = k)) := by
      have e : (ks.flatMap fun k' => C.filter fun x => key x = k') =
          (ks.flatMap fun k' => (C.filter fun x => !decide (key x = k)).filter
            fun x => key x = k') := by
        apply flatMap_congr'
        intro k' hk'
        rw [List.filter_filter]
        apply List.filter_congr
        intro x _
        by_cases hx : key x = k'
        · have : k' ≠ k := fun e => hnd.1 (e ▸ hk')
          simp [hx, this]
        · simp [hx]
      rw [e]
      apply ih _ hnd.2
      intro x hx
      simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at hx
      rcases List.mem_cons.1 (hcov x hx.1) with h | h
      · exact absurd h hx.2
      · exact h
    exact (List.Perm.append (List.Perm.refl _) hrest).trans (List.filter_append_perm _ C)

/-- In a list made of one block per key, filtering by a key leaves exactly its block. -/
theorem filter_flatMap_block (A : κ → List α) (hA : ∀ k, ∀ x ∈ A k, key x = k) :
    ∀ (ks : List κ) (k : κ), ks.Nodup → k ∈ ks →
      ((ks.flatMap A).filter fun x => key x = k) = A k := by
  intro ks
  induction ks with
  | nil => intro _ _ h; simp at h
  | cons k' ks ih =>
    intro k hnd hk
    rw [List.nodup_cons] at hnd
    simp only [List.flatMap_cons, List.filter_append]
    rcases List.mem_cons.1 hk with rfl | hk
    · have h1 : ((A k).filter fun x => key x = k) = A k :=
        List.filter_eq_self.2 fun x hx => by simp [hA k x hx]
      have h2 : ((ks.flatMap A).filter fun x => key x = k) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx
        obtain ⟨k'', hk'', hx⟩ := List.mem_flatMap.1 hx
        have := hA k'' x hx
        simp only [decide_eq_true_eq, this]
        intro e
        exact hnd.1 (e ▸ hk'')
      rw [h1, h2, List.append_nil]
    · have hne : k' ≠ k := fun e => hnd.1 (e ▸ hk)
      have h1 : ((A k').filter fun x => key x = k) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx
        simp [hA k' x hx, hne]
      rw [h1, List.nil_append]
      exact ih k hnd.2 hk

end blocks

/-! ### Keyed operations -/

variable {σ ι ο K : Type} [DecidableEq K]

/-- The key of an operation paired with its output. -/
abbrev keyOf (p : Op (K × ι) ο × ο) : K := p.1.input.1

def unkeyP (p : Op (K × ι) ο × ο) : Op ι ο × ο := (p.1.unkey, p.2)

def rekey (k : K) (op : Op ι ο) : Op (K × ι) ο :=
  { call := op.call, input := (k, op.input), ret := op.ret }

def rekeyP (k : K) (p : Op ι ο × ο) : Op (K × ι) ο × ο := (rekey k p.1, p.2)

omit [DecidableEq K] in
theorem rekeyP_unkeyP {k : K} {p : Op (K × ι) ο × ο} (h : keyOf p = k) :
    rekeyP k (unkeyP p) = p := by
  obtain ⟨⟨call, ⟨k', i⟩, ret⟩, o⟩ := p
  simp only [keyOf] at h
  subst h
  rfl

omit [DecidableEq K] in
theorem precedes_unkey (a b : Op (K × ι) ο) : precedes a.unkey b.unkey ↔ precedes a b := by
  simp [precedes, Op.unkey]

omit [DecidableEq K] in
theorem precedes_rekey (k k' : K) (a b : Op ι ο) :
    precedes (rekey k a) (rekey k' b) ↔ precedes a b := by
  simp [precedes, rekey]

/-! ### Legality decomposes by key -/

/-- The input/output pairs of key `k`, without the key. -/
def projL (k : K) (L : List ((K × ι) × ο)) : List (ι × ο) :=
  (L.filter fun p => p.1.1 = k).map fun p => (p.1.2, p.2)

theorem legal_keyed (M : Model σ ι ο) :
    ∀ (L : List ((K × ι) × ο)) (f : K → σ),
      Legal (Keyed K M) f L ↔ ∀ k, Legal M (f k) (projL k L) := by
  intro L
  induction L with
  | nil => intro f; simp [Legal, projL]
  | cons p L ih =>
    intro f
    obtain ⟨⟨k0, i⟩, o⟩ := p
    have hproj : ∀ k, projL k (((k0, i), o) :: L) =
        if k0 = k then (i, o) :: projL k L else projL k L := by
      intro k
      by_cases h : k0 = k <;> simp [projL, h]
    have hstep : ∀ f' : K → σ, (Keyed K M).step f (k0, i) o = some f' ↔
        ∃ s', M.step (f k0) i o = some s' ∧ (fun k => if k = k0 then s' else f k) = f' := by
      intro f'
      simp only [Keyed, Option.map_eq_some_iff]
    simp only [Legal, hstep]
    constructor
    · rintro ⟨f', ⟨s', hs, rfl⟩, hrest⟩ k
      rw [ih] at hrest
      rw [hproj]
      by_cases hk : k0 = k
      · subst hk
        simp only [↓reduceIte]
        refine ⟨s', hs, ?_⟩
        simpa using hrest k0
      · simp only [hk, ↓reduceIte]
        have := hrest k
        simpa [Ne.symm hk] using this
    · intro h
      have h0 := h k0
      rw [hproj] at h0
      simp only [↓reduceIte] at h0
      obtain ⟨s', hs, h0⟩ := h0
      refine ⟨_, ⟨s', hs, rfl⟩, ?_⟩
      rw [ih]
      intro k
      by_cases hk : k = k0
      · subst hk; simpa using h0
      · have := h k
        rw [hproj] at this
        simpa [hk, Ne.symm hk] using this

/-- Turning a list of operations with outputs into the input/output pairs commutes with
restricting to one key. -/
theorem projL_map (k : K) (l : List (Op (K × ι) ο × ο)) :
    projL k (l.map fun p => (p.1.input, p.2)) =
      ((l.filter fun p => keyOf p = k).map unkeyP).map fun p => (p.1.input, p.2) := by
  simp only [projL, List.filter_map, List.map_map]
  rfl

/-! ### Completions and keys -/

theorem completion_mem {h : List (Op ι ο)} {c : List (Op ι ο × ο)} (hc : Completion h c) :
    ∀ p ∈ c, p.1 ∈ h := by
  induction hc with
  | nil => simp
  | returned _ _ ih =>
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · simp
    · exact List.mem_cons_of_mem _ (ih p hp)
  | tookEffect _ _ _ ih =>
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · simp
    · exact List.mem_cons_of_mem _ (ih p hp)
  | noEffect _ _ ih =>
    intro p hp
    exact List.mem_cons_of_mem _ (ih p hp)

theorem project_cons (k : K) (op : Op (K × ι) ο) (h : List (Op (K × ι) ο)) :
    project k (op :: h) = if op.input.1 = k then op.unkey :: project k h else project k h := by
  by_cases hk : op.input.1 = k <;> simp [project, hk]

theorem completion_project {h : List (Op (K × ι) ο)} {c : List (Op (K × ι) ο × ο)}
    (hc : Completion h c) (k : K) :
    Completion (project k h) ((c.filter fun p => keyOf p = k).map unkeyP) := by
  induction hc with
  | nil => exact Completion.nil
  | @returned op h c t o hr _ ih =>
    rw [project_cons]
    by_cases hk : op.input.1 = k
    · simp only [hk, ↓reduceIte, List.filter_cons, keyOf, decide_true, List.map_cons]
      exact Completion.returned (t := t) (by simpa [Op.unkey] using hr) ih
    · simpa [hk, List.filter_cons, keyOf] using ih
  | @tookEffect op h c o hr _ ih =>
    rw [project_cons]
    by_cases hk : op.input.1 = k
    · simp only [hk, ↓reduceIte, List.filter_cons, keyOf, decide_true, List.map_cons]
      exact Completion.tookEffect o (by simpa [Op.unkey] using hr) ih
    · simpa [hk, List.filter_cons, keyOf] using ih
  | @noEffect op h c hr _ ih =>
    rw [project_cons]
    by_cases hk : op.input.1 = k
    · simp only [hk, ↓reduceIte]
      exact Completion.noEffect (by simpa [Op.unkey] using hr) ih
    · simpa [hk] using ih

/-! ### "Only if": restricting a linearization to one key -/

theorem linearizable_project (M : Model σ ι ο) {h : List (Op (K × ι) ο)}
    (hlin : Linearizable (Keyed K M) h) (k : K) : Linearizable M (project k h) := by
  obtain ⟨c, l, hc, hperm, hpw, hleg⟩ := hlin
  refine ⟨_, (l.filter fun p => keyOf p = k).map unkeyP, completion_project hc k,
    (hperm.filter _).map _, ?_, ?_⟩
  · refine List.Pairwise.map _ (fun a b h => ?_) (hpw.filter _)
    simpa [unkeyP, precedes_unkey] using h
  · have := (legal_keyed M _ _).1 hleg k
    rw [projL_map] at this
    exact this

/-! ### "If", step 1: one completion of the whole history -/

theorem completion_nil_inv {c : List (Op ι ο × ο)} (hc : Completion ([] : List (Op ι ο)) c) :
    c = [] := by
  cases hc; rfl

theorem completion_cons_inv {a : Op ι ο} {h : List (Op ι ο)} {c : List (Op ι ο × ο)}
    (hc : Completion (a :: h) c) :
    (∃ t o c', a.ret = some (t, o) ∧ c = (a, o) :: c' ∧ Completion h c') ∨
    (∃ o c', a.ret = none ∧ c = (a, o) :: c' ∧ Completion h c') ∨
    (a.ret = none ∧ Completion h c) := by
  cases hc with
  | returned hr hc' => exact Or.inl ⟨_, _, _, hr, rfl, hc'⟩
  | tookEffect o hr hc' => exact Or.inr (Or.inl ⟨o, _, hr, rfl, hc'⟩)
  | noEffect hr hc' => exact Or.inr (Or.inr ⟨hr, hc'⟩)

/-- One completion per key combine into a completion of the whole history. -/
theorem completion_lift :
    ∀ (h : List (Op (K × ι) ο)) (c : K → List (Op ι ο × ο)),
      (∀ k, Completion (project k h) (c k)) →
      ∃ C, Completion h C ∧ ∀ k, (C.filter fun p => keyOf p = k).map unkeyP = c k := by
  intro h
  induction h with
  | nil =>
    intro c hc
    refine ⟨[], Completion.nil, fun k => ?_⟩
    exact (completion_nil_inv (by simpa [project] using hc k)).symm
  | cons op h ih =>
    intro c hc
    have h0 := hc op.input.1
    rw [project_cons] at h0
    simp only [↓reduceIte] at h0
    -- the family after removing `op` from its key
    have rest : ∀ c', Completion (project op.input.1 h) c' →
        ∀ k, Completion (project k h) (if k = op.input.1 then c' else c k) := by
      intro c' hc' k
      by_cases hk : k = op.input.1
      · subst hk; simpa using hc'
      · have := hc k
        rw [project_cons] at this
        simpa [hk, Ne.symm hk] using this
    have filt : ∀ (C' : List (Op (K × ι) ο × ο)) c',
        (∀ k, (C'.filter fun p => keyOf p = k).map unkeyP =
          if k = op.input.1 then c' else c k) →
        ∀ k, k ≠ op.input.1 → (C'.filter fun p => keyOf p = k).map unkeyP = c k := by
      intro C' c' hC' k hk
      simpa [hk] using hC' k
    have same : ∀ (C' : List (Op (K × ι) ο × ο)) c',
        (∀ k, (C'.filter fun p => keyOf p = k).map unkeyP =
          if k = op.input.1 then c' else c k) →
        (C'.filter fun p => keyOf p = op.input.1).map unkeyP = c' := by
      intro C' c' hC'
      simpa using hC' op.input.1
    rcases completion_cons_inv h0 with ⟨t, o, c', hr, he, hc'⟩ | ⟨o, c', hr, he, hc'⟩ | ⟨hr, hc'⟩
    · obtain ⟨C', hC', hf⟩ := ih _ (rest c' hc')
      refine ⟨(op, o) :: C', Completion.returned (t := t) hr hC', fun k => ?_⟩
      by_cases hk : k = op.input.1
      · subst hk
        simp [keyOf, same C' c' hf, he, unkeyP]
      · have hk' : op.input.1 ≠ k := fun e => hk e.symm
        simp only [List.filter_cons, keyOf, hk', decide_false, Bool.false_eq_true, ↓reduceIte]
        exact filt C' c' hf k hk
    · obtain ⟨C', hC', hf⟩ := ih _ (rest c' hc')
      refine ⟨(op, o) :: C', Completion.tookEffect o hr hC', fun k => ?_⟩
      by_cases hk : k = op.input.1
      · subst hk
        simp [keyOf, same C' c' hf, he, unkeyP]
      · have hk' : op.input.1 ≠ k := fun e => hk e.symm
        simp only [List.filter_cons, keyOf, hk', decide_false, Bool.false_eq_true, ↓reduceIte]
        exact filt C' c' hf k hk
    · obtain ⟨C', hC', hf⟩ := ih _ (rest (c op.input.1) hc')
      refine ⟨C', Completion.noEffect hr hC', fun k => ?_⟩
      by_cases hk : k = op.input.1
      · subst hk
        exact same C' _ hf
      · exact filt C' _ hf k hk

/-! ### "If", step 2: points -/

/-- Pair each operation of a sequence with its point: the latest invocation time among it
and the operations before it (and `m`). -/
def annotate : Nat → List (Op (K × ι) ο × ο) → List (Nat × (Op (K × ι) ο × ο))
  | _, [] => []
  | m, p :: rest => (max m p.1.call, p) :: annotate (max m p.1.call) rest

omit [DecidableEq K] in
theorem annotate_snd : ∀ (m : Nat) (l : List (Op (K × ι) ο × ο)), (annotate m l).map Prod.snd = l
  | _, [] => rfl
  | m, p :: rest => by simp [annotate, annotate_snd _ rest]

omit [DecidableEq K] in
theorem annotate_ge : ∀ (m : Nat) (l : List (Op (K × ι) ο × ο)), ∀ q ∈ annotate m l, m ≤ q.1
  | _, [] => by simp [annotate]
  | m, p :: rest => by
    intro q hq
    simp only [annotate, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (Nat.le_max_left _ _) (annotate_ge _ rest q hq)

omit [DecidableEq K] in
theorem annotate_mono : ∀ (m : Nat) (l : List (Op (K × ι) ο × ο)),
    (annotate m l).Pairwise fun a b => decide (a.1 ≤ b.1) = true
  | _, [] => List.Pairwise.nil
  | m, p :: rest => by
    simp only [annotate]
    refine List.Pairwise.cons (fun q hq => ?_) (annotate_mono _ rest)
    simpa using annotate_ge _ rest q hq

omit [DecidableEq K] in
theorem annotate_call : ∀ (m : Nat) (l : List (Op (K × ι) ο × ο)),
    ∀ q ∈ annotate m l, q.2.1.call ≤ q.1
  | _, [] => by simp [annotate]
  | m, p :: rest => by
    intro q hq
    simp only [annotate, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact Nat.le_max_right _ _
    · exact annotate_call _ rest q hq

omit [DecidableEq K] in
/-- Points come no later than responses, provided the sequence respects real-time order,
its operations are well formed, and `m` is no later than any response. -/
theorem annotate_ret : ∀ (m : Nat) (l : List (Op (K × ι) ο × ο)),
    l.Pairwise (fun a b => ¬ precedes b.1 a.1) →
    (∀ p ∈ l, ∀ t o, p.1.ret = some (t, o) → p.1.call ≤ t) →
    (∀ p ∈ l, ∀ t o, p.1.ret = some (t, o) → m ≤ t) →
    ∀ q ∈ annotate m l, ∀ t o, q.2.1.ret = some (t, o) → q.1 ≤ t
  | _, [] => by simp [annotate]
  | m, p :: rest => by
    intro hpw hwf hm q hq t o hr
    rw [List.pairwise_cons] at hpw
    simp only [annotate, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact Nat.max_le.2 ⟨hm _ (by simp) t o hr, hwf _ (by simp) t o hr⟩
    · refine annotate_ret _ rest hpw.2 (fun p' hp' => hwf p' (List.mem_cons_of_mem _ hp'))
        ?_ q hq t o hr
      intro p' hp' t' o' hr'
      refine Nat.max_le.2 ⟨hm p' (List.mem_cons_of_mem _ hp') t' o' hr', ?_⟩
      have := hpw.1 p' hp'
      simp only [precedes, hr'] at this
      omega

/-! ### "If", step 3: merging -/

theorem linearizable_of_project (M : Model σ ι ο) {h : List (Op (K × ι) ο)}
    (hwf : WellFormed h) (H : ∀ k, Linearizable M (project k h)) :
    Linearizable (Keyed K M) h := by
  -- one completion and linearization per key
  obtain ⟨W, hW⟩ := Classical.axiomOfChoice
    (r := fun k (w : List (Op ι ο × ο) × List (Op ι ο × ο)) =>
      Completion (project k h) w.1 ∧ w.2.Perm w.1 ∧
      w.2.Pairwise (fun a b => ¬ precedes b.1 a.1) ∧
      Legal M M.init (w.2.map fun p => (p.1.input, p.2)))
    (fun k => by
      obtain ⟨c, l, hc, hp, hpw, hl⟩ := H k
      exact ⟨(c, l), hc, hp, hpw, hl⟩)
  obtain ⟨C, hC, hCf⟩ := completion_lift h (fun k => (W k).1) (fun k => (hW k).1)
  have hCmem : ∀ p ∈ C, p.1 ∈ h := completion_mem hC
  let ks := dedup (h.map fun op => op.input.1)
  have hks : ∀ p ∈ C, keyOf p ∈ ks := fun p hp =>
    mem_dedup.2 (List.mem_map.2 ⟨p.1, hCmem p hp, rfl⟩)
  -- the linearization of key `k`, with keys put back
  let Lk : K → List (Op (K × ι) ο × ο) := fun k => (W k).2.map (rekeyP k)
  have hLk_perm : ∀ k, (Lk k).Perm (C.filter fun p => keyOf p = k) := by
    intro k
    have h1 : (Lk k).Perm (((C.filter fun p => keyOf p = k).map unkeyP).map (rekeyP k)) := by
      rw [hCf k]
      exact (hW k).2.1.map _
    refine h1.trans (List.Perm.of_eq ?_)
    rw [List.map_map]
    conv => rhs; rw [← List.map_id (C.filter fun p => keyOf p = k)]
    apply List.map_congr_left
    intro p hp
    exact rekeyP_unkeyP (by simpa using (List.mem_filter.1 hp).2)
  have hLk_mem : ∀ k, ∀ p ∈ Lk k, p ∈ C ∧ keyOf p = k := by
    intro k p hp
    have := List.mem_filter.1 ((hLk_perm k).mem_iff.1 hp)
    exact ⟨this.1, by simpa using this.2⟩
  have hLk_pw : ∀ k, (Lk k).Pairwise (fun a b => ¬ precedes b.1 a.1) := by
    intro k
    refine List.Pairwise.map _ (fun a b h => ?_) (hW k).2.2.1
    simpa [rekeyP, precedes_rekey] using h
  have hLk_wf : ∀ k, ∀ p ∈ Lk k, ∀ t o, p.1.ret = some (t, o) → p.1.call ≤ t :=
    fun k p hp t o hr => hwf p.1 (hCmem p (hLk_mem k p hp).1) t o hr
  -- annotate every per-key linearization with points
  let A : K → List (Nat × (Op (K × ι) ο × ο)) := fun k => annotate 0 (Lk k)
  have hA_snd : ∀ k, ∀ q ∈ A k, q.2 ∈ Lk k := by
    intro k q hq
    rw [← annotate_snd 0 (Lk k)]
    exact List.mem_map_of_mem hq
  have hA_key : ∀ k, ∀ q ∈ A k, keyOf q.2 = k := fun k q hq => (hLk_mem k _ (hA_snd k q hq)).2
  have hA_call : ∀ k, ∀ q ∈ A k, q.2.1.call ≤ q.1 := fun k => annotate_call 0 (Lk k)
  have hA_ret : ∀ k, ∀ q ∈ A k, ∀ t o, q.2.1.ret = some (t, o) → q.1 ≤ t :=
    fun k => annotate_ret 0 (Lk k) (hLk_pw k) (hLk_wf k) (fun _ _ _ _ _ => Nat.zero_le _)
  -- sort everything by point, stably
  let le : Nat × (Op (K × ι) ο × ο) → Nat × (Op (K × ι) ο × ο) → Bool :=
    fun a b => decide (a.1 ≤ b.1)
  have htrans : ∀ a b c, le a b = true → le b c = true → le a c = true := by
    intro a b c h1 h2
    simp only [le, decide_eq_true_eq] at *
    omega
  have htotal : ∀ a b, (le a b || le b a) = true := by
    intro a b
    simp only [le, Bool.or_eq_true, decide_eq_true_eq]
    omega
  let big := ks.flatMap A
  let merged := big.mergeSort le
  have hmem : ∀ q ∈ merged, ∃ k, q ∈ A k := by
    intro q hq
    obtain ⟨k, _, hk⟩ := List.mem_flatMap.1 (List.mem_mergeSort.1 hq)
    exact ⟨k, hk⟩
  -- each key's operations appear in the merged sequence in their original order
  have hblock : ∀ k ∈ ks, (merged.filter fun q => keyOf q.2 = k) = A k := by
    intro k hk
    have hsub : (A k).Sublist merged :=
      List.sublist_mergeSort htrans htotal (annotate_mono 0 (Lk k)) (sublist_flatMap_of_mem A hk)
    have hsub' : (A k).Sublist (merged.filter fun q => keyOf q.2 = k) := by
      have := hsub.filter (fun q => keyOf q.2 = k)
      rwa [List.filter_eq_self.2 (fun q hq => by simp [hA_key k q hq])] at this
    have hlen : (merged.filter fun q => keyOf q.2 = k).length = (A k).length := by
      rw [((List.mergeSort_perm big le).filter _).length_eq]
      rw [filter_flatMap_block (fun q => keyOf q.2) A hA_key ks k (nodup_dedup _) hk]
    exact (hsub'.eq_of_length hlen.symm).symm
  refine ⟨C, merged.map Prod.snd, hC, ?_, ?_, ?_⟩
  · -- a reordering of the completion
    refine ((List.mergeSort_perm big le).map Prod.snd).trans ?_
    have e : big.map Prod.snd = ks.flatMap Lk := by
      simp only [big, List.map_flatMap]
      apply flatMap_congr'
      intro k _
      exact annotate_snd 0 (Lk k)
    rw [e]
    exact (perm_flatMap_left fun k _ => hLk_perm k).trans
      (perm_flatMap_filter keyOf ks C (nodup_dedup _) hks)
  · -- real-time order: points never decrease and lie inside their operation's interval
    have hsorted := List.pairwise_mergeSort htrans htotal big
    refine List.Pairwise.map Prod.snd (fun a b h => h) (hsorted.imp_of_mem ?_)
    intro a b ha hb hab hp
    obtain ⟨ka, hka⟩ := hmem a ha
    obtain ⟨kb, hkb⟩ := hmem b hb
    simp only [le, decide_eq_true_eq] at hab
    unfold precedes at hp
    rcases hr : b.2.1.ret with _ | ⟨t, o⟩
    · simp [hr] at hp
    · simp only [hr] at hp
      have h1 := hA_ret kb b hkb t o hr
      have h2 := hA_call ka a hka
      omega
  · -- legal: the restriction to each key is that key's linearization
    rw [legal_keyed]
    intro k
    rw [projL_map]
    show Legal M M.init _
    by_cases hk : k ∈ ks
    · have e : ((merged.map Prod.snd).filter fun p => keyOf p = k) = Lk k := by
        rw [List.filter_map]
        have : merged.filter ((fun p => decide (keyOf p = k)) ∘ Prod.snd) = A k := hblock k hk
        rw [this]
        exact annotate_snd 0 (Lk k)
      have e2 : (Lk k).map unkeyP = (W k).2 := by
        simp only [Lk, List.map_map]
        exact List.map_id'' (fun p => rfl) _
      rw [e, e2]
      exact (hW k).2.2.2
    · have e : ((merged.map Prod.snd).filter fun p => keyOf p = k) = [] := by
        rw [List.filter_eq_nil_iff]
        intro p hp hpk
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        obtain ⟨k', hk'⟩ := hmem q hq
        have hin := hLk_mem k' _ (hA_snd k' q hk')
        have hpk' : keyOf q.2 = k := by simpa using hpk
        exact hk (hpk' ▸ hks _ hin.1)
      rw [e]
      trivial

/-- **Locality.** A well-formed history of the keyed store is linearizable exactly when the
operations on each key form a linearizable history of the per-key object. -/
theorem locality (M : Model σ ι ο) (h : List (Op (K × ι) ο)) (hwf : WellFormed h) :
    Linearizable (Keyed K M) h ↔ ∀ k, Linearizable M (project k h) :=
  ⟨linearizable_project M, linearizable_of_project M hwf⟩

end Locality

end Linproof

namespace Linproof

variable {σ ι ο K : Type} [DecidableEq K]

theorem wellFormed_project {h : List (Op (K × ι) ο)} (hwf : WellFormed h) (k : K) :
    WellFormed (project k h) := by
  intro op hop t o hr
  obtain ⟨op', hop', rfl⟩ := List.mem_map.1 hop
  exact hwf op' (List.mem_filter.1 hop').1 t o hr

theorem linearizable_nil (M : Model σ ι ο) : Linearizable M [] :=
  ⟨[], [], Completion.nil, List.Perm.refl _, List.Pairwise.nil, trivial⟩

variable (M : Model σ ι ο) (P : PendingSteps M) [DecidableEq σ] [Hashable σ]

/-- **The keyed checker is sound and complete**: it checks each key separately, and by the
locality theorem that decides linearizability of the whole keyed history. -/
theorem checkKeyed_iff (h : List (Op (K × ι) ο)) (hwf : WellFormed h) :
    checkKeyed M P h = true ↔ Linearizable (Keyed K M) h := by
  rw [Locality.locality M h hwf]
  simp only [checkKeyed, List.all_eq_true]
  constructor
  · intro H k
    by_cases hk : k ∈ keysOf h
    · exact (check_iff M P _ (wellFormed_project hwf k)).1 (H k hk)
    · have : project k h = [] := by
        rw [project, List.map_eq_nil_iff, List.filter_eq_nil_iff]
        intro op hop hk'
        exact hk (mem_keysOf.2 ⟨op, hop, by simpa using hk'⟩)
      rw [this]
      exact linearizable_nil M
  · intro H k _
    exact (check_iff M P _ (wellFormed_project hwf k)).2 (H k)

end Linproof
