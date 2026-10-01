import Linproof.Search

/-!
# From the search invariant to the definition

`Search.Ext` talks about indices into an array of operations; `Linearizable` (in
`Spec.lean`) talks about lists of operations and the inductive `Completion`. This file
proves that they agree at the start configuration:

    Ext ops (List.finRange ops.size) M.init ↔ Linearizable M ops.toList

Going from indices to operations is a `map`. Going back needs care because a history may
contain several identical operations: `completion_indices` recovers which positions a
completion kept, and `perm_map_lift` transports the order of the linearization back to those
positions.
-/

namespace Linproof

/-! ### List lemmas -/

/-- If `l` is a reordering of `m.map g`, it is `m'.map g` for a reordering `m'` of `m`. -/
theorem perm_map_lift {α β : Type} (g : α → β) :
    ∀ {l : List β} {m : List α}, l.Perm (m.map g) → ∃ m' : List α, m'.Perm m ∧ m'.map g = l := by
  intro l
  induction l with
  | nil =>
    intro m h
    have := h.nil_eq
    rw [eq_comm, List.map_eq_nil_iff] at this
    subst this
    exact ⟨[], List.Perm.refl _, rfl⟩
  | cons a l ih =>
    intro m h
    have ha : a ∈ m.map g := h.mem_iff.1 (by simp)
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
    obtain ⟨s, t, rfl⟩ := List.append_of_mem hx
    have h' : (g x :: l).Perm (g x :: (s ++ t).map g) := by
      refine h.trans ?_
      simp only [List.map_append, List.map_cons]
      exact List.perm_middle
    obtain ⟨m', hm', hmap⟩ := ih h'.cons_inv
    refine ⟨x :: m', ?_, by simp [hmap]⟩
    exact (hm'.cons x).trans List.perm_middle.symm

theorem nodup_of_map {α β : Type} {f : α → β} {l : List α} (h : (l.map f).Nodup) : l.Nodup :=
  List.Pairwise.of_map f (fun _ _ h e => h (congrArg f e)) h

/-- For a list of pairs with distinct first components, membership is a lookup. -/
theorem mem_iff_lookup {α β : Type} [DecidableEq α] :
    ∀ {R : List (α × β)} {a : α} {b : β}, (R.map Prod.fst).Nodup →
      ((a, b) ∈ R ↔ R.lookup a = some b) := by
  intro R
  induction R with
  | nil => simp
  | cons p R ih =>
    intro a b hnd
    obtain ⟨k, v⟩ := p
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [List.lookup_cons]
    by_cases hak : a = k
    · subst hak
      simp only [beq_self_eq_true, List.mem_cons, Prod.mk.injEq, true_and, Option.some.injEq]
      constructor
      · rintro (rfl | hm)
        · rfl
        · exact absurd (List.mem_map_of_mem (f := Prod.fst) hm) hnd.1
      · rintro rfl; exact Or.inl rfl
    · have : (a == k) = false := by simpa using hak
      simp only [this, List.mem_cons, Prod.mk.injEq, hak, false_and, false_or]
      exact ih hnd.2

namespace Bridge

variable {ι ο : Type}

theorem nodup_map_succ {n : Nat} {I : List (Fin n × ο)} (h : (I.map Prod.fst).Nodup) :
    ((I.map fun p => (p.1.succ, p.2)).map Prod.fst).Nodup := by
  have : (I.map fun p => (p.1.succ, p.2)).map Prod.fst = (I.map Prod.fst).map Fin.succ := by
    simp only [List.map_map]; rfl
  rw [this]
  exact List.Pairwise.map Fin.succ (fun a b h e => h (Fin.succ_inj.1 e)) h

/-! ### Completions given by a choice of outputs -/

/-- The completion that keeps operation `i` with output `o` when `F i = some o`, in
history order. -/
def compOf (l : List (Op ι ο)) (F : Fin l.length → Option ο) : List (Op ι ο × ο) :=
  (List.finRange l.length).filterMap fun i => (F i).map fun o => (l[i], o)

theorem compOf_cons (op : Op ι ο) (l : List (Op ι ο)) (F : Fin (op :: l).length → Option ο) :
    compOf (op :: l) F =
      match F 0 with
      | some o => (op, o) :: compOf l (fun i => F i.succ)
      | none => compOf l (fun i => F i.succ) := by
  unfold compOf
  simp only [List.length_cons, List.finRange_succ, List.filterMap_cons, List.filterMap_map]
  rcases F 0 with _ | o
  · simp only [Option.map_none]
    rfl
  · simp only [Option.map_some, Fin.getElem_fin, Fin.val_zero, List.getElem_cons_zero]
    rfl

theorem completion_compOf :
    ∀ (l : List (Op ι ο)) (F : Fin l.length → Option ο),
      (∀ i : Fin l.length, ∀ t o, l[i].ret = some (t, o) → F i = some o) →
      Completion l (compOf l F) := by
  intro l
  induction l with
  | nil =>
    intro F _
    simp only [compOf, List.length_nil, List.finRange_zero, List.filterMap_nil]
    exact Completion.nil
  | cons op l ih =>
    intro F hF
    have hrest := ih (fun i => F i.succ) (fun i t o h => hF i.succ t o (by simpa using h))
    rw [compOf_cons]
    rcases hF0 : F 0 with _ | o
    · rcases hr : op.ret with _ | ⟨t, o⟩
      · exact Completion.noEffect hr hrest
      · have := hF 0 t o (by simpa using hr)
        rw [hF0] at this
        cases this
    · rcases hr : op.ret with _ | ⟨t, o'⟩
      · exact Completion.tookEffect o hr hrest
      · have := hF 0 t o' (by simpa using hr)
        rw [hF0] at this
        cases this
        exact Completion.returned hr hrest

/-! ### Recovering positions from a completion -/

theorem completion_indices :
    ∀ {l : List (Op ι ο)} {c : List (Op ι ο × ο)}, Completion l c →
      ∃ I : List (Fin l.length × ο),
        c = I.map (fun p => (l[p.1], p.2)) ∧
        (I.map Prod.fst).Nodup ∧
        (∀ p ∈ I, ∀ t o, l[p.1].ret = some (t, o) → p.2 = o) ∧
        (∀ i : Fin l.length, ∀ t o, l[i].ret = some (t, o) → i ∈ I.map Prod.fst) := by
  intro l c h
  induction h with
  | nil => exact ⟨[], rfl, List.nodup_nil, by simp, fun i => i.elim0⟩
  | @returned op h c t o hr _ ih =>
    obtain ⟨I, hc, hnd, hout, hcov⟩ := ih
    refine ⟨(0, o) :: I.map (fun p => (p.1.succ, p.2)), ?_, ?_, ?_, ?_⟩
    · simp [hc]
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, nodup_map_succ hnd⟩
      simp only [List.map_map, List.mem_map, Function.comp_apply, not_exists, not_and]
      intro p _ h
      exact Fin.succ_ne_zero _ h
    · intro p hp t' o' hr'
      simp only [List.mem_cons, List.mem_map] at hp
      rcases hp with rfl | ⟨q, hq, rfl⟩
      · simp only [Fin.getElem_fin, Fin.val_zero, List.getElem_cons_zero] at hr'
        rw [hr] at hr'
        cases hr'
        rfl
      · exact hout q hq t' o' (by simpa using hr')
    · intro i t' o' hr'
      refine Fin.cases ?_ (fun j hr' => ?_) i hr'
      · intro _; simp
      · have := hcov j t' o' (by simpa using hr')
        simp only [List.map_cons, List.map_map, List.mem_cons, List.mem_map, Function.comp_apply]
        exact Or.inr (by obtain ⟨q, hq, e⟩ := List.mem_map.1 this; exact ⟨q, hq, by rw [e]⟩)
  | @tookEffect op h c o hr _ ih =>
    obtain ⟨I, hc, hnd, hout, hcov⟩ := ih
    refine ⟨(0, o) :: I.map (fun p => (p.1.succ, p.2)), ?_, ?_, ?_, ?_⟩
    · simp [hc]
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, nodup_map_succ hnd⟩
      simp only [List.map_map, List.mem_map, Function.comp_apply, not_exists, not_and]
      intro p _ h
      exact Fin.succ_ne_zero _ h
    · intro p hp t' o' hr'
      simp only [List.mem_cons, List.mem_map] at hp
      rcases hp with rfl | ⟨q, hq, rfl⟩
      · simp only [Fin.getElem_fin, Fin.val_zero, List.getElem_cons_zero] at hr'
        rw [hr] at hr'
        cases hr'
      · exact hout q hq t' o' (by simpa using hr')
    · intro i t' o' hr'
      refine Fin.cases ?_ (fun j hr' => ?_) i hr'
      · intro _; simp
      · have := hcov j t' o' (by simpa using hr')
        simp only [List.map_cons, List.map_map, List.mem_cons, List.mem_map, Function.comp_apply]
        exact Or.inr (by obtain ⟨q, hq, e⟩ := List.mem_map.1 this; exact ⟨q, hq, by rw [e]⟩)
  | @noEffect op h c hr _ ih =>
    obtain ⟨I, hc, hnd, hout, hcov⟩ := ih
    refine ⟨I.map (fun p => (p.1.succ, p.2)), ?_, ?_, ?_, ?_⟩
    · simp [hc]
    · exact nodup_map_succ hnd
    · intro p hp t' o' hr'
      simp only [List.mem_map] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      exact hout q hq t' o' (by simpa using hr')
    · intro i t' o' hr'
      refine Fin.cases ?_ (fun j hr' => ?_) i hr'
      · intro hr0
        simp only [Fin.getElem_fin, Fin.val_zero, List.getElem_cons_zero] at hr0
        rw [hr] at hr0
        cases hr0
      · have := hcov j t' o' (by simpa using hr')
        simp only [List.map_map, List.mem_map, Function.comp_apply]
        obtain ⟨q, hq, e⟩ := List.mem_map.1 this
        exact ⟨q, hq, by rw [e]⟩

/-! ### The bridge -/

variable {σ : Type}

theorem op_eq (ops : Array (Op ι ο)) (i : Fin ops.size) : Search.op ops i = ops.toList[i.1] := by
  simp [Search.op]

theorem wf_iff (ops : Array (Op ι ο)) : Search.WF ops ↔ WellFormed ops.toList := by
  constructor
  · intro h op hop t o hr
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hop
    have := h ⟨i, hi⟩ t o (by rw [op_eq]; exact hr)
    rwa [op_eq] at this
  · intro h i t o hr
    rw [op_eq] at hr ⊢
    exact h _ (List.getElem_mem _) t o hr

/-- **The start configuration of the search is exactly the definition.** -/
theorem ext_iff_linearizable (M : Model σ ι ο) (ops : Array (Op ι ο)) :
    Search.Ext M ops (List.finRange ops.size) M.init ↔ Linearizable M ops.toList := by
  constructor
  · rintro ⟨R, hnd, -, hcov, hout, hpw, hleg⟩
    let F : Fin ops.toList.length → Option ο := fun i => R.lookup i
    have hF : ∀ i o, F i = some o ↔ (i, o) ∈ R := fun i o => (mem_iff_lookup hnd).symm
    let Rs : List (Fin ops.size × ο) :=
      (List.finRange ops.size).filterMap fun i => (F i).map fun o => (i, o)
    have hRs : R.Perm Rs := by
      refine (List.perm_ext_iff_of_nodup (nodup_of_map hnd) ?_).2 ?_
      · refine List.Pairwise.filterMap _ ?_ (List.nodup_finRange _)
        intro a a' hne b hb b' hb' e
        simp only [Option.map_eq_some_iff] at hb hb'
        obtain ⟨_, _, rfl⟩ := hb
        obtain ⟨_, _, rfl⟩ := hb'
        exact hne (congrArg Prod.fst e)
      · rintro ⟨i, o⟩
        simp only [Rs, List.mem_filterMap, List.mem_finRange, true_and, Option.map_eq_some_iff,
          Prod.mk.injEq]
        constructor
        · intro h; exact ⟨i, o, (hF i o).2 h, rfl, rfl⟩
        · rintro ⟨j, o', h, rfl, rfl⟩; exact (hF j o').1 h
    let g : Fin ops.size × ο → Op ι ο × ο := fun p => (ops.toList[p.1.1], p.2)
    refine ⟨compOf ops.toList F, R.map g, ?_, ?_, ?_, ?_⟩
    · apply completion_compOf
      intro i t o hr
      have hi := hcov i (List.mem_finRange i) t o (by rw [op_eq]; simpa using hr)
      obtain ⟨p, hp, hpi⟩ := List.mem_map.1 hi
      obtain ⟨j, o'⟩ := p
      simp only at hpi
      subst hpi
      have := hout _ hp t o (by rw [op_eq]; simpa using hr)
      simp only at this
      subst this
      exact (hF j o').2 hp
    · have : compOf ops.toList F = Rs.map g := by
        simp only [compOf, Rs, g, List.map_filterMap, Option.map_map]
        rfl
      rw [this]
      exact hRs.map g
    · refine List.Pairwise.map g (fun a b h => ?_) hpw
      simpa [g, op_eq] using h
    · have e : ((fun p : Op ι ο × ο => (p.1.input, p.2)) ∘ g) =
          fun p => ((Search.op ops p.1).input, p.2) := by
        funext p; simp [g, op_eq]
      rw [List.map_map, e]
      exact hleg
  · rintro ⟨c, lin, hc, hperm, hpw, hleg⟩
    obtain ⟨I, rfl, hnd, hout, hcov⟩ := completion_indices hc
    obtain ⟨R, hRI, rfl⟩ := perm_map_lift _ hperm
    refine ⟨R, (hRI.map Prod.fst).nodup_iff.2 hnd, fun p _ => List.mem_finRange _, ?_, ?_, ?_, ?_⟩
    · intro i _ t o hr
      exact (hRI.map Prod.fst).mem_iff.2 (hcov i t o (by rw [op_eq] at hr; simpa using hr))
    · intro p hp t o hr
      exact hout p (hRI.mem_iff.1 hp) t o (by rw [op_eq] at hr; simpa using hr)
    · rw [List.pairwise_map] at hpw
      refine hpw.imp (fun h => ?_)
      simpa [op_eq] using h
    · rw [List.map_map] at hleg
      have e : (fun p : Fin ops.size × ο => ((Search.op ops p.1).input, p.2)) =
          ((fun p : Op ι ο × ο => (p.1.input, p.2)) ∘ fun p => (ops.toList[p.1], p.2)) := by
        funext p; simp [op_eq]
      rw [e]
      exact hleg

end Bridge

end Linproof
