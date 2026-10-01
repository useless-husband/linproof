import Linproof.Search
import Std.Data.HashSet

/-!
# The fast search: events, memoisation, incremental hashing

`Search.search` recomputes, at every step, the earliest pending response and the minimal
operations by scanning every remaining operation, which makes it quadratic. The executable
search `fsearch` keeps the configuration in a form where one step costs about as much as
the number of candidates, as Porcupine does:

* **Events.** The invocations and responses of the remaining operations, sorted by time
  (invocations first at equal times). The candidates are exactly the invocations before the
  first response, and that response's time is the earliest pending response
  (`scan_minRet`, `scan_cands`).
* **Memoisation.** Every configuration from which the search has failed is remembered in a
  hash set and never explored again. Successes need no memo: the first one ends the search.
* **Incremental hashing.** A configuration is hashed by the exclusive-or of a fixed random
  value per linearized operation (Zobrist hashing), updated in constant time. The hash is
  only a hint for the hash set: the memo key also contains the remaining operations and the
  state, and keys are compared in full, so the hash plays no part in the proofs.

`fsearch_eq` proves that `fsearch` returns the same verdict as `Search.search`, by induction
on the number of remaining events, under an invariant (`EvInv`) that the events are sorted
and are exactly the events of the remaining operations.
-/

namespace Linproof

namespace Search

variable {σ ι ο : Type} (M : Model σ ι ο) (P : PendingSteps M) (ops : Array (Op ι ο))

/-! ### Threading a memo through a list of choices -/

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

/-! ### Events -/

/-- An invocation (`isRet = false`) or a response (`isRet = true`) of operation `idx`. -/
structure Ev (n : Nat) where
  time : Nat
  isRet : Bool
  idx : Fin n
  deriving DecidableEq, Repr

/-- Events are ordered by time; at equal times invocations come first, so that operations
whose intervals touch are concurrent. -/
def Ev.le {n : Nat} (a b : Ev n) : Bool :=
  decide (a.time < b.time) || (decide (a.time = b.time) && (!a.isRet || b.isRet))

theorem Ev.le_trans {n : Nat} (a b c : Ev n) (h1 : Ev.le a b = true) (h2 : Ev.le b c = true) :
    Ev.le a c = true := by
  simp only [Ev.le, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at *
  rcases a with ⟨ta, ra, _⟩
  rcases b with ⟨tb, rb, _⟩
  rcases c with ⟨tc, rc, _⟩
  simp only at *
  cases ra <;> cases rb <;> cases rc <;> simp at * <;> omega

theorem Ev.le_total {n : Nat} (a b : Ev n) : (Ev.le a b || Ev.le b a) = true := by
  simp only [Ev.le, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
  rcases a with ⟨ta, ra, _⟩
  rcases b with ⟨tb, rb, _⟩
  simp only
  cases ra <;> cases rb <;> simp <;> omega

/-- The invocation event of operation `x`. -/
def callEv (x : Fin ops.size) : Ev ops.size := ⟨(op ops x).call, false, x⟩

/-- The response event of operation `x`, if it returned. -/
def retEv (x : Fin ops.size) : Option (Ev ops.size) :=
  (op ops x).ret.map fun r => ⟨r.1, true, x⟩

/-- `e` is one of the events of its own operation. -/
def Genuine (e : Ev ops.size) : Prop := e = callEv ops e.idx ∨ retEv ops e.idx = some e

/-- The sorted events of the operations in `rem`. -/
def events (rem : List (Fin ops.size)) : List (Ev ops.size) :=
  (rem.map (callEv ops) ++ rem.filterMap (retEv ops)).mergeSort Ev.le

/-- Remove the events of the operation whose invocation event is `e`. -/
def removeEv (ev : List (Ev ops.size)) (e : Ev ops.size) : List (Ev ops.size) :=
  match retEv ops e.idx with
  | some r => (ev.erase e).erase r
  | none => ev.erase e

/-- Split the events at the first response: the invocations before it (the candidates) and
its time (the earliest pending response), or `none` if no response remains. -/
def scan {n : Nat} : List (Ev n) → List (Ev n) → List (Ev n) × Option Nat
  | [], acc => (acc.reverse, none)
  | e :: rest, acc => if e.isRet then (acc.reverse, some e.time) else scan rest (e :: acc)

/-- A fixed pseudo-random value per operation (the SplitMix64 finaliser). -/
def zobrist {n : Nat} (x : Fin n) : UInt64 :=
  let z := (x.val.toUInt64 + 1) * 0x9E3779B97F4A7C15
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  z ^^^ (z >>> 31)

/-! ### Facts about events -/

theorem scan_mem {n : Nat} :
    ∀ (ev acc : List (Ev n)) (e : Ev n), e ∈ (scan ev acc).1 → e ∈ acc ∨ e ∈ ev := by
  intro ev
  induction ev with
  | nil => intro acc e h; simpa [scan] using h
  | cons x rest ih =>
    intro acc e h
    unfold scan at h
    split at h
    · exact Or.inl (by simpa using h)
    · rcases ih _ e h with h | h
      · rcases List.mem_cons.1 h with rfl | h
        · exact Or.inr (by simp)
        · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

theorem scan_none {n : Nat} :
    ∀ (ev acc : List (Ev n)), (scan ev acc).2 = none → ∀ e ∈ ev, e.isRet = false := by
  intro ev
  induction ev with
  | nil => intro _ _ e h; simp at h
  | cons x rest ih =>
    intro acc h e he
    unfold scan at h
    split at h
    · simp at h
    · rcases List.mem_cons.1 he with rfl | he
      · simpa using ‹¬ e.isRet = true›
      · exact ih _ h e he

theorem scan_some {n : Nat} :
    ∀ (ev acc : List (Ev n)) (m : Nat), (scan ev acc).2 = some m →
      ∃ pre r post, ev = pre ++ r :: post ∧ (∀ e ∈ pre, e.isRet = false) ∧ r.isRet = true ∧
        r.time = m ∧ ∀ e, e ∈ (scan ev acc).1 ↔ e ∈ acc ∨ e ∈ pre := by
  intro ev
  induction ev with
  | nil => intro _ _ h; simp [scan] at h
  | cons x rest ih =>
    intro acc m h
    unfold scan at h ⊢
    split
    · rename_i hx
      simp only [hx, ↓reduceIte, Option.some.injEq] at h
      exact ⟨[], x, rest, rfl, by simp, hx, h, by simp⟩
    · rename_i hx
      simp only [hx, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨pre, r, post, he, hpre, hr, ht, hmem⟩ := ih _ m h
      refine ⟨x :: pre, r, post, by simp [he], ?_, hr, ht, ?_⟩
      · intro e he'
        rcases List.mem_cons.1 he' with rfl | he'
        · simpa using hx
        · exact hpre e he'
      · intro e
        rw [hmem e]
        simp only [List.mem_cons]
        constructor
        · rintro ((rfl | h) | h)
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · rintro (h | rfl | h)
          · exact Or.inl (Or.inr h)
          · exact Or.inl (Or.inl rfl)
          · exact Or.inr h

theorem length_removeEv {ev : List (Ev ops.size)} {e : Ev ops.size} (he : e ∈ ev) :
    (removeEv ops ev e).length < ev.length := by
  have h1 : (ev.erase e).length < ev.length := by
    rw [List.length_erase_of_mem he]
    have := List.length_pos_of_mem he
    omega
  unfold removeEv
  split
  · exact Nat.lt_of_le_of_lt List.erase_sublist.length_le h1
  · exact h1

theorem callEv_genuine (x : Fin ops.size) : Genuine ops (callEv ops x) := Or.inl rfl

theorem genuine_call {e : Ev ops.size} (hg : Genuine ops e) (hr : e.isRet = false) :
    e = callEv ops e.idx := by
  rcases hg with h | h
  · exact h
  · unfold retEv at h
    rcases hret : (op ops e.idx).ret with _ | ⟨t, o⟩
    · simp [hret] at h
    · simp only [hret, Option.map_some, Option.some.injEq] at h
      rw [← h] at hr
      simp at hr

theorem genuine_ret {e : Ev ops.size} (hg : Genuine ops e) (hr : e.isRet = true) :
    ∃ o, (op ops e.idx).ret = some (e.time, o) := by
  rcases hg with h | h
  · rw [h] at hr; simp [callEv] at hr
  · unfold retEv at h
    rcases hret : (op ops e.idx).ret with _ | ⟨t, o⟩
    · simp [hret] at h
    · simp only [hret, Option.map_some, Option.some.injEq] at h
      exact ⟨o, by rw [← h]⟩

theorem retEv_of_ret {x : Fin ops.size} {t : Nat} {o : ο} (h : (op ops x).ret = some (t, o)) :
    retEv ops x = some ⟨t, true, x⟩ := by
  simp [retEv, h]

/-- The invariant of the fast search: `ev` lists, sorted and without repetition, exactly the
events of the operations in `rem`. -/
def EvInv (rem : List (Fin ops.size)) (ev : List (Ev ops.size)) : Prop :=
  rem.Nodup ∧ ev.Nodup ∧ ev.Pairwise (fun a b => Ev.le a b = true) ∧
    ∀ e, e ∈ ev ↔ e.idx ∈ rem ∧ Genuine ops e

theorem evInv_events {rem : List (Fin ops.size)} (hnd : rem.Nodup) :
    EvInv ops rem (events ops rem) := by
  refine ⟨hnd, ?_, List.pairwise_mergeSort Ev.le_trans Ev.le_total _, ?_⟩
  · refine (List.mergeSort_perm _ _).symm.nodup ?_
    rw [List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Pairwise.map _ (fun a b h e => h (congrArg Ev.idx e)) hnd
    · refine List.Pairwise.filterMap _ ?_ hnd
      intro a a' hne b hb b' hb' e
      simp only [retEv, Option.map_eq_some_iff] at hb hb'
      obtain ⟨_, _, rfl⟩ := hb
      obtain ⟨_, _, rfl⟩ := hb'
      exact hne (congrArg Ev.idx e)
    · intro a ha b hb e
      obtain ⟨x, _, rfl⟩ := List.mem_map.1 ha
      obtain ⟨y, _, hy⟩ := List.mem_filterMap.1 hb
      simp only [retEv, Option.map_eq_some_iff] at hy
      obtain ⟨_, _, rfl⟩ := hy
      simp [callEv] at e
  · intro e
    rw [events, List.mem_mergeSort, List.mem_append, List.mem_map, List.mem_filterMap]
    constructor
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, hr⟩)
      · exact ⟨hx, callEv_genuine ops x⟩
      · have : e.idx = x := by
          simp only [retEv, Option.map_eq_some_iff] at hr
          obtain ⟨_, _, rfl⟩ := hr
          rfl
        subst this
        exact ⟨hx, Or.inr hr⟩
    · rintro ⟨hx, hg | hg⟩
      · exact Or.inl ⟨e.idx, hx, hg.symm⟩
      · exact Or.inr ⟨e.idx, hx, hg⟩

theorem evInv_remove {rem : List (Fin ops.size)} {ev : List (Ev ops.size)} {e : Ev ops.size}
    (hI : EvInv ops rem ev) (he : e ∈ ev) (hcall : e.isRet = false) :
    EvInv ops (rem.erase e.idx) (removeEv ops ev e) := by
  obtain ⟨hnd, hevnd, hpw, hmem⟩ := hI
  have hgen := ((hmem e).1 he).2
  have hecall := genuine_call ops hgen hcall
  have hsub : (removeEv ops ev e).Sublist ev := by
    unfold removeEv
    split
    · exact List.erase_sublist.trans List.erase_sublist
    · exact List.erase_sublist
  refine ⟨hnd.erase _, ?_, hpw.sublist hsub, ?_⟩
  · unfold removeEv
    split
    · exact (hevnd.erase _).erase _
    · exact hevnd.erase _
  · intro e'
    rw [List.Nodup.mem_erase_iff hnd]
    -- an event of operation `e.idx` is either `e` or its response
    have hsame : e'.idx = e.idx → Genuine ops e' → e' = e ∨ retEv ops e.idx = some e' := by
      intro hidx hg
      rcases hg with h | h
      · left; rw [h, hecall, hidx]
      · right; rw [← hidx]; exact h
    unfold removeEv
    split
    · rename_i r hr
      have hrid : r.idx = e.idx := by
        simp only [retEv, Option.map_eq_some_iff] at hr
        obtain ⟨_, _, rfl⟩ := hr
        rfl
      rw [List.Nodup.mem_erase_iff (hevnd.erase _), List.Nodup.mem_erase_iff hevnd, hmem]
      constructor
      · rintro ⟨hne1, hne2, hidx, hg⟩
        refine ⟨⟨fun h => ?_, hidx⟩, hg⟩
        rcases hsame h hg with h' | h'
        · exact hne2 h'
        · rw [hr] at h'
          exact hne1 (Option.some.inj h').symm
      · rintro ⟨⟨hne, hidx⟩, hg⟩
        refine ⟨fun h => hne (h ▸ hrid), fun h => hne (h ▸ rfl), hidx, hg⟩
    · rename_i hr
      rw [List.Nodup.mem_erase_iff hevnd, hmem]
      constructor
      · rintro ⟨hne, hidx, hg⟩
        refine ⟨⟨fun h => ?_, hidx⟩, hg⟩
        rcases hsame h hg with h' | h'
        · exact hne h'
        · rw [hr] at h'
          cases h'
      · rintro ⟨⟨hne, hidx⟩, hg⟩
        exact ⟨fun h => hne (h ▸ rfl), hidx, hg⟩

/-- The first response's time is the earliest pending response. -/
theorem scan_minRet {rem : List (Fin ops.size)} {ev : List (Ev ops.size)}
    (hI : EvInv ops rem ev) : (scan ev []).2 = minRet ops rem := by
  obtain ⟨_, _, hpw, hmem⟩ := hI
  rcases hs : (scan ev []).2 with _ | m
  · symm
    rw [minRet_eq_none]
    intro i hi
    rcases hr : (op ops i).ret with _ | ⟨t, o⟩
    · rfl
    · have : (⟨t, true, i⟩ : Ev ops.size) ∈ ev :=
        (hmem _).2 ⟨hi, Or.inr (retEv_of_ret ops hr)⟩
      simpa using scan_none ev [] hs _ this
  · obtain ⟨pre, r, post, hev, hpre, hr, ht, -⟩ := scan_some ev [] m hs
    have hrin : r ∈ ev := by rw [hev]; simp
    obtain ⟨hridx, hrg⟩ := (hmem r).1 hrin
    obtain ⟨o, hro⟩ := genuine_ret ops hrg hr
    symm
    rw [minRet, List.min?_eq_some_iff]
    refine ⟨List.mem_filterMap.2 ⟨r.idx, hridx, by simp [hro, ht]⟩, ?_⟩
    intro b hb
    obtain ⟨i, hi, hib⟩ := List.mem_filterMap.1 hb
    rcases hret : (op ops i).ret with _ | ⟨t, o'⟩
    · simp [hret] at hib
    · simp only [hret, Option.map_some, Option.some.injEq] at hib
      subst hib
      have hin : (⟨t, true, i⟩ : Ev ops.size) ∈ ev :=
        (hmem _).2 ⟨hi, Or.inr (retEv_of_ret ops hret)⟩
      rw [hev, List.mem_append] at hin
      rcases hin with hin | hin
      · simpa using hpre _ hin
      · rw [hev, List.pairwise_append, List.pairwise_cons] at hpw
        rcases List.mem_cons.1 hin with he | he
        · rw [← he] at ht; simp at ht; omega
        · have := hpw.2.1.1 _ he
          simp only [Ev.le, hr, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
          omega

/-- The invocations before the first response are exactly those of the minimal operations. -/
theorem scan_cands {rem : List (Fin ops.size)} {ev : List (Ev ops.size)} {m : Nat}
    (hI : EvInv ops rem ev) (hs : (scan ev []).2 = some m) :
    (∀ e ∈ (scan ev []).1, e ∈ ev ∧ e.isRet = false) ∧
    ∀ x, callEv ops x ∈ (scan ev []).1 ↔ x ∈ rem ∧ (op ops x).call ≤ m := by
  obtain ⟨_, _, hpw, hmem⟩ := hI
  obtain ⟨pre, r, post, hev, hpre, hr, ht, hcs⟩ := scan_some ev [] m hs
  rw [hev, List.pairwise_append, List.pairwise_cons] at hpw
  refine ⟨fun e he => ?_, fun x => ?_⟩
  · have hepre : e ∈ pre := by simpa using (hcs e).1 he
    exact ⟨by rw [hev]; simp [hepre], hpre e hepre⟩
  · rw [hcs]
    simp only [List.not_mem_nil, false_or]
    constructor
    · intro hx
      have hin : callEv ops x ∈ ev := by rw [hev]; simp [hx]
      refine ⟨((hmem _).1 hin).1, ?_⟩
      have := hpw.2.2 _ hx r (by simp)
      simp only [Ev.le, callEv, ht, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
      omega
    · rintro ⟨hx, hc⟩
      have hin : callEv ops x ∈ ev := (hmem _).2 ⟨hx, callEv_genuine ops x⟩
      rw [hev, List.mem_append] at hin
      rcases hin with hin | hin
      · exact hin
      · rcases List.mem_cons.1 hin with he | he
        · rw [← he] at hr; simp [callEv] at hr
        · have := hpw.2.1.1 _ he
          simp only [Ev.le, callEv, hr, ht, Bool.or_eq_true, Bool.and_eq_true,
            decide_eq_true_eq] at this
          simp at this
          omega

/-! ### The fast memoised search -/

/-- List equality that stops as soon as the rest of both lists is the same object in memory.
Logically it is plain equality (`withPtrEq a b k h` is defined as `k ()`; the shortcut is
core Lean's runtime implementation of `withPtrEq`). Lists of remaining operations reached
along different paths share their tails, because `List.erase` keeps the tail after the
erased element, so a memo hit compares only the few elements near the front. -/
def listEqS {α : Type} [DecidableEq α] : (l₁ l₂ : List α) → {b : Bool // b = true ↔ l₁ = l₂}
  | [], [] => ⟨true, by simp⟩
  | [], _ :: _ => ⟨false, by simp⟩
  | _ :: _, [] => ⟨false, by simp⟩
  | a :: as, b :: bs =>
    ⟨withPtrEq (a :: as) (b :: bs) (fun _ => decide (a = b) && (listEqS as bs).1)
      (fun h => by
        simp only [List.cons.injEq] at h
        simp [h.1, (listEqS as bs).2.2 h.2]),
     by
      show (decide (a = b) && (listEqS as bs).1) = true ↔ _
      rw [Bool.and_eq_true, decide_eq_true_eq, (listEqS as bs).2, List.cons.injEq]⟩

/-- Memo keys: the configuration (remaining operations that returned, remaining operations
that did not, and the state) and its hash. -/
structure Key (n : Nat) (σ : Type) where
  zh : UInt64
  remR : List (Fin n)
  remP : List (Fin n)
  s : σ

/-- Keys are equal when all their fields are; the hash is compared first, the lists last. -/
def Key.beq {n : Nat} {σ : Type} [DecidableEq σ] (a b : Key n σ) : Bool :=
  decide (a.zh = b.zh) && decide (a.s = b.s) && (listEqS a.remR b.remR).1 &&
    (listEqS a.remP b.remP).1

instance {n : Nat} {σ : Type} [DecidableEq σ] : BEq (Key n σ) := ⟨Key.beq⟩

instance {n : Nat} {σ : Type} [DecidableEq σ] : LawfulBEq (Key n σ) where
  eq_of_beq {a b} h := by
    change Key.beq a b = true at h
    simp only [Key.beq, Bool.and_eq_true, decide_eq_true_eq, (listEqS _ _).2] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    cases a; cases b
    simp_all
  rfl {a} := by
    change Key.beq a a = true
    simp [Key.beq, (listEqS a.remR a.remR).2, (listEqS a.remP a.remP).2]

instance {n : Nat} {σ : Type} [Hashable σ] : Hashable (Key n σ) :=
  ⟨fun k => mixHash k.zh (hash k.s)⟩

variable [DecidableEq σ] [Hashable σ]

/-- The set of configurations known to fail. -/
abbrev Memo := Std.HashSet (Key ops.size σ)

/-- Candidate moves of operations that returned: each invocation before the first response,
with each state its operation can lead to (moves that are not kept are skipped). -/
def fcandsR (cs : List (Ev ops.size)) (s : σ) : List (Ev ops.size × σ) :=
  cs.flatMap fun e => ((succs M P ops s e.idx).filter (keep ops s e.idx)).map (e, ·)

/-- Candidate moves of operations that never returned: those invoked no later than `m`. -/
def fcandsP (remP : List (Fin ops.size)) (m : Nat) (s : σ) : List (Fin ops.size × σ) :=
  (remP.filter fun x => decide ((op ops x).call ≤ m)).flatMap
    fun x => ((succs M P ops s x).filter (keep ops s x)).map (x, ·)

omit [Hashable σ] in
theorem mem_fcandsP {remP : List (Fin ops.size)} {m : Nat} {s : σ} {x : Fin ops.size} {s' : σ} :
    (x, s') ∈ fcandsP M P ops remP m s ↔
      x ∈ remP ∧ (op ops x).call ≤ m ∧ s' ∈ succs M P ops s x ∧ keep ops s x s' = true := by
  simp only [fcandsP, List.mem_flatMap, List.mem_filter, List.mem_map, decide_eq_true_eq,
    Prod.mk.injEq]
  constructor
  · rintro ⟨y, ⟨hy, hc⟩, s'', ⟨hs, hk⟩, rfl, rfl⟩
    exact ⟨hy, hc, hs, hk⟩
  · rintro ⟨hy, hc, hs, hk⟩
    exact ⟨x, ⟨hy, hc⟩, s', ⟨hs, hk⟩, rfl, rfl⟩

set_option linter.unusedVariables false in
/-- **The executable search.** The remaining operations are split into those that returned
(`remR`, whose invocations and responses are in the sorted event list `ev`) and those that
never returned (`remP`, ordered by invocation). Moves of operations that never returned are
tried first, then moves of returned operations: the order of candidates does not affect the
answer, only how soon it is found (see `docs/DESIGN.md` for the measurements behind this
choice). `zh` is the configuration's hash, `s` the model state, `V` the memo of failed
configurations. -/
def fsearch (remR remP : List (Fin ops.size)) (ev : List (Ev ops.size)) (zh : UInt64) (s : σ)
    (V : Memo ops (σ := σ)) : Bool × Memo ops (σ := σ) :=
  if V.contains ⟨zh, remR, remP, s⟩ then (false, V)
  else
    match hs : scan ev [] with
    | (_, none) => (true, V)
    | (cs, some m) =>
      match anyThread (fcandsP M P ops remP m s).attach V
          (fun c V => fsearch remR (remP.erase c.1.1) ev (zh ^^^ zobrist c.1.1) c.1.2 V) with
      | (true, V') => (true, V')
      | (false, V') =>
        match anyThread (fcandsR M P ops cs s).attach V'
            (fun c V => fsearch (remR.erase c.1.1.idx) remP (removeEv ops ev c.1.1)
              (zh ^^^ zobrist c.1.1.idx) c.1.2 V) with
        | (true, V'') => (true, V'')
        | (false, V'') => (false, V''.insert ⟨zh, remR, remP, s⟩)
termination_by ev.length + remP.length
decreasing_by
  · have hx : c.1.1 ∈ remP := ((mem_fcandsP M P ops).1 c.2).1
    have := length_erase_lt hx
    omega
  · obtain ⟨e, he, hc⟩ := List.mem_flatMap.1 c.2
    obtain ⟨_, _, hce⟩ := List.mem_map.1 hc
    rw [← hce]
    have he' : e ∈ (scan ev []).1 := by rw [hs]; exact he
    rcases scan_mem ev [] e he' with h | h
    · simp at h
    · have := length_removeEv ops h
      dsimp only at this ⊢
      omega

/-- Every configuration in the memo is one from which `search` fails. -/
def MemoOK (V : Memo ops (σ := σ)) : Prop :=
  ∀ k : Key ops.size σ, V.contains k = true → search M P ops (k.remR ++ k.remP) k.s = false

theorem memoOK_empty : MemoOK M P ops ∅ := by
  intro k h
  simp at h

/-- The invariant of the fast search. -/
def FInv (remR remP : List (Fin ops.size)) (ev : List (Ev ops.size)) : Prop :=
  EvInv ops remR ev ∧ (remR ++ remP).Nodup ∧
    (∀ x ∈ remR, (op ops x).ret.isSome) ∧ (∀ x ∈ remP, (op ops x).ret = none)

omit [DecidableEq σ] [Hashable σ] in
theorem minRet_append_pending {remR remP : List (Fin ops.size)}
    (h : ∀ x ∈ remP, (op ops x).ret = none) : minRet ops (remR ++ remP) = minRet ops remR := by
  have : (remP.filterMap fun j => (op ops j).ret.map Prod.fst) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro x hx
    simp [h x hx]
  simp only [minRet, List.filterMap_append, this, List.append_nil]

theorem fsearch_eq :
    ∀ (n : Nat) (remR remP : List (Fin ops.size)) (ev : List (Ev ops.size)) (zh : UInt64)
      (s : σ) (V : Memo ops (σ := σ)),
      ev.length + remP.length = n → FInv ops remR remP ev → MemoOK M P ops V →
      (fsearch M P ops remR remP ev zh s V).1 = search M P ops (remR ++ remP) s ∧
        MemoOK M P ops (fsearch M P ops remR remP ev zh s V).2 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro remR remP ev zh s V hlen hI hV
    obtain ⟨hEv, hnd, hret, hpend⟩ := hI
    rw [fsearch]
    by_cases hc : V.contains ⟨zh, remR, remP, s⟩ = true
    · simp only [hc, ↓reduceIte]
      exact ⟨(hV _ hc).symm, hV⟩
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      have hmr := scan_minRet ops hEv
      rw [← minRet_append_pending ops (remR := remR) hpend] at hmr
      rw [search_eq]
      split
      · rename_i hs
        rw [hs] at hmr
        rw [← hmr]
        exact ⟨rfl, hV⟩
      · rename_i cs m hs
        rw [hs] at hmr
        rw [← hmr]
        simp only
        have hcs := scan_cands ops hEv (by rw [hs])
        rw [hs] at hcs
        obtain ⟨hcs1, hcs2⟩ := hcs
        have hndR : remR.Nodup := (List.nodup_append.1 hnd).1
        have hdisj := (List.nodup_append.1 hnd).2.2
        -- the two kinds of moves, as erasures from `remR ++ remP`
        have hR : ∀ x ∈ remR, (remR.erase x) ++ remP = (remR ++ remP).erase x :=
          fun x hx => (List.erase_append_left remP hx).symm
        have hP : ∀ x ∈ remP, remR ++ remP.erase x = (remR ++ remP).erase x :=
          fun x hx => (List.erase_append_right remP (fun h => hdisj x h x hx rfl)).symm
        -- recursive calls on returned operations
        have hrecR : ∀ c ∈ (fcandsR M P ops cs s).attach, ∀ V', MemoOK M P ops V' →
            (fsearch M P ops (remR.erase c.1.1.idx) remP (removeEv ops ev c.1.1)
                (zh ^^^ zobrist c.1.1.idx) c.1.2 V').1 =
              search M P ops ((remR ++ remP).erase c.1.1.idx) c.1.2 ∧
            MemoOK M P ops (fsearch M P ops (remR.erase c.1.1.idx) remP (removeEv ops ev c.1.1)
                (zh ^^^ zobrist c.1.1.idx) c.1.2 V').2 := by
          intro c _ V' hV'
          obtain ⟨e, he, hce⟩ := List.mem_flatMap.1 c.2
          obtain ⟨_, _, hce⟩ := List.mem_map.1 hce
          rw [← hce]
          obtain ⟨heev, hecall⟩ := hcs1 e he
          have hxR : e.idx ∈ remR := ((hEv.2.2.2 e).1 heev).1
          have hlt : (removeEv ops ev e).length + remP.length < n :=
            hlen ▸ (by have := length_removeEv ops heev; omega)
          rw [← hR _ hxR]
          refine ih _ hlt _ _ _ _ _ _ rfl ⟨evInv_remove ops hEv heev hecall, ?_, ?_, hpend⟩ hV'
          · rw [hR _ hxR]; exact hnd.erase _
          · exact fun y hy => hret y (List.mem_of_mem_erase hy)
        -- recursive calls on operations that never returned
        have hrecP : ∀ c ∈ (fcandsP M P ops remP m s).attach, ∀ V', MemoOK M P ops V' →
            (fsearch M P ops remR (remP.erase c.1.1) ev (zh ^^^ zobrist c.1.1) c.1.2 V').1 =
              search M P ops ((remR ++ remP).erase c.1.1) c.1.2 ∧
            MemoOK M P ops
              (fsearch M P ops remR (remP.erase c.1.1) ev (zh ^^^ zobrist c.1.1) c.1.2 V').2 := by
          intro c _ V' hV'
          have hxP : c.1.1 ∈ remP := ((mem_fcandsP M P ops).1 c.2).1
          have hlt : ev.length + (remP.erase c.1.1).length < n := by
            have := length_erase_lt hxP
            omega
          rw [← hP _ hxP]
          refine ih _ hlt _ _ _ _ _ _ rfl ⟨hEv, ?_, hret, ?_⟩ hV'
          · rw [hP _ hxP]; exact hnd.erase _
          · exact fun y hy => hpend y (List.mem_of_mem_erase hy)
        obtain ⟨h1, h2⟩ := anyThread_spec
          (fun (c : {x // x ∈ fcandsP M P ops remP m s}) =>
            search M P ops ((remR ++ remP).erase c.1.1) c.1.2)
          (MemoOK M P ops)
          (fun (c : {x // x ∈ fcandsP M P ops remP m s}) V =>
            fsearch M P ops remR (remP.erase c.1.1) ev (zh ^^^ zobrist c.1.1) c.1.2 V)
          _ hrecP V hV
        -- the fast candidates and `cands` lead to the same answer
        have hany : ((cands M P ops (remR ++ remP) s m).attach.any fun c =>
              search M P ops ((remR ++ remP).erase c.1.1) c.1.2) =
            (((fcandsR M P ops cs s).attach.any fun c =>
              search M P ops ((remR ++ remP).erase c.1.1.idx) c.1.2) ||
             ((fcandsP M P ops remP m s).attach.any fun c =>
              search M P ops ((remR ++ remP).erase c.1.1) c.1.2)) := by
          apply Bool.eq_iff_iff.2
          simp only [Bool.or_eq_true, List.any_eq_true, List.mem_attach, true_and,
            Subtype.exists]
          constructor
          · rintro ⟨⟨x, s'⟩, hc, hrec⟩
            obtain ⟨hx, hcall, hs', hk⟩ := (mem_cands M P ops).1 hc
            rcases List.mem_append.1 hx with hx | hx
            · left
              have he := (hcs2 x).2 ⟨hx, hcall⟩
              exact ⟨(callEv ops x, s'), List.mem_flatMap.2 ⟨callEv ops x, he,
                List.mem_map.2 ⟨s', List.mem_filter.2 ⟨hs', hk⟩, rfl⟩⟩, hrec⟩
            · right
              exact ⟨(x, s'), (mem_fcandsP M P ops).2 ⟨hx, hcall, hs', hk⟩, hrec⟩
          · rintro (⟨⟨e, s'⟩, hc, hrec⟩ | ⟨⟨x, s'⟩, hc, hrec⟩)
            · obtain ⟨e', he', hce⟩ := List.mem_flatMap.1 hc
              obtain ⟨s'', hs'', hce⟩ := List.mem_map.1 hce
              rw [List.mem_filter] at hs''
              simp only [Prod.mk.injEq] at hce
              obtain ⟨rfl, rfl⟩ := hce
              obtain ⟨heev, hecall⟩ := hcs1 e' he'
              have hgen := ((hEv.2.2.2 e').1 heev).2
              have heq := genuine_call ops hgen hecall
              have hx := (hcs2 e'.idx).1 (heq ▸ he')
              exact ⟨(e'.idx, s''), (mem_cands M P ops).2
                ⟨List.mem_append_left _ hx.1, hx.2, hs''.1, hs''.2⟩, hrec⟩
            · obtain ⟨hx, hcall, hs', hk⟩ := (mem_fcandsP M P ops).1 hc
              exact ⟨(x, s'), (mem_cands M P ops).2
                ⟨List.mem_append_right _ hx, hcall, hs', hk⟩, hrec⟩
        rw [hany, Bool.or_comm]
        rcases hat : anyThread (fcandsP M P ops remP m s).attach V
            (fun c V => fsearch M P ops remR (remP.erase c.1.1) ev (zh ^^^ zobrist c.1.1)
              c.1.2 V) with ⟨b, V'⟩
        rw [hat] at h1 h2
        simp only at h1 h2
        cases b with
        | true => exact ⟨by rw [← h1]; rfl, h2⟩
        | false =>
          dsimp only
          obtain ⟨h3, h4⟩ := anyThread_spec
            (fun (c : {x // x ∈ fcandsR M P ops cs s}) =>
              search M P ops ((remR ++ remP).erase c.1.1.idx) c.1.2)
            (MemoOK M P ops)
            (fun (c : {x // x ∈ fcandsR M P ops cs s}) V =>
              fsearch M P ops (remR.erase c.1.1.idx) remP (removeEv ops ev c.1.1)
                (zh ^^^ zobrist c.1.1.idx) c.1.2 V)
            _ hrecR V' h2
          rcases hat2 : anyThread (fcandsR M P ops cs s).attach V'
              (fun c V => fsearch M P ops (remR.erase c.1.1.idx) remP (removeEv ops ev c.1.1)
                (zh ^^^ zobrist c.1.1.idx) c.1.2 V) with ⟨b2, V''⟩
          rw [hat2] at h3 h4
          simp only at h3 h4
          rw [← h1, ← h3]
          cases b2 with
          | true => exact ⟨rfl, h4⟩
          | false =>
            refine ⟨rfl, ?_⟩
            intro k hin
            rw [Std.HashSet.contains_insert] at hin
            rcases Bool.or_eq_true_iff.1 hin with heq | hin
            · have heq : (⟨zh, remR, remP, s⟩ : Key ops.size σ) = k := LawfulBEq.eq_of_beq heq
              subst heq
              show search M P ops (remR ++ remP) s = false
              rw [search_eq, ← hmr]
              simp only
              rw [hany, Bool.or_comm, ← h1, ← h3]
              rfl
            · exact h4 k hin

end Search

end Linproof
