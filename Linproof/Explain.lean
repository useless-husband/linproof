import Linproof.Checker

/-!
# Explaining a violation (not verified)

When the checker answers "not linearizable", the tool runs this second search to say *why*.
It explores the same configurations as `fsearch` and remembers the deepest one: the longest
sequence of operations it could linearize (counting operations that returned), the model
state after it, and the operations that real-time order allowed next. At that point none of
the operations that returned can be applied, otherwise the search would have gone deeper.

This is diagnostics only. It is not covered by the theorems, and the verdict never depends on
it: `Main.lean` runs it after the verified checker has answered. It is a total function
(same termination argument as `fsearch`).
-/

namespace Linproof

namespace Search

variable {σ ι ο : Type} (M : Model σ ι ο) (P : PendingSteps M) (ops : Array (Op ι ο))
variable [DecidableEq σ] [Hashable σ]

/-- The deepest configuration found so far. -/
structure Deepest (n : Nat) (σ : Type) where
  /-- Operations linearized that had returned. -/
  depth : Nat
  /-- The partial linearization, most recent first: each operation with the state after it. -/
  path : List (Fin n × σ)
  /-- The state after the partial linearization. -/
  state : σ
  /-- The operations that real-time order allows next. -/
  next : List (Fin n)

set_option linter.unusedVariables false in
/-- `fsearch` that also records the deepest configuration. -/
def esearch (remR remP : List (Fin ops.size)) (ev : List (Ev ops.size)) (zh : UInt64) (s : σ)
    (path : List (Fin ops.size × σ)) (depth : Nat)
    (st : Memo ops (σ := σ) × Deepest ops.size σ) :
    Bool × (Memo ops (σ := σ) × Deepest ops.size σ) :=
  if st.1.contains ⟨zh, remR, remP, s⟩ then (false, st)
  else
    match hs : scan ev [] with
    | (_, none) => (true, st)
    | (cs, some m) =>
      let st :=
        if depth > st.2.depth || (depth == st.2.depth && st.2.path.isEmpty) then
          (st.1, { depth, path, state := s,
                   next := cs.map (·.idx) ++ remP.filter fun x => decide ((op ops x).call ≤ m) })
        else st
      match anyThread (fcandsR M P ops cs s).attach st
          (fun c st => esearch (remR.erase c.1.1.idx) remP (removeEv ops ev c.1.1)
            (zh ^^^ zobrist c.1.1.idx) c.1.2 ((c.1.1.idx, c.1.2) :: path) (depth + 1) st) with
      | (true, st') => (true, st')
      | (false, st') =>
        match anyThread (fcandsP M P ops remP m s).attach st'
            (fun c st => esearch remR (remP.erase c.1.1) ev (zh ^^^ zobrist c.1.1) c.1.2
              ((c.1.1, c.1.2) :: path) depth st) with
        | (true, st'') => (true, st'')
        | (false, st'') => (false, (st''.1.insert ⟨zh, remR, remP, s⟩, st''.2))
termination_by ev.length + remP.length
decreasing_by
  · obtain ⟨e, he, hc⟩ := List.mem_flatMap.1 c.2
    obtain ⟨_, _, hce⟩ := List.mem_map.1 hc
    rw [← hce]
    have he' : e ∈ (scan ev []).1 := by rw [hs]; exact he
    rcases scan_mem ev [] e he' with h | h
    · simp at h
    · have := length_removeEv ops h
      dsimp only at this ⊢
      omega
  · have hx : c.1.1 ∈ remP := ((mem_fcandsP M P ops).1 c.2).1
    have := length_erase_lt hx
    omega

end Search

/-- The deepest configuration the search reaches on a history, or `none` if the history is
linearizable. -/
def explain {σ ι ο : Type} [DecidableEq σ] [Hashable σ] (M : Model σ ι ο) (P : PendingSteps M)
    (h : List (Op ι ο)) : Option (Search.Deepest h.toArray.size σ) :=
  let ops := h.toArray
  let remR := startRemR ops
  let start : Search.Deepest ops.size σ := { depth := 0, path := [], state := M.init, next := [] }
  match Search.esearch M P ops remR (startRemP ops) (Search.events ops remR) 0 M.init [] 0
      (∅, start) with
  | (true, _) => none
  | (false, (_, d)) => some d

end Linproof
