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

def returned (x : Fin ops.size) : Bool := (op ops x).ret.isSome

set_option linter.unusedVariables false in
/-- `fsearch` that also records the deepest configuration. -/
def esearch (rem : List (Fin ops.size)) (ev : List (Ev ops.size)) (zh : UInt64) (s : σ)
    (path : List (Fin ops.size × σ)) (depth : Nat)
    (st : Memo ops (σ := σ) × Deepest ops.size σ) :
    Bool × (Memo ops (σ := σ) × Deepest ops.size σ) :=
  if st.1.contains ⟨zh, rem, s⟩ then (false, st)
  else
    match hs : scan ev [] with
    | (_, none) => (true, st)
    | (cs, some _) =>
      let st :=
        if depth > st.2.depth || (depth == st.2.depth && st.2.path.isEmpty) then
          (st.1, { depth, path, state := s, next := cs.map (·.idx) })
        else st
      match anyThread (fcands M P ops cs s).attach st
          (fun c st => esearch (rem.erase c.1.1.idx) (removeEv ops ev c.1.1)
            (zh ^^^ zobrist c.1.1.idx) c.1.2 ((c.1.1.idx, c.1.2) :: path)
            (if returned ops c.1.1.idx then depth + 1 else depth) st) with
      | (true, st') => (true, st')
      | (false, st') => (false, (st'.1.insert ⟨zh, rem, s⟩, st'.2))
termination_by ev.length
decreasing_by
  obtain ⟨e, he, hc⟩ := List.mem_flatMap.1 c.2
  obtain ⟨_, _, hce⟩ := List.mem_map.1 hc
  rw [← hce]
  have he' : e ∈ (scan ev []).1 := by rw [hs]; exact he
  rcases scan_mem ev [] e he' with h | h
  · simp at h
  · exact length_removeEv ops h

end Search

/-- The deepest configuration the search reaches on a history, or `none` if the history is
linearizable. -/
def explain {σ ι ο : Type} [DecidableEq σ] [Hashable σ] (M : Model σ ι ο) (P : PendingSteps M)
    (h : List (Op ι ο)) : Option (Search.Deepest h.toArray.size σ) :=
  let ops := h.toArray
  let rem := startRem ops
  let start : Search.Deepest ops.size σ := { depth := 0, path := [], state := M.init, next := [] }
  match Search.esearch M P ops rem (Search.events ops rem) 0 M.init [] 0 (∅, start) with
  | (true, _) => none
  | (false, (_, d)) => some d

end Linproof
