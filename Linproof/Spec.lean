/-!
# The trusted specification

**This is the only file you have to read and agree with to trust a verdict of `linproof`.**
Every other file under `Linproof/` either is proved correct against the definitions below
(the checker, the locality theorem) or is plain input/output code (parsing and printing,
listed as trusted in the README).

The file uses nothing beyond core Lean. Two library notions appear:

* `l.Perm c` — `l` is a reordering of `c` (same elements, same multiplicities);
* `l.Pairwise R` — `R a b` holds whenever `a` occurs before `b` in `l`.

Part 1 defines linearizability for an arbitrary deterministic sequential specification.
Part 2 defines the specifications that the command-line tool checks against.
-/

namespace Linproof

/-! ## Part 1: histories and linearizability -/

/-- A sequential specification, given as a deterministic state machine.
`step s i o = some s'` means: in state `s`, an operation with input `i` may return output
`o`, and the object is then in state `s'`. `step s i o = none` means that output is
impossible in state `s`. -/
structure Model (State Input Output : Type) where
  init : State
  step : State → Input → Output → Option State

/-- One operation of a concurrent history. It was invoked at time `call` with argument
`input`. `ret = some (t, o)` records that it returned output `o` at time `t`. `ret = none`
means no response was observed (the client crashed or timed out): the operation may or may
not have taken effect. -/
structure Op (Input Output : Type) where
  call : Nat
  input : Input
  ret : Option (Nat × Output)

variable {State Input Output : Type}

/-- Real-time order: `a` returned before `b` was invoked. The comparison is strict, so two
operations whose intervals touch (`a` returns at the instant `b` is invoked) are concurrent. -/
def precedes (a b : Op Input Output) : Prop :=
  match a.ret with
  | some (t, _) => t < b.call
  | none => False

/-- A history is well formed when no operation returns before it is invoked. -/
def WellFormed (h : List (Op Input Output)) : Prop :=
  ∀ op ∈ h, ∀ t o, op.ret = some (t, o) → op.call ≤ t

/-- `Completion h c`: `c` lists the operations of `h` that take effect, in history order,
each paired with the output it produced. An operation that returned is kept, with the output
that was observed. An operation that never returned is either kept, with any output, or
dropped. This is Herlihy and Wing's "append responses to some pending invocations and
remove the others". -/
inductive Completion : List (Op Input Output) → List (Op Input Output × Output) → Prop
  | nil : Completion [] []
  | returned {op h c t o} : op.ret = some (t, o) → Completion h c →
      Completion (op :: h) ((op, o) :: c)
  | tookEffect {op h c} (o : Output) : op.ret = none → Completion h c →
      Completion (op :: h) ((op, o) :: c)
  | noEffect {op h c} : op.ret = none → Completion h c → Completion (op :: h) c

/-- Running the operations of the list one after another, starting in state `s`, is allowed
by the specification. -/
def Legal (M : Model State Input Output) : State → List (Input × Output) → Prop
  | _, [] => True
  | s, (i, o) :: rest => ∃ s', M.step s i o = some s' ∧ Legal M s' rest

/-- **Linearizability.** The history `h` is linearizable with respect to `M` when some
completion `c` of `h` can be arranged in a sequence `l` that

* respects real-time order: no operation is placed before an operation that returned before
  it was invoked, and
* is accepted by the sequential specification from its initial state. -/
def Linearizable (M : Model State Input Output) (h : List (Op Input Output)) : Prop :=
  ∃ (c l : List (Op Input Output × Output)), Completion h c ∧ l.Perm c ∧
    l.Pairwise (fun a b => ¬ precedes b.1 a.1) ∧
    Legal M M.init (l.map fun p => (p.1.input, p.2))

/-! ## Part 2: the specifications checked by the command-line tool -/

/-- A key-value store whose keys hold independent objects, each specified by `M`. The state
maps every key to the state of its object; an input is a key and an input for that key's
object. -/
def Keyed (K : Type) [DecidableEq K] (M : Model State Input Output) :
    Model (K → State) (K × Input) Output where
  init := fun _ => M.init
  step f ki o := (M.step (f ki.1) ki.2 o).map fun s' k => if k = ki.1 then s' else f k

/-- Register contents: JSON `null`, an integer or a string. -/
inductive Val where
  | null
  | int (i : Int)
  | str (s : String)
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- Operations on a register. `cas e n` sets the register to `n` if it holds `e`. -/
inductive RegInput where
  | read
  | write (v : Val)
  | cas (expected new : Val)
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- Responses of a register: the value read, `ok`, or `fail` for a compare-and-set that did
not match. -/
inductive RegOutput where
  | value (v : Val)
  | ok
  | fail
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- A compare-and-set register holding `init` at the start (`null` by default, which is how
a Jepsen register test sees a key that does not exist yet). -/
def casRegister (init : Val := .null) : Model Val RegInput RegOutput where
  init := init
  step s i o :=
    match i, o with
    | .read, .value v => if v = s then some s else none
    | .write v, .ok => some v
    | .cas e n, .ok => if s = e then some n else none
    | .cas e _, .fail => if s = e then none else some s
    | _, _ => none

/-- A read/write register: the compare-and-set register without `cas`. -/
def register (init : Val := .null) : Model Val RegInput RegOutput where
  init := init
  step s i o :=
    match i, o with
    | .read, .value v => if v = s then some s else none
    | .write v, .ok => some v
    | _, _ => none

/-- Operations on one key of the string key-value store: `get`, `put` (overwrite) and
`append` (concatenate). This is the store of Porcupine's key-value tests. -/
inductive KVInput where
  | get
  | put (v : String)
  | append (v : String)
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- Responses of the key-value store: the string read by `get`, or `ok`. -/
inductive KVOutput where
  | value (v : String)
  | ok
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- One key of the string key-value store. A key that was never written reads as `""`. -/
def kvCell : Model String KVInput KVOutput where
  init := ""
  step s i o :=
    match i, o with
    | .get, .value v => if v = s then some s else none
    | .put v, .ok => some v
    | .append v, .ok => some (s ++ v)
    | _, _ => none

/-- The string key-value store: one `kvCell` per key. -/
def kvStore : Model (String → String) (String × KVInput) KVOutput :=
  Keyed String kvCell

end Linproof
