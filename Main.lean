import Linproof

/-!
# `linproof` command-line tool (trusted glue)

Reads histories, runs the verified checker and prints the verdicts. The decision itself is
`Linproof.check` / `Linproof.checkKeyed` (through `checkWithStats` and `checkKeyedReport`,
which return the same verdicts plus statistics, by definition), covered by `check_iff` and
`checkKeyed_iff`. This file only parses arguments, reads files and prints. The explanation
printed for a violation comes from `Linproof.explain`, which is diagnostics and not verified.
-/

open Linproof

def version : String := "0.1.0"

def usage : String :=
"linproof — a verified linearizability checker

usage:
  linproof check [--model M] [--verbose] [--quiet] [--jobs N] [--all-keys] FILE...
  linproof version

models:
  register       read/write register (values: null, integers, strings; starts at null)
  cas-register   register with compare-and-set (default)
  kv             string key-value store with get/put/append (every op needs a \"key\")

Operations with a \"key\" field are checked per key (locality theorem). FILE may be - for
standard input. The history format is described in the README.

options:
  --verbose, -v  print the whole partial linearization of a violation, not its end
  --quiet, -q    print one line per file: \"FILE: linearizable\" or \"FILE: not linearizable\"
  --no-memo      use the plain, unmemoised search (also verified; exponential, for testing)
  --jobs N, -j N check up to N keys in parallel (default 4)
  --all-keys     check every key; by default a keyed history stops at the first key that
                 is not linearizable, which already decides the verdict

exit status: 0 all linearizable, 1 some history not linearizable,
             2 usage, input or well-formedness error"

structure Options where
  model : String := "cas-register"
  files : Array String := #[]
  quiet : Bool := false
  verbose : Bool := false
  noMemo : Bool := false
  jobs : Nat := 4
  allKeys : Bool := false

def parseOptions : List String → Options → Except String Options
  | [], o => .ok o
  | "--model" :: m :: rest, o => parseOptions rest { o with model := m }
  | "--quiet" :: rest, o => parseOptions rest { o with quiet := true }
  | "-q" :: rest, o => parseOptions rest { o with quiet := true }
  | "--verbose" :: rest, o => parseOptions rest { o with verbose := true }
  | "-v" :: rest, o => parseOptions rest { o with verbose := true }
  | "--no-memo" :: rest, o => parseOptions rest { o with noMemo := true }
  | "--all-keys" :: rest, o => parseOptions rest { o with allKeys := true }
  | "--jobs" :: n :: rest, o | "-j" :: n :: rest, o =>
    match n.toNat? with
    | some j => if j ≥ 1 then parseOptions rest { o with jobs := j } else .error "--jobs needs at least 1"
    | none => .error s!"--jobs needs a number, not {n}"
  | f :: rest, o =>
    if f.startsWith "-" && f != "-" then .error s!"unknown option {f}"
    else parseOptions rest { o with files := o.files.push f }

/-- How to print operations and states of a model. -/
structure Describe (σ ι ο : Type) where
  /-- An operation, with its output if it returned. -/
  op : ι → Option ο → String
  state : σ → String
  /-- Why an operation that returned `o` cannot take effect in state `s`. -/
  whyNot : σ → ι → ο → String
  /-- What the state is, for sentences such as "the register holds 3". -/
  object : String

def regDescribe : Describe Val RegInput RegOutput where
  op i o :=
    match i, o with
    | .read, some (.value v) => s!"read -> {History.describeVal v}"
    | .read, _ => "read"
    | .write v, _ => s!"write {History.describeVal v}"
    | .cas e n, some .ok => s!"cas {History.describeVal e} -> {History.describeVal n}: ok"
    | .cas e n, some .fail => s!"cas {History.describeVal e} -> {History.describeVal n}: fail"
    | .cas e n, _ => s!"cas {History.describeVal e} -> {History.describeVal n}"
  state := History.describeVal
  whyNot s i o :=
    match i, o with
    | .read, .value v => s!"it read {History.describeVal v}, but the register holds {History.describeVal s}"
    | .cas e _, .ok => s!"it succeeded, but the register holds {History.describeVal s}, not {History.describeVal e}"
    | .cas e _, .fail => s!"it failed, but the register holds {History.describeVal e}, so it would succeed"
    | _, _ => "not possible in this state"
  object := "register"

def kvDescribe : Describe String KVInput KVOutput where
  op i o :=
    match i, o with
    | .get, some (.value v) => s!"get -> {Json.quote v}"
    | .get, _ => "get"
    | .put v, _ => s!"put {Json.quote v}"
    | .append v, _ => s!"append {Json.quote v}"
  state := Json.quote
  whyNot s i o :=
    match i, o with
    | .get, .value v => s!"it read {Json.quote v}, but the key holds {Json.quote s}"
    | _, _ => "not possible in this state"
  object := "key"

def fmtMs (ns : Nat) : String :=
  let ms := ns / 1000000
  let frac := (ns / 10000) % 100
  s!"{ms}.{if frac < 10 then "0" else ""}{frac} ms"

def describeLine {σ ι ο : Type} (D : Describe σ ι ο) (m : History.Meta) (op : Op ι ο) : String :=
  let proc := match m.process with
    | some p => s!" process {p}"
    | none => ""
  let span := match op.ret with
    | some (t, _) => s!"[{op.call}, {t}]"
    | none => s!"[{op.call}, -]"
  s!"line {m.line}{proc}: {D.op op.input (op.ret.map (·.2))} {span}"

/-- Print why a history (or one key's history) is not linearizable. Diagnostics only. -/
def printExplanation {σ ι ο : Type} [DecidableEq σ] [Hashable σ]
    (M : Model σ ι ο) (P : PendingSteps M) (D : Describe σ ι ο) (verbose : Bool)
    (sub : Array (History.Meta × Op ι ο)) (indent : String) : IO Unit := do
  let h := sub.toList.map (·.2)
  match explain M P h with
  | none =>
    IO.println s!"{indent}(no explanation: the diagnostic search did not find the violation)"
  | some d =>
    let returned := (h.filter (·.ret.isSome)).length
    let path := d.path.reverse
    IO.println s!"{indent}The longest partial linearization found places {d.depth} of the {returned} operations that returned."
    let shown := if verbose then path else path.drop (path.length - 8)
    if shown.length < path.length then
      IO.println s!"{indent}Its last {shown.length} steps (--verbose shows all {path.length}):"
    else if !path.isEmpty then
      IO.println s!"{indent}Its steps:"
    for (x, s) in shown do
      let some (m, op) := sub[x.val]? | continue
      let note := if op.ret.isNone then " (never returned; takes effect here)" else ""
      IO.println s!"{indent}  {describeLine D m op}{note}   => {D.state s}"
    IO.println s!"{indent}Then the {D.object} holds {D.state d.state}, and no operation that real-time order allows next can follow:"
    for x in d.next do
      let some (m, op) := sub[x.val]? | continue
      match op.ret with
      | some (_, o) =>
        IO.println s!"{indent}  {describeLine D m op}: {D.whyNot d.state op.input o}"
      | none => pure ()

/-- Outcome of checking one key (or the whole history when it has no keys). -/
structure KeyResult where
  key : Option String
  ops : Nat
  ok : Bool
  configs : Nat

inductive Outcome where
  | linearizable
  | notLinearizable
  | error

/-- Check the keys of a keyed history, at most `jobs` at a time. Key `k`'s verdict is
`check M P (project k kh)` (through `checkWithStats`), and the history is linearizable iff all
of them are `true`: that is `checkKeyed`, covered by `checkKeyed_iff`. Unless `all` is set,
stop at the first key that is not linearizable (its verdict decides the history's). Returns
the results that finished and whether every key was checked. Tasks still running when it
stops cannot be cancelled (they are pure); `main` exits the process when it is done. -/
def checkKeysParallel {σ ι ο : Type} [DecidableEq σ] [Hashable σ]
    (M : Model σ ι ο) (P : PendingSteps M) (jobs : Nat) (all noMemo : Bool)
    (kh : List (Op (String × ι) ο)) : IO (Array (String × Bool × Nat) × Bool) := do
  let keys := (keysOf kh).toArray
  let work (k : String) : Unit → String × Bool × Nat := fun _ =>
    if noMemo then (k, checkUnmemoised M P (project k kh), 0)
    else (k, checkWithStats M P (project k kh))
  let mut running : List (Task (String × Bool × Nat)) := []
  let mut next := 0
  let mut results : Array (String × Bool × Nat) := #[]
  -- every round finishes at least one task, so `keys.size + 1` rounds are enough
  for _ in [0:keys.size + 1] do
    while running.length < jobs && next < keys.size do
      running := running ++ [Task.spawn (work keys[next]!)]
      next := next + 1
    match h : running with
    | [] => break
    | t :: ts =>
      let _ ← IO.waitAny (t :: ts)
      let mut still := []
      for task in running do
        if ← IO.hasFinished task then results := results.push task.get
        else still := still ++ [task]
      running := still
      if !all && results.any (!·.2.1) then break
  return (results, results.size == keys.size)

/-- Evaluate a value before continuing (keeps the timing honest). -/
@[noinline] def forceIO {α : Type} (a : α) : IO α := pure a

/-- Check a history of model `M`, keyed or not, and print the result. -/
def runModel {σ ι ο : Type} [DecidableEq σ] [Hashable σ]
    (M : Model σ ι ο) (P : PendingSteps M) (D : Describe σ ι ο) (opts : Options)
    (file name : String) (lines : Array (History.Meta × Op ι ο)) (requireKeys : Bool) :
    IO Outcome := do
  let ops := lines.toList.map (·.2)
  let keyed := requireKeys || lines.any (·.1.key.isSome)
  if keyed then
    if let some (m, _) := lines.find? (·.1.key.isNone) then
      IO.eprintln s!"{file}: line {m.line}: every operation needs a \"key\" in a keyed history"
      return .error
  -- Well-formedness is decided by the verified `isWellFormed` before checking.
  if !isWellFormed ops then
    let bad := lines.find? fun (_, op) => match op.ret with
      | some (t, _) => op.call > t
      | none => false
    match bad with
    | some (m, op) =>
      IO.eprintln s!"{file}: line {m.line}: the operation returns before it is invoked (call {op.call})"
    | none => IO.eprintln s!"{file}: the history is not well formed"
    return .error
  let t0 ← IO.monoNanosNow
  -- The verdict `allOk` is computed by a verified function: `check` (through
  -- `checkWithStats`, whose first component is `check` by definition), `checkKeyed` (through
  -- `checkKeyedReport`, likewise), or their unmemoised counterparts with `--no-memo`.
  let kh : List (Op (String × ι) ο) :=
    lines.toList.map fun (m, op) =>
      { call := op.call, input := (m.key.getD "", op.input), ret := op.ret }
  let (allOk, complete, results) ← do
    if keyed then
      let (rs, complete) ← checkKeysParallel M P opts.jobs opts.allKeys opts.noMemo kh
      -- linearizable iff every key was checked and every key's verdict is `true`
      let ok := complete && rs.all (·.2.1)
      pure (ok, complete, rs.toList.map fun (k, ok, configs) =>
        ({ key := some k, ops := (project k kh).length, ok, configs } : KeyResult))
    else
      let (ok, configs) ← forceIO <| if opts.noMemo then (checkUnmemoised M P ops, 0)
        else checkWithStats M P ops
      pure (ok, true, [({ key := none, ops := ops.length, ok, configs } : KeyResult)])
  let t1 ← IO.monoNanosNow
  let configs := results.foldl (· + ·.configs) 0
  if opts.quiet then
    IO.println s!"{file}: {if allOk then "linearizable" else "not linearizable"}"
  else
    let pending := (ops.filter (·.ret.isNone)).length
    let keysNote := if keyed then s!", {(keysOf kh).length} keys" else ""
    IO.println s!"{file}: {ops.length} operations ({pending} never returned){keysNote}, model {name}"
    let stats := if opts.noMemo then "unmemoised" else s!"{configs} configurations ruled out"
    IO.println s!"{if allOk then "LINEARIZABLE" else "NOT LINEARIZABLE"} ({fmtMs (t1 - t0)}, {stats})"
    if !allOk then
      if keyed then
        let bad := results.filter (!·.ok)
        let nkeys := (keysOf kh).length
        if complete then
          IO.println s!"{bad.length} of {nkeys} keys are not linearizable."
        else
          IO.println s!"Stopped at the first key that is not linearizable ({results.length} of {nkeys} keys checked; --all-keys checks every key)."
        for r in bad do
          let k := r.key.getD ""
          IO.println s!"\nkey {Json.quote k} ({r.ops} operations):"
          let sub := lines.filter (·.1.key == some k)
          printExplanation M P D opts.verbose sub "  "
      else
        IO.println ""
        printExplanation M P D opts.verbose lines ""
  return (if allOk then .linearizable else .notLinearizable)

def readInput (file : String) : IO String :=
  if file = "-" then do
    let stdin ← IO.getStdin
    let mut acc := ""
    repeat
      let line ← stdin.getLine
      if line.isEmpty then break
      acc := acc ++ line
    return acc
  else IO.FS.readFile file

def checkFile (opts : Options) (file : String) : IO Outcome := do
  let text ← try readInput file
    catch e => IO.eprintln s!"cannot read {file}: {e}"; return .error
  match opts.model with
  | "register" | "cas-register" =>
    match History.parseLines History.parseRegOp text with
    | .error e => IO.eprintln s!"{file}: {e}"; return .error
    | .ok lines =>
      if opts.model = "register" then
        if let some (m, _) := lines.find? (fun (_, op) => match op.input with
            | .cas _ _ => true
            | _ => false) then
          IO.eprintln s!"{file}: line {m.line}: cas is not an operation of the register model (use --model cas-register)"
          return .error
        runModel (register .null) (registerSteps .null) regDescribe opts file "register" lines false
      else
        runModel (casRegister .null) (casRegisterSteps .null) regDescribe opts file
          "cas-register" lines false
  | "kv" =>
    match History.parseLines History.parseKVOp text with
    | .error e => IO.eprintln s!"{file}: {e}"; return .error
    | .ok lines => runModel kvCell kvCellSteps kvDescribe opts file "kv" lines true
  | other => IO.eprintln s!"unknown model {other} (expected register, cas-register or kv)"; return .error

def runCheck (opts : Options) : IO UInt32 := do
  if opts.files.isEmpty then
    IO.eprintln usage
    return 2
  let mut status : UInt32 := 0
  for file in opts.files do
    match ← checkFile opts file with
    | .linearizable => pure ()
    | .notLinearizable => if status == 0 then status := 1
    | .error => status := 2
  return status

def main (args : List String) : IO UInt32 := do
  match args with
  | ["version"] | ["--version"] => IO.println s!"linproof {version}"; return 0
  | ["help"] | ["--help"] | ["-h"] => IO.println usage; return 0
  | "check" :: rest =>
    match parseOptions rest {} with
    | .ok opts =>
      let status ← runCheck opts
      -- Key checks still running after a violation was found are not needed; exiting the
      -- process stops them.
      IO.Process.exit status.toUInt8
    | .error e => IO.eprintln s!"{e}\n\n{usage}"; return 2
  | _ => IO.eprintln usage; return 2
