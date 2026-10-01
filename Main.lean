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
  linproof check [--model M] [--verbose] [--quiet] [--jobs N] [--all-keys] [--timeout S] FILE...
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
  --timeout S    give up on a file after S seconds and report it as unknown (exit status 3)

exit status: 0 all linearizable, 1 some history not linearizable,
             2 usage, input or well-formedness error, 3 some history unknown (time limit)"

structure Options where
  model : String := "cas-register"
  files : Array String := #[]
  quiet : Bool := false
  verbose : Bool := false
  noMemo : Bool := false
  jobs : Nat := 4
  allKeys : Bool := false
  timeout : Option Nat := none

def parseOptions : List String → Options → Except String Options
  | [], o => .ok o
  | "--model" :: m :: rest, o => parseOptions rest { o with model := m }
  | "--quiet" :: rest, o => parseOptions rest { o with quiet := true }
  | "-q" :: rest, o => parseOptions rest { o with quiet := true }
  | "--verbose" :: rest, o => parseOptions rest { o with verbose := true }
  | "-v" :: rest, o => parseOptions rest { o with verbose := true }
  | "--no-memo" :: rest, o => parseOptions rest { o with noMemo := true }
  | "--all-keys" :: rest, o => parseOptions rest { o with allKeys := true }
  | "--timeout" :: n :: rest, o =>
    match n.toNat? with
    | some t => if t ≥ 1 then parseOptions rest { o with timeout := some t }
                else .error "--timeout needs at least 1 second"
    | none => .error s!"--timeout needs a number of seconds, not {n}"
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

/-- A task that finishes when the time limit passes, or `none` without a limit. It runs on
its own thread so that it is not queued behind the checks. -/
def startTimer (timeout : Option Nat) : IO (Option (Task Unit)) :=
  match timeout with
  | none => pure none
  | some s => do
    let t ← IO.asTask (prio := .dedicated) (IO.sleep (s * 1000).toUInt32)
    pure (some (t.map fun _ => ()))

/-- Wait until one of the tasks finishes (returning its value) or the timer does (`none`). -/
def waitFirst {α : Type} (timer : Option (Task Unit)) (t : Task α) (ts : List (Task α)) :
    IO (Option α) :=
  match timer with
  | none => some <$> IO.waitAny (t :: ts)
  | some tm => IO.waitAny ((tm.map fun _ => none) :: t.map some :: ts.map (·.map some))

/-- Print why a history (or one key's history) is not linearizable. Diagnostics only. -/
def printExplanation {σ ι ο : Type} [DecidableEq σ] [Hashable σ]
    (M : Model σ ι ο) (P : PendingSteps M) (D : Describe σ ι ο) (verbose : Bool)
    (timer : Option (Task Unit)) (sub : Array (History.Meta × Op ι ο)) (indent : String) :
    IO Unit := do
  let h := sub.toList.map (·.2)
  let task := Task.spawn (prio := .dedicated) fun _ => explain M P h
  match ← waitFirst timer task [] with
  | none =>
    IO.println s!"{indent}(no explanation: the time limit was reached)"
  | some none =>
    IO.println s!"{indent}(no explanation: the diagnostic search did not find the violation)"
  | some (some d) =>
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
  | unknown
  | error

/-- Check the keys of a keyed history, at most `jobs` at a time. The groups are those of
`groupByKey`, key `k`'s verdict is `check M P group` (through `checkWithStats`), and the
history is linearizable iff all of them are `true`: that is `checkKeyed`, covered by
`checkKeyed_iff`. Unless `all` is set, stop at the first key that is not linearizable (its
verdict decides the history's); stop too when the timer finishes. Returns the results that
finished (key, verdict, statistic, number of operations), the number of keys, and whether the
time limit was reached. Tasks still running when it stops cannot be cancelled (they are
pure); `main` exits the process when it is done. -/
def checkKeysParallel {σ ι ο : Type} [DecidableEq σ] [Hashable σ]
    (M : Model σ ι ο) (P : PendingSteps M) (jobs : Nat) (all noMemo : Bool)
    (timer : Option (Task Unit)) (kh : List (Op (String × ι) ο)) :
    IO (Array (String × Bool × Nat × Nat) × Nat × Bool) := do
  let groups := (groupByKey kh).toList.toArray
  let work (g : String × Array (Op ι ο)) : Unit → String × Bool × Nat × Nat := fun _ =>
    if noMemo then (g.1, checkUnmemoised M P g.2.toList, 0, g.2.size)
    else
      let (ok, configs) := checkWithStats M P g.2.toList
      (g.1, ok, configs, g.2.size)
  let mut running : List (Task (String × Bool × Nat × Nat)) := []
  let mut next := 0
  let mut results : Array (String × Bool × Nat × Nat) := #[]
  let mut timedOut := false
  -- every round finishes at least one task or ends the loop, so `groups.size + 1` rounds
  -- are enough
  for _ in [0:groups.size + 1] do
    while running.length < jobs && next < groups.size do
      running := running ++ [Task.spawn (work groups[next]!)]
      next := next + 1
    match running with
    | [] => break
    | t :: ts =>
      if (← waitFirst timer t ts).isNone then
        timedOut := true
        break
      let mut still := []
      for task in running do
        if ← IO.hasFinished task then results := results.push task.get
        else still := still ++ [task]
      running := still
      if !all && results.any (!·.2.1) then break
  return (results, groups.size, timedOut)

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
  let timer ← startTimer opts.timeout
  -- `outcome` is decided by verified functions only: `check` (through `checkWithStats`, whose
  -- first component is `check` by definition) or, per key, the same calls that `checkKeyed`
  -- combines with `List.all`; with `--no-memo` their unmemoised counterparts.
  let (outcome, complete, nkeys, results) ← do
    if keyed then
      let (rs, nkeys, _) ← checkKeysParallel M P opts.jobs opts.allKeys opts.noMemo timer kh
      let complete := rs.size == nkeys
      let outcome :=
        if rs.any (!·.2.1) then Outcome.notLinearizable   -- some key fails: checkKeyed = false
        else if complete then Outcome.linearizable          -- every key passes: checkKeyed = true
        else Outcome.unknown                                -- time limit reached first
      pure (outcome, complete, nkeys, rs.toList.map fun (k, ok, configs, n) =>
        ({ key := some k, ops := n, ok, configs } : KeyResult))
    else
      let task := Task.spawn (prio := .dedicated) fun _ =>
        if opts.noMemo then (checkUnmemoised M P ops, 0) else checkWithStats M P ops
      match ← waitFirst timer task [] with
      | some (ok, configs) =>
        pure (if ok then Outcome.linearizable else Outcome.notLinearizable, true, 0,
          [({ key := none, ops := ops.length, ok, configs } : KeyResult)])
      | none => pure (Outcome.unknown, false, 0, [])
  let t1 ← IO.monoNanosNow
  let configs := results.foldl (· + ·.configs) 0
  let word := match outcome with
    | .linearizable => "linearizable"
    | .notLinearizable => "not linearizable"
    | _ => s!"unknown (no verdict within {opts.timeout.getD 0} s)"
  if opts.quiet then
    IO.println s!"{file}: {word}"
  else
    let pending := (ops.filter (·.ret.isNone)).length
    let keysNote := if keyed then s!", {nkeys} keys" else ""
    IO.println s!"{file}: {ops.length} operations ({pending} never returned){keysNote}, model {name}"
    let stats := if opts.noMemo then "unmemoised" else s!"{configs} configurations ruled out"
    match outcome with
    | .linearizable => IO.println s!"LINEARIZABLE ({fmtMs (t1 - t0)}, {stats})"
    | .notLinearizable => IO.println s!"NOT LINEARIZABLE ({fmtMs (t1 - t0)}, {stats})"
    | _ =>
      let keysDone := if keyed then s!", {results.length} of {nkeys} keys checked" else ""
      IO.println s!"UNKNOWN: no verdict within the {opts.timeout.getD 0} s time limit{keysDone}"
    if outcome matches .notLinearizable then
      if keyed then
        let bad := results.filter (!·.ok)
        if complete then
          IO.println s!"{bad.length} of {nkeys} keys are not linearizable."
        else
          IO.println s!"Stopped at the first key that is not linearizable ({results.length} of {nkeys} keys checked; --all-keys checks every key)."
        for r in bad do
          let k := r.key.getD ""
          IO.println s!"\nkey {Json.quote k} ({r.ops} operations):"
          let sub := lines.filter (·.1.key == some k)
          printExplanation M P D opts.verbose timer sub "  "
      else
        IO.println ""
        printExplanation M P D opts.verbose timer lines ""
  return outcome

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
    | .notLinearizable => if status == 0 || status == 3 then status := 1
    | .unknown => if status == 0 then status := 3
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
