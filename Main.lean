import Linproof

/-!
# `linproof` command-line tool (trusted glue)

Reads histories, runs the verified checker and prints the verdicts. The decision itself is
`Linproof.check` / `Linproof.checkKeyed` (through `checkWithStats` and `checkKeyedResults`,
which return the same verdicts plus a statistic), covered by `check_iff` and
`checkKeyed_iff`. This file only parses arguments, reads files and prints.
-/

open Linproof

def version : String := "0.1.0"

def usage : String :=
"linproof — a verified linearizability checker

usage:
  linproof check [--model M] [--no-memo] [--quiet] FILE...
  linproof version

models:
  register       read/write register (values: null, integers, strings; starts at null)
  cas-register   register with compare-and-set (default)
  kv             string key-value store with get/put/append (every op needs a \"key\")

Operations with a \"key\" field are checked per key (locality theorem).

exit status: 0 all linearizable, 1 some history not linearizable,
             2 usage, input or well-formedness error"

structure Options where
  model : String := "cas-register"
  files : Array String := #[]
  quiet : Bool := false
  noMemo : Bool := false

def parseOptions : List String → Options → Except String Options
  | [], o => .ok o
  | "--model" :: m :: rest, o => parseOptions rest { o with model := m }
  | "--quiet" :: rest, o => parseOptions rest { o with quiet := true }
  | "-q" :: rest, o => parseOptions rest { o with quiet := true }
  | "--no-memo" :: rest, o => parseOptions rest { o with noMemo := true }
  | f :: rest, o =>
    if f.startsWith "-" && f != "-" then .error s!"unknown option {f}"
    else parseOptions rest { o with files := o.files.push f }

/-- Outcome of checking one key (or the whole history when it has no keys). -/
structure KeyResult where
  key : Option String
  ops : Nat
  ok : Bool
  configs : Nat

def fmtMs (ns : Nat) : String :=
  let ms := ns / 1000000
  let frac := (ns / 10000) % 100
  s!"{ms}.{if frac < 10 then "0" else ""}{frac} ms"

inductive Outcome where
  | linearizable
  | notLinearizable
  | error

/-- Check a history of model `M`, keyed or not, and print the result. -/
def runModel {σ ι ο : Type} [DecidableEq σ] [Hashable σ]
    (M : Model σ ι ο) (P : PendingSteps M) (opts : Options) (file name : String)
    (lines : Array (History.Meta × Op ι ο)) (requireKeys : Bool) : IO Outcome := do
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
  let results : List KeyResult :=
    if keyed then
      let kh : List (Op (String × ι) ο) :=
        lines.toList.map fun (m, op) =>
          { call := op.call, input := (m.key.getD "", op.input), ret := op.ret }
      let rs := if opts.noMemo then
          (keysOf kh).map fun k => (k, checkUnmemoised M P (project k kh), 0)
        else checkKeyedResults M P kh
      rs.map fun (k, ok, configs) => { key := some k, ops := (project k kh).length, ok, configs }
    else
      let (ok, configs) := if opts.noMemo then (checkUnmemoised M P ops, 0)
        else checkWithStats M P ops
      [{ key := none, ops := ops.length, ok, configs }]
  -- force the evaluation before reading the clock again
  let allOk := results.all (·.ok)
  let configs := results.foldl (· + ·.configs) 0
  let t1 ← IO.monoNanosNow
  if opts.quiet then
    IO.println s!"{file}: {if allOk then "linearizable" else "not linearizable"}"
  else
    let pending := (ops.filter (·.ret.isNone)).length
    let keysNote := if keyed then s!", {results.length} keys" else ""
    IO.println s!"{file}: {ops.length} operations ({pending} never returned){keysNote}, model {name}"
    if keyed then
      for r in results do
        if !r.ok then
          IO.println s!"  key {Json.quote (r.key.getD "")}: NOT linearizable ({r.ops} operations)"
    let stats := if opts.noMemo then "unmemoised" else s!"{configs} configurations ruled out"
    IO.println s!"{if allOk then "LINEARIZABLE" else "NOT LINEARIZABLE"} ({fmtMs (t1 - t0)}, {stats})"
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
        runModel (register .null) (registerSteps .null) opts file "register" lines false
      else
        runModel (casRegister .null) (casRegisterSteps .null) opts file "cas-register" lines false
  | "kv" =>
    match History.parseLines History.parseKVOp text with
    | .error e => IO.eprintln s!"{file}: {e}"; return .error
    | .ok lines => runModel kvCell kvCellSteps opts file "kv" lines true
  | other => IO.eprintln s!"unknown model {other}"; return .error

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
    | .ok opts => runCheck opts
    | .error e => IO.eprintln s!"{e}\n\n{usage}"; return 2
  | _ => IO.eprintln usage; return 2
