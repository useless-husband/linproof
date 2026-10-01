import Linproof.Json
import Linproof.Spec

/-!
# The history file format (trusted, not verified)

A history is a JSON-lines file: one operation per line, blank lines ignored.

```
{"process": 0, "call": 0, "return": 5, "op": "write", "input": 1}
{"process": 1, "call": 2, "return": 7, "op": "read", "output": 1}
{"process": 2, "call": 3, "op": "cas", "input": [1, 2]}
{"process": 0, "call": 8, "return": 9, "op": "cas", "input": [1, 3], "output": false}
```

* `call` (required) and `return` (optional) are non-negative integer timestamps. An operation
  without `return` (or with `"return": null`) never returned: its effect may or may not have
  happened, and its `output` is ignored.
* `op` and `input`/`output` depend on the model; see the README.
* `key` (optional, string or integer) makes the history keyed: each key is an independent
  object and is checked on its own (the locality theorem).
* `process` (optional) is only used when printing operations.

This module only builds `Op` values; it does not decide anything about linearizability.
-/

namespace Linproof.History

open Json

/-- Where an operation came from, for messages. -/
structure Meta where
  line : Nat
  process : Option Int := none
  key : Option String := none
  deriving Inhabited

def describeVal : Val → String
  | .null => "null"
  | .int i => toString i
  | .str s => Json.quote s

def toVal : Value → Except String Val
  | .null => .ok .null
  | .num i => .ok (.int i)
  | .str s => .ok (.str s)
  | _ => .error "a value must be null, an integer or a string"

def toStr : Value → Except String String
  | .str s => .ok s
  | _ => .error "expected a string"

def toNat (what : String) : Value → Except String Nat
  | .num i => if i ≥ 0 then .ok i.toNat else .error s!"{what} must not be negative"
  | _ => .error s!"{what} must be an integer"

/-- The fields shared by every model. -/
def parseCommon (line : Nat) (j : Value) :
    Except String (Meta × Nat × Option Nat × String × Option Value × Option Value) := do
  let .obj _ := j | throw "each line must be a JSON object"
  let call ← match j.get? "call" with
    | some v => toNat "call" v
    | none => throw "missing \"call\""
  let ret ← match j.get? "return" with
    | none | some .null => pure none
    | some v => some <$> toNat "return" v
  let op ← match j.get? "op" with
    | some (.str s) => pure s
    | _ => throw "missing or non-string \"op\""
  let process ← match j.get? "process" with
    | none | some .null => pure none
    | some (.num i) => pure (some i)
    | some _ => throw "\"process\" must be an integer"
  let key ← match j.get? "key" with
    | none | some .null => pure none
    | some (.str s) => pure (some s)
    | some (.num i) => pure (some (toString i))
    | some _ => throw "\"key\" must be a string or an integer"
  pure ({ line, process, key }, call, ret, op, j.get? "input", j.get? "output")

/-- Parse one operation on a (compare-and-set) register. -/
def parseRegOp (line : Nat) (j : Value) : Except String (Meta × Op RegInput RegOutput) := do
  let (info, call, ret, op, input, output) ← parseCommon line j
  let (inp, out) ← match op with
    | "read" =>
      match ret with
      | none => pure (RegInput.read, RegOutput.value .null)
      | some _ =>
        match output with
        | some v => do pure (RegInput.read, RegOutput.value (← toVal v))
        | none => throw "a read that returned needs an \"output\""
    | "write" =>
      match input with
      | some v => do pure (RegInput.write (← toVal v), RegOutput.ok)
      | none => throw "a write needs an \"input\""
    | "cas" =>
      match input with
      | some (.arr [e, n]) => do
        let e ← toVal e
        let n ← toVal n
        match ret, output with
        | none, _ => pure (RegInput.cas e n, RegOutput.ok)
        | some _, some (.bool true) => pure (RegInput.cas e n, RegOutput.ok)
        | some _, some (.bool false) => pure (RegInput.cas e n, RegOutput.fail)
        | some _, _ => throw "a cas that returned needs \"output\": true or false"
      | _ => throw "a cas needs \"input\": [expected, new]"
    | other => throw s!"unknown register operation \"{other}\" (expected read, write or cas)"
  pure (info, { call, input := inp, ret := ret.map (·, out) })

/-- Parse one operation on the string key-value store (without its key). -/
def parseKVOp (line : Nat) (j : Value) : Except String (Meta × Op KVInput KVOutput) := do
  let (info, call, ret, op, input, output) ← parseCommon line j
  let (inp, out) ← match op with
    | "get" =>
      match ret with
      | none => pure (KVInput.get, KVOutput.value "")
      | some _ =>
        match output with
        | some v => do pure (KVInput.get, KVOutput.value (← toStr v))
        | none => throw "a get that returned needs an \"output\""
    | "put" =>
      match input with
      | some v => do pure (KVInput.put (← toStr v), KVOutput.ok)
      | none => throw "a put needs an \"input\""
    | "append" =>
      match input with
      | some v => do pure (KVInput.append (← toStr v), KVOutput.ok)
      | none => throw "an append needs an \"input\""
    | other => throw s!"unknown key-value operation \"{other}\" (expected get, put or append)"
  pure (info, { call, input := inp, ret := ret.map (·, out) })

/-- Parse a whole file with the given line parser. Errors carry the line number. -/
def parseLines {α : Type} (parseOp : Nat → Value → Except String α) (text : String) :
    Except String (Array α) := do
  let mut out := #[]
  let mut lineNo := 0
  for raw in text.splitOn "\n" do
    lineNo := lineNo + 1
    if raw.all Json.isWs then continue
    let j ← match Json.parse raw with
      | .ok j => pure j
      | .error e => throw s!"line {lineNo}: {e}"
    match parseOp lineNo j with
    | .ok a => out := out.push a
    | .error e => throw s!"line {lineNo}: {e}"
  pure out

end Linproof.History
