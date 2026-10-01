import Linproof

/-!
# Runtime tests

The theorems cover the checker; these tests cover what they do not:

* the trusted JSON and history parsers;
* that the specification says what a reader expects, on hand-written histories whose verdict
  is worked out by hand in the comments;
* the compiled code: the fast search (hash sets, `withPtrEq`) against the plain search, and
  the explanation search against the verdict, on random histories with fixed seeds.
-/

open Linproof

/-! ## A tiny test harness -/

structure Results where
  passed : Nat := 0
  failed : Array String := #[]

def expect (r : Results) (name : String) (ok : Bool) : Results :=
  if ok then { r with passed := r.passed + 1 } else { r with failed := r.failed.push name }

/-! ## Building histories -/

abbrev ROp := Op RegInput RegOutput

instance : Inhabited ROp := ⟨{ call := 0, input := .read, ret := none }⟩
instance : Inhabited (Op KVInput KVOutput) := ⟨{ call := 0, input := .get, ret := none }⟩

def iv (v : Option Int) : Val := match v with | some i => .int i | none => .null

def w (c r : Nat) (v : Int) : ROp := { call := c, input := .write (.int v), ret := some (r, .ok) }
def wP (c : Nat) (v : Int) : ROp := { call := c, input := .write (.int v), ret := none }
def rd (c r : Nat) (v : Option Int) : ROp :=
  { call := c, input := .read, ret := some (r, .value (iv v)) }
def rdP (c : Nat) : ROp := { call := c, input := .read, ret := none }
def cs (c r : Nat) (e n : Option Int) (ok : Bool) : ROp :=
  { call := c, input := .cas (iv e) (iv n), ret := some (r, if ok then .ok else .fail) }
def csP (c : Nat) (e n : Option Int) : ROp := { call := c, input := .cas (iv e) (iv n), ret := none }

def casCheck (h : List ROp) : Bool := check (casRegister .null) (casRegisterSteps .null) h
def regCheck (h : List ROp) : Bool := check (register .null) (registerSteps .null) h

abbrev KOp := Op (String × KVInput) KVOutput
def put (k : String) (c r : Nat) (v : String) : KOp :=
  { call := c, input := (k, .put v), ret := some (r, .ok) }
def app (k : String) (c r : Nat) (v : String) : KOp :=
  { call := c, input := (k, .append v), ret := some (r, .ok) }
def get (k : String) (c r : Nat) (v : String) : KOp :=
  { call := c, input := (k, .get), ret := some (r, .value v) }
def kvCheck (h : List KOp) : Bool := checkKeyed kvCell kvCellSteps h

/-! ## Hand-checked histories -/

def specTests (r : Results) : Results :=
  let r := expect r "empty history" (casCheck [])
  let r := expect r "read of the initial null" (casCheck [rd 0 1 none])
  let r := expect r "read of a value nobody wrote" (!casCheck [rd 0 1 (some 1)])
  let r := expect r "read after a completed write" (casCheck [w 0 1 1, rd 2 3 (some 1)])
  let r := expect r "stale read after a completed write" (!casCheck [w 0 1 1, rd 2 3 none])
  -- the read overlaps the write: it may come before or after it
  let r := expect r "concurrent read sees old value" (casCheck [w 0 5 1, rd 1 2 none])
  let r := expect r "concurrent read sees new value" (casCheck [w 0 5 1, rd 1 2 (some 1)])
  -- intervals [0,2] and [2,3] touch, so they are concurrent
  let r := expect r "touching intervals are concurrent" (casCheck [w 0 2 1, rd 2 3 none])
  let r := expect r "disjoint intervals are ordered" (!casCheck [w 0 1 1, rd 2 3 none])
  -- once a read has seen the new value, a later read cannot see the old one
  let r := expect r "no going back in time"
    (!casCheck [w 0 10 1, rd 1 2 (some 1), rd 3 4 none])
  let r := expect r "two concurrent reads in either order"
    (casCheck [w 0 10 1, rd 1 5 (some 1), rd 2 6 none])
  -- operations that never returned
  let r := expect r "a pending write may take effect" (casCheck [wP 0 1, rd 5 6 (some 1)])
  let r := expect r "a pending write may never take effect" (casCheck [wP 0 1, rd 5 6 none])
  let r := expect r "a pending write takes effect between two reads"
    (casCheck [wP 0 1, rd 1 2 none, rd 3 4 (some 1)])
  let r := expect r "a pending write cannot act before it is invoked"
    (!casCheck [rd 0 1 (some 1), wP 2 1])
  let r := expect r "a pending write takes effect at most once"
    (!casCheck [wP 0 1, w 1 2 2, rd 3 4 (some 1), rd 5 6 (some 2), rd 7 8 (some 1)])
  let r := expect r "a pending read is harmless" (casCheck [rdP 0, w 1 2 3, rd 4 5 (some 3)])
  -- compare-and-set
  let r := expect r "successful cas from null" (casCheck [cs 0 1 none (some 1) true, rd 2 3 (some 1)])
  let r := expect r "successful cas needs a match" (!casCheck [cs 0 1 (some 5) (some 1) true])
  let r := expect r "failed cas needs a mismatch" (casCheck [cs 0 1 (some 5) (some 1) false])
  let r := expect r "failed cas cannot fail on a match" (!casCheck [cs 0 1 none (some 1) false])
  let r := expect r "a failed cas has no effect"
    (casCheck [w 0 1 2, cs 2 3 (some 5) (some 1) false, rd 4 5 (some 2)])
  let r := expect r "a pending cas may succeed" (casCheck [csP 0 none (some 7), rd 3 4 (some 7)])
  let r := expect r "a pending cas only succeeds on a match"
    (!casCheck [w 0 1 3, csP 2 none (some 7), rd 3 4 (some 7)])
  let r := expect r "cas chain" (casCheck
    [w 0 1 0, cs 2 3 (some 0) (some 1) true, cs 4 5 (some 1) (some 2) true,
     cs 6 7 (some 1) (some 3) false, rd 8 9 (some 2)])
  -- identical operations
  let r := expect r "duplicate writes" (casCheck [w 0 3 1, w 0 3 1, rd 4 5 (some 1)])
  let r := expect r "duplicate pending writes" (casCheck [wP 0 1, wP 0 1, rd 4 5 (some 1)])
  -- the read/write register has no compare-and-set
  let r := expect r "register: a returned cas is impossible" (!regCheck [cs 0 1 none (some 1) true])
  let r := expect r "register: a pending cas never takes effect" (regCheck [csP 0 none (some 1), rd 2 3 none])
  let r := expect r "register: reads and writes" (regCheck [w 0 4 1, w 1 5 2, rd 6 7 (some 2)])
  -- the key-value store, checked key by key
  let r := expect r "kv: independent keys" (kvCheck
    [put "a" 0 1 "x", put "b" 2 3 "y", get "a" 4 5 "x", get "b" 6 7 "y"])
  let r := expect r "kv: appends" (kvCheck
    [app "a" 0 5 "1", app "a" 1 6 "2", get "a" 7 8 "21"])
  let r := expect r "kv: a violation on one key" (!kvCheck
    [put "a" 0 1 "x", put "b" 2 3 "y", get "a" 4 5 "x", get "b" 6 7 "x"])
  let r := expect r "kv: missing key reads empty" (kvCheck [get "z" 0 1 ""])
  -- a violation that needs the order across keys? none exists: that is the locality theorem
  let r := expect r "kv: per-key orders that look inconsistent across keys are fine" (kvCheck
    [put "a" 0 10 "1", put "b" 0 10 "1", get "a" 1 2 "", get "b" 1 2 "1",
     get "a" 3 4 "1", get "b" 3 4 "1"])
  r

/-! ## Parsers -/

def jsonTests (r : Results) : Results :=
  let ok (s : String) := (Json.parse s).toBool
  let r := expect r "json: object" (ok "{\"a\": 1, \"b\": [true, false, null], \"c\": \"x\"}")
  let r := expect r "json: nested" (ok "[[[[]]], {}, {\"a\": {\"b\": [1]}}]")
  let r := expect r "json: negative and zero" (ok "[-1, 0, -0, 12345678901234567890123]")
  let r := expect r "json: whitespace" (ok " \t{ \"a\" : 1 }\r ")
  let r := expect r "json: rejects floats" (!ok "1.5")
  let r := expect r "json: rejects exponents" (!ok "1e5")
  let r := expect r "json: rejects leading zeros" (!ok "01")
  let r := expect r "json: rejects trailing commas" (!ok "[1,]" && !ok "{\"a\":1,}")
  let r := expect r "json: rejects trailing text" (!ok "{} x")
  let r := expect r "json: rejects unterminated strings" (!ok "\"abc")
  let r := expect r "json: rejects control characters" (!ok "\"a\nb\"")
  let r := expect r "json: rejects bad escapes" (!ok "\"\\x\"")
  let r := expect r "json: rejects lone surrogates" (!ok "\"\\ud800\"" && !ok "\"\\udc00\"")
  let r := expect r "json: rejects bare words" (!ok "nul" && !ok "tru")
  let r := expect r "json: decodes escapes" (match Json.parse "\"a\\n\\t\\\"\\\\\\/\\u00e9\\ud83d\\ude00\"" with
    | .ok (.str s) => s == "a\n\t\"\\/é😀"
    | _ => false)
  let r := expect r "json: big integers" (match Json.parse "-98765432109876543210" with
    | .ok (.num i) => i == -98765432109876543210
    | _ => false)
  let r := expect r "json: duplicate keys keep the first" (match Json.parse "{\"a\":1,\"a\":2}" with
    | .ok v => match v.get? "a" with | some (.num 1) => true | _ => false
    | _ => false)
  r

def historyTests (r : Results) : Results :=
  let reg (s : String) := History.parseLines History.parseRegOp s
  let kv (s : String) := History.parseLines History.parseKVOp s
  let r := expect r "history: register ops" (match reg
      "{\"call\":0,\"return\":1,\"op\":\"write\",\"input\":3}\n\n{\"call\":2,\"op\":\"read\"}\n{\"call\":3,\"return\":4,\"op\":\"cas\",\"input\":[3,\"x\"],\"output\":false}\n" with
    | .ok a => a.size == 3 &&
        (match a[0]!.2.input, a[0]!.2.ret with | .write (.int 3), some (1, .ok) => true | _, _ => false) &&
        (match a[1]!.2.input, a[1]!.2.ret with | .read, none => true | _, _ => false) &&
        (match a[2]!.2.input, a[2]!.2.ret with
          | .cas (.int 3) (.str "x"), some (4, .fail) => true | _, _ => false) &&
        a[1]!.1.line == 3
    | .error _ => false)
  let r := expect r "history: return null means pending"
    (match reg "{\"call\":0,\"return\":null,\"op\":\"write\",\"input\":1}" with
      | .ok a => a[0]!.2.ret.isNone | .error _ => false)
  let r := expect r "history: keys and processes" (match kv
      "{\"process\":7,\"call\":0,\"return\":1,\"op\":\"get\",\"key\":5,\"output\":\"\"}" with
    | .ok a => a[0]!.1.key == some "5" && a[0]!.1.process == some 7
    | .error _ => false)
  let errLine {α : Type} (res : Except String α) (n : Nat) : Bool := match res with
    | .error e => e.startsWith s!"line {n}:"
    | .ok _ => false
  let r := expect r "history: bad json reports its line"
    (errLine (reg "{\"call\":0,\"op\":\"read\"}\n{oops}") 2)
  let r := expect r "history: missing call" (errLine (reg "{\"op\":\"read\"}") 1)
  let r := expect r "history: negative time" (errLine (reg "{\"call\":-1,\"op\":\"read\"}") 1)
  let r := expect r "history: returned read needs output"
    (errLine (reg "{\"call\":0,\"return\":1,\"op\":\"read\"}") 1)
  let r := expect r "history: cas needs a pair"
    (errLine (reg "{\"call\":0,\"return\":1,\"op\":\"cas\",\"input\":1,\"output\":true}") 1)
  let r := expect r "history: cas output must be boolean"
    (errLine (reg "{\"call\":0,\"return\":1,\"op\":\"cas\",\"input\":[1,2],\"output\":1}") 1)
  let r := expect r "history: unknown op" (errLine (reg "{\"call\":0,\"op\":\"incr\"}") 1)
  let r := expect r "history: kv values are strings"
    (errLine (kv "{\"call\":0,\"return\":1,\"op\":\"put\",\"key\":\"a\",\"input\":1}") 1)
  let r := expect r "history: values must be scalars"
    (errLine (reg "{\"call\":0,\"return\":1,\"op\":\"write\",\"input\":[1]}") 1)
  r

/-! ## Random histories: fast search = plain search = explanation -/

/-- A 64-bit linear congruential generator; good enough to vary small histories. -/
structure Rng where
  s : UInt64

def Rng.next (g : Rng) (n : Nat) : Nat × Rng :=
  let s := g.s * 6364136223846793005 + 1442695040888963407
  (((s >>> 33).toNat) % n, ⟨s⟩)

def randomHistory (g : Rng) (len : Nat) : List ROp × Rng := Id.run do
  let mut g := g
  let mut out := []
  for _ in [0:len] do
    let (c, g1) := g.next 12
    let (d, g2) := g1.next 5
    let (kind, g3) := g2.next 3
    let (v, g4) := g3.next 3
    let (v2, g5) := g4.next 3
    let (pend, g6) := g5.next 6
    let (okb, g7) := g6.next 2
    g := g7
    let ret := if pend == 0 then none else some (c + d)
    let op : ROp := match kind with
      | 0 => { call := c, input := .read,
               ret := ret.map (·, .value (if v == 2 then .null else .int v)) }
      | 1 => { call := c, input := .write (.int v), ret := ret.map (·, .ok) }
      | _ => { call := c, input := .cas (if v == 2 then .null else .int v) (.int v2),
               ret := ret.map (·, if okb == 0 then .ok else .fail) }
    out := op :: out
  return (out, g)

def randomTests (r : Results) (seed : UInt64) (count : Nat) : Results := Id.run do
  let mut r := r
  let mut g : Rng := ⟨seed⟩
  let mut lin := 0
  for i in [0:count] do
    let (len, g1) := g.next 9
    let (h, g2) := randomHistory g1 len
    g := g2
    let M := casRegister .null
    let P := casRegisterSteps .null
    let fast := check M P h
    let plain := checkUnmemoised M P h
    let expl := (explain M P h).isNone
    if fast then lin := lin + 1
    r := expect r s!"random #{i} (seed {seed}): fast {fast} = plain {plain}" (fast == plain)
    r := expect r s!"random #{i} (seed {seed}): explanation agrees" (fast == expl)
  -- the generator must produce both verdicts, or the test proves little
  r := expect r s!"random (seed {seed}): both verdicts occur ({lin} of {count} linearizable)"
    (lin > count / 10 && lin < count - count / 10)
  return r

def main : IO UInt32 := do
  let mut r : Results := {}
  r := specTests r
  r := jsonTests r
  r := historyTests r
  r := randomTests r 42 3000
  r := randomTests r 2026 3000
  for f in r.failed do
    IO.eprintln s!"FAIL {f}"
  IO.println s!"{r.passed} passed, {r.failed.size} failed"
  return (if r.failed.isEmpty then 0 else 1)
