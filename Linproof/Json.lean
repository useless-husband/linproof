/-!
# A small JSON parser (trusted, not verified)

`linproof` reads one JSON value per line. This parser covers the JSON grammar of RFC 8259
except non-integer numbers, which histories do not need and which are rejected with an
error rather than rounded. It is part of the trusted code listed in the README: the theorems
are about what the checker does with the operations once they have been read.

All functions are total. Recursion is bounded by fuel arguments that start larger than any
input can use (every call consumes a character or is followed by one that does); running out
is reported as an error.
-/

namespace Linproof.Json

/-- A JSON value. Numbers are integers. -/
inductive Value where
  | null
  | bool (b : Bool)
  | num (i : Int)
  | str (s : String)
  | arr (xs : List Value)
  | obj (kvs : List (String × Value))
  deriving Inhabited, Repr

def isWs (c : Char) : Bool := c = ' ' || c = '\t' || c = '\n' || c = '\r'

def skipWs : List Char → List Char
  | c :: cs => if isWs c then skipWs cs else c :: cs
  | [] => []

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def hex4 : List Char → Option (Nat × List Char)
  | a :: b :: c :: d :: rest => do
    let a ← hexVal a
    let b ← hexVal b
    let c ← hexVal c
    let d ← hexVal d
    pure (((a * 16 + b) * 16 + c) * 16 + d, rest)
  | _ => none

/-- Decode a `\u` escape, including a UTF-16 surrogate pair. Returns the character and the
input after it. -/
def unicodeEscape (cs : List Char) : Except String (Char × List Char) :=
  match hex4 cs with
  | none => .error "bad \\u escape"
  | some (hi, rest) =>
    if 0xD800 ≤ hi && hi < 0xDC00 then
      match rest with
      | '\\' :: 'u' :: rest' =>
        match hex4 rest' with
        | some (lo, rest'') =>
          if 0xDC00 ≤ lo && lo < 0xE000 then
            .ok (Char.ofNat (0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00)), rest'')
          else .error "bad surrogate pair"
        | none => .error "bad \\u escape"
      | _ => .error "unpaired surrogate"
    else if 0xDC00 ≤ hi && hi < 0xE000 then .error "unpaired surrogate"
    else .ok (Char.ofNat hi, rest)

/-- Parse the rest of a string literal (after the opening quote). -/
def parseStringBody : Nat → String → List Char → Except String (String × List Char)
  | 0, _, _ => .error "string too long"
  | _ + 1, _, [] => .error "unterminated string"
  | _ + 1, acc, '"' :: rest => .ok (acc, rest)
  | fuel + 1, acc, '\\' :: c :: rest =>
    match c with
    | '"' => parseStringBody fuel (acc.push '"') rest
    | '\\' => parseStringBody fuel (acc.push '\\') rest
    | '/' => parseStringBody fuel (acc.push '/') rest
    | 'b' => parseStringBody fuel (acc.push (Char.ofNat 8)) rest
    | 'f' => parseStringBody fuel (acc.push (Char.ofNat 12)) rest
    | 'n' => parseStringBody fuel (acc.push '\n') rest
    | 'r' => parseStringBody fuel (acc.push '\r') rest
    | 't' => parseStringBody fuel (acc.push '\t') rest
    | 'u' =>
      match unicodeEscape rest with
      | .ok (ch, rest') => parseStringBody fuel (acc.push ch) rest'
      | .error e => .error e
    | _ => .error s!"bad escape \\{c}"
  | fuel + 1, acc, c :: rest =>
    if c.toNat < 0x20 then .error "control character in string"
    else parseStringBody fuel (acc.push c) rest

/-- Parse a string literal body (after the opening quote). -/
def parseString (cs : List Char) : Except String (String × List Char) :=
  parseStringBody (cs.length + 1) "" cs

def digits (acc : Nat) (count : Nat) : List Char → Nat × Nat × List Char
  | c :: cs => if c.isDigit then digits (acc * 10 + (c.toNat - '0'.toNat)) (count + 1) cs
               else (acc, count, c :: cs)
  | [] => (acc, count, [])

def parseNumber (cs : List Char) : Except String (Int × List Char) := do
  let (neg, cs) := match cs with
    | '-' :: rest => (true, rest)
    | _ => (false, cs)
  let (n, count, rest) := digits 0 0 cs
  if count = 0 then throw "expected a digit"
  if count > 1 && cs.head? = some '0' then throw "leading zero in number"
  match rest with
  | c :: _ =>
    if c = '.' || c = 'e' || c = 'E' then
      throw "only integer numbers are supported"
  | [] => pure ()
  pure (if neg then -(n : Int) else n, rest)

def expectLit (lit : List Char) (v : Value) (cs : List Char) : Except String (Value × List Char) :=
  if lit.isPrefixOf cs then .ok (v, cs.drop lit.length)
  else .error s!"unexpected input near {String.ofList (cs.take 12)}"

mutual
  def parseValue (fuel : Nat) (cs : List Char) : Except String (Value × List Char) :=
    match fuel with
    | 0 => .error "input too deeply nested"
    | fuel + 1 =>
      match skipWs cs with
      | '{' :: rest => parseObject fuel [] (skipWs rest) true
      | '[' :: rest => parseArray fuel [] (skipWs rest) true
      | '"' :: rest => do
        let (s, rest) ← parseString rest
        pure (.str s, rest)
      | 't' :: rest => expectLit ['r', 'u', 'e'] (.bool true) rest
      | 'f' :: rest => expectLit ['a', 'l', 's', 'e'] (.bool false) rest
      | 'n' :: rest => expectLit ['u', 'l', 'l'] .null rest
      | cs@(c :: _) =>
        if c = '-' || c.isDigit then do
          let (n, rest) ← parseNumber cs
          pure (.num n, rest)
        else .error s!"unexpected character '{c}'"
      | [] => .error "unexpected end of input"

  def parseArray (fuel : Nat) (acc : List Value) (cs : List Char) (first : Bool) :
      Except String (Value × List Char) :=
    match fuel with
    | 0 => .error "input too deeply nested"
    | fuel + 1 =>
      match cs with
      | ']' :: rest => if first then .ok (.arr [], rest) else .error "expected a value"
      | _ => do
        let (v, rest) ← parseValue fuel cs
        match skipWs rest with
        | ',' :: rest => parseArray fuel (v :: acc) (skipWs rest) false
        | ']' :: rest => pure (.arr (v :: acc).reverse, rest)
        | _ => throw "expected ',' or ']'"

  def parseObject (fuel : Nat) (acc : List (String × Value)) (cs : List Char) (first : Bool) :
      Except String (Value × List Char) :=
    match fuel with
    | 0 => .error "input too deeply nested"
    | fuel + 1 =>
      match cs with
      | '}' :: rest => if first then .ok (.obj [], rest) else .error "expected a key"
      | '"' :: rest => do
        let (k, rest) ← parseString rest
        match skipWs rest with
        | ':' :: rest =>
          let (v, rest) ← parseValue fuel rest
          match skipWs rest with
          | ',' :: rest => parseObject fuel ((k, v) :: acc) (skipWs rest) false
          | '}' :: rest => pure (.obj ((k, v) :: acc).reverse, rest)
          | _ => throw "expected ',' or '}'"
        | _ => throw "expected ':'"
      | _ => .error "expected a string key"
end

/-- Parse a complete JSON text. -/
def parse (s : String) : Except String Value := do
  let cs := s.toList
  let (v, rest) ← parseValue (4 * cs.length + 4) cs
  match skipWs rest with
  | [] => pure v
  | _ => throw "trailing characters after the JSON value"

/-- Look up a key in an object (the first occurrence). -/
def Value.get? (v : Value) (k : String) : Option Value :=
  match v with
  | .obj kvs => kvs.lookup k
  | _ => none

/-- Render a string as a JSON string literal. -/
def quote (s : String) : String :=
  let body := s.foldl (fun acc c =>
    match c with
    | '"' => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | c =>
      if c.toNat < 0x20 then
        let h := Nat.toDigits 16 c.toNat
        acc ++ "\\u" ++ String.ofList (List.replicate (4 - h.length) '0' ++ h)
      else acc.push c) ""
  "\"" ++ body ++ "\""

end Linproof.Json
