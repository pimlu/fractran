import Fractran.Runtime.Cycle

/-!
# FRACTRAN program & input parser (mathlib-free)

A small recursive-descent parser for FRACTRAN programs and initial states,
mirroring `web-build/src/parser.peggy` with two changes:

* No integer-division `/` operator anywhere — the only `/` allowed is as a
  fraction separator (synonymous with `%`).
* The top-level grammar (program fractions, initial state) is a *factored*
  expression: products of prime powers, no `+` or `-`. This lets us evaluate
  to a `RegMap` directly, never realizing huge values like `67^159995`.
  `+` and `-` are still allowed inside `^` exponents (which evaluate as
  ordinary `Nat` arithmetic and are typically small).

Grammar:

```
ProgFracs   ::= Frac (FracSep Frac)*
FracSep     ::= ',' WS* | NL+ WS*
Frac        ::= Mul ('%' | '/') Mul        -- '/' here is the FRACTION sep
Mul         ::= Pow ('*' Pow)*
Pow         ::= Base ('^' NatExpr)?        -- exponent: ordinary Nat
Base        ::= Integer | '(' Mul ')'

ProgInput   ::= PairList | Mul
PairList    ::= Pair (',' Pair)*
Pair        ::= '[' NatExpr ',' NatExpr ']'

NatExpr     ::= AddNat
AddNat      ::= MulNat (('+' | '-') MulNat)*
MulNat      ::= PowNat ('*' PowNat)*
PowNat      ::= NatAtom ('^' PowNat)?      -- right-associative
NatAtom     ::= Integer | '(' NatExpr ')'

Integer     ::= [0-9]+                     -- decimal
              | [0-9a-fA-F]+ 'h'           -- hex
              | [01]+ 'b'                  -- binary
```

Whitespace (` `, `\t`) is ignored anywhere between tokens. Newlines also
serve as fraction separators (in addition to `,`). `#` starts a line
comment that runs to end-of-line.

Mathlib-free so this module can ship in the WASM closure.
-/

namespace Fractran.Parse

/-! ## Trial-division factorization -/

private partial def extractPower (n p e : Nat) : Nat × Nat :=
  if n % p == 0 then extractPower (n / p) p (e + 1) else (n, e)

private partial def trialLoop (n p : Nat) (acc : List (Nat × Nat)) :
    List (Nat × Nat) :=
  if n == 1 then acc.reverse
  else if p * p > n then ((n, 1) :: acc).reverse
  else
    let (n', e) := extractPower n p 0
    if e > 0 then trialLoop n' (p + 1) ((p, e) :: acc)
    else trialLoop n (p + 1) acc

/-- Trial-division factorization. For `n ≤ 1` returns `[]`. Cost is O(√n)
    in the worst case (n is a large prime); FRACTRAN literals are typically
    small, so this is fine in practice. -/
def factorize (n : Nat) : List (Nat × Nat) :=
  if n ≤ 1 then [] else trialLoop n 2 []

/-! ## Factored RegMap operations

These never realize the underlying `Nat` value. Multiplication sums
exponents; exponentiation multiplies them. Used to evaluate the
top-level (factored) expressions.
-/

private def regMapMul (a b : RegMap) : RegMap :=
  b.foldl (fun acc p e => acc.insert p (acc.getD p 0 + e)) a

private def regMapPow (a : RegMap) (k : Nat) : RegMap :=
  if k == 0 then RegMap.ofFactors []
  else if k == 1 then a
  else a.foldl (fun acc p e => acc.insert p (e * k)) (RegMap.ofFactors [])

/-! ## Cursor + low-level helpers -/

abbrev Cursor := List Char

private partial def skipSpaces : Cursor → Cursor
  | ' '  :: rest => skipSpaces rest
  | '\t' :: rest => skipSpaces rest
  | cs => cs

/-- Strip `#` line comments and CR characters from the input string,
    leaving newlines as the only line-break marker. -/
private def stripComments (s : String) : String :=
  let lines := s.splitOn "\n" |>.map fun line =>
    match line.splitOn "#" with
    | [] => ""
    | head :: _ => head
  String.intercalate "\n" lines |>.replace "\r" ""

private def isDecDigit (c : Char) : Bool := c.isDigit
private def isBinDigit (c : Char) : Bool := c == '0' || c == '1'
private def isHexDigit (c : Char) : Bool :=
  c.isDigit || ('a' ≤ c ∧ c ≤ 'f') || ('A' ≤ c ∧ c ≤ 'F')

private def hexValue (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

private partial def collectHexLike (cs : Cursor) (acc : List Char) :
    List Char × Cursor :=
  match cs with
  | c :: rest =>
    if isHexDigit c then collectHexLike rest (c :: acc)
    else (acc.reverse, c :: rest)
  | [] => (acc.reverse, [])

private def digitsToNat (chars : List Char) (base : Nat) : Nat :=
  chars.foldl (fun acc c => acc * base + hexValue c) 0

/-- Parse an integer literal. Returns the value and the remaining cursor.

    Tricky case: `b` (the binary suffix) is itself a hex digit. We greedily
    consume hex-like chars; afterwards, if the last char is `b` and the rest
    parses as binary, treat it as a binary literal. Otherwise the trailing
    char must be `h` (hex marker), or the whole run must be decimal. -/
private def parseInteger (cs : Cursor) : Except String (Nat × Cursor) := do
  let cs := skipSpaces cs
  let (chars, cs') := collectHexLike cs []
  if chars.isEmpty then
    Except.error s!"expected integer, got {String.ofList (cs.take 8)}…"
  else
    match cs' with
    | 'h' :: rest =>
      Except.ok (digitsToNat chars 16, rest)
    | _ =>
      -- Try binary: chars ends in 'b' and the prefix is all 0/1.
      match chars.reverse with
      | 'b' :: prefRev =>
        let bits := prefRev.reverse
        if !bits.isEmpty ∧ bits.all isBinDigit then
          Except.ok (digitsToNat bits 2, cs')
        else if chars.all isDecDigit then
          Except.ok (digitsToNat chars 10, cs')
        else
          Except.error s!"ambiguous integer literal {String.ofList chars} (use 'h' suffix for hex)"
      | _ =>
        if chars.all isDecDigit then
          Except.ok (digitsToNat chars 10, cs')
        else
          Except.error s!"ambiguous integer literal {String.ofList chars} (use 'h' suffix for hex)"

/-! ## Recursive-descent parser

Two parser families: `parseMul` (factored, returns `RegMap`) and
`parseNatExpr` (Nat-valued, used inside `^` exponents and `[p,v]` pairs).
They're mutually recursive through `parseBase` (which can recurse into
`parseMul`) and `parsePowNat` (which uses `parseNatExpr` via parens).
-/

mutual

partial def parseMul (cs : Cursor) : Except String (RegMap × Cursor) := do
  let (head, cs) ← parsePow cs
  parseMulRest head cs

partial def parseMulRest (acc : RegMap) (cs : Cursor) :
    Except String (RegMap × Cursor) := do
  let cs := skipSpaces cs
  match cs with
  | '*' :: rest => do
    let (next, cs') ← parsePow rest
    parseMulRest (regMapMul acc next) cs'
  | _ => Except.ok (acc, cs)

partial def parsePow (cs : Cursor) : Except String (RegMap × Cursor) := do
  let (base, cs) ← parseBase cs
  let (expsRev, cs) ← parseExpChain cs []
  if expsRev.isEmpty then Except.ok (base, cs)
  else
    -- Right-assoc fold: 2^3^4 = 2^(3^4). expsRev is [last_parsed, ..., first_parsed],
    -- so foldl with init=1 builds e₁ ^ (e₂ ^ ... ^ eₙ).
    let final := expsRev.foldl (fun acc e => e ^ acc) 1
    Except.ok (regMapPow base final, cs)

/-- Parse zero or more `^ NatAtom` suffixes. Limiting the exponent to an
    atom (literal or paren-expr) — not a full `NatExpr` — matches the peggy
    `Pow := Factor (^ Factor)*` rule, so `2^2*5` correctly parses as
    `(2^2) * 5 = 20` rather than `2^(2*5) = 1024`. -/
partial def parseExpChain (cs : Cursor) (acc : List Nat) :
    Except String (List Nat × Cursor) := do
  let cs := skipSpaces cs
  match cs with
  | '^' :: rest => do
    let (atom, cs') ← parseNatAtom rest
    parseExpChain cs' (atom :: acc)
  | _ => Except.ok (acc, cs)

partial def parseBase (cs : Cursor) : Except String (RegMap × Cursor) := do
  let cs := skipSpaces cs
  match cs with
  | '(' :: rest => do
    let (m, cs') ← parseMul rest
    let cs' := skipSpaces cs'
    match cs' with
    | ')' :: rest' => Except.ok (m, rest')
    | _ => Except.error s!"expected ')' near {String.ofList (cs'.take 8)}…"
  | _ => do
    let (n, cs') ← parseInteger cs
    Except.ok (RegMap.ofFactors (factorize n), cs')

partial def parseNatExpr (cs : Cursor) : Except String (Nat × Cursor) :=
  parseAddNat cs

partial def parseAddNat (cs : Cursor) : Except String (Nat × Cursor) := do
  let (head, cs) ← parseMulNat cs
  parseAddNatRest head cs

partial def parseAddNatRest (acc : Nat) (cs : Cursor) :
    Except String (Nat × Cursor) := do
  let cs := skipSpaces cs
  match cs with
  | '+' :: rest => do
    let (next, cs') ← parseMulNat rest
    parseAddNatRest (acc + next) cs'
  | '-' :: rest => do
    let (next, cs') ← parseMulNat rest
    if acc < next then
      Except.error s!"subtraction underflow: {acc} - {next}"
    else
      parseAddNatRest (acc - next) cs'
  | _ => Except.ok (acc, cs)

partial def parseMulNat (cs : Cursor) : Except String (Nat × Cursor) := do
  let (head, cs) ← parsePowNat cs
  parseMulNatRest head cs

partial def parseMulNatRest (acc : Nat) (cs : Cursor) :
    Except String (Nat × Cursor) := do
  let cs := skipSpaces cs
  match cs with
  | '*' :: rest => do
    let (next, cs') ← parsePowNat rest
    parseMulNatRest (acc * next) cs'
  | _ => Except.ok (acc, cs)

partial def parsePowNat (cs : Cursor) : Except String (Nat × Cursor) := do
  let (base, cs) ← parseNatAtom cs
  let cs := skipSpaces cs
  match cs with
  | '^' :: rest => do
    -- right-associative: parse the rhs as another PowNat
    let (exp, cs') ← parsePowNat rest
    Except.ok (base ^ exp, cs')
  | _ => Except.ok (base, cs)

partial def parseNatAtom (cs : Cursor) : Except String (Nat × Cursor) := do
  let cs := skipSpaces cs
  match cs with
  | '(' :: rest => do
    let (n, cs') ← parseNatExpr rest
    let cs' := skipSpaces cs'
    match cs' with
    | ')' :: rest' => Except.ok (n, rest')
    | _ => Except.error s!"expected ')' near {String.ofList (cs'.take 8)}…"
  | _ => parseInteger cs

end

/-! ## Top-level entry points -/

/-- Skip spaces and tabs AND newlines (used between fractions). -/
private partial def skipSpacesAndNewlines : Cursor → Cursor
  | ' '  :: rest => skipSpacesAndNewlines rest
  | '\t' :: rest => skipSpacesAndNewlines rest
  | '\n' :: rest => skipSpacesAndNewlines rest
  | cs => cs

private def parseFraction (cs : Cursor) :
    Except String ((RegMap × RegMap) × Cursor) := do
  let (num, cs) ← parseMul cs
  let cs := skipSpaces cs
  match cs with
  | '%' :: rest | '/' :: rest => do
    let (den, cs') ← parseMul rest
    Except.ok ((num, den), cs')
  | _ => Except.error s!"expected '%' or '/' (fraction separator) near {String.ofList (cs.take 8)}…"

private partial def parseFractionList (cs : Cursor)
    (acc : List (RegMap × RegMap)) : Except String (List (RegMap × RegMap)) := do
  let cs := skipSpacesAndNewlines cs
  if cs.isEmpty then Except.ok acc.reverse
  else do
    let (frac, cs') ← parseFraction cs
    let cs' := skipSpaces cs'
    -- Consume one separator: ',' or one-or-more newlines. Then the next
    -- iteration's `skipSpacesAndNewlines` swallows extras.
    match cs' with
    | ',' :: rest => parseFractionList rest (frac :: acc)
    | '\n' :: rest => parseFractionList rest (frac :: acc)
    | [] => Except.ok (frac :: acc).reverse
    | c :: _ => Except.error s!"expected ',' or newline between fractions (saw '{c}')"

/-- Parse a complete program file: a list of fractions separated by `,`
    and/or newlines. Lines beginning with `#` (or anywhere `#` appears) are
    treated as comments through end-of-line. -/
def parseProgram (input : String) : Except String (List (RegMap × RegMap)) := do
  let stripped := stripComments input
  parseFractionList stripped.toList []

/-- Parse a `Pair` `[ NatExpr , NatExpr ]`. -/
private def parsePair (cs : Cursor) : Except String ((Nat × Nat) × Cursor) := do
  let cs := skipSpaces cs
  match cs with
  | '[' :: rest => do
    let (p, cs') ← parseNatExpr rest
    let cs' := skipSpaces cs'
    match cs' with
    | ',' :: rest' => do
      let (v, cs'') ← parseNatExpr rest'
      let cs'' := skipSpaces cs''
      match cs'' with
      | ']' :: rest'' => Except.ok ((p, v), rest'')
      | _ => Except.error "expected ']' to close pair"
    | _ => Except.error "expected ',' inside pair"
  | _ => Except.error "expected '[' to start pair"

private partial def parsePairListRest (acc : List (Nat × Nat)) (cs : Cursor) :
    Except String (List (Nat × Nat)) := do
  let cs := skipSpaces cs
  match cs with
  | ',' :: rest => do
    let (pair, cs') ← parsePair rest
    parsePairListRest (pair :: acc) cs'
  | [] => Except.ok acc.reverse
  | _ => Except.error s!"unexpected trailing input near {String.ofList (cs.take 8)}…"

/-- Parse the initial-state argument: either a `[prime, exp]` pair list, or
    a single factored expression. -/
def parseInput (input : String) : Except String RegMap := do
  let stripped := stripComments input
  let cs := skipSpacesAndNewlines stripped.toList
  match cs with
  | '[' :: _ => do
    -- pair list
    let (head, cs') ← parsePair cs
    let pairs ← parsePairListRest [head] cs'
    Except.ok (RegMap.ofFactors pairs)
  | _ => do
    let (m, cs') ← parseMul cs
    let cs' := skipSpacesAndNewlines cs'
    if cs'.isEmpty then Except.ok m
    else Except.error s!"unexpected trailing input in initial state near {String.ofList (cs'.take 8)}…"

end Fractran.Parse
