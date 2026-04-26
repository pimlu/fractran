import Fractran.Runtime.Cycle

namespace Fractran.JsBridge.Runner

/-- Like `cycleRunAux`, but with an early-exit when `st.halted` is set. Lets
    callers pass an arbitrarily-large fuel without burning cycles after the
    program halts. Structurally recursive on `Nat`, so no `partial def` (and no
    Lean RC bugs around tail-call inc/dec patterns we hit with `partial`). -/
def runWithLimit (table : Array (List Candidate))
    (fallback : List Candidate) (thresh dmaxes : RegMap) :
    CycleState → Nat → CycleState
  | st, 0 => st
  | st, fuel + 1 =>
    if st.halted then st
    else runWithLimit table fallback thresh dmaxes
      (cycleStep table fallback thresh dmaxes st) fuel

/-- Effectively-unbounded analog of `cycleRunFromRegProg`. Hardcodes a fuel of
    `2^63`; halting programs short-circuit on the `halted` check, while truly
    nonterminating ones rely on the worker being `terminate()`d externally. -/
def cycleRunUntilHalt (cyclen : Nat) (hcyclen : 0 < cyclen)
    (regProg : List (RegMap × RegMap)) (m : RegMap) : CycleState :=
  let table := optTable regProg
  let cands := allCandidates regProg
  let thresh := dthreshMap regProg cyclen
  let dmaxes := dmaxesMap regProg
  let initState : CycleState :=
    { m := m
      cands := cands
      buf := CBuf.empty cyclen hcyclen
      stepsSimulated := 0 }
  runWithLimit table cands thresh dmaxes initState (2 ^ 63)

end Fractran.JsBridge.Runner

/-!
# JS / WASM bridge

Exports `fractran_run_lean : String → String` for the browser worker. Wire format
is whitespace-separated `Nat` tokens. The runner is unbounded (`partial def
runUntilHalt` below) — the worker terminates itself externally if a program is
nonterminating.

Input:
```
<cyclen> <numFractions>
  for each fraction:
    <num_factor_count> <p_1> <e_1> ... <p_n> <e_n>
    <den_factor_count> <p_1> <e_1> ... <p_n> <e_n>
<init_factor_count> <p_1> <e_1> ... <p_n> <e_n>
```

Output:
```
OK <halted:0|1> <stepsSimulated> <result_factor_count> <p_1> <e_1> ...
```
or `ERR <reason>` on parse failure / preconditions.
-/

namespace Fractran.JsBridge

private partial def pairUp : List Nat → List (Nat × Nat)
  | a :: b :: rest => (a, b) :: pairUp rest
  | _ => []

private def takeNats (n : Nat) (xs : List Nat) : Option (List Nat × List Nat) :=
  if n ≤ xs.length then some (xs.take n, xs.drop n) else none

private def parseRegMapBlock : List Nat → Option (RegMap × List Nat)
  | count :: rest => do
    let (flat, rest') ← takeNats (count * 2) rest
    some (RegMap.ofFactors (pairUp flat), rest')
  | [] => none

private partial def parseFractions :
    Nat → List Nat → Option (List (RegMap × RegMap) × List Nat)
  | 0, tokens => some ([], tokens)
  | n + 1, tokens => do
    let (num, rest1) ← parseRegMapBlock tokens
    let (den, rest2) ← parseRegMapBlock rest1
    let (rest, final) ← parseFractions n rest2
    some ((num, den) :: rest, final)

private def tokenize (s : String) : Option (List Nat) :=
  let toks := (s.split Char.isWhitespace).toList.map String.Slice.toString
  toks.filter (· ≠ "") |>.mapM String.toNat?

private def encodeRegMap (m : RegMap) : String :=
  let factors := m.toList
  let body := factors.foldl (fun acc (p, e) => acc ++ s!" {p} {e}") ""
  s!"{factors.length}{body}"

private def encodeResult (st : CycleState) : String :=
  let halted := if st.halted then 1 else 0
  s!"OK {halted} {st.stepsSimulated} {encodeRegMap st.m}"

def fractranRunStr (input : String) : String :=
  match tokenize input with
  | none => "ERR tokenize"
  | some tokens =>
    match tokens with
    | cyclen :: numFractions :: rest =>
      if h : 0 < cyclen then
        match parseFractions numFractions rest with
        | none => "ERR fractions"
        | some (regProg, rest2) =>
          match parseRegMapBlock rest2 with
          | none => "ERR init"
          | some (init, _) =>
            encodeResult (Runner.cycleRunUntilHalt cyclen h regProg init)
      else "ERR cyclen_zero"
    | _ => "ERR header_too_short"

@[export fractran_run_lean]
def fractranRunLean (input : String) : String := fractranRunStr input

end Fractran.JsBridge
