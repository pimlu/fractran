import Fractran.Runtime.Cycle

namespace Fractran.JsBridge.Runner

/-- Result of running the cycle-detecting interpreter under the JS bridge:
    the final `CycleState` plus the cycle length when the runner detected an
    infinite loop (0 otherwise). The proof-side `cycleRunFromRegProg` doesn't
    return this because `Correct` only distinguishes "halted" vs. "still
    running"; the JS bridge surfaces the third case to the UI. -/
structure RunResult where
  state : CycleState
  /-- Logic-state cycle length when an infinite loop was detected, else 0.
      "Infinite loop" means: the buffer matched the current logic state, and
      `leapCount` reported `none` (no data register has finite life), so no
      number of cycle repetitions could ever escape. -/
  loopLen : Nat := 0

/-- Inspect the current state for a definite infinite loop without stepping.
    Mirrors the cycle-detection branch of `cycleStep`: split the state, look
    up the logic component in the buffer, and ask `leapCount` whether any
    data register has finite life. `none` from `leapCount` means the cycle
    is permanent — return its length. -/
def detectInfiniteLoop (thresh dmaxes : RegMap) (st : CycleState) : Option Nat :=
  if st.halted then none
  else
    let state := stateSplit thresh st.m
    match st.buf.getRange Prod.snd state.snd with
    | none => none
    | some range =>
      let startData := (range.getLast!).fst
      let endData := state.fst
      let history := endData :: (range.dropLast.map Prod.fst)
      match leapCount dmaxes history startData endData with
      | none => some range.length
      | some _ => none

/-- Like `cycleRunAux`, but with early-exit on `st.halted` and on definite
    infinite-loop detection. Lets callers pass an arbitrarily-large fuel
    without burning cycles after the program halts or after we've proven it
    will never halt. Structurally recursive on `Nat`, so no `partial def`. -/
def runWithLimit (table : Array (List Candidate))
    (fallback : List Candidate) (thresh dmaxes : RegMap) :
    CycleState → Nat → RunResult
  | st, 0 => { state := st }
  | st, fuel + 1 =>
    if st.halted then { state := st }
    else
      match detectInfiniteLoop thresh dmaxes st with
      | some k => { state := st, loopLen := k }
      | none => runWithLimit table fallback thresh dmaxes
        (cycleStep table fallback thresh dmaxes st) fuel

/-- Effectively-unbounded analog of `cycleRunFromRegProg`. Hardcodes a fuel of
    `2^63`; halting programs short-circuit on the `halted` check, definite
    infinite loops short-circuit on `detectInfiniteLoop`, and anything else
    relies on the worker being `terminate()`d externally. -/
def cycleRunUntilHalt (cyclen : Nat) (hcyclen : 0 < cyclen)
    (regProg : List (RegMap × RegMap)) (m : RegMap) : RunResult :=
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
OK <halted:0|1> <loopLen> <stepsSimulated> <result_factor_count> <p_1> <e_1> ...
```
`loopLen = 0` means no infinite loop was detected (program either halted or
hit fuel exhaustion). `loopLen > 0` means the runner detected a definite
infinite loop of that cycle length; `result_factor_count`/factors describe
the state at the point of detection. `ERR <reason>` on parse failure /
preconditions.
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

private def encodeResult (r : Runner.RunResult) : String :=
  let st := r.state
  let halted := if st.halted then 1 else 0
  s!"OK {halted} {r.loopLen} {st.stepsSimulated} {encodeRegMap st.m}"

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
