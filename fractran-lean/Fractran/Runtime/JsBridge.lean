import Fractran.Runtime.Cycle
import Fractran.Runtime.Parse

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

Exports `fractran_run_lean : String → String → String → String` for the
browser worker. Three plain-text args:

* `cyclenStr` — cycle-detection buffer length, decimal `Nat`.
* `programSrc` — source text of the FRACTRAN program (see `Fractran.Parse`).
* `inputSrc`  — source text of the initial state.

Output:

```
OK <halted:0|1> <loopLen> <stepsSimulated> <result_factor_count> <p_1> <e_1> ...
ERR <reason>
```

`loopLen = 0` means no infinite loop was detected (program either halted or
hit fuel exhaustion). `loopLen > 0` means the runner detected a definite
infinite loop of that cycle length; the factors describe the state at the
point of detection.
-/

namespace Fractran.JsBridge

private def encodeRegMap (m : RegMap) : String :=
  let factors := m.toList
  let body := factors.foldl (fun acc (p, e) => acc ++ s!" {p} {e}") ""
  s!"{factors.length}{body}"

private def encodeResult (r : Runner.RunResult) : String :=
  let st := r.state
  let halted := if st.halted then 1 else 0
  s!"OK {halted} {r.loopLen} {st.stepsSimulated} {encodeRegMap st.m}"

def fractranRunStr (cyclenStr programSrc inputSrc : String) : String :=
  match cyclenStr.trimAscii.toString.toNat? with
  | none => "ERR bad_cyclen"
  | some 0 => "ERR cyclen_zero"
  | some (cyclen + 1) =>
    match Fractran.Parse.parseProgram programSrc with
    | .error e => s!"ERR program: {e}"
    | .ok regProg =>
      match Fractran.Parse.parseInput inputSrc with
      | .error e => s!"ERR input: {e}"
      | .ok init =>
        encodeResult (Runner.cycleRunUntilHalt (cyclen + 1) (Nat.succ_pos _) regProg init)

@[export fractran_run_lean]
def fractranRunLean (cyclenStr programSrc inputSrc : String) : String :=
  fractranRunStr cyclenStr programSrc inputSrc

end Fractran.JsBridge
