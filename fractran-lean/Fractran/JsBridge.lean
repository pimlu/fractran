import Fractran.Cycle
import Fractran.Runtime.JsBridge

set_option linter.style.show false

/-!
# JS Bridge runner — proof side

The runtime side (`Fractran.Runtime.JsBridge`) wraps the cycle-detecting
interpreter with two extra early-exits that don't appear in the proven
`cycleRunAux`:

1. `halted` — return immediately, state unchanged.
2. `detectInfiniteLoop` returns `some k` — return immediately, state unchanged,
   `loopLen := k`.

Neither exit changes the state, so the `naiveRun` invariant carried by
`cycleStep_correct` survives into `runWithLimit`. That gives us
`runWithLimit_correct` below — the analogue of `cycleRunAux_correct` for the
JS bridge runner. The structure of the proof mirrors `cycleRunAux_correct`
exactly, with two extra "no step taken" branches that are trivial.

## What's not proven here

`detectInfiniteLoop_sound` (below) — when `detectInfiniteLoop` returns
`some k`, the program from this state never halts. Currently a `sorry`.
The mathematical content extends the existing `cycle_properties` /
`leap_correct` chain (which handles a *specific finite* number of cycle
repetitions) to "any number of repetitions are safe," which then implies
`naiveRun prog n j ≠ none` for all `j ≥ st.stepsSimulated`.
-/

namespace Fractran.JsBridge.Runner

/-- **Soundness of infinite-loop detection.** When `detectInfiniteLoop`
    fires, the program from `st` truly never halts.

    The mathematical claim: `leapCount` returning `none` means every data
    register is constant or strictly increasing across one cycle, so the
    cycle invariant survives any number of repetitions, so the same
    fraction sequence fires forever, so `naiveStep` never returns `none`.

    Currently a `sorry`. Proving it requires extending `cycle_properties`
    (which is currently parameterised by a specific safe-repetition count
    `c`) to "for all `c`, c repetitions are safe under the
    `leapCount = none` hypothesis," then chaining via `naiveRun_add`. -/
theorem detectInfiniteLoop_sound
    (prog : FractranProg) (n : ℕ)
    (hw : prog.WellFormed) (hn : 0 < n)
    (thresh dmaxes : RegMap) (st : CycleState) (k : ℕ)
    (_htable_consistent : thresh = dthreshMap prog.toRegProg st.buf.cap)
    (_hdmaxes_consistent : dmaxes = dmaxesMap prog.toRegProg)
    (_hinv : naiveRun prog n st.stepsSimulated = some (RegMap.unfmap st.m))
    (_hwf : RegMap.WF st.m)
    (_hbuf : BufferInvariant prog n thresh st.buf st.stepsSimulated)
    (_hloop : detectInfiniteLoop thresh dmaxes st = some k) :
    ∀ j, st.stepsSimulated ≤ j → naiveRun prog n j ≠ none := by
  sorry

/-- **`runWithLimit` preserves the `naiveRun` invariant.**

    For every state in the result trajectory: either it's halted (and
    `naiveStep` returns `none`), or it matches `naiveRun` at its
    `stepsSimulated`. Loop-detected exits (where `result.loopLen > 0`)
    fall in the "still running" case — the state hasn't changed, so the
    incoming `naiveRun` invariant is preserved verbatim.

    This says nothing about whether the loop-detected exit is *correct* in
    the sense of "the program will never halt" — that's
    `detectInfiniteLoop_sound` above. It only says the reported state is
    a real reachable state. -/
theorem runWithLimit_correct
    (prog : FractranProg) (n : ℕ)
    (hw : prog.WellFormed) (hn : 0 < n)
    (table : Array (List Candidate)) (fallback : List Candidate)
    (thresh dmaxes : RegMap) (st : CycleState) (fuel : ℕ)
    (htable : table = optTable prog.toRegProg)
    (hfallback : fallback = allCandidates prog.toRegProg)
    (hthresh : thresh = dthreshMap prog.toRegProg st.buf.cap)
    (hdmaxes : dmaxes = dmaxesMap prog.toRegProg)
    (hinv : naiveRun prog n st.stepsSimulated = some (RegMap.unfmap st.m))
    (hhalted_inv : st.halted → naiveStep prog (RegMap.unfmap st.m) = none)
    (hwf : RegMap.WF st.m)
    (helim : ElimInvariant prog.toRegProg st.cands st.m)
    (hbuf : BufferInvariant prog n thresh st.buf st.stepsSimulated) :
    let st' := (runWithLimit table fallback thresh dmaxes st fuel).state
    if st'.halted then
      naiveRun prog n st'.stepsSimulated = some (RegMap.unfmap st'.m) ∧
      naiveStep prog (RegMap.unfmap st'.m) = none
    else
      naiveRun prog n st'.stepsSimulated = some (RegMap.unfmap st'.m) := by
  induction fuel generalizing st with
  | zero =>
    -- (runWithLimit ... st 0).state reduces definitionally to st.
    show if st.halted then
        naiveRun prog n st.stepsSimulated = some (RegMap.unfmap st.m) ∧
        naiveStep prog (RegMap.unfmap st.m) = none
      else
        naiveRun prog n st.stepsSimulated = some (RegMap.unfmap st.m)
    cases hh : st.halted
    · exact hinv
    · exact ⟨hinv, hhalted_inv hh⟩
  | succ fuel ih =>
    -- Re-express the goal so the let-bound expression is the explicit
    -- if/match form (definitionally equal to the recursive call). `change`
    -- doesn't unify the inner `match` cleanly here, so we use `show`.
    show let st' := (if st.halted then ({ state := st } : RunResult)
                     else match detectInfiniteLoop thresh dmaxes st with
                          | some k => { state := st, loopLen := k }
                          | none => runWithLimit table fallback thresh dmaxes
                              (cycleStep table fallback thresh dmaxes st) fuel).state
          if st'.halted then
            naiveRun prog n st'.stepsSimulated = some (RegMap.unfmap st'.m) ∧
            naiveStep prog (RegMap.unfmap st'.m) = none
          else
            naiveRun prog n st'.stepsSimulated = some (RegMap.unfmap st'.m)
    cases hh : st.halted
    · -- not halted: outer if takes the else branch (st.halted = false)
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases hd : detectInfiniteLoop thresh dmaxes st with
      | some k =>
        -- early exit on loop detection, state = st (st.halted = false here)
        simp only [hh, Bool.false_eq_true, ↓reduceIte]
        exact hinv
      | none =>
        -- recurse on cycleStep via ih
        have hstep := cycleStep_correct prog n hw hn table fallback thresh dmaxes st
          htable hfallback hthresh hdmaxes hinv hhalted_inv hwf helim hbuf
        obtain ⟨hinv', hhalted', hwf', helim', hbuf'⟩ := hstep
        have hthresh' : thresh = dthreshMap prog.toRegProg
            (cycleStep table fallback thresh dmaxes st).buf.cap := by
          rw [hthresh, cycleStep_preserves_cap]
        exact ih _ hthresh' hinv' hhalted' hwf' helim' hbuf'
    · -- already halted: outer if takes the then branch, state = st
      simp only [hh, ↓reduceIte]
      exact ⟨hinv, hhalted_inv hh⟩

/-! ## Top-level wrapper for `cycleRunUntilHalt`

`cycleRunUntilHalt` is the entry point used by the wire-format bridge: it
takes a pre-factored program (`List (RegMap × RegMap)`) and an initial
`RegMap`, and runs `runWithLimit` with a hardcoded `2^63` fuel. To get a
`Correct`-style statement we need a `Nat`-keyed wrapper that goes through
`prog.toRegProg` and `RegMap.facmap`, mirroring `cycleRunNat`. -/

/-- Run `cycleRunUntilHalt` from a `Nat` initial state via `RegMap.facmap`. -/
def cycleRunUntilHaltNat (cyclen : ℕ) (hcyclen : 0 < cyclen)
    (prog : FractranProg) (n : ℕ) : RunResult :=
  cycleRunUntilHalt cyclen hcyclen prog.toRegProg (RegMap.facmap n)

/-- **Top-level invariant for `cycleRunUntilHaltNat`.**

    Mirrors `cycleRun_correct` but for the JS bridge runner. The result's
    `state` field always corresponds to a real reachable state of the naive
    interpreter. Says nothing about `loopLen` — see `detectInfiniteLoop_sound`. -/
theorem cycleRunUntilHaltNat_naiveRun_consistent
    (cyclen : ℕ) (hcyclen : 0 < cyclen)
    (prog : FractranProg) (n : ℕ)
    (hw : prog.WellFormed) (hn : 0 < n) :
    let result := cycleRunUntilHaltNat cyclen hcyclen prog n
    let st' := result.state
    if st'.halted then
      naiveRun prog n st'.stepsSimulated = some (RegMap.unfmap st'.m) ∧
      naiveStep prog (RegMap.unfmap st'.m) = none
    else
      naiveRun prog n st'.stepsSimulated = some (RegMap.unfmap st'.m) := by
  let table := optTable prog.toRegProg
  let cands := allCandidates prog.toRegProg
  let thresh := dthreshMap prog.toRegProg cyclen
  let dmaxes := dmaxesMap prog.toRegProg
  let initState : CycleState :=
    { m := RegMap.facmap n, cands := cands, buf := CBuf.empty cyclen hcyclen,
      stepsSimulated := 0 }
  have hinit : naiveRun prog n 0 = some (RegMap.unfmap (RegMap.facmap n)) := by
    simp [naiveRun, RegMap.facmap_unfmap n hn]
  have hinit' : naiveRun prog n initState.stepsSimulated = some initState.m.unfmap := hinit
  exact runWithLimit_correct prog n hw hn table cands thresh dmaxes initState (2 ^ 63)
    rfl rfl (by simp [initState, thresh]) rfl hinit'
    (by simp [initState]) (RegMap.facmap_wf n) (allCandidates_invariant prog.toRegProg _)
    (bufferInvariant_empty prog n thresh cyclen hcyclen 0)

end Fractran.JsBridge.Runner
