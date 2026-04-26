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

/-- One-step unfolding of `detectInfiniteLoop` with the `let` bindings inlined.
    Holds definitionally, but exposed as a named lemma so that `rw` lets us
    case-split on the underlying `if`/`match`/`match` without the lets
    getting in the way. -/
private theorem detectInfiniteLoop_unfold (thresh dmaxes : RegMap) (st : CycleState) :
    detectInfiniteLoop thresh dmaxes st =
      if st.halted then none
      else
        match st.buf.getRange Prod.snd (stateSplit thresh st.m).snd with
        | none => none
        | some range =>
          match leapCount dmaxes
              ((stateSplit thresh st.m).fst :: range.dropLast.map Prod.fst)
              (range.getLast!).fst (stateSplit thresh st.m).fst with
          | none => some range.length
          | some _ => none := rfl

/-- **Soundness of infinite-loop detection.** When `detectInfiniteLoop`
    fires, the program from `st` truly never halts.

    The mathematical claim: `leapCount` returning `none` means every data
    register has either zero data delta or a strictly increasing one (with
    safe margin) across the cycle, so the cycle invariant survives any
    number of repetitions, so the same fraction sequence fires forever, so
    `naiveStep` never returns `none`.

    Proof structure (chains the three lemmas added in `Cycle.lean`):
    1. Unpack `hloop` to get the buffer match `range` and `leapCount = none`.
    2. Mirror `leap_correct`'s prelude: extract `m_start` from the buffer,
       build `hone_cycle`, `hcycle_inv`, and `regRun`-level `st_m_alt`.
    3. Combine `leapCount_none_implies_data_le` with `stateSplit_recover` and
       the buffer's logic-state match to get `m_start ≤ st_m_alt` per prime.
    4. Build the per-`c` `hsafe` predicate of `iterated_cycle_per_reg` from
       `cycle_low_intermediate_implies_eq` (logic-register branch) and the
       absolute non-negativity (data-register branch).
    5. For any `j ≥ st.stepsSimulated`, pick `c = (j - stepsSimulated) / L
       + 1` so that `j ≤ stepsSimulated + L * c`. Apply
       `iterated_cycle_per_reg` to get `regRun` succeeding at `L * (c + 1)`,
       lift to `naiveRun` via `regRun_map_unfmap`, then contradict any
       hypothetical `naiveRun ... j = none` via `naiveRun_none_of_ge`. -/
theorem detectInfiniteLoop_sound
    (prog : FractranProg) (n : ℕ)
    (hw : prog.WellFormed) (_hn : 0 < n)
    (thresh dmaxes : RegMap) (st : CycleState) (k : ℕ)
    (hthresh : thresh = dthreshMap prog.toRegProg st.buf.cap)
    (_hdmaxes : dmaxes = dmaxesMap prog.toRegProg)
    (hinv : naiveRun prog n st.stepsSimulated = some (RegMap.unfmap st.m))
    (hwf : RegMap.WF st.m)
    (hbuf : BufferInvariant prog n thresh st.buf st.stepsSimulated)
    (hloop : detectInfiniteLoop thresh dmaxes st = some k) :
    ∀ j, st.stepsSimulated ≤ j → naiveRun prog n j ≠ none := by
  -- Step 1: Unpack hloop into st.halted = false, getRange = some range,
  --         leapCount = none. detectInfiniteLoop wraps an `if`, then a `let`
  --         that hides a nested `match`; we destructure manually because
  --         `split_ifs` doesn't peel through the `let`.
  obtain ⟨range, hnh, hgr, hlc⟩ : ∃ range,
      st.halted = false ∧
      st.buf.getRange Prod.snd (stateSplit thresh st.m).snd = some range ∧
      leapCount dmaxes
        ((stateSplit thresh st.m).fst :: range.dropLast.map Prod.fst)
        (range.getLast!).fst (stateSplit thresh st.m).fst = none := by
    rw [detectInfiniteLoop_unfold] at hloop
    cases hh : st.halted
    · -- st.halted = false
      simp only [hh, Bool.false_eq_true, ↓reduceIte] at hloop
      cases hgr : st.buf.getRange Prod.snd (stateSplit thresh st.m).snd
      · rw [hgr] at hloop; simp at hloop
      · rename_i range
        rw [hgr] at hloop
        simp only at hloop  -- iota-reduce `match some range`
        cases hlc : leapCount dmaxes
            ((stateSplit thresh st.m).fst :: range.dropLast.map Prod.fst)
            (range.getLast!).fst (stateSplit thresh st.m).fst
        · exact ⟨range, rfl, rfl, hlc⟩
        · rw [hlc] at hloop; simp at hloop
    · -- st.halted = true
      simp [hh] at hloop
  clear hloop  -- already extracted what we need
  -- Step 2: Extract m_start from buffer (bundled).
  obtain ⟨m_start, st_m_alt, hLpos, hL_le_steps, hL_cap, hstart_wf,
          hstart_run, _hone_cycle, hreg_one, hwf_st_m_alt, hgetD_alt,
          hcycle_inv, hlogic_match, hrange_getLast!⟩ :=
    cycle_match_extracts_m_start prog n hw _hn thresh st hthresh hinv hwf hbuf range hgr
  set L := range.length
  -- Transfer CycleInvariant to st_m_alt (same getD per prime).
  have hcycle_inv_alt : CycleInvariant prog.toRegProg st.buf.cap m_start st_m_alt := by
    intro p
    have hg : st_m_alt.getD p 0 = st.m.getD p 0 := hgetD_alt p
    rcases hcycle_inv p with heq | ⟨h₁, h₂⟩
    · left; rw [hg]; exact heq
    · right; refine ⟨h₁, ?_⟩; rw [hg]; exact h₂
  -- Step 3: Absolute delta is non-negative for every prime (combining
  --         leapCount_none_implies_data_le, stateSplit_recover, and the
  --         buffer's logic-state match).
  have habs_le : ∀ p, m_start.getD p 0 ≤ st_m_alt.getD p 0 := by
    intro p
    have hdata_le := leapCount_none_implies_data_le dmaxes
      ((stateSplit thresh st.m).fst :: range.dropLast.map Prod.fst)
      (range.getLast!).fst (stateSplit thresh st.m).fst hlc p
    rw [hrange_getLast!] at hdata_le
    have hs_decomp : m_start.getD p 0 =
        (stateSplit thresh m_start).fst.getD p 0 +
        (stateSplit thresh m_start).snd.getD p 0 := by
      have hrec := stateSplit_recover thresh m_start p
      simp only [] at hrec
      rw [RegMap.mul_getD] at hrec; linarith
    have he_decomp : st.m.getD p 0 =
        (stateSplit thresh st.m).fst.getD p 0 +
        (stateSplit thresh st.m).snd.getD p 0 := by
      have hrec := stateSplit_recover thresh st.m p
      simp only [] at hrec
      rw [RegMap.mul_getD] at hrec; linarith
    have hlg := hlogic_match p
    have hga := hgetD_alt p
    omega
  -- Step 4: Build hsafe for any c.
  have hsafe_for : ∀ (c : ℕ), ∀ i, i < L → ∀ m_i, RegMap.WF m_i →
      regRun prog.toRegProg m_start i = some m_i →
      ∀ p, (m_i.getD p 0 < maxDenom prog.toRegProg p →
              (c : ℤ) * ((st_m_alt.getD p 0 : ℤ) - (m_start.getD p 0 : ℤ)) = 0) ∧
           (m_i.getD p 0 ≥ maxDenom prog.toRegProg p →
              (m_i.getD p 0 : ℤ) +
                (c : ℤ) * ((st_m_alt.getD p 0 : ℤ) - (m_start.getD p 0 : ℤ)) ≥
              maxDenom prog.toRegProg p) := by
    intro c i hi m_i _hwf_mi hrun_mi p
    refine ⟨?_, ?_⟩
    · intro hp_low
      have heq : m_start.getD p 0 = st_m_alt.getD p 0 :=
        cycle_low_intermediate_implies_eq prog hw st.buf.cap L hLpos hL_cap
          m_start st_m_alt hstart_wf hreg_one hcycle_inv_alt
          i hi m_i hrun_mi p hp_low
      have : (st_m_alt.getD p 0 : ℤ) - (m_start.getD p 0 : ℤ) = 0 := by
        rw [heq]; ring
      rw [this]; ring
    · intro hp_high
      have hdelta_nonneg : (0 : ℤ) ≤
          (st_m_alt.getD p 0 : ℤ) - (m_start.getD p 0 : ℤ) := by
        have := habs_le p; omega
      have hc_nonneg : (0 : ℤ) ≤ (c : ℤ) := by positivity
      have hcmul_nonneg : (0 : ℤ) ≤
          (c : ℤ) * ((st_m_alt.getD p 0 : ℤ) - (m_start.getD p 0 : ℤ)) :=
        mul_nonneg hc_nonneg hdelta_nonneg
      have : (maxDenom prog.toRegProg p : ℤ) ≤ (m_i.getD p 0 : ℤ) := by
        exact_mod_cast hp_high
      linarith
  -- Step 5: For any j ≥ st.stepsSimulated, naiveRun cannot be none.
  intro j hj hjnone
  -- Pick c large enough that j ≤ st.stepsSimulated + L * c.
  set c := (j - st.stepsSimulated) / L + 1 with hc_def
  have hj_bound : j ≤ st.stepsSimulated + L * c := by
    have hmod : (j - st.stepsSimulated) % L < L := Nat.mod_lt _ hLpos
    have hdiv_eq := Nat.div_add_mod (j - st.stepsSimulated) L
    have : (j - st.stepsSimulated) < L * c := by
      rw [hc_def, Nat.mul_add, Nat.mul_one]; omega
    omega
  -- Apply iterated_cycle_per_reg to get regRun for L * (c + 1) steps.
  obtain ⟨m_final, hreg_final, _hwf_final, _hdiff_final⟩ :=
    iterated_cycle_per_reg prog hw m_start st_m_alt L hstart_wf hwf_st_m_alt
      hreg_one c (hsafe_for c)
  -- Lift to naiveRun.
  have hnaive_final : naiveRun prog (RegMap.unfmap m_start) (L * (c + 1)) =
      some (RegMap.unfmap m_final) := by
    have h := regRun_map_unfmap prog m_start hstart_wf (L * (c + 1)) hw
    rw [hreg_final] at h; simpa using h.symm
  have hbig : naiveRun prog n (st.stepsSimulated - L + L * (c + 1)) =
      some (RegMap.unfmap m_final) := by
    have h := naiveRun_add prog n (st.stepsSimulated - L) (L * (c + 1))
    rw [hstart_run] at h
    change naiveRun prog n (st.stepsSimulated - L + L * (c + 1)) =
      naiveRun prog (RegMap.unfmap m_start) (L * (c + 1)) at h
    rw [h]; exact hnaive_final
  have hsimplify : st.stepsSimulated - L + L * (c + 1) = st.stepsSimulated + L * c := by
    rw [Nat.mul_add, Nat.mul_one]; omega
  rw [hsimplify] at hbig
  -- Contradiction: naiveRun n j = none implies naiveRun n (stepsSimulated + L*c) = none.
  have hnone_big := naiveRun_none_of_ge prog n hj_bound hjnone
  rw [hbig] at hnone_big
  exact Option.some_ne_none _ hnone_big

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
