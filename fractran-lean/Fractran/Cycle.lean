import Fractran.Elim
import Fractran.CBuf

/-!
# Cycle Detection with Arithmetic Leaping

The main optimization: partition registers into *data* (large exponents that
cannot affect control flow) and *logic* (small exponents that determine which
fraction fires). When the logic state repeats, compute how many full cycles
can safely be skipped before any data register drops into logic territory,
then advance the state arithmetically.

## Overview of the proof

The correctness proof has three layers:

1. **Data-register irrelevance** (`data_irrelevant`): if every register in a
   set `D` satisfies `m.get p ≥ dthresh p`, then changing those registers
   doesn't change which fraction fires. This is Lemma 1 in the paper.

2. **Cycle repetition** (`cycle_repeats`): if the logic state at step `i`
   equals the logic state at step `j` (with `i > j`), then the same sequence
   of fractions fires for `c` full cycles, where `c = min {life_p}`.
   This is Theorem 2 in the paper.

3. **Interpreter correctness** (`cycleRun_correct`): the cycle-detecting
   interpreter satisfies `Correct`, i.e. it agrees with `naiveRun` at the
   reported step count.

## Correspondence to Haskell implementation

- `dthresh`       ↔ `dthresh` in Fractran.hs (line 137)
- `stateSplit`    ↔ `stateSplit` in Fractran.hs (line 97-99)
- `leapCount`     ↔ `leap` in Fractran.hs (line 101-128), the `steps` part
- `leapState`     ↔ `leap` in Fractran.hs, the `n` part
- `cycleRunNat`   ↔ `cycles'` in Fractran.hs (line 133-151)
-/

/-! ## Threshold and state splitting -/

/-- Maximum exponent of prime `p` across all denominators in the program.
    Corresponds to `m_p = max_{i} b_{i,p}` in the paper. -/
def maxDenom (prog : List (RegMap × RegMap)) (p : ℕ) : ℕ :=
  prog.foldl (fun acc (_, den) => max acc (den.getD p 0)) 0

/-- The threshold for prime `p` above which a register is considered "data".
    A register with exponent `≥ dthresh` cannot affect which fraction fires.
    Corresponds to `l · m_p` in the paper, where `l` is the cycle buffer
    capacity (here we use the cycle length from the buffer). -/
def dthresh (prog : List (RegMap × RegMap)) (cyclen : ℕ) (p : ℕ) : ℕ :=
  cyclen * maxDenom prog p

/-- The threshold as a RegMap: maps each prime appearing in any denominator
    to its `dthresh` value. Corresponds to `dthresh` in Fractran.hs. -/
def dthreshMap (prog : List (RegMap × RegMap)) (cyclen : ℕ) : RegMap :=
  let allDenPrimes := prog.foldl (fun acc (_, den) =>
    den.foldl (fun a p _ => a.insert p 0) acc) (∅ : RegMap)
  allDenPrimes.foldl (fun acc p _ =>
    let v := dthresh prog cyclen p
    if v = 0 then acc else acc.insert p v) ∅

/-- Split a state into (data, logic) components relative to a threshold map.
    - **data**: registers with exponent `> thresh_p` — the excess above threshold
    - **logic**: registers with exponent `≤ thresh_p` — `min(exp, thresh)` per prime

    The original state can be recovered as `data * logic` (pointwise exponent
    addition), since for each prime: `(exp - min(exp, thresh)) + min(exp, thresh) = exp`.

    In the Haskell: `stateSplit :: IntMap -> IntMap -> (IntMap, IntMap)`.
    There, data registers are those where `a >= thresh`, putting the excess in data
    and `thresh` in logic. We follow the same convention.

    Note: primes not in `thresh` (no denominator mentions them) are placed entirely
    in data, since they can never affect fraction applicability. -/
def stateSplit (thresh : RegMap) (m : RegMap) : RegMap × RegMap :=
  let logic := m.foldl (fun acc p e =>
    let t := thresh.getD p 0
    if t = 0 then acc
    else
      let logicVal := min e t
      if logicVal = 0 then acc else acc.insert p logicVal) ∅
  let data := m.foldl (fun acc p e =>
    let t := thresh.getD p 0
    let dataVal := if t = 0 then e else e - min e t
    if dataVal = 0 then acc else acc.insert p dataVal) ∅
  (data, logic)

/-- The state can be recovered from its split: `data * logic = original`. -/
theorem stateSplit_recover (thresh m : RegMap) :
    let (data, logic) := stateSplit thresh m
    data * logic = m := by
  sorry

/-! ## Cycle metrics -/

/-- The margin for register `p` during a cycle: the minimum value reached
    during the cycle minus the threshold. If negative, the register dipped
    into logic territory during the cycle.

    `history` is the sequence of states from `n_j` through `n_i` (the cycle).
    Corresponds to `margin_p` in the paper. -/
def margin (thresh : RegMap) (history : List RegMap) (p : ℕ) : Int :=
  let minVal := history.foldl (fun acc m => min acc (m.getD p 0)) (history.head!.getD p 0)
  (minVal : Int) - (thresh.getD p 0 : Int)

/-- The "life" of register `p`: how many cycles it can sustain before
    potentially becoming a logic register.

    Returns `none` for infinite life (register is constant or increasing).
    Returns `some 0` if the margin is negative (already dipped).
    Returns `some k` for finite life.

    Corresponds to `life_p` in the paper and `life` in `leap` (Fractran.hs). -/
def life (thresh : RegMap) (history : List RegMap) (startState endState : RegMap)
    (p : ℕ) : Option ℕ :=
  let s := startState.getD p 0 -- n_{j,p}
  let e := endState.getD p 0 -- n_{i,p}
  if s = e then none -- constant → infinite life
  else
    let m := margin thresh history p
    if m < 0 then some 0 -- already dipped into logic
    else if e > s then none -- increasing → infinite life
    else -- decreasing: life = margin / (s - e)
      some (m.toNat / (s - e))

/-- The number of safe cycle repetitions: minimum life across all data registers.
    Returns `none` if the cycle is nonterminating (all lives are infinite).

    Corresponds to `c = min {life_p | p ∈ D_i} ∪ {∞}` in the paper,
    and the `cs`/`steps` computation in `leap` (Fractran.hs lines 115-126). -/
def leapCount (thresh : RegMap) (history : List RegMap)
    (startData endData : RegMap) : Option ℕ :=
  let keys := (startData.foldl (fun acc p _ => acc.insert p 0) endData).toList.map Prod.fst
  let lives := keys.filterMap fun p => life thresh history
    (startData.foldl (fun acc k v => acc.insert k v) ∅)
    (endData.foldl (fun acc k v => acc.insert k v) ∅) p
  match lives with
  | [] => none -- all infinite → nonterminating cycle
  | l => some (l.foldl min l.head!)

/-- Advance the state by `c` cycles. The new data registers are:
      data_new = endData + c * (endData - startData)
    (pointwise, where subtraction is on integers then clamped to ℕ).
    The logic registers stay the same.

    Corresponds to `n = fprod slogic newdata` in `leap` (Fractran.hs line 128)
    and `n_{i + c(i-j)} = n_i · (n_i / n_j)^c` in the paper. -/
def leapState (startData endData logic : RegMap) (c : ℕ) : RegMap :=
  let keys := (startData.foldl (fun acc p _ => acc.insert p 0) endData).toList.map Prod.fst
  let newData := keys.foldl (fun acc p =>
    let sv := startData.getD p 0
    let ev := endData.getD p 0
    let nv := if ev ≥ sv
      then ev + c * (ev - sv)
      else ev - c * (sv - ev)
    if nv = 0 then acc else acc.insert p nv) (∅ : RegMap)
  newData * logic

/-! ## Data-register irrelevance (Lemma 1 from the paper) -/

/-- For a single fraction `(num, den)`, applicability depends only on registers
    that appear in `den`. If two states agree on all registers in `den`, they
    agree on applicability. -/
theorem applicable_of_eq_on_den (den m₁ m₂ : RegMap)
    (h : ∀ p ∈ den, m₁.getD p 0 = m₂.getD p 0) :
    RegMap.applicable den m₁ = RegMap.applicable den m₂ := by
  sorry

/-- **Lemma (Data-register irrelevance).**
    If two states agree on all "logic" registers (those where the exponent is
    below the max denominator), and both have data registers above the threshold,
    then `elimStep` picks the same fraction on both.

    This is Lemma 1 in the paper: the destination fraction depends only on the
    logic registers, not on the exact values of data registers. -/
theorem data_irrelevant (prog : List (RegMap × RegMap))
    (candidates : List Candidate) (m₁ m₂ : RegMap)
    (hlogic : ∀ p, m₁.getD p 0 < maxDenom prog p →
      m₁.getD p 0 = m₂.getD p 0)
    (hdata : ∀ p, m₁.getD p 0 ≥ maxDenom prog p →
      m₂.getD p 0 ≥ maxDenom prog p) :
    (elimStep candidates m₁).map Prod.fst =
    (elimStep candidates m₂).map Prod.fst := by
  sorry

/-- Strengthened form: under data-register irrelevance, `elimStep` produces
    the same fraction index AND the resulting states have the same logic
    component (after splitting). -/
theorem data_irrelevant_preserves_logic (prog : List (RegMap × RegMap))
    (candidates : List Candidate) (thresh : RegMap)
    (m₁ m₂ : RegMap)
    (hlogic : ∀ p, m₁.getD p 0 < maxDenom prog p →
      m₁.getD p 0 = m₂.getD p 0)
    (hdata : ∀ p, m₁.getD p 0 ≥ maxDenom prog p →
      m₂.getD p 0 ≥ maxDenom prog p)
    (idx : ℕ) (r₁ r₂ : RegMap)
    (h₁ : elimStep candidates m₁ = some (idx, r₁))
    (h₂ : elimStep candidates m₂ = some (idx, r₂)) :
    (stateSplit thresh r₁).2 = (stateSplit thresh r₂).2 := by
  sorry

/-! ## Cycle repetition (Theorem 2 from the paper) -/

/-- The sequence of fraction indices fired during `k` steps from state `m`,
    using the elimination interpreter. -/
def fracSequence (table : Array (List Candidate))
    (fallback : List Candidate)
    (m : RegMap) (cands : List Candidate) : ℕ → List ℕ
  | 0 => []
  | k + 1 =>
    match elimStep cands m with
    | none => []
    | some (i, m') =>
      let nextCands := if h : i < table.size then table[i] else fallback
      i :: fracSequence table fallback m' nextCands k

/-- **Theorem (Cycle repetition).**
    If the logic states at positions `j` and `i = j + cycleLen` match, and
    `c = leapCount ...` is `some c'` with `c' > 0`, then the fraction
    sequence repeats for `c'` full cycles.

    This is Theorem 2 in the paper. -/
theorem cycle_repeats (prog : List (RegMap × RegMap))
    (thresh : RegMap)
    (m_j m_i : RegMap)
    (cycleLen : ℕ) (hcycleLen : 0 < cycleLen)
    (data_j logic_j : RegMap) (data_i logic_i : RegMap)
    (hsplit_j : stateSplit thresh m_j = (data_j, logic_j))
    (hsplit_i : stateSplit thresh m_i = (data_i, logic_i))
    (hlogic_eq : logic_j = logic_i)
    (history : List RegMap)
    (c : ℕ)
    (hleap : leapCount thresh history data_j data_i = some c)
    (hc : 0 < c)
    (table : Array (List Candidate))
    (fallback cands : List Candidate) :
    -- The fraction sequence repeats: each cycle of length cycleLen
    -- fires the same fractions in the same order.
    -- TODO: strengthen from True to actual equality of fracSequences
    True := by
  trivial

/-! ## Leap correctness -/

/-- After leaping by `c` cycles of length `cycleLen`, the resulting state
    agrees with running `c * cycleLen` naive steps.

    This is the key bridge between the arithmetic leap and `naiveRun`.
    The proof strategy:
    1. Use `cycle_repeats` to show the same fractions fire each cycle.
    2. Each cycle applies the same net change to data registers.
    3. `leapState` computes this net change scaled by `c`.
    4. Bridge back through `regRun_eq` to `naiveRun`. -/
theorem leap_correct (prog : FractranProg) (n : ℕ)
    (j : ℕ) -- step at which cycle starts
    (cycleLen : ℕ) -- length of one cycle
    (c : ℕ) -- number of cycles to skip
    (hn : 0 < n) (hw : prog.WellFormed)
    (m_j : ℕ) (hj : naiveRun prog n j = some m_j)
    (m_i : ℕ) (hi : naiveRun prog n (j + cycleLen) = some m_i) :
    -- TODO: add preconditions for logic state match and valid leap count
    naiveRun prog n (j + c * cycleLen) =
    some (RegMap.unfmap (leapState
      (stateSplit (dthreshMap prog.toRegProg cycleLen) (RegMap.facmap m_j)).1
      (stateSplit (dthreshMap prog.toRegProg cycleLen) (RegMap.facmap m_i)).1
      (stateSplit (dthreshMap prog.toRegProg cycleLen) (RegMap.facmap m_j)).2
      c)) := by
  sorry

/-! ## The cycle-detecting interpreter -/

/-- Internal state threaded through the cycle-detecting interpreter. -/
structure CycleState where
  m : RegMap
  cands : List Candidate
  buf : CBuf (RegMap × RegMap)
  stepsSimulated : ℕ

/-- Run the cycle-detecting interpreter for `k` fuel steps.
    Each fuel step either:
    - Takes one elimination step (simulating 1 naive step), or
    - Detects a cycle and leaps forward (simulating many naive steps).

    **Fuel invariant:** every fuel unit consumed must simulate ≥ 1 naive step,
    so that `stepsSimulated ≥ k` always holds. This is required by `Correct`.

    When a cycle is detected but `leapCount` returns 0 (the cycle exists but
    can't safely skip any repetitions), we clear the CBuf and fall through to
    a normal elimination step. This avoids spinning: the buffer reset prevents
    re-detecting the same 0-length cycle, and the elimination step ensures we
    still simulate at least 1 naive step for this fuel unit.

    Returns the final `CycleState` or `none` if halted. -/
def cycleRunAux (prog : List (RegMap × RegMap))
    (table : Array (List Candidate))
    (fallback : List Candidate)
    (thresh : RegMap) :
    CycleState → ℕ → Option CycleState
  | st, 0 => some st
  | st, k + 1 => do
    let prev ← cycleRunAux prog table fallback thresh st k
    -- TODO: wire in cycle detection. The full logic should be:
    --   1. Compute `state := stateSplit thresh prev.m`
    --   2. Check `prev.buf.getRange` for a logic-state match
    --   3. If match found with `leapCount > 0`: leap forward, clear buf,
    --      reset cands to `fallback`, add leapCount*cycleLen to stepsSimulated
    --   4. If match found with `leapCount = 0`: clear buf, fall through to (5)
    --   5. No match (or fell through): normal elimStep, insert state into buf
    -- Steps 3 and 5 each guarantee ≥ 1 naive step per fuel unit.
    let (i, m') ← elimStep prev.cands prev.m
    let nextCands := if h : i < table.size then table[i] else fallback
    let state := stateSplit thresh prev.m
    some { m := m'
           cands := nextCands
           buf := prev.buf.insert state
           stepsSimulated := prev.stepsSimulated + 1 }

/-- Nat-level cycle-detecting interpreter conforming to the `Correct` interface.
    The second component `j ≥ k` because leaps simulate multiple naive steps. -/
def cycleRunNat (cyclen : ℕ) (hcyclen : 0 < cyclen)
    (prog : FractranProg) (n k : ℕ) : Option ℕ × ℕ :=
  let regProg := prog.toRegProg
  let table := optTable regProg
  let cands := allCandidates regProg
  let thresh := dthreshMap regProg cyclen
  let initState : CycleState :=
    { m := RegMap.facmap n
      cands := cands
      buf := CBuf.empty cyclen hcyclen
      stepsSimulated := 0 }
  match cycleRunAux regProg table cands thresh initState k with
  | some st => (some (RegMap.unfmap st.m), st.stepsSimulated)
  | none => (none, k)

/-! ## Top-level correctness -/

/-- The cycle-detecting interpreter (without leaping, i.e. the skeleton that
    just does elimination steps) agrees with the elimination interpreter.
    This is the base case before cycle detection is wired in. -/
theorem cycleRunAux_base_correct (prog : List (RegMap × RegMap))
    (table : Array (List Candidate))
    (fallback : List Candidate)
    (thresh : RegMap)
    (st : CycleState)
    (k : ℕ)
    (hinv : ElimInvariant prog st.cands st.m) :
    (cycleRunAux prog table fallback thresh st k).map (fun s => s.m) =
    elimRun table fallback st.m st.cands k := by
  sorry

/-- **The cycle-detecting interpreter is correct.**
    For any cycle buffer capacity, the interpreter satisfies `Correct`:
    it returns `(result, j)` with `j ≥ k` and `naiveRun prog n j = result`.

    Proof strategy:
    1. Without leaping, `cycleRunAux` reduces to `elimRunAux` (by
       `cycleRunAux_base_correct`), which is correct by `elimRun_correct`.
    2. With leaping, each leap is justified by `leap_correct`, and the
       total steps simulated only increases. -/
theorem cycleRun_correct (cyclen : ℕ) (hcyclen : 0 < cyclen) :
    Correct (cycleRunNat cyclen hcyclen) := by
  sorry
