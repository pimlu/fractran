import Fractran.Runtime.Elim
import Fractran.Runtime.CBuf

/-!
# Cycle Detection with Arithmetic Leaping (runtime)

The mathlib-free runtime side of the cycle-detecting interpreter. The
correctness proofs (data-register irrelevance, cycle repetition, top-level
`Correct` predicate), the `CycleInvariant` / `BufferInvariant` / `CandidatesWF`
predicates, and the Nat-keyed wrappers that go through `toRegProg`/`facmap`
all live in `Fractran.Cycle`.

What's here:

- threshold map and state splitting (`maxDenom`, `dthresh`, `dthreshMap`,
  `stateSplit`)
- leap arithmetic (`margin`, `life`, `leapCount`, `leapState`)
- the `BEq RegMap` instance used by `CBuf.getRange` for cycle detection
- max-denominator map (`dmaxesMap`)
- `CycleState` structure
- the per-step interpreter (`cycleStep`) and the iterator (`cycleRunAux`)
-/

/-! ## Threshold and state splitting -/

/-- Maximum exponent of prime `p` across all denominators in the program.
    Corresponds to `m_p = max_{i} b_{i,p}` in the paper. -/
def maxDenom (prog : List (RegMap × RegMap)) (p : Nat) : Nat :=
  prog.foldl (fun acc (_, den) => max acc (den.getD p 0)) 0

/-- The threshold for prime `p` above which a register is considered "data".
    A register with exponent `≥ dthresh` cannot affect which fraction fires.
    Corresponds to `l · m_p` in the paper, where `l` is the cycle buffer
    capacity (here we use the cycle length from the buffer). -/
def dthresh (prog : List (RegMap × RegMap)) (cyclen : Nat) (p : Nat) : Nat :=
  cyclen * maxDenom prog p

/-- The threshold as a RegMap: maps each prime appearing in any denominator
    to its `dthresh` value. Corresponds to `dthresh` in Fractran.hs. -/
def dthreshMap (prog : List (RegMap × RegMap)) (cyclen : Nat) : RegMap :=
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

/-! ## Leap arithmetic -/

/-- For data register `p`, the difference between its minimum exponent across
    the cycle history and the threshold. Used in `life` to compute how many
    cycle repetitions are safe before `p` could enter logic territory.

    Corresponds to `margin_p` in `leap` (Fractran.hs). -/
def margin (thresh : RegMap) (history : List RegMap) (p : Nat) : Int :=
  let minVal := history.foldl (fun acc m => min acc (m.getD p 0)) (history.head!.getD p 0)
  (minVal : Int) - (thresh.getD p 0 : Int)

/-- The "life" of register `p`: how many cycles it can sustain before
    potentially becoming a logic register.

    Returns `none` for infinite life (register is constant or increasing).
    Returns `some 0` if the margin is negative (already dipped).
    Returns `some k` for finite life.

    Corresponds to `life_p` in the paper and `life` in `leap` (Fractran.hs). -/
def life (thresh : RegMap) (history : List RegMap) (startState endState : RegMap)
    (p : Nat) : Option Nat :=
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
    (startData endData : RegMap) : Option Nat :=
  let keys := (startData.foldl (fun acc p _ => acc.insert p 0) endData).toList.map Prod.fst
  let lives := keys.filterMap fun p => life thresh history
    (startData.foldl (fun acc k v => acc.insert k v) ∅)
    (endData.foldl (fun acc k v => acc.insert k v) ∅) p
  match lives with
  | [] => none -- all infinite → nonterminating cycle
  | l => some (l.foldl min l.head!)

/-- The new data state after leaping `c` cycle repetitions, multiplied back
    in with the logic state. For each register `p`, the per-cycle delta is
    `endData[p] - startData[p]`, applied `c` extra times beyond the natural
    cycle endpoint. -/
def leapState (startData endData logic : RegMap) (c : Nat) : RegMap :=
  let keys := (startData.foldl (fun acc p _ => acc.insert p 0) endData).toList.map Prod.fst
  let newData := keys.foldl (fun acc p =>
    let sv := startData.getD p 0
    let ev := endData.getD p 0
    let nv := if ev ≥ sv
      then ev + c * (ev - sv)
      else ev - c * (sv - ev)
    if nv = 0 then acc else acc.insert p nv) (∅ : RegMap)
  newData * logic

/-! ## Equality and max-denominator infrastructure -/

/-- Canonical comparison for RegMap (sorted key-value lists).
    Used by `CBuf.getRange` to detect repeated logic states. -/
instance : BEq RegMap where
  beq a b := a.toList == b.toList

/-- Max denominator per prime across all fractions. Corresponds to
    `dmaxes = M.unionsWith max $ map snd fmaps` in Fractran.hs. -/
def dmaxesMap (prog : List (RegMap × RegMap)) : RegMap :=
  prog.foldl (fun acc (_, den) =>
    den.foldl (fun a p e =>
      let cur := a.getD p 0
      if e > cur then a.insert p e else a) acc) ∅

/-! ## The cycle-detecting interpreter -/

/-- Internal state threaded through the cycle-detecting interpreter. -/
structure CycleState where
  m : RegMap
  cands : List Candidate
  buf : CBuf (RegMap × RegMap)
  stepsSimulated : Nat
  halted : Bool := false

/-- One iteration of the cycle-detecting interpreter.
    - If the logic state was seen before, attempt an arithmetic leap.
    - Otherwise, run a single elimination step and record the new logic state. -/
def cycleStep (table : Array (List Candidate))
    (fallback : List Candidate)
    (thresh dmaxes : RegMap)
    (st : CycleState) : CycleState :=
  if st.halted then st
  else
  -- 1. Split current state into (data, logic) components
  let state := stateSplit thresh st.m
  -- 2. Check if the logic state was seen before in the buffer
  match st.buf.getRange Prod.snd state.snd with
  | some range =>
    -- Cycle detected! range is newest-first, match is last element.
    let startData := (range.getLast!).fst  -- matching (oldest) entry's data
    let endData := state.fst               -- current state's data
    -- history: current data + intermediate datas (excluding the match)
    let history := endData :: (range.dropLast.map Prod.fst)
    let c := match leapCount dmaxes history startData endData with
      | some c => c
      | none => 0  -- nonterminating cycle or can't compute, treat as c=0
    if c = 0 then
      -- Can't safely leap; reset buffer and do a normal step
      match elimStep st.cands st.m with
      | none => { st with halted := true }
      | some (i, m') =>
        let nextCands := if h : i < table.size then table[i] else fallback
        { m := m', cands := nextCands,
          buf := CBuf.empty st.buf.cap st.buf.hCapPos,
          stepsSimulated := st.stepsSimulated + 1 }
    else
      -- Leap forward by c cycle repetitions
      let newM := leapState startData endData state.snd c
      { m := newM, cands := fallback,
        buf := CBuf.empty st.buf.cap st.buf.hCapPos,
        stepsSimulated := st.stepsSimulated + range.length * c }
  | none =>
    -- No cycle detected, do a normal elimination step
    match elimStep st.cands st.m with
    | none => { st with halted := true }
    | some (i, m') =>
      let nextCands := if h : i < table.size then table[i] else fallback
      { m := m', cands := nextCands,
        buf := st.buf.insert state,
        stepsSimulated := st.stepsSimulated + 1 }

/-- Iterate `cycleStep` for `fuel` steps. Tail-recursive. -/
def cycleRunAux (table : Array (List Candidate))
    (fallback : List Candidate)
    (thresh dmaxes : RegMap) :
    CycleState → Nat → CycleState
  | st, 0 => st
  | st, fuel + 1 =>
    cycleRunAux table fallback thresh dmaxes
      (cycleStep table fallback thresh dmaxes st) fuel

/-- Build a `RegMap` from an explicit list of `(prime, exponent)` pairs.
    The mathlib-free analogue of `RegMap.facmap` — the caller does the
    factorization themselves, so this works in the runtime closure. -/
def RegMap.ofFactors (factors : List (Nat × Nat)) : RegMap :=
  factors.foldl (fun acc (p, e) => acc.insert p e) ∅

/-- Top-level cycle-detecting interpreter taking an already-factored program.

    The `Fractran.Cycle.cycleRunFromMap` wrapper accepts a `FractranProg`
    (a list of `(Nat, Nat)` fractions) and calls `prog.toRegProg` to convert
    each numerator and denominator via `RegMap.facmap`. That conversion uses
    `Nat.primeFactorsList` from mathlib, so it pulls mathlib into the import
    closure. This variant skips the conversion: callers pass the program as
    a `List (RegMap × RegMap)` they built themselves (e.g. via
    `RegMap.ofFactors`), keeping the closure mathlib-free. -/
def cycleRunFromRegProg (cyclen : Nat) (hcyclen : 0 < cyclen)
    (regProg : List (RegMap × RegMap)) (m : RegMap) (k : Nat) : CycleState :=
  let table := optTable regProg
  let cands := allCandidates regProg
  let thresh := dthreshMap regProg cyclen
  let dmaxes := dmaxesMap regProg
  let initState : CycleState :=
    { m := m
      cands := cands
      buf := CBuf.empty cyclen hcyclen
      stepsSimulated := 0 }
  cycleRunAux table cands thresh dmaxes initState k
