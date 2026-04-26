import Fractran.Runtime.Register

/-!
# Static Fraction Elimination (runtime)

After fraction `j` fires, some fractions `k < j` provably cannot fire next.
Specifically, if `den_k` shares no prime with `num_j`, then `k`'s denominator
requirements can only have worsened (the primes it needs either stayed the same
or decreased), so `k` remains inapplicable.

`optTable` precomputes, for each fraction index, the narrowed candidate list
for the next step. `elimStep` scans only the candidates, returning both the
fraction index (needed to look up the next candidate list) and the new state.

This module is used both standalone (via `elimRunNat`, proven `Correct` in
`Fractran.Elim`) and as a building block for the cycle-detecting interpreter,
which threads the candidate list through its own control loop and resets to
the full list after arithmetic leaps.

## Candidate list format

A candidate list has type `List ((RegMap × RegMap) × Nat)` — each entry is a
fraction `(num, den)` paired with its index in the original program. This
matches the output of `List.zipIdx` on the register program.

The `optTable_size` lemma, the `ElimInvariant` predicate, the Nat-keyed
wrapper `elimRunNat`, and all correctness proofs live in `Fractran.Elim`.
-/

/-! ## Definitions -/

/-- Two register maps share at least one key (prime factor). -/
def RegMap.sharesKey (a b : RegMap) : Bool :=
  a.toList.any fun (p, _) => b.contains p

/-- A candidate entry: a fraction `(num, den)` paired with its program index. -/
abbrev Candidate := (RegMap × RegMap) × Nat

/-- Full indexed fraction list: each fraction paired with its program index.
    Used as the initial candidate list and after cycle-detection leaps. -/
def allCandidates (prog : List (RegMap × RegMap)) : List Candidate :=
  prog.zipIdx

/-- Precompute the candidate table. Entry `i` lists the fractions that could
    fire after fraction `i` fires:
    - All fractions `j ≥ i` (always candidates — their position means they
      weren't checked before `i`)
    - Fractions `k < i` only if `den_k` shares a prime with `num_i`
      (otherwise `k` was already inapplicable and can only have gotten worse) -/
def optTable (prog : List (RegMap × RegMap)) : Array (List Candidate) :=
  let indexed := allCandidates prog
  Array.ofFn fun (i : Fin prog.length) =>
    let (pre, post) := List.splitAt i.val indexed
    let num := prog[i].1
    List.filter (fun ((_, den), _) => RegMap.sharesKey num den) pre ++ post

/-- One step with a candidate list: find the first applicable fraction.
    Returns the fraction's program index and the resulting register state,
    or `none` if no candidate applies (the program halts).

    This is the per-step primitive shared by both the standalone elimination
    interpreter and the cycle-detecting interpreter. -/
def elimStep (candidates : List Candidate) (m : RegMap) :
    Option (Nat × RegMap) :=
  candidates.findSome? fun ((num, den), i) =>
    if RegMap.applicable den m then some (i, RegMap.applyFrac num den m) else none

/-! ## Standalone elimination interpreter -/

/-- Run the elimination interpreter for `k` steps, threading the candidate
    list: after fraction `i` fires, the next step scans `table[i]`.
    Returns `(state, candidates)` or `none` if halted. -/
def elimRunAux (table : Array (List Candidate))
    (fallback : List Candidate)
    (m : RegMap) (cands : List Candidate) :
    Nat → Option (RegMap × List Candidate)
  | 0 => some (m, cands)
  | k + 1 => do
    let (m', cands') ← elimRunAux table fallback m cands k
    let (i, m'') ← elimStep cands' m'
    let nextCands := if h : i < table.size then table[i] else fallback
    return (m'', nextCands)

/-- Run the elimination interpreter, returning only the final state. -/
def elimRun (table : Array (List Candidate))
    (fallback : List Candidate)
    (m : RegMap) (cands : List Candidate) (k : Nat) : Option RegMap :=
  (elimRunAux table fallback m cands k).map Prod.fst

/-- Halt-aware variant of `elimRunAux`: returns the result and the exact number
    of successful steps. If the program halts before fuel runs out, the step
    count is the count of successful steps before halting; otherwise it is `k`. -/
def elimRunExactAux (table : Array (List Candidate)) (fallback : List Candidate) :
    RegMap → List Candidate → Nat → Option (RegMap × List Candidate) × Nat
  | m, cands, 0     => (some (m, cands), 0)
  | m, cands, k + 1 =>
    match elimStep cands m with
    | none         => (none, 0)
    | some (i, m') =>
      let nextCands := if h : i < table.size then table[i] else fallback
      let res := elimRunExactAux table fallback m' nextCands k
      (res.1, res.2 + 1)
