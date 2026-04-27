import Fractran.Runtime.Basic
import Mathlib.Data.Nat.Notation

/-!
# FRACTRAN proof-side predicates

The runtime data (`FractranProg`, `naiveStep`, `naiveRun`) lives in
`Fractran.Runtime.Basic` so it can be compiled to C without mathlib in the
import closure. This file adds the proof-side predicates used by the
correctness theorems.
-/

/-- `HaltsIn prog n k` holds when the program reaches a halting state in exactly `k` steps
    from `n` — i.e., `naiveRun prog n k = some m` for some `m` with no applicable fraction. -/
def HaltsIn (prog : FractranProg) (n : ℕ) (k : ℕ) : Prop :=
  ∃ m, naiveRun prog n k = some m ∧ naiveStep prog m = none

/-- Correctness predicate for any nat-level FRACTRAN interpreter.
    An interpreter takes a program, initial state, and fuel `k`, and returns a pair
    `(result, j)` where `result` is the outcome (`some s` = still running at state `s`,
    `none` = halted) and `j` is the number of naive steps simulated.

    Correctness requires:
    - If `result = none`: the program halted at exactly `j` successful steps
      (i.e., `HaltsIn prog n j`). `j` may be less than `k`.
    - If `result = some m`: the program is still running at state `m` after `j` steps,
      with `j ≥ k` (a cycle-detecting interpreter may simulate beyond fuel via leaping).

    Restricted to well-formed programs (positive numerators and denominators),
    which is standard for FRACTRAN (Conway's formulation uses positive rationals). -/
def FractranProg.WellFormed (prog : FractranProg) : Prop :=
  ∀ pq ∈ prog, 0 < pq.1 ∧ 0 < pq.2

def Correct (interp : FractranProg → ℕ → ℕ → Option ℕ × ℕ) : Prop :=
  ∀ prog n k, prog.WellFormed → 0 < n →
    let (result, j) := interp prog n k
    match result with
    | none => HaltsIn prog n j
    | some m => k ≤ j ∧ naiveRun prog n j = some m
