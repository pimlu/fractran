import Mathlib.Data.Nat.Notation

/-- A FRACTRAN program: an ordered list of fractions, each given as a
    (numerator, denominator) pair. -/
abbrev FractranProg := List (ℕ × ℕ)

/-- One step of the naive FRACTRAN interpreter.
    Scans for the first fraction `(p, q)` such that `q ∣ n`, returning `n / q * p`.
    Returns `none` if no fraction applies (the program halts). -/
def naiveStep (prog : FractranProg) (n : ℕ) : Option ℕ :=
  prog.findSome? fun (p, q) => if q ∣ n then some (n / q * p) else none

/-- Run the naive interpreter for exactly `k` steps from state `n`.
    Returns `some m` if the program reaches state `m` after exactly `k` steps;
    returns `none` if it halted at some earlier step. -/
def naiveRun (prog : FractranProg) (n : ℕ) : ℕ → Option ℕ
  | 0     => some n
  | k + 1 => naiveRun prog n k >>= naiveStep prog

/-- `HaltsIn prog n k` holds when the program reaches a halting state in exactly `k` steps
    from `n` — i.e., `naiveRun prog n k = some m` for some `m` with no applicable fraction. -/
def HaltsIn (prog : FractranProg) (n : ℕ) (k : ℕ) : Prop :=
  ∃ m, naiveRun prog n k = some m ∧ naiveStep prog m = none

/-- Correctness predicate for any nat-level FRACTRAN interpreter.
    An interpreter takes a program, initial state, and fuel `k`, and returns a pair
    `(result, j)` where `result` is the outcome (`some s` = still running at state `s`,
    `none` = halted) and `j` is the number of naive steps simulated.

    Correctness requires:
    - `j ≥ k`: at least as many naive steps are simulated as fuel consumed, and
    - `naiveRun prog n j = result`: the naive interpreter agrees at `j` steps.

    This handles both normal halts (`none`) and cycle detection (`some s`, where the
    interpreter stopped early but FRACTRAN was still running) uniformly.

    Restricted to well-formed programs (positive numerators and denominators),
    which is standard for FRACTRAN (Conway's formulation uses positive rationals). -/
def FractranProg.WellFormed (prog : FractranProg) : Prop :=
  ∀ pq ∈ prog, 0 < pq.1 ∧ 0 < pq.2

def Correct (interp : FractranProg → ℕ → ℕ → Option ℕ × ℕ) : Prop :=
  ∀ prog n k, prog.WellFormed → 0 < n →
    let (result, j) := interp prog n k
    k ≤ j ∧ naiveRun prog n j = result
