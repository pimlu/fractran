/-!
# FRACTRAN core data types and naive interpreter (runtime)

This module is the mathlib-free foundation: just the `FractranProg` type and
the naive interpreter. It uses `Nat` directly (not the `ℕ` notation, which is
provided by mathlib) so the C codegen for this module doesn't drag in mathlib.

Proof-side predicates (`WellFormed`, `HaltsIn`, `Correct`) live in
`Fractran.Basic`, which imports this module.
-/

/-- A FRACTRAN program: an ordered list of fractions, each given as a
    (numerator, denominator) pair. -/
abbrev FractranProg := List (Nat × Nat)

/-- One step of the naive FRACTRAN interpreter.
    Scans for the first fraction `(p, q)` such that `q ∣ n`, returning `n / q * p`.
    Returns `none` if no fraction applies (the program halts). -/
def naiveStep (prog : FractranProg) (n : Nat) : Option Nat :=
  prog.findSome? fun (p, q) => if q ∣ n then some (n / q * p) else none

/-- Run the naive interpreter for exactly `k` steps from state `n`.
    Returns `some m` if the program reaches state `m` after exactly `k` steps;
    returns `none` if it halted at some earlier step. -/
def naiveRun (prog : FractranProg) (n : Nat) : Nat → Option Nat
  | 0     => some n
  | k + 1 => naiveRun prog n k >>= naiveStep prog
