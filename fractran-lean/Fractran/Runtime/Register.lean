import Fractran.Runtime.Basic
import Std.Data.TreeMap

/-!
# Register-based FRACTRAN interpreter (runtime)

Mathlib-free data definitions for the register-based interpreter. The
homomorphism lemmas, the `Finsupp` bridge, and `facmap` (which depends on
`Nat.primeFactorsList`) live in `Fractran.Register` on the proof side.

`RegMap`-keyed runners (`regStep`, `regRun`, `regRunExact`) are here so they
can be linked into the WASM build without dragging mathlib into the closure.
The `Nat`-keyed wrapper `regRunNat` stays in the proof file because it has to
call `facmap` to convert from a plain natural.
-/

/-- Register map: maps primes to their exponents in the current FRACTRAN state.
    Primes absent from the map have exponent 0 by convention. -/
abbrev RegMap := Std.TreeMap Nat Nat compare

namespace RegMap

/-! ## Core operations -/

/-- Exponent of prime `p` in the map (0 if absent). -/
def get (m : RegMap) (p : Nat) : Nat := m.getD p 0

/-- Pointwise exponent addition — corresponds to multiplication of underlying numbers. -/
instance : Mul RegMap where
  mul m₁ m₂ := m₁.foldl (fun acc p e => acc.insert p (acc.get p + e)) m₂

/-- Empty map — corresponds to the number 1 (no prime factors). -/
instance : One RegMap where
  one := ∅

/-- Pointwise exponent subtraction (saturating) — corresponds to division.
    Keys that reach 0 are erased so zero-exponent primes are never stored. -/
instance : Div RegMap where
  div m₁ m₂ := m₂.foldl (fun acc p e =>
    let v := acc.get p - e
    if v = 0 then acc.erase p else acc.insert p v) m₁

/-- Reconstruct the natural number from its register representation. -/
def unfmap (m : RegMap) : Nat :=
  m.foldl (fun acc p e => acc * p ^ e) 1

/-- True iff every exponent in `den` is ≤ the corresponding exponent in `m`.
    Equivalent to: `unfmap den` divides `unfmap m`. -/
def applicable (den m : RegMap) : Bool :=
  den.all fun p e => m.get p ≥ e

/-- Apply fraction `(num, den)` to state `m`: divide out `den`, multiply in `num`. -/
def applyFrac (num den m : RegMap) : RegMap := m / den * num

end RegMap

/-! ## Interpreter -/

/-- One step of the register-based interpreter.
    Scans for the first fraction whose denominator is applicable and applies it. -/
def regStep (prog : List (RegMap × RegMap)) (m : RegMap) : Option RegMap :=
  prog.findSome? fun (num, den) =>
    if RegMap.applicable den m then some (RegMap.applyFrac num den m) else none

/-- Run the register interpreter for exactly `k` steps from state `m`.
    Returns `some m'` if still running after `k` steps, `none` if it halted earlier. -/
def regRun (prog : List (RegMap × RegMap)) (m : RegMap) : Nat → Option RegMap
  | 0     => some m
  | k + 1 => regRun prog m k >>= regStep prog

/-- Halt-aware variant of `regRun`: returns the final state and the exact number
    of successful naive steps. If the program halts before fuel runs out, the
    step count is the count of successful steps before halting (so `j < k`);
    otherwise `j = k`. -/
def regRunExact (prog : List (RegMap × RegMap)) : RegMap → Nat → Option RegMap × Nat
  | m, 0     => (some m, 0)
  | m, k + 1 =>
    match regStep prog m with
    | none    => (none, 0)
    | some m' =>
      let res := regRunExact prog m' k
      (res.1, res.2 + 1)
