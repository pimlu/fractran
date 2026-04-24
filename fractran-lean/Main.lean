import Fractran.Basic
import Fractran.Register

/-!
# FRACTRAN demo

Runs a few small FRACTRAN programs with both the naive and register-based
interpreters, printing each step so we can see they agree.
-/

/-- Run the naive interpreter, collecting all states until halt or fuel runs out. -/
def naiveTrace (prog : FractranProg) (n : ℕ) (fuel : ℕ) : List ℕ :=
  go n fuel [n]
where
  go (n : ℕ) : ℕ → List ℕ → List ℕ
    | 0,     acc => acc.reverse
    | k + 1, acc =>
      match naiveStep prog n with
      | none   => acc.reverse
      | some n' => go n' k (n' :: acc)

/-- Run the register interpreter, collecting all states until halt or fuel runs out. -/
def regTrace (prog : FractranProg) (n : ℕ) (fuel : ℕ) : List ℕ :=
  let rprog := prog.toRegProg
  let m := RegMap.facmap n
  go rprog m fuel [n]
where
  go (rprog : List (RegMap × RegMap)) (m : RegMap) : ℕ → List ℕ → List ℕ
    | 0,     acc => acc.reverse
    | k + 1, acc =>
      match regStep rprog m with
      | none    => acc.reverse
      | some m' => go rprog m' k (RegMap.unfmap m' :: acc)

def runDemo (name : String) (prog : FractranProg) (n : ℕ) (fuel : ℕ) : IO Unit := do
  IO.println s!"--- {name} ---"
  IO.println s!"Program: {prog}"
  IO.println s!"Input:   {n}"
  let naive := naiveTrace prog n fuel
  let reg   := regTrace prog n fuel
  IO.println s!"Naive:    {naive}"
  IO.println s!"Register: {reg}"
  if naive == reg then
    IO.println s!"Match: yes"
  else
    IO.println s!"MISMATCH!"
  IO.println ""

def main : IO Unit := do
  -- Addition: [5/2, 5/3] on 2^a * 3^b computes 5^(a+b)
  -- Input: 2^3 * 3^2 = 72, expect 5^5 = 3125
  runDemo "Addition (2^3 * 3^2 -> 5^5 = 3125)" [(5, 2), (5, 3)] 72 100

  -- Multiplication: [455/33, 11/13, 1/11, 3/7, 11/2, 1/3]
  -- Computes 2^a * 3^b -> 5^(a*b)
  -- Input: 2^3 * 3^4 = 648, expect 5^12 = 244140625
  runDemo "Multiplication (2^3 * 3^4 -> 5^12)" [(455, 33), (11, 13), (1, 11), (3, 7), (11, 2), (1, 3)] 648 1000

  -- Simple halving: [1/2] on 2^k gives 2^(k-1), ..., 2^0 = 1, then halts
  -- Input: 2^5 = 32
  runDemo "Halving (2^5 = 32 -> 1)" [(1, 2)] 32 100

  -- Doubling: [2/3] on 3^k gives 2^k
  -- Input: 3^4 = 81, expect 2^4 = 16
  runDemo "Doubling (3^4 = 81 -> 2^4 = 16)" [(2, 3)] 81 100
