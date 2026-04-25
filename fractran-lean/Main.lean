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

/-! ## Self-interpreter (24 fractions) -/

/-- Compute a natural number from prime factorization pairs. -/
def fromFactors (factors : List (ℕ × ℕ)) : ℕ :=
  factors.foldl (fun acc (p, e) => acc * p ^ e) 1

/-- Take the base-b digits of n and reinterpret them in base (b+1).
    E.g. rebase 355 10 = 3*11^2 + 5*11 + 5 = 423. -/
def rebase (n b : ℕ) : ℕ :=
  if h : b ≤ 1 then n
  else if hn : n < b then n
  else rebase (n / b) b * (b + 1) + n % b
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- Number of digits of n in base b (at least 1). -/
def numDigits (n b : ℕ) : ℕ :=
  if h : b ≤ 1 then 1
  else if hn : n < b then 1
  else 1 + numDigits (n / b) b
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- Encode a FRACTRAN program for the self-interpreter.
    From low to high: den₁, sentinel, num₁, sentinel, ..., denₖ, sentinel, numₖ, sentinel.
    Sentinel digit = b, overall base = b+1. -/
def encodeProg (prog : FractranProg) (b : ℕ) : ℕ :=
  let base := b + 1
  prog.reverse.foldl (fun acc (num, den) =>
    let acc := acc * base + b                          -- sentinel
    let acc := acc * base ^ numDigits num b + rebase num b  -- num digits
    let acc := acc * base + b                          -- sentinel
    acc * base ^ numDigits den b + rebase den b        -- den digits
  ) 0

/-- The 24-fraction self-interpreter parameterized by base b ≥ 2. -/
def selfInterpProg (b : ℕ) : FractranProg :=
  let f := fromFactors
  [ (2, 3),                                                              -- 1
    (5, 7),                                                              -- 2
    (f [(7,12), (41,1)], f [(5,12), (23,1)]),                            -- 3
    (f [(7,13)], f [(5,13), (37,1)]),                                    -- 4
    (f [(3,10), (7,3), (13,1)], f [(5,13), (31,1)]),                     -- 5
    (f [(3,2), (7,11), (19,1), (41,1)], f [(2,2), (5,11), (29,1)]),      -- 6
    (f [(3,3), (7,10), (19,1), (23,1)], f [(2,3), (5,10), (29,1), (41,1)]), -- 7
    (f [(3,1), (7,12), (19,1), (37,1)], f [(2,3), (5,10), (29,1)]),      -- 8
    (f [(3,4), (7,8), (29,1)], f [(2,4), (5,8), (19,1)]),                -- 9
    (f [(3,4), (7,8), (11,b), (31,1)], f [(2,4), (5,8), (13,b+1)]),      -- 10
    (f [(3,13), (11,b)], f [(2,4), (5,9), (13,b), (41,1)]),              -- 11
    (f [(3,12), (7,1), (11,b), (19,1)], f [(2,5), (5,8), (13,b)]),       -- 12
    (f [(3,2), (7,10), (11,1)], f [(2,4), (5,8), (13,1)]),               -- 13
    (f [(3,8), (7,4), (19,b)], f [(2,8), (5,4), (29,1)]),                -- 14
    (f [(3,8), (7,4), (13,1)], f [(2,8), (5,4), (31,1)]),                -- 15
    (f [(3,12)], f [(2,12), (29,1)]),                                     -- 16
    (f [(3,13), (17,1), (19,1)], f [(2,13), (37,1)]),                     -- 17
    (f [(7,13)], f [(2,12), (5,1), (23,1)]),                              -- 18
    (f [(3,12), (7,1), (31,1)], f [(2,12), (5,1), (11,1)]),               -- 19
    (f [(3,12), (7,1)], f [(2,12), (5,1), (17,1)]),                       -- 20
    (f [(3,10), (7,1)], f [(2,10), (5,1), (41,1)]),                       -- 21
    (f [(3,10), (7,3), (37,1)], f [(2,10), (5,3), (17,1)]),               -- 22
    (f [(3,3), (7,4)], f [(2,1), (5,6)]),                                 -- 23
    (f [(3,4), (7,4)], f [(2,8)])                                         -- 24
  ]

/-- Build the start state RegMap for the self-interpreter.
    Start state = 31^f(P) * 17^N * 5^13 * 19 -/
def selfInterpStart (prog : FractranProg) (n : ℕ) (b : ℕ) : RegMap :=
  let fP := encodeProg prog b
  (((Std.TreeMap.empty.insert 31 fP).insert 17 n).insert 5 13).insert 19 1

/-- Run the register interpreter on a RegMap, returning the final RegMap. -/
def regRunFinal (rprog : List (RegMap × RegMap)) (m : RegMap)
    (fuel : ℕ) : RegMap × ℕ :=
  go m fuel 0
where
  go (m : RegMap) : ℕ → ℕ → RegMap × ℕ
    | 0,     steps => (m, steps)
    | k + 1, steps =>
      match regStep rprog m with
      | none    => (m, steps)
      | some m' => go m' k (steps + 1)

def runSelfInterp : IO Unit := do
  let b := 2
  let innerProg : FractranProg := [(5, 2), (5, 3)]
  let inputN := 6
  let prog := selfInterpProg b
  let rprog := prog.toRegProg
  let startMap := selfInterpStart innerProg inputN b
  IO.println s!"--- Self-interpreter demo ---"
  IO.println s!"Inner program: {innerProg}"
  IO.println s!"Input: {inputN}"
  IO.println s!"Base: {b}"
  IO.println s!"Program encoding: {encodeProg innerProg b}"
  IO.println s!"Self-interp has {prog.length} fractions"
  let (finalMap, steps) := regRunFinal rprog startMap 1000000000
  let result := finalMap.getD 17 0
  IO.println s!"Steps taken: {steps}"
  IO.println s!"Register 17 (result): {result}"
  IO.println s!"Expected: 25"
  if result == 25 then
    IO.println "SUCCESS!"
  else
    IO.println s!"Got {result}, investigating..."
    IO.println s!"Final registers: {finalMap.toList}"
  IO.println ""

def main : IO Unit := do
  runDemo "Addition (2^3 * 3^2 -> 5^5 = 3125)" [(5, 2), (5, 3)] 72 100
  runDemo "Multiplication (2^3 * 3^4 -> 5^12)"
    [(455, 33), (11, 13), (1, 11), (3, 7), (11, 2), (1, 3)] 648 1000
  runDemo "Halving (2^5 = 32 -> 1)" [(1, 2)] 32 100
  runDemo "Doubling (3^4 = 81 -> 2^4 = 16)" [(2, 3)] 81 100
  runSelfInterp
