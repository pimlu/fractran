import Fractran.Runtime.Cycle

/-!
# Runtime-only FRACTRAN demo

This entry point uses only `Fractran.Runtime.*` modules — its import closure
contains no mathlib. Programs are passed as `List (RegMap × RegMap)` directly,
with each numerator and denominator factored by the caller via
`RegMap.ofFactors`. This is the entry point intended for the WASM build.
-/

/-- Hamming weight program, factored by hand:
    `[(33, 20), (5, 11), (13, 10), (1, 5), (2, 3), (10, 7), (7, 2)]`. -/
def hammingProg : List (RegMap × RegMap) :=
  [ (RegMap.ofFactors [(3, 1), (11, 1)], RegMap.ofFactors [(2, 2), (5, 1)])  -- 33/20
  , (RegMap.ofFactors [(5, 1)],          RegMap.ofFactors [(11, 1)])          -- 5/11
  , (RegMap.ofFactors [(13, 1)],         RegMap.ofFactors [(2, 1), (5, 1)])   -- 13/10
  , (RegMap.ofFactors [],                RegMap.ofFactors [(5, 1)])           -- 1/5
  , (RegMap.ofFactors [(2, 1)],          RegMap.ofFactors [(3, 1)])           -- 2/3
  , (RegMap.ofFactors [(2, 1), (5, 1)],  RegMap.ofFactors [(7, 1)])           -- 10/7
  , (RegMap.ofFactors [(7, 1)],          RegMap.ofFactors [(2, 1)])           -- 7/2
  ]

def main : IO Unit := do
  let k := 128
  let kpop := 2 ^ k - 1
  let cyclen := 2
  let fuel := 1000000
  let initMap : RegMap := Std.TreeMap.empty.insert 2 kpop
  let result := cycleRunFromRegProg cyclen (by omega) hammingProg initMap fuel
  IO.println s!"--- Hamming weight of 2^(2^{k} - 1) (runtime build) ---"
  IO.println s!"Input exponent of 2: {kpop}"
  IO.println s!"Cycle length: {cyclen}, Steps simulated: {result.stepsSimulated}"
  IO.println s!"Halted: {result.halted}"
  let popcount := result.m.getD 13 0
  IO.println s!"Hamming weight (exponent of 13): {popcount}"
  IO.println s!"Expected: {k}"
  if popcount == k && result.halted then
    IO.println "SUCCESS!"
  else
    IO.println "FAILED"
