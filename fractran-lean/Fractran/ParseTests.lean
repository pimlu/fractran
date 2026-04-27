import Fractran.Runtime.Parse

/-!
# Parser test suite

A collection of `example` lemmas exercising `Fractran.Parse`. Each test runs
the parser on a literal input and compares the result against an explicit
expected value, evaluated at build time via `native_decide`.

The parser is `partial def`, so we can't reduce it by `rfl`/`decide`;
`native_decide` compiles the call and runs it natively. To dodge spotty
`DecidableEq` instance synthesis on deeply-nested option/except/list types,
we lower every comparison to `Bool` via `BEq` (`matchExc`), and the test
asserts `_ = true`.

`RegMap` results are normalized to `.toList` (sorted `(prime, exp)` pairs)
so the tests don't depend on internal `TreeMap` representation.
-/

namespace Fractran.ParseTests

open Fractran.Parse

/-! ## Helpers — strip the cursor, normalize RegMap, compare via BEq. -/

private def matchExc {α} [BEq α] (e : Except String α) (expected : α) : Bool :=
  match e with
  | .ok x    => x == expected
  | .error _ => false

private def isErr {α} (e : Except String α) : Bool :=
  match e with
  | .ok _    => false
  | .error _ => true

private def runMul (s : String) : Except String (List (Nat × Nat)) :=
  match parseMul s.toList with
  | .ok (m, _)  => .ok m.toList
  | .error e    => .error e

private def runProgram (s : String) :
    Except String (List (List (Nat × Nat) × List (Nat × Nat))) :=
  match parseProgram s with
  | .ok fracs   => .ok (fracs.map (fun (n, d) => (n.toList, d.toList)))
  | .error e    => .error e

private def runInput (s : String) : Except String (List (Nat × Nat)) :=
  match parseInput s with
  | .ok m       => .ok m.toList
  | .error e    => .error e

/-! ## `factorize` -/

example : factorize 1   = []                       := by native_decide
example : factorize 2   = [(2, 1)]                 := by native_decide
example : factorize 12  = [(2, 2), (3, 1)]         := by native_decide
example : factorize 67  = [(67, 1)]                := by native_decide
example : factorize 100 = [(2, 2), (5, 2)]         := by native_decide
example : factorize 159995 = [(5, 1), (11, 1), (2909, 1)] := by native_decide

/-! ## Integer literals (decimal / hex / binary)

Exercised through `parseMul` with a single literal — we get the literal's
factored form back. -/

example : matchExc (runMul "0")     []                = true := by native_decide
example : matchExc (runMul "1")     []                = true := by native_decide
example : matchExc (runMul "7")     [(7, 1)]          = true := by native_decide
example : matchExc (runMul "12")    [(2, 2), (3, 1)]  = true := by native_decide

-- Hex: must end in 'h'.
example : matchExc (runMul "Ah")    [(2, 1), (5, 1)]              = true := by native_decide
example : matchExc (runMul "ffh")   [(3, 1), (5, 1), (17, 1)]     = true := by native_decide
example : matchExc (runMul "10h")   [(2, 4)]                      = true := by native_decide

-- Binary: must end in 'b'. 'b' is also a hex digit; the parser disambiguates
-- by checking that the prefix is all 0/1.
example : matchExc (runMul "0b")    []                = true := by native_decide
example : matchExc (runMul "10b")   [(2, 1)]          = true := by native_decide
example : matchExc (runMul "111b")  [(7, 1)]          = true := by native_decide
example : matchExc (runMul "1011b") [(11, 1)]         = true := by native_decide

-- Ambiguous cases should error.
example : isErr (runMul "12b")      = true := by native_decide  -- 2 isn't binary
example : isErr (runMul "abc")      = true := by native_decide  -- needs 'h' suffix

/-! ## Multiplication and exponentiation (factored grammar) -/

example : matchExc (runMul "2*3")          [(2, 1), (3, 1)]        = true := by native_decide
example : matchExc (runMul "2*3*5")        [(2, 1), (3, 1), (5, 1)] = true := by native_decide
example : matchExc (runMul "2^3")          [(2, 3)]                = true := by native_decide
example : matchExc (runMul "2^10")         [(2, 10)]               = true := by native_decide
example : matchExc (runMul "67^159995")    [(67, 159995)]          = true := by native_decide

-- The bug we fixed: 2^2*5 must parse as (2^2)*5, not 2^(2*5).
example : matchExc (runMul "2^2*5")        [(2, 2), (5, 1)]        = true := by native_decide
example : matchExc (runMul "2^3 * 5^7")    [(2, 3), (5, 7)]        = true := by native_decide

-- Same prime appearing twice — exponents add.
example : matchExc (runMul "2*2")          [(2, 2)]                = true := by native_decide
example : matchExc (runMul "2^3*2^4")      [(2, 7)]                = true := by native_decide
example : matchExc (runMul "2^2 * 2^2")    [(2, 4)]                = true := by native_decide
-- `2^2 * 2^2` and `2^(2+2)` should give the same factored form ({2: 4}).
example : matchExc (runMul "2^(2+2)")      [(2, 4)]                = true := by native_decide

-- Parens around base: (2*3)^4 = 6^4 = {2:4, 3:4}.
example : matchExc (runMul "(2*3)^4")      [(2, 4), (3, 4)]        = true := by native_decide

-- Right-associative ^ : 2^3^2 = 2^(3^2) = 2^9.
example : matchExc (runMul "2^3^2")        [(2, 9)]                = true := by native_decide

/-! ## Exponent arithmetic (Nat grammar inside `^`) -/

example : matchExc (runMul "2^(3+4)")      [(2, 7)]                = true := by native_decide
example : matchExc (runMul "2^(10-3)")     [(2, 7)]                = true := by native_decide
example : matchExc (runMul "2^(3*4)")      [(2, 12)]               = true := by native_decide
example : matchExc (runMul "2^(2^3)")      [(2, 8)]                = true := by native_decide
example : matchExc (runMul "2^(1+2*3)")    [(2, 7)]                = true := by native_decide  -- precedence

-- Subtraction is left-associative on Nat; we error on underflow rather
-- than silently truncating to 0. `2-3+4` would equal 4 under Nat sub but
-- is mathematically 3, so we reject it.
example : isErr (runMul "2^(2-3+4)")       = true := by native_decide
example : matchExc (runMul "2^(5-3+4)")    [(2, 6)]                = true := by native_decide
example : matchExc (runMul "2^(3-3)")      []                      = true := by native_decide  -- exp 0 → empty map

-- + and - are NOT allowed at the top level — only inside ^ exponent context.
-- A bare top-level `2+3` should fail to parse cleanly: parseMul returns
-- `2`, then the trailing `+3` is unconsumed. `parseInput` (which checks for
-- trailing input) catches this.
example : isErr (runInput "2+3")           = true := by native_decide

/-! ## Whitespace tolerance -/

example : matchExc (runMul "  2 ^ 3  *  5 ^ 7  ")
                                          [(2, 3), (5, 7)] = true := by native_decide
example : matchExc (runMul "2 *\t3")       [(2, 1), (3, 1)] = true := by native_decide

/-! ## Programs (lists of fractions) -/

-- % as fraction separator
example : matchExc (runProgram "3 % 2") [([(3, 1)], [(2, 1)])] = true := by native_decide

-- / as fraction separator (synonymous with %)
example : matchExc (runProgram "3 / 2") [([(3, 1)], [(2, 1)])] = true := by native_decide

-- Multiple fractions, newline-separated
example : matchExc (runProgram "3 % 2\n5 % 7")
    [([(3, 1)], [(2, 1)]), ([(5, 1)], [(7, 1)])] = true := by native_decide

-- Multiple fractions, comma-separated
example : matchExc (runProgram "3 % 2, 5 % 7")
    [([(3, 1)], [(2, 1)]), ([(5, 1)], [(7, 1)])] = true := by native_decide

-- Comments and blank lines
example : matchExc (runProgram "# header\n3 % 2  # inline comment\n\n5 % 7\n")
    [([(3, 1)], [(2, 1)]), ([(5, 1)], [(7, 1)])] = true := by native_decide

-- Hamming weight program (matches src/Demo.hs)
example : matchExc (runProgram
    "3*11 % 2^2*5\n5 % 11\n13 % 2*5\n1 % 5\n2 % 3\n2*5 % 7\n7 % 2")
    [
      ([(3, 1), (11, 1)], [(2, 2), (5, 1)]),
      ([(5, 1)],          [(11, 1)]),
      ([(13, 1)],         [(2, 1), (5, 1)]),
      ([],                [(5, 1)]),       -- 1 % 5
      ([(2, 1)],          [(3, 1)]),
      ([(2, 1), (5, 1)],  [(7, 1)]),
      ([(7, 1)],          [(2, 1)])
    ] = true := by native_decide

/-! ## Initial states -/

example : matchExc (runInput "2^3")        [(2, 3)] = true := by native_decide
example : matchExc (runInput "5 * 7^2 * 67^159995")
    [(5, 1), (7, 2), (67, 159995)] = true := by native_decide

-- Pair-list syntax: [prime, exponent], comma-separated.
example : matchExc (runInput "[2, 3]")     [(2, 3)] = true := by native_decide
example : matchExc (runInput "[2, 3], [5, 7]")
    [(2, 3), (5, 7)] = true := by native_decide

-- Pair list with arithmetic inside.
example : matchExc (runInput "[2, 1+2], [5, 7]")
    [(2, 3), (5, 7)] = true := by native_decide

end Fractran.ParseTests
