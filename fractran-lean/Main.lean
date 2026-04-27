import Fractran.Runtime.JsBridge
import Fractran.Runtime.Parse

/-!
# `fractran` — run an arbitrary FRACTRAN program

Reads a FRACTRAN program (one or more fractions, separated by commas or
newlines) and an initial state, then runs them through the proven
cycle-detecting interpreter.

## Usage

```sh
fractran <program-file> <initial-state> [cyclen]
```

* `<program-file>`: text with one fraction per line (or comma-separated).
  `#` starts a line comment; blank lines OK. Each fraction is
  `<num> % <den>` or `<num> / <den>` (both spellings accepted).
* `<initial-state>`: either a factored expression (`5 * 7^2 * 67^159995`)
  or a `[prime, exponent]` pair list (`[2, 3], [5, 1]`).
* `[cyclen]`: cycle-detection buffer length. Defaults to 4.

Inside numerators/denominators/state, only multiplication `*` and
exponentiation `^` are allowed at the top level. `+` and `-` are legal
inside `^` exponents (which evaluate as ordinary `Nat` arithmetic).
Integer literals: decimal, `1ah` for hex, `1011b` for binary.

Example program file (Hamming weight, from `src/Demo.hs`):

```
3*11 % 2^2*5
5 % 11
13 % 2*5
1 % 5
2 % 3
2*5 % 7
7 % 2
```

Run it:

```sh
fractran hamming.frac '2^3'
```
-/

open Fractran.JsBridge

/-- Format a `RegMap` as `p1^e1 * p2^e2 * ...`, or `1` when empty. -/
def formatRegMap (m : RegMap) : String :=
  let factors := m.toList
  if factors.isEmpty then "1"
  else
    let parts := factors.map (fun (p, e) => if e == 1 then s!"{p}" else s!"{p}^{e}")
    String.intercalate " * " parts

def runAndPrint (cyclen : Nat) (fractions : List (RegMap × RegMap))
    (init : RegMap) : IO Unit := do
  if h : 0 < cyclen then
    let result := Runner.cycleRunUntilHalt cyclen h fractions init
    let st := result.state
    IO.println s!"halted:   {st.halted}"
    IO.println s!"steps:    {st.stepsSimulated}"
    if result.loopLen > 0 then
      IO.println s!"loopLen:  {result.loopLen}  (definite infinite loop detected)"
    IO.println s!"state:    {formatRegMap st.m}"
  else
    IO.eprintln "ERROR: cyclen must be positive"
    IO.Process.exit 1

def usage : IO Unit := do
  IO.eprintln "usage: fractran <program-file> <initial-state> [cyclen]"
  IO.eprintln "  cyclen defaults to 4"

def main (args : List String) : IO Unit := do
  let (progPath, stateStr, cyclen) ← match args with
    | [p, s] => pure (p, s, 4)
    | [p, s, c] =>
      match c.toNat? with
      | some n => pure (p, s, n)
      | none => do usage; IO.eprintln s!"  bad cyclen: {c}"; IO.Process.exit 1
    | _ => do usage; IO.Process.exit 1
  let input ← IO.FS.readFile progPath
  let fractions ← match Fractran.Parse.parseProgram input with
    | Except.ok fs => pure fs
    | Except.error e => do IO.eprintln s!"program parse error: {e}"; IO.Process.exit 1
  let init ← match Fractran.Parse.parseInput stateStr with
    | Except.ok m => pure m
    | Except.error e => do IO.eprintln s!"initial state parse error: {e}"; IO.Process.exit 1
  runAndPrint cyclen fractions init
