# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

A high-performance FRACTRAN interpreter written in Haskell. FRACTRAN programs are ordered lists of fractions; evaluation repeatedly multiplies the current state by the first fraction whose product is an integer, halting when none qualify. This repo achieves 30x+ speedups over naive implementations via two algorithmic innovations: static fraction elimination and cycle detection with arithmetic "leaping."

The whitepaper `termpd.tex` contains the formal proofs and benchmarks. `fractran-lean/` is a Lean 4 formalization (using mathlib). `web/` is a browser build using Asterius (Haskell-to-WASM compiler).

## Building and running

```sh
./build.sh          # compile with GHC (outputs ./fractran binary)
./build.sh clean    # remove build products (out/ directory)
./fractran          # run the demo benchmarks
```

The build uses `ghc --make -prof -fprof-auto` and writes object/interface files to `out/`.

For the browser build (requires Docker):
```sh
./build.sh --browser    # runs Asterius via Docker, populates web/gen/
cd web && yarn          # install JS dependencies
yarn run serve          # serve locally
```

## Core architecture

### State representation

FRACTRAN state is a big integer, but internally represented as `IntMap = Map Int Integer` mapping each prime factor to its exponent (a register machine view). `facmap :: Integer -> IntMap` converts to this form; `unfmap :: IntMap -> Integer` converts back.

### Source files

- **`src/Fractran.hs`** — the core library. Contains all three evaluation strategies and the cycle detection algorithm.
- **`src/CBuf.hs`** — circular buffer with O(log n) membership testing via an accompanying `Set`. Used by cycle detection to track recent logic states.
- **`src/Others.hs`** — naive and register-based evaluators kept for benchmarking comparison.
- **`src/Demo.hs`** — hardcoded FRACTRAN programs (`primegame`, `hamming`, `fteval`, etc.) and the `demo` entry point.
- **`src/main.hs`** — calls `demo`.

### Three evaluation strategies (fastest last)

**1. Naive** (`Others.hs: naive`, `naive'`): Direct rational arithmetic on `Integer`. Simple but slow — each step multiplies a big integer and checks if the denominator is 1.

**2. Register-based** (`Others.hs: regBased`): Works on `IntMap` instead. Fraction application becomes map arithmetic (add numerator exponents, subtract denominator exponents). Avoids huge GCD/multiplication operations.

**3. Cycle-detecting** (`Fractran.hs: cycles`, `cycles'`): The main result. Returns `[CycleStep]` where `CycleStep = Step IntMap | Leap Integer`. A `Leap k` means k steps were skipped via arithmetic.

### Fraction elimination (`optArr`, `fracOpt`)

After applying fraction `j`, some fractions `k < j` can never be the next applicable fraction — specifically, any `k` whose denominator shares a prime with `j`'s numerator could not have been satisfied last time (since `j` fired instead). `optArr` precomputes an array (indexed by source fraction) of valid candidate destination fractions. This turns O(l) fraction testing into O(1) to O(l/2) in practice.

### Cycle detection (`cycles`, `leap`, `stateSplit`)

The key insight: partition registers into *logic* registers (small — comparable to denominators, affect which fraction fires) and *data* registers (large — cannot affect control flow). Logic state is `n mod dthresh` conceptually; the threshold is `cyclen * max_denominator` per prime.

When the circular buffer (`CBuf`) sees a repeated logic state, `leap` computes how many times the cycle can safely repeat before some data register would drop into logic territory (`life_p` per register, take the minimum). The state is then advanced arithmetically by `min(life_p) * cycle_length` steps.

`stateSplit :: IntMap -> IntMap -> (IntMap, IntMap)` partitions a state given the threshold map. `CBuf` is keyed by logic state (the `snd` of the split pair) for O(log C) lookup.

`stepCount :: [CycleStep] -> [(Integer, IntMap)]` converts the output stream to `(cumulative_step_count, state)` pairs, accumulating leap counts.

### Key types

```haskell
type IntMap = M.Map Int Integer        -- prime → exponent
data CycleStep = Step IntMap | Leap Integer
data CBuf a b = CBuf Int (Q.Seq a) (S.Set b) (a -> b)  -- capacity, sequence, set, key fn
```

### FRACTRAN programs in Demo.hs

`primegame` (Conway's prime generator), `hamming` (Hamming weight), `paper` (addition preserving input), `mult` (multiplication), `fteval` (84-fraction self-interpreter), `nonterm` (nonterminating cycle for testing).

The `cyclen` parameter to `cycles` is the circular buffer capacity — larger values detect longer cycles at higher memory cost. The paper uses 2 for PRIMEGAME and 16 for the self-interpreter.

## Lean formalization (`fractran-lean/`)

Lean 4 project using mathlib (v4.30.0-rc2). Build with `cd fractran-lean && lake build`.

### Correctness framework

A FRACTRAN program is `List (ℕ × ℕ)` (numerator, denominator pairs). The reference semantics are:

- **`naiveStep`** (`Basic.lean`): scans for the first fraction `(p, q)` where `q ∣ n`, returning `n / q * p`. Returns `none` if no fraction applies (halt).
- **`naiveRun`** (`Basic.lean`): iterates `naiveStep` for `k` steps. Returns `some m` if still running, `none` if halted.
- **`WellFormed`** (`Basic.lean`): all numerators and denominators are positive.
- **`Correct`** (`Basic.lean`): any interpreter `interp prog n k → (Option ℕ, ℕ)` is correct if it returns `(result, j)` with `j ≥ k` and `naiveRun prog n j = result`. This handles both halting and cycle-detection interpreters uniformly.

### What's proven

**Register interpreter** (`Register.lean`): `RegMap` is `Std.TreeMap ℕ ℕ` mapping primes to exponents. Key results:
- `facmap`/`unfmap` round-trip: `unfmap (facmap n) = n` for `n > 0`
- Homomorphisms: `unfmap (m₁ * m₂) = unfmap m₁ * unfmap m₂`, `unfmap (m / den) = unfmap m / unfmap den` (when applicable)
- `applicable den m ↔ unfmap den ∣ unfmap m` for well-formed maps
- **`regRun_correct`**: the register interpreter satisfies `Correct`

The proof strategy bridges computation (`TreeMap`) and reasoning (`Finsupp`/`Nat.factorization`) via `toFinsupp`.

### Future work — two optimizations to formalize

The goal is to formalize the two algorithmic innovations from the Haskell implementation and prove them `Correct` against `naiveRun`.

**1. Static fraction elimination** (Haskell: `optArr`, `fracOpt` in `Fractran.hs`): After fraction `j` fires, precompute which earlier fractions `k < j` can possibly fire next. Fraction `k` is skipped if its denominator shares no prime with `j`'s numerator (if `j` fired, it added those primes, so `k`'s denominator test could not have newly become satisfiable). This is a per-step optimization that reduces the fraction scan from O(l) toward O(1).

**2. Cycle detection with arithmetic leaping** (Haskell: `cycles`, `leap`, `stateSplit` in `Fractran.hs`): Partition registers into *logic* (small exponents that affect control flow) and *data* (large exponents that cannot). When the logic state repeats, compute how many full cycles can be safely skipped before any data register drops into logic territory, then advance the state arithmetically. This is the main speedup (30x+ on benchmarks). Key components:
- `stateSplit`: partition state by threshold `dthresh = cyclen * max_denominator` per prime
- `CBuf`: circular buffer with set-backed membership for detecting logic-state repeats
- `leap`: given a repeated logic state, compute the number of safe cycle repetitions and the resulting state
