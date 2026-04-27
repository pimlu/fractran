# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

A high-performance FRACTRAN interpreter written in Haskell. FRACTRAN programs are ordered lists of fractions; evaluation repeatedly multiplies the current state by the first fraction whose product is an integer, halting when none qualify. This repo achieves 30x+ speedups over naive implementations via two algorithmic innovations: static fraction elimination and cycle detection with arithmetic "leaping."

The whitepaper `termpd.tex` contains the formal proofs and benchmarks. `fractran-lean/` is a Lean 4 formalization (using mathlib) plus a CLI binary, a node demo, and a React web UI built on a WASM compile of the Lean runtime — see `fractran-lean/web-build/` (front-end) and `fractran-lean/wasm-build/` (em++ link of the Lean-generated C). The legacy Haskell-via-Asterius `web/` directory still exists but is no longer the recommended browser path.

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

The Lean side mirrors the Haskell implementation: it has the naive interpreter, the register-based interpreter, the static fraction-elimination optimization, and the cycle-detecting interpreter with arithmetic leaping. All four satisfy a single uniform correctness predicate (`Correct`).

### Correctness framework

A FRACTRAN program is `List (ℕ × ℕ)` (numerator, denominator pairs). Reference semantics:

- **`naiveStep`** (`Runtime/Basic.lean`): scans for the first fraction `(p, q)` where `q ∣ n`, returning `n / q * p`. Returns `none` if no fraction applies (halt).
- **`naiveRun`** (`Runtime/Basic.lean`): iterates `naiveStep` for `k` steps. Returns `some m` if still running, `none` if halted.
- **`WellFormed`** (`Basic.lean`): all numerators and denominators are positive.
- **`Correct`** (`Basic.lean`): any interpreter `interp prog n k → (Option ℕ × ℕ)` is correct if it returns `(result, j)` with `j ≥ k` and `naiveRun prog n j = result`. This handles both halting and cycle-detection interpreters uniformly.

### Runtime / proof split

Each Lean module is split in two:
- `Fractran/Runtime/X.lean` — data types, computational definitions, runners. Imports only `Std` and `Init` (no mathlib). These are the modules whose Lake-generated C output ships in the WASM build.
- `Fractran/X.lean` — proofs and predicates that need mathlib (`Finsupp`, `Nat.factorization`, etc.). Imports the runtime side and adds theorems on top of it.

The split exists so the WASM build can compile only the runtime modules — every `Runtime/*.olean` has zero mathlib in its `importArts`. The native build still pulls in everything for the full proofs.

Layout:

```
Fractran/
  Runtime/Basic.lean        # FractranProg, naiveStep, naiveRun
  Runtime/Register.lean     # RegMap (= Std.TreeMap ℕ ℕ), Mul/Div/applicable, regStep/Run
  Runtime/CBuf.lean         # circular buffer
  Runtime/Elim.lean         # optTable, elimStep — static fraction elimination
  Runtime/Cycle.lean        # cycleStep, cycleRunFromRegProg, leapState, dthreshMap
  Runtime/Parse.lean        # parser for the surface syntax (program + state)
  Runtime/JsBridge.lean     # runWithLimit + @[export] fractran_run_lean entry point
  Basic.lean, Register.lean, CBuf.lean, Elim.lean, Cycle.lean,
  JsBridge.lean             # proofs (incl. detectInfiniteLoop_sound)
  ParseTests.lean           # native_decide test suite for the parser
```

### What's proven

**Register interpreter** (`Register.lean`): `RegMap = Std.TreeMap ℕ ℕ`. Key results:
- `facmap`/`unfmap` round-trip: `unfmap (facmap n) = n` for `n > 0`.
- Homomorphisms: `unfmap (m₁ * m₂) = unfmap m₁ * unfmap m₂`, `unfmap (m / den) = unfmap m / unfmap den` (when applicable).
- `applicable den m ↔ unfmap den ∣ unfmap m` for well-formed maps.
- **`regRun_correct`**: the register interpreter satisfies `Correct`.

The proof strategy bridges computation (`TreeMap`) and reasoning (`Finsupp`/`Nat.factorization`) via `toFinsupp`.

**Static fraction elimination** (`Elim.lean`): `optTable` precomputes, per fraction index, which fractions can fire next. `ElimInvariant` says the candidate list is a sublist of all candidates and every omitted entry is currently inapplicable. Theorems show:
- `elimStep_eq_regStep` under the invariant.
- `optTable_preserves_invariant` after a step.
- **`elimRun_correct`**: the elimination interpreter satisfies `Correct`.

**Cycle detection with arithmetic leaping** (`Cycle.lean`): Partition registers into *logic* (`exp ≤ thresh`) and *data* (`exp > thresh`) where `thresh = cyclen * max_denominator` per prime. The proof has three layers:
1. `data_irrelevant`: changing data registers can't change which fraction fires (Lemma 1 in the paper).
2. `cycle_properties` / `cycle_same_fracs`: if two states share their logic component and the cycle invariant holds, the same fraction sequence fires for the configured number of cycle repetitions (Theorem 2).
3. `leap_correct` + `cycleRunAux_correct` + **`cycleRun_correct`**: the cycle-detecting interpreter satisfies `Correct`.

`cycleRunFromRegProg` is the runtime-callable entry: takes a pre-factored program (`List (RegMap × RegMap)`) and a starting `RegMap`, returns a `CycleState`. The `Nat`-keyed wrapper `cycleRunNat` lives on the proof side because it uses `RegMap.facmap` (which uses `Nat.primeFactorsList` from mathlib).

### Entry points (lakefile.toml targets)

| Target | Source | Purpose |
|---|---|---|
| `fractran` | `Main.lean` | The CLI: parses a program file + initial-state arg via `Fractran.Runtime.Parse`, runs `Runner.cycleRunUntilHalt`, prints the result. Usage: `fractran <prog-file> <state> [cyclen]`. |
| `fractran-demo` | `Demo.lean` | Hardcoded demos — cycle test, Hamming weight of `2^(2^128 - 1)`, and the 24-fraction self-interpreter. Proof-side build (full mathlib import closure). |
| `fractran-runtime-demo` | `MainRuntime.lean` | Runtime-only Hamming demo with the program pre-factored via `RegMap.ofFactors`. Zero mathlib in the import closure — sanity-check entry point for the WASM build. |
| `fractran-web-lib` | `MainWeb.lean` | Empty `def main` (just initializes the Lean runtime). Pulled into the WASM artifact alongside `Fractran.Runtime.JsBridge`, which `@[export]`s `fractran_run_lean : String → String → String → String` (cyclen / program / initial state, all parsed by `Fractran.Runtime.Parse`). |

### WASM build (`fractran-lean/wasm-build/`)

Compiles `fractran-runtime-demo` to `fractran.{js,wasm}` (~1.5 MB). The full reproducible flow:

```sh
cd fractran-lean/wasm-build
source <emsdk>/emsdk_env.sh
make setup        # clones lean4 + libuv, fetches + PGP-verifies GMP
make build-deps   # builds libgmp, libuv, libleanrt, libInit, libStd for WASM
make              # links the demo
node build/fractran.js
```

Key facts:
- We do **not** build the lean compiler. `lean4/stage0/stdlib/` ships pre-generated `.c` files for `Init` and `Std` (the bootstrap output); we feed those directly to `em++`.
- We do **not** link `libleancpp.a` (kernel/elaborator/parser). Runtime-only modules don't need it.
- Two patches under `wasm-build/patches/` are applied idempotently by `build-deps.sh`: a one-line addition to libuv's CMake for Emscripten, and a small `lthread::imp` stub for Lean's runtime to avoid `pthread_create` failing under emscripten without `-pthread`.
- GMP is PGP-verified using a pinned signing key checked into `wasm-build/keys/`, in an ephemeral `GNUPGHOME` (the user's `~/.gnupg` is never touched).

See `wasm-build/README.md` for the full prerequisites and configuration knobs.
