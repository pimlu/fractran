# WASM build

Builds the runtime-only fractran demo (`fractran-runtime-demo`) for the browser
or node. Outputs `build/fractran.js` + `build/fractran.wasm` (~1.5 MB total).

## End-to-end on a fresh clone

```sh
# 0. Activate emsdk and have it on PATH
source <emsdk>/emsdk_env.sh

# 1. One-time bootstrap of the GMP signing key (only needed if
#    keys/gmp-signing-key.asc is not already committed)
./keys/fetch-gmp-key.sh
git add wasm-build/keys/gmp-signing-key.asc
git commit -m "Pin GMP signing key"

# 2. Fetch source dependencies — clones lean4 (matching ../lean-toolchain)
#    and libuv, downloads + PGP-verifies GMP
make setup

# 3. Build WASM static archives — emconfigure GMP, emcmake libuv, em++
#    libleanrt + libInit + libStd. Slow on first run (~10 min); incremental
#    after that.
make build-deps

# 4. Compile + link the demo
make
node build/fractran.js
```

Expected output of step 4:

```
--- Hamming weight of 2^(2^128 - 1) (runtime build) ---
Input exponent of 2: 340282366920938463463374607431768211455
Cycle length: 2, Steps simulated: 1020847100762815390390123822295304634365
Halted: true
Hamming weight (exponent of 13): 128
Expected: 128
SUCCESS!
```

The WASM binary is computing `popcount(2^128 - 1) = 128` via cycle detection
over 10²¹ simulated FRACTRAN steps.

## What gets built

| Target | Source | Toolchain |
|---|---|---|
| `libgmp.a` (WASM) | gmp-6.3.0 source | `emconfigure` + `emmake` |
| `libuv.a` (WASM) | libuv v1.48.0 + small lean4 patch | `emcmake` + `emmake` |
| `libleanrt.a` (WASM) | `lean4/src/runtime/*.cpp` (24 files) | `em++` |
| `libInit.a` (WASM) | `lean4/stage0/stdlib/Init/*.c` (~588 files) | `em++` |
| `libStd.a` (WASM) | `lean4/stage0/stdlib/Std/*.c` (~442 files) | `em++` |
| `fractran.{js,wasm}` | `Fractran.Runtime.*` Lake C output + above | `em++` |

We do **not** build the lean compiler/parser/elaborator — `stage0/stdlib/`
ships pre-generated `.c` files (the bootstrap output of `lean` applied to
`Init`/`Std` source). We feed those directly to `em++`.

## Trust model

GMP is downloaded as a tarball from gmplib.org and PGP-verified against
Niels Möller's signing key (fingerprint pinned in `setup.sh`,
public key committed at `keys/gmp-signing-key.asc`). Verification uses an
ephemeral `GNUPGHOME` — your `~/.gnupg` is never touched. See
`keys/README.md` for the full rationale.

`lean4` and `libuv` come from their official GitHub repos at pinned tags.

## Patches we apply

Both stored under `patches/`, applied idempotently by `build-deps.sh`:

- **`libuv-emscripten.patch`** — adds `src/unix/no-proctitle.c` to libuv's
  CMake build for Emscripten. Lifted from lean4's own `src/CMakeLists.txt`,
  which inlines the same patch when targeting Emscripten.
- **`lean4-emscripten-thread.patch`** — under `LEAN_EMSCRIPTEN`, makes
  `lthread::imp` run its closure synchronously instead of calling
  `pthread_create`. Without `-pthread`, emscripten's `pthread_create` returns
  `ENOTSUP` and Lean's runtime throws `failed to create thread` during init.
  Tasks (`lean_task_spawn`) would deadlock if called after this — but the
  fractran demo doesn't use tasks.

## Configuration knobs

`make help` prints the resolved values. Override on the command line:

| Variable | Default | What |
|---|---|---|
| `LEAN_PREFIX` | `$(lean --print-prefix)` | Lean toolchain include dir |
| `LEAN_WASM_LIBS` | `deps/lean-wasm/lib` | where libleanrt/Init/Std land |
| `GMP_WASM_LIB` / `GMP_WASM_INCLUDE` | `deps/gmp-wasm/{lib,include}` | |
| `LIBUV_WASM_LIB` / `LIBUV_WASM_INCLUDE` | `deps/libuv-wasm/{lib,include}` | |
| `GMP_VERSION` (setup.sh) | `6.3.0` | GMP tarball version + checksum branch |
| `LIBUV_TAG` (setup.sh) | `v1.48.0` | libuv git tag (matches lean4) |

## Calling from the browser

The web target (`fractran-web.{js,wasm}`) exposes `_fractran_run`, a thin
C wrapper (`bridge.cpp`) around the Lean export
`fractran_run_lean : String → String → String → String` defined in
`Fractran.Runtime.JsBridge`. The three string args are cyclen, program
source, and initial-state source; Lean parses them via
`Fractran.Runtime.Parse` and runs `Runner.cycleRunUntilHalt`.

Wire-up:

1. The `@[export fractran_run_lean]` attribute on the Lean def causes the
   Lean compiler to emit a `lean_object* fractran_run_lean(...)` symbol.
2. `bridge.cpp` defines `fractran_run(const char*, const char*, const char*)`,
   marshalling C strings to Lean strings via `lean_mk_string` and copying
   the result string out to a `malloc`'d buffer the caller frees.
3. The Makefile passes `--export=fractran_run` (and `_main`) via
   `-sEXPORTED_FUNCTIONS`.
4. JS side: `Module.ccall('fractran_run', 'number', ['string', 'string',
   'string'], [cyclen, programSrc, inputSrc])`. The returned pointer is a
   `char*` containing `OK ...` or `ERR ...`; read with
   `Module.UTF8ToString(ptr)` and free with `Module._free(ptr)`.

To expose any other Lean function the same way, add an `@[export]` binding,
list its C name in `-sEXPORTED_FUNCTIONS`, and (for non-trivial argument
types) add a marshalling shim to `bridge.cpp`.

## Project layout

```
wasm-build/
  Makefile              # link orchestration (also setup / build-deps / clean)
  setup.sh              # clones lean4 + libuv, fetches+verifies GMP
  build-deps.sh         # builds GMP, libuv, libleanrt, libInit, libStd for WASM
  README.md             # this file
  patches/
    libuv-emscripten.patch
    lean4-emscripten-thread.patch
  keys/
    fetch-gmp-key.sh    # one-time: fetch + pin the GMP signing key
    gmp-signing-key.asc # committed public key
    README.md           # trust model
  build/                # gitignored — .o files + fractran.{js,wasm}
  deps/                 # gitignored — sources + WASM-built archives
```

## Make targets

```
make            # link demo (default)
make setup      # fetch sources into deps/
make build-deps # WASM-build the static libraries
make c-files    # regenerate Lake's C output (rerun if Lean changes)
make clean      # remove build/
make distclean  # also remove deps/
make check-deps # verify the WASM static libs are present
make help       # show resolved configuration
```
