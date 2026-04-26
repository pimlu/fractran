# WASM build

Builds the runtime-only fractran demo (`fractran-runtime-demo`) for the browser.
Inputs are the C files Lake generates from the `Fractran.Runtime.*` modules;
outputs are `build/fractran.js` + `build/fractran.wasm`.

The Lean → C step is already handled by Lake. This directory only deals with the
C → WASM step. You'll need to build two static libraries from source first:
the Lean runtime and GMP, both compiled to WebAssembly.

## Quick check

```sh
# From wasm-build/
make help              # see configured paths
make c-files           # regenerate Lake's C output (also runs as part of `make`)
make check-deps        # verify WASM-built libs exist (will fail on a fresh checkout)
```

## Prerequisites

### 1. emscripten

Install the [emsdk](https://emscripten.org/docs/getting_started/downloads.html)
and activate it in your shell:

```sh
source <emsdk>/emsdk_env.sh
which em++   # should resolve
```

### 2. Fetch sources

On first checkout, fetch and pin the GMP signing key (one-time):

```sh
./keys/fetch-gmp-key.sh
git add wasm-build/keys/gmp-signing-key.asc
git commit -m "Pin GMP signing key"
```

Then run setup. This will work without changes on every subsequent clone of
the repo, since the key file is committed:

```sh
make setup
```

`setup.sh` reads `../lean-toolchain` to learn the Lean version, clones
`leanprover/lean4` at the matching tag into `deps/lean4/`, downloads the GMP
tarball into `deps/gmp-<version>/`, and PGP-verifies it against the pinned
key. The verification uses an ephemeral `GNUPGHOME` — your `~/.gnupg` is
never touched. See `keys/README.md` for the trust model.

Override the GMP version with `GMP_VERSION=...` if you need to.

### 3. Lean runtime built for WASM

The Lean toolchain ships its runtime archives (`libleanrt.a`, `libInit.a`,
`libStd.a`, `libleancpp.a`) as native binaries — unusable for WASM. Build
from the cloned source:

```sh
cd deps/lean4
mkdir build-wasm && cd build-wasm
emcmake cmake .. -DCMAKE_BUILD_TYPE=Release
emmake make -j8
```

Then point the Makefile at the built archives. Either copy them to
`wasm-build/deps/lean-wasm/lib/` (the default) or override on the command line:

```sh
make LEAN_WASM_LIBS=$(pwd)/lib
```

> **Heads up:** the Lean runtime port to WASM is not officially supported.
> Expect to patch CMake flags around threading/atomics, possibly disable
> `libuv` (we don't use async I/O), and fight the C++ standard library setup.
> Budget real time for this step.

### 4. GMP built for WASM

```sh
cd deps/gmp-<version>
emconfigure ./configure --host=none --disable-assembly \
    --prefix=$(pwd)/../gmp-wasm
emmake make -j8
emmake make install
```

After this, `deps/gmp-wasm/lib/libgmp.a` and `deps/gmp-wasm/include/gmp.h` exist
where the Makefile expects them. Or use a pre-built port like
[gmp-wasm](https://github.com/Daninet/gmp-wasm) and override `GMP_WASM_LIB` /
`GMP_WASM_INCLUDE`.

## Running the build

Once the prereqs are in place:

```sh
make
# build/fractran.js + build/fractran.wasm
```

The default link produces a CLI-style WASM module. To run under Node:

```sh
node build/fractran.js
```

## Calling from the browser

The default link exports just `_main`. To expose more functions (e.g.
`cycleRunFromRegProg`), add `@[export]` attributes to the relevant Lean
definitions in `Fractran/Runtime/Cycle.lean`, then add the C names to
`-sEXPORTED_FUNCTIONS` in the Makefile's `LDFLAGS`. The Lean compiler
emits one C function per exported binding.

## Project layout

```
wasm-build/
  Makefile         # build orchestration
  README.md        # this file
  build/           # gitignored — emit dir for .o, .wasm, .js
  deps/            # gitignored — drop WASM-built lean4 + GMP here
```

## What's actually getting compiled

```
$ make help     # at the bottom, lists configured paths
```

The link line is:

```
em++ build/MainRuntime.o \
     build/Fractran/Runtime/{Basic,Register,CBuf,Elim,Cycle}.o \
     -L$(LEAN_WASM_LIBS) -lleancpp -lInit -lStd -lleanrt \
     -L$(GMP_WASM_LIB) -lgmp \
     -sALLOW_MEMORY_GROWTH=1 ... -o build/fractran.js
```

Six object files. No mathlib in the closure. The native build of the same
target weighs in around 2.7 MB; the WASM output should be of similar order.
