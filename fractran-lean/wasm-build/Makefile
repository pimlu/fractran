# Makefile for the WASM build of fractran-runtime-demo.
#
# Compiles the C output of `lake build fractran-runtime-demo` with emscripten,
# linking against WASM-built Lean runtime and GMP. Outputs build/fractran.{js,wasm}.
#
# Prerequisites (none of these are downloaded automatically — see README.md):
#
#   1. emsdk activated in this shell (`source emsdk_env.sh` from emsdk repo).
#      All emcc/em++ commands must be on PATH.
#
#   2. The Lean toolchain Lake used to generate the C files. We auto-detect
#      this via `lean --print-prefix`. Override with LEAN_PREFIX if needed.
#
#   3. WASM-built Lean static archives in $(LEAN_WASM_LIBS):
#        libleanrt.a libInit.a libStd.a libleancpp.a
#      You build these from the leanprover/lean4 source at the matching tag
#      (read fractran-lean/lean-toolchain) using emcmake / emmake. See README.
#
#   4. WASM-built GMP at $(GMP_WASM_LIB)/libgmp.a with headers at $(GMP_WASM_INCLUDE).
#      Use the gmp-wasm port or build GMP from source with `emconfigure`.
#
# Usage:
#   make                    # full build (c-files + wasm)
#   make c-files            # regenerate Lake's C output
#   make clean              # remove build/ outputs
#   make distclean          # also drop downloaded deps (if any are placed under deps/)

# ---- Configurable paths (override on the command line) -----------------------

# Lean toolchain prefix (provides include/lean/*.h)
LEAN_PREFIX     ?= $(shell lean --print-prefix)

# Where the WASM-built Lean archives live. Defaults to deps/lean-wasm/lib;
# you'll need to point this at your actual emcmake/emmake output.
LEAN_WASM_LIBS  ?= $(abspath deps/lean-wasm/lib)

# Where the WASM-built GMP lives.
GMP_WASM_LIB     ?= $(abspath deps/gmp-wasm/lib)
GMP_WASM_INCLUDE ?= $(abspath deps/gmp-wasm/include)

# Where the WASM-built libuv lives.
LIBUV_WASM_LIB     ?= $(abspath deps/libuv-wasm/lib)
LIBUV_WASM_INCLUDE ?= $(abspath deps/libuv-wasm/include)

# Lean project root (where lakefile.toml lives)
LEAN_PROJECT    ?= $(abspath ..)

# C source dir (relative to project root). Lake writes .c files here.
LEAN_IR_DIR     := $(LEAN_PROJECT)/.lake/build/ir

# Output directory (gitignored)
BUILD_DIR       := build

# ---- Source files ------------------------------------------------------------

# Modules shared between the node and web builds.
LEAN_MODULES_SHARED := \
    Fractran/Runtime/Basic \
    Fractran/Runtime/Register \
    Fractran/Runtime/CBuf \
    Fractran/Runtime/Elim \
    Fractran/Runtime/Cycle

# Node target: hardcoded Hamming demo. MainRuntime defines `def main`.
LEAN_MODULES_NODE := MainRuntime $(LEAN_MODULES_SHARED)

# Web target: empty `def main` in MainWeb (Lean runtime init only) plus the
# JsBridge module that defines @[export] fractran_run_lean.
LEAN_MODULES_WEB := MainWeb Fractran/Runtime/JsBridge $(LEAN_MODULES_SHARED)

# Concatenation of all modules — used for compiling .o files (each module
# compiled once, linked into whichever binary needs it).
LEAN_MODULES := $(sort $(LEAN_MODULES_NODE) $(LEAN_MODULES_WEB))

LEAN_C_SRCS    := $(addprefix $(LEAN_IR_DIR)/,$(addsuffix .c,$(LEAN_MODULES)))
WASM_OBJS_NODE := $(addprefix $(BUILD_DIR)/,$(addsuffix .o,$(LEAN_MODULES_NODE)))
WASM_OBJS_WEB  := $(addprefix $(BUILD_DIR)/,$(addsuffix .o,$(LEAN_MODULES_WEB)))
BRIDGE_OBJ     := $(BUILD_DIR)/bridge.o

# ---- Compiler flags ----------------------------------------------------------

# Lean's generated code is C++ (uses `extern "C" {}` blocks). Use em++.
EMCXX        ?= em++

# Optimization. -O2 is a reasonable default; bump to -O3 if you want.
OPT          ?= -O2

# Match the flags build-deps.sh used to compile libInit/libStd: same C++
# standard (C++20 — atomic::wait/notify), same LEAN_* macros. Note: NO
# -fno-exceptions; Lean's runtime uses `throw`. Catch blocks are still
# omitted at -O1+ by emscripten default.
CXXFLAGS_BASE := $(OPT) -std=c++20 -fvisibility=hidden \
                 -DLEAN_BUILD_FOR_RELEASE \
                 -DLEAN_EMSCRIPTEN \
                 -DLEAN_MULTI_THREAD
# $GEN_INC has the no-mimalloc config.h that build-deps.sh wrote. It must
# come BEFORE $(LEAN_PREFIX)/include (which has the toolchain's mimalloc-on
# config.h). Otherwise lean.h inlines mi_malloc_* calls and we get undefined
# symbols at link time.
GEN_INC       := $(abspath build/wasm-deps/gen-include)
CXXFLAGS_INC  := -I$(GEN_INC) -I$(LEAN_PREFIX)/include \
                 -I$(GMP_WASM_INCLUDE) -I$(LIBUV_WASM_INCLUDE)

# Link flags. `-sALLOW_MEMORY_GROWTH=1` is essential — the demo allocates
# big integers and lists. `-sINITIAL_MEMORY` gives us headroom up front.
# `-sSTACK_SIZE` because Lean recurses on big lists.
LDFLAGS := \
    $(OPT) \
    -sALLOW_MEMORY_GROWTH=1 \
    -sINITIAL_MEMORY=64MB \
    -sSTACK_SIZE=8MB \
    -sASSERTIONS=1 \
    -L$(LEAN_WASM_LIBS) \
    -L$(GMP_WASM_LIB) \
    -L$(LIBUV_WASM_LIB)

# Web-targeted link flags. Same base flags plus:
#   MODULARIZE + EXPORT_ES6   - emit an ES module whose default export is a
#                               Module factory. Lets the worker do
#                               `import Module from './fractran-web.js'`.
#   INVOKE_RUN=0              - don't auto-run main; the worker calls
#                               Module.callMain([]) explicitly to initialize
#                               the Lean runtime, then ccall fractran_run.
#   EXPORTED_FUNCTIONS        - keep `_fractran_run` (defined in bridge.cpp,
#                               wraps the Lean-generated fractran_run_lean)
#                               and `_free` (so JS can free the returned
#                               malloc'd char*).
#   EXPORTED_RUNTIME_METHODS  - JS-side helpers: callMain to init, ccall to
#                               invoke the bridge, UTF8ToString to decode.
#   ENVIRONMENT=web,worker    - drop the node-only code paths to shrink output.
LDFLAGS_WEB := \
    $(LDFLAGS) \
    -sMODULARIZE=1 \
    -sEXPORT_ES6=1 \
    -sINVOKE_RUN=0 \
    -sNO_EXIT_RUNTIME=1 \
    -sEXPORTED_FUNCTIONS=_fractran_run,_main,_malloc,_free \
    -sEXPORTED_RUNTIME_METHODS=callMain,ccall,UTF8ToString \
    -sENVIRONMENT=web,worker

# Order matters for static linking: Init+Std reference leanrt symbols; leanrt
# pulls in libuv stubs and gmp. We don't link libleancpp (kernel/elaborator)
# because we never build it — runtime-only modules don't need it.
LDLIBS := -lInit -lStd -lleanrt -luv -lgmp

# ---- Targets -----------------------------------------------------------------

.PHONY: all setup build-deps c-files clean distclean check-deps help

all: $(BUILD_DIR)/fractran.js $(BUILD_DIR)/fractran-web.js

# Fetch lean4 source (matching lean-toolchain) and GMP tarball into deps/.
# Does not build them — see README for emcmake/emconfigure commands.
setup:
	@./setup.sh

# Build the WASM static archives we need (libleanrt.a, libInit.a, libStd.a)
# from the cloned lean4. Skips the parser/elaborator/kernel — those targets
# aren't requested. Intermediate output goes under deps/lean4/build-wasm/.
build-deps:
	@./build-deps.sh

# Force a Lake rebuild of the runtime demo (regenerates the .c files we link).
c-files:
	@echo "==> Regenerating C files via Lake (node + web)"
	cd $(LEAN_PROJECT) && lake build fractran-runtime-demo fractran-web-lib

# Compile each Lean-generated .c into a .o under build/.
$(BUILD_DIR)/%.o: $(LEAN_IR_DIR)/%.c | $(BUILD_DIR)
	@mkdir -p $(dir $@)
	$(EMCXX) $(CXXFLAGS_BASE) $(CXXFLAGS_INC) -c $< -o $@

# Compile the C++ bridge (in-tree, not from Lake's IR dir).
$(BRIDGE_OBJ): bridge.cpp | $(BUILD_DIR)
	$(EMCXX) $(CXXFLAGS_BASE) $(CXXFLAGS_INC) -c $< -o $@

# Static archives we link against. Listing them here makes the link a real
# dependency — `make` will re-link if any of them change (e.g. after rebuilding
# libleanrt.a via `make build-deps` after a patch update).
WASM_STATIC_LIBS := \
    $(LEAN_WASM_LIBS)/libleanrt.a \
    $(LEAN_WASM_LIBS)/libInit.a \
    $(LEAN_WASM_LIBS)/libStd.a \
    $(GMP_WASM_LIB)/libgmp.a \
    $(LIBUV_WASM_LIB)/libuv.a

# Link the node demo (MainRuntime + shared runtime modules).
$(BUILD_DIR)/fractran.js: $(WASM_OBJS_NODE) $(WASM_STATIC_LIBS) | check-deps
	$(EMCXX) $(LDFLAGS) $(WASM_OBJS_NODE) $(LDLIBS) -o $@
	@echo
	@echo "==> Built $(BUILD_DIR)/fractran.js + $(BUILD_DIR)/fractran.wasm"

# Link the web variant (MainWeb + JsBridge + shared modules + bridge.cpp).
# Produces an ES module (fractran-web.js) plus the wasm sidecar.
$(BUILD_DIR)/fractran-web.js: $(WASM_OBJS_WEB) $(BRIDGE_OBJ) $(WASM_STATIC_LIBS) | check-deps
	$(EMCXX) $(LDFLAGS_WEB) $(WASM_OBJS_WEB) $(BRIDGE_OBJ) $(LDLIBS) -o $@
	@echo
	@echo "==> Built $(BUILD_DIR)/fractran-web.js + $(BUILD_DIR)/fractran-web.wasm"

$(BUILD_DIR):
	@mkdir -p $(BUILD_DIR)

# Sanity-check that the user has built / placed the prerequisite static libs.
check-deps:
	@missing= ; \
	for lib in libleanrt.a libInit.a libStd.a ; do \
	  if [ ! -f "$(LEAN_WASM_LIBS)/$$lib" ]; then \
	    missing="$$missing $(LEAN_WASM_LIBS)/$$lib" ; \
	  fi ; \
	done ; \
	if [ ! -f "$(GMP_WASM_LIB)/libgmp.a" ]; then \
	  missing="$$missing $(GMP_WASM_LIB)/libgmp.a" ; \
	fi ; \
	if [ ! -f "$(LIBUV_WASM_LIB)/libuv.a" ]; then \
	  missing="$$missing $(LIBUV_WASM_LIB)/libuv.a" ; \
	fi ; \
	if [ -n "$$missing" ]; then \
	  echo "ERROR: missing WASM-built static libraries:" ; \
	  for f in $$missing ; do echo "  $$f" ; done ; \
	  echo ; \
	  echo "See wasm-build/README.md for how to build them." ; \
	  exit 1 ; \
	fi
	@if ! command -v $(EMCXX) >/dev/null 2>&1 ; then \
	  echo "ERROR: $(EMCXX) not on PATH. Activate emsdk first." ; \
	  exit 1 ; \
	fi

clean:
	rm -rf $(BUILD_DIR)

distclean: clean
	rm -rf deps

help:
	@echo "Targets:"
	@echo "  all         - build node + web variants (default)"
	@echo "  $(BUILD_DIR)/fractran.js     - node sanity demo (runs main on import)"
	@echo "  $(BUILD_DIR)/fractran-web.js - web ES module (default export = Module factory)"
	@echo "  setup       - fetch lean4 + GMP sources into deps/"
	@echo "  build-deps  - build WASM lean4 + GMP archives into deps/{lean-wasm,gmp-wasm}/"
	@echo "  c-files     - regenerate Lake's C output"
	@echo "  check-deps  - verify WASM static libs and emcc toolchain are present"
	@echo "  clean       - remove $(BUILD_DIR)/"
	@echo "  distclean   - also remove deps/"
	@echo
	@echo "Configurable paths (override on command line, e.g. make GMP_WASM_LIB=...):"
	@echo "  LEAN_PREFIX       = $(LEAN_PREFIX)"
	@echo "  LEAN_WASM_LIBS    = $(LEAN_WASM_LIBS)"
	@echo "  GMP_WASM_LIB      = $(GMP_WASM_LIB)"
	@echo "  GMP_WASM_INCLUDE  = $(GMP_WASM_INCLUDE)"
