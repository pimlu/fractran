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

# Lean project root (where lakefile.toml lives)
LEAN_PROJECT    ?= $(abspath ..)

# C source dir (relative to project root). Lake writes .c files here.
LEAN_IR_DIR     := $(LEAN_PROJECT)/.lake/build/ir

# Output directory (gitignored)
BUILD_DIR       := build

# ---- Source files ------------------------------------------------------------

# Modules in the runtime closure. Order doesn't matter for compilation.
LEAN_MODULES := \
    MainRuntime \
    Fractran/Runtime/Basic \
    Fractran/Runtime/Register \
    Fractran/Runtime/CBuf \
    Fractran/Runtime/Elim \
    Fractran/Runtime/Cycle

LEAN_C_SRCS  := $(addprefix $(LEAN_IR_DIR)/,$(addsuffix .c,$(LEAN_MODULES)))
WASM_OBJS    := $(addprefix $(BUILD_DIR)/,$(addsuffix .o,$(LEAN_MODULES)))

# ---- Compiler flags ----------------------------------------------------------

# Lean's generated code is C++ (uses `extern "C" {}` blocks). Use em++.
EMCXX        ?= em++

# Optimization. -O2 is a reasonable default; bump to -O3 if you want.
OPT          ?= -O2

# Lean codegen depends on the same flags leanc passes. Most important:
# -DLEAN_BUILD_FOR_RELEASE for runtime macros, -fvisibility=hidden for size,
# -fno-exceptions to match the runtime's no-exceptions build.
CXXFLAGS_BASE := $(OPT) -std=c++17 -fno-exceptions -fvisibility=hidden \
                 -DLEAN_BUILD_FOR_RELEASE
CXXFLAGS_INC  := -I$(LEAN_PREFIX)/include -I$(GMP_WASM_INCLUDE)

# Link flags. `-sALLOW_MEMORY_GROWTH=1` is essential — the demo allocates
# big integers and lists. `-sINITIAL_MEMORY` gives us headroom up front.
# `-sSTACK_SIZE` because Lean recurses on big lists.
LDFLAGS := \
    $(OPT) \
    -sALLOW_MEMORY_GROWTH=1 \
    -sINITIAL_MEMORY=64MB \
    -sSTACK_SIZE=8MB \
    -sNO_EXIT_RUNTIME=0 \
    -sASSERTIONS=1 \
    -L$(LEAN_WASM_LIBS) \
    -L$(GMP_WASM_LIB)

# Order matters for static linking: leanrt depends on Init/Std, leancpp glues
# them together, and gmp is a leaf.
LDLIBS := -lleancpp -lInit -lStd -lleanrt -lgmp

# ---- Targets -----------------------------------------------------------------

.PHONY: all setup c-files clean distclean check-deps help

all: $(BUILD_DIR)/fractran.js

# Fetch lean4 source (matching lean-toolchain) and GMP tarball into deps/.
# Does not build them — see README for emcmake/emconfigure commands.
setup:
	@./setup.sh

# Force a Lake rebuild of the runtime demo (regenerates the .c files we link).
c-files:
	@echo "==> Regenerating C files via Lake"
	cd $(LEAN_PROJECT) && lake build fractran-runtime-demo

# Compile each Lean-generated .c into a .o under build/.
$(BUILD_DIR)/%.o: $(LEAN_IR_DIR)/%.c | $(BUILD_DIR)
	@mkdir -p $(dir $@)
	$(EMCXX) $(CXXFLAGS_BASE) $(CXXFLAGS_INC) -c $< -o $@

# Link everything into the final wasm + js loader.
$(BUILD_DIR)/fractran.js: $(WASM_OBJS) | check-deps
	$(EMCXX) $(LDFLAGS) $(WASM_OBJS) $(LDLIBS) -o $@
	@echo
	@echo "==> Built $(BUILD_DIR)/fractran.js + $(BUILD_DIR)/fractran.wasm"

$(BUILD_DIR):
	@mkdir -p $(BUILD_DIR)

# Sanity-check that the user has built / placed the prerequisite static libs.
check-deps:
	@missing= ; \
	for lib in libleanrt.a libInit.a libStd.a libleancpp.a ; do \
	  if [ ! -f "$(LEAN_WASM_LIBS)/$$lib" ]; then \
	    missing="$$missing $(LEAN_WASM_LIBS)/$$lib" ; \
	  fi ; \
	done ; \
	if [ ! -f "$(GMP_WASM_LIB)/libgmp.a" ]; then \
	  missing="$$missing $(GMP_WASM_LIB)/libgmp.a" ; \
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
	@echo "  all         - build $(BUILD_DIR)/fractran.{js,wasm} (default)"
	@echo "  setup       - fetch lean4 + GMP sources into deps/"
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
