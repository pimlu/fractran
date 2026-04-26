#!/usr/bin/env bash
# Clone source dependencies for the WASM build:
#   - leanprover/lean4 at the tag matching ../lean-toolchain
#   - GMP (current stable, downloaded as tarball — GMP has no official git repo)
#
# This script only fetches sources; it does NOT build them. See the README for
# the build commands (emcmake / emmake for Lean, emconfigure / emmake for GMP).
#
# Idempotent: if a target directory already exists, the corresponding clone
# step is skipped with a message.

set -euo pipefail

WASM_BUILD_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LEAN_PROJECT="$(cd "$WASM_BUILD_DIR/.." && pwd)"
DEPS_DIR="$WASM_BUILD_DIR/deps"

# ---- Preflight: required tools and files -------------------------------------

missing_tools=""
for tool in git curl tar gpg shasum awk; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    missing_tools="$missing_tools $tool"
  fi
done
if [[ -n "$missing_tools" ]]; then
  echo "ERROR: missing required tools:$missing_tools" >&2
  echo "       Install via your package manager (e.g. 'brew install gnupg' on macOS)." >&2
  exit 1
fi

# Pinned GMP signing key must already be committed. If not, point the user at
# the bootstrap script before we do anything that takes a while.
if [[ ! -f "$WASM_BUILD_DIR/keys/gmp-signing-key.asc" ]] \
   && [[ ! -d "$DEPS_DIR/gmp-${GMP_VERSION:-6.3.0}" ]]; then
  echo "ERROR: missing committed GMP signing key at" >&2
  echo "         $WASM_BUILD_DIR/keys/gmp-signing-key.asc" >&2
  echo "       Run wasm-build/keys/fetch-gmp-key.sh once to fetch and commit it." >&2
  exit 1
fi

# ---- Lean version detection --------------------------------------------------

TOOLCHAIN_FILE="$LEAN_PROJECT/lean-toolchain"
if [[ ! -f "$TOOLCHAIN_FILE" ]]; then
  echo "ERROR: $TOOLCHAIN_FILE not found." >&2
  exit 1
fi

# Format is `leanprover/lean4:v4.30.0-rc2`. Strip everything up to and
# including the colon to get the git tag.
TOOLCHAIN="$(tr -d '[:space:]' < "$TOOLCHAIN_FILE")"
LEAN_TAG="${TOOLCHAIN#*:}"
if [[ -z "$LEAN_TAG" || "$LEAN_TAG" == "$TOOLCHAIN" ]]; then
  echo "ERROR: could not parse tag from lean-toolchain: '$TOOLCHAIN'" >&2
  exit 1
fi

# ---- GMP version + PGP signing key -------------------------------------------

GMP_VERSION="${GMP_VERSION:-6.3.0}"
GMP_TARBALL="gmp-${GMP_VERSION}.tar.xz"
GMP_SIG="${GMP_TARBALL}.sig"
GMP_URL="https://gmplib.org/download/gmp/${GMP_TARBALL}"
GMP_SIG_URL="https://gmplib.org/download/gmp/${GMP_SIG}"

# Fingerprint of Niels Möller's GMP signing key (per gmplib.org). This is the
# trust anchor: it's the fingerprint we commit as part of the repo. If gmplib
# rotates keys, update this and re-fetch the public key file.
GMP_KEY_FINGERPRINT="343C2FF0FBEE5EC2EDBEF399F3599FF828C67298"

# Path to the committed public key. Acts as a lockfile alongside the
# fingerprint above. setup.sh imports this into an ephemeral keyring (not the
# user's ~/.gnupg) and refuses to proceed if its fingerprint doesn't match.
GMP_KEY_FILE="$WASM_BUILD_DIR/keys/gmp-signing-key.asc"

# ---- Clone lean4 -------------------------------------------------------------

LEAN_SRC="$DEPS_DIR/lean4"

if [[ -d "$LEAN_SRC/.git" ]]; then
  echo "==> $LEAN_SRC already exists; skipping clone."
  echo "    (To re-clone: rm -rf $LEAN_SRC)"
else
  echo "==> Cloning leanprover/lean4 at $LEAN_TAG into $LEAN_SRC"
  mkdir -p "$DEPS_DIR"
  git clone --depth 1 --branch "$LEAN_TAG" \
    https://github.com/leanprover/lean4.git "$LEAN_SRC"
fi

# ---- Download GMP ------------------------------------------------------------

GMP_SRC="$DEPS_DIR/gmp-${GMP_VERSION}"

if [[ -d "$GMP_SRC" ]]; then
  echo "==> $GMP_SRC already exists; skipping download."
  echo "    (To re-download: rm -rf $GMP_SRC)"
else
  # Ephemeral GNUPGHOME — the user's ~/.gnupg is never touched.
  TMPHOME="$(mktemp -d -t fractran-gpg.XXXXXX)"
  trap 'rm -rf "$TMPHOME"' EXIT
  export GNUPGHOME="$TMPHOME"
  chmod 700 "$TMPHOME"

  echo "==> Importing GMP signing key from $GMP_KEY_FILE into ephemeral keyring"
  gpg --batch --quiet --import "$GMP_KEY_FILE"

  # Confirm the imported key matches our pinned fingerprint. Defense against
  # tampering with the committed .asc file.
  imported_fp="$(gpg --batch --with-colons --fingerprint "$GMP_KEY_FINGERPRINT" 2>/dev/null \
    | awk -F: '$1=="fpr" {print $10; exit}')"
  if [[ "$imported_fp" != "$GMP_KEY_FINGERPRINT" ]]; then
    echo "ERROR: fingerprint of $GMP_KEY_FILE does not match pinned value" >&2
    echo "  expected: $GMP_KEY_FINGERPRINT" >&2
    echo "  imported: ${imported_fp:-<key not found>}" >&2
    exit 1
  fi
  echo "    OK ($GMP_KEY_FINGERPRINT)"

  echo "==> Downloading GMP $GMP_VERSION + signature"
  mkdir -p "$DEPS_DIR"
  cd "$DEPS_DIR"
  curl -fL -O "$GMP_URL"
  curl -fL -O "$GMP_SIG_URL"

  echo "==> Verifying PGP signature"
  if ! gpg --batch --verify "$GMP_SIG" "$GMP_TARBALL" 2>&1 | tee /tmp/gmp-verify.log | grep -q "Good signature"; then
    echo "ERROR: PGP verification failed for $GMP_TARBALL" >&2
    cat /tmp/gmp-verify.log >&2
    rm -f "$GMP_TARBALL" "$GMP_SIG"
    exit 1
  fi
  echo "    OK"

  echo "==> Extracting $GMP_TARBALL"
  tar -xf "$GMP_TARBALL"
  rm -f "$GMP_TARBALL" "$GMP_SIG"
fi

# ---- Done --------------------------------------------------------------------

cat <<EOF

==> Sources fetched into $DEPS_DIR:
    - lean4    @ $LEAN_TAG
    - gmp      @ $GMP_VERSION

Next steps (see wasm-build/README.md for details):

  1. Activate emsdk in your shell:
       source <emsdk>/emsdk_env.sh

  2. Build Lean for WASM:
       cd $LEAN_SRC
       mkdir -p build-wasm && cd build-wasm
       emcmake cmake .. -DCMAKE_BUILD_TYPE=Release
       emmake make -j8
       # Copy libleanrt.a libInit.a libStd.a libleancpp.a to:
       #   $DEPS_DIR/lean-wasm/lib/

  3. Build GMP for WASM:
       cd $GMP_SRC
       emconfigure ./configure --host=none --disable-assembly \\
           --prefix=$DEPS_DIR/gmp-wasm
       emmake make -j8
       emmake make install

  4. Build the demo:
       cd $WASM_BUILD_DIR
       make
EOF
