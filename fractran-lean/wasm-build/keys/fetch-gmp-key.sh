#!/usr/bin/env bash
# One-time bootstrap: fetch the GMP signing key from a public keyserver,
# verify it has the fingerprint pinned in setup.sh, and write it to
# wasm-build/keys/gmp-signing-key.asc for committing to the repo.
#
# Uses an ephemeral GNUPGHOME — the user's ~/.gnupg is never touched.
#
# Run once:
#   $ ./keys/fetch-gmp-key.sh
# Then commit the resulting .asc file.

set -euo pipefail

KEYS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WASM_BUILD_DIR="$(cd "$KEYS_DIR/.." && pwd)"

# Read the pinned fingerprint from setup.sh so it stays in one place.
GMP_KEY_FINGERPRINT="$(grep -E '^GMP_KEY_FINGERPRINT=' "$WASM_BUILD_DIR/setup.sh" \
  | head -1 | sed -E 's/.*"([A-F0-9]+)".*/\1/')"

if [[ -z "$GMP_KEY_FINGERPRINT" ]]; then
  echo "ERROR: could not parse GMP_KEY_FINGERPRINT from setup.sh" >&2
  exit 1
fi

OUT="$KEYS_DIR/gmp-signing-key.asc"

if [[ -f "$OUT" ]]; then
  echo "ERROR: $OUT already exists. Remove it first if you really want to refetch." >&2
  exit 1
fi

if ! command -v gpg >/dev/null 2>&1; then
  echo "ERROR: gpg is required. Install via 'brew install gnupg' or 'apt install gnupg'." >&2
  exit 1
fi

# Ephemeral keyring
TMPHOME="$(mktemp -d -t fractran-gpg-fetch.XXXXXX)"
trap 'rm -rf "$TMPHOME"' EXIT
export GNUPGHOME="$TMPHOME"
chmod 700 "$TMPHOME"

# Try a few keyservers in order. Different networks block different ones.
KEYSERVERS=(
  "hkps://keys.openpgp.org"
  "hkps://keyserver.ubuntu.com"
  "hkps://pgp.mit.edu"
)

echo "==> Fetching key $GMP_KEY_FINGERPRINT"
fetched=0
for ks in "${KEYSERVERS[@]}"; do
  echo "    trying $ks"
  if gpg --batch --keyserver "$ks" --recv-keys "$GMP_KEY_FINGERPRINT" 2>&1 | grep -q "imported\|not changed"; then
    fetched=1
    break
  fi
done

if [[ $fetched -ne 1 ]]; then
  echo "ERROR: could not fetch key from any keyserver." >&2
  echo "       You can fetch it manually and place an ASCII-armored export at:" >&2
  echo "         $OUT" >&2
  exit 1
fi

# Sanity-check: imported key has the expected fingerprint.
imported_fp="$(gpg --batch --with-colons --fingerprint "$GMP_KEY_FINGERPRINT" 2>/dev/null \
  | awk -F: '$1=="fpr" {print $10; exit}')"

if [[ "$imported_fp" != "$GMP_KEY_FINGERPRINT" ]]; then
  echo "ERROR: fetched key fingerprint mismatch" >&2
  echo "  expected: $GMP_KEY_FINGERPRINT" >&2
  echo "  got:      ${imported_fp:-<empty>}" >&2
  exit 1
fi

# Export ASCII-armored to the keys dir.
gpg --batch --armor --export "$GMP_KEY_FINGERPRINT" > "$OUT"

cat <<EOF

==> Wrote $OUT

Fingerprint (pinned in setup.sh):
  $GMP_KEY_FINGERPRINT

Now commit the file:
  git add wasm-build/keys/gmp-signing-key.asc
  git commit -m "Pin GMP signing key for WASM build"

Subsequent runs of \`make setup\` will use the committed key directly — no
keyserver access required, and your global ~/.gnupg is never touched.
EOF
