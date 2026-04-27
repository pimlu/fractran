# Pinned trust anchors

This directory holds the OpenPGP signing keys used to verify the WASM build's
external sources. The contents act as a lockfile — they are checked into the
repo so anyone cloning gets identical, verified inputs.

## How verification works

1. The expected key fingerprint is **hardcoded in `wasm-build/setup.sh`**
   (`GMP_KEY_FINGERPRINT`). That value is the actual trust anchor.
2. The corresponding public key is **committed here** as `*.asc`.
3. Before using a committed key, `setup.sh` imports it into a brand-new
   ephemeral `GNUPGHOME` (your `~/.gnupg` is never touched) and confirms its
   fingerprint matches the value pinned in `setup.sh`. Any tampering with the
   `.asc` file is caught at this step.
4. Only then is the corresponding tarball signature verified.

So: anyone wanting to subvert the build has to alter both `setup.sh` and the
key file, in matching ways, in a commit you accept. The pin makes that loud.

## Bootstrapping the GMP key

If `gmp-signing-key.asc` is missing (e.g., on a fresh repo before anyone has
run the bootstrap), run:

```sh
./fetch-gmp-key.sh
```

This fetches the key from a public keyserver, verifies it matches the
fingerprint pinned in `setup.sh`, writes the ASCII-armored export to
`gmp-signing-key.asc`, and tells you to commit it.

The script tries multiple keyservers (`keys.openpgp.org`, `keyserver.ubuntu.com`,
`pgp.mit.edu`) since networks block different ones.

## Rotating the key

If gmplib publishes a new signing key:

1. Update `GMP_KEY_FINGERPRINT` in `wasm-build/setup.sh` to the new value.
2. Delete `gmp-signing-key.asc`.
3. Run `./fetch-gmp-key.sh` to fetch the new key.
4. Commit the updated `setup.sh` and the new `.asc` together.

Reviewers should confirm the new fingerprint matches what gmplib publishes
before merging.
