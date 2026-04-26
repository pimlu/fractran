import Fractran.Runtime.JsBridge

/-!
# Web build entry point

The browser worker calls the C wrapper around `fractran_run_lean` (defined in
`Fractran.Runtime.JsBridge`). `main` exists only so that the worker can call
`Module.callMain([])` once on startup to initialize the Lean runtime — it
returns immediately and prints nothing.

Compare with `MainRuntime.lean`, which runs a hardcoded Hamming demo for
node-side sanity checking.
-/

def main : IO Unit := pure ()
