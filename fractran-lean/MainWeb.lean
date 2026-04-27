import Fractran.Runtime.JsBridge

/-!
# Web build entry point

The browser worker calls the C wrapper (`wasm-build/bridge.cpp`) around
`fractran_run_lean : String → String → String → String` (defined in
`Fractran.Runtime.JsBridge`), passing raw text for cyclen / program / state.
Lean does the parsing via `Fractran.Parse` and the running via
`Runner.cycleRunUntilHalt`. `main` exists only so the worker can call
`Module.callMain([])` once on startup to initialize the Lean runtime — it
returns immediately and prints nothing.

Compare with `MainRuntime.lean`, which runs a hardcoded Hamming demo for
node-side sanity checking.
-/

def main : IO Unit := pure ()
