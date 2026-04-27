// JS / WASM bridge for fractran_run.
//
// JS calls `Module._fractran_run(cyclen_cstr, program_cstr, input_cstr)` via
// ccall. We wrap each C string into a Lean String, invoke the Lean-generated
// `fractran_run_lean`, copy the result out into a malloc'd buffer, and dec_ref
// the Lean object. The caller owns the returned buffer and must
// `Module._free()` it.
#include <lean/lean.h>
#include <emscripten.h>
#include <string.h>
#include <stdlib.h>

extern "C" {

// Defined in Fractran/Runtime/JsBridge.lean (via @[export]).
lean_object* fractran_run_lean(lean_object* cyclen, lean_object* program,
                               lean_object* input);

EMSCRIPTEN_KEEPALIVE
char* fractran_run(const char* cyclen_cstr, const char* program_cstr,
                   const char* input_cstr) {
    // lean_mk_string copies the contents and returns an owned reference.
    // Ownership of each Lean object is transferred to the Lean function;
    // we don't dec_ref them here.
    lean_object* cyclen_lean  = lean_mk_string(cyclen_cstr);
    lean_object* program_lean = lean_mk_string(program_cstr);
    lean_object* input_lean   = lean_mk_string(input_cstr);
    lean_object* result_lean  = fractran_run_lean(cyclen_lean, program_lean,
                                                  input_lean);
    // The pointer aliases the lean object's internal buffer; copy it out
    // so we can release the lean object.
    const char* result_cstr = lean_string_cstr(result_lean);
    size_t len = strlen(result_cstr);
    char* copy = (char*)malloc(len + 1);
    memcpy(copy, result_cstr, len + 1);
    lean_dec(result_lean);
    return copy;
}

}
