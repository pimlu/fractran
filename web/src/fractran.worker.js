import * as rts from "../gen/rts.mjs";
import req from "../gen/Browser.req.mjs";
import wasmPath from '../gen/Browser.wasm';

let wasmModule = WebAssembly.compileStreaming(fetch(wasmPath));

let instance = wasmModule.then(m =>
    rts.newAsteriusInstance(Object.assign(req, {module: m}))
  ).catch(err => console.error(err));

onmessage = function(e) {
  let {data} = e;
  let {input, program, len} = data;
  instance.then(i =>
    i.exports.hsRunDynamic(len, program, input)
  ).then(out => {
    postMessage({
      good: true,
      out
    });
  }).catch(err => {
    postMessage({
      good: false,
      err: 'FRACTRAN engine error, likely it detected an infinite loop in your FRACTRAN code.'
    });
  }).then(close);
}
