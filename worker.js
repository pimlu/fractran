var window = self;
importScripts('fractran.js');

onmessage = function(e) {
  var data = e.data;
  var input = data.input, program = data.program, len = data.len;
  var facd = input[0]==='[';
  var fn;
  if(len) {
    fn = Haste['runCyc'+(facd?'':'F')].bind(Haste, len);
  } else {
    fn = Haste['runReg'+(facd?'':'F')].bind(Haste);
  }
  try {
    postMessage({
      good: true,
      out: fn(program, input)
    });
  } catch(err) {
    postMessage({
      good: false,
      err: err
    });
  }
  close();
}