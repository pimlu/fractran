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
    if(err.message && (err.message.includes('too much recursion') ||
      err.message.includes('call stack size exceeded'))) {
      err = {
        message: 'Haste stack overflow\'d while running our Haskell code. :( '+
         'This is a known issue with Haste, if you have large inputs run the '+
         'Haskell code natively, it\'ll be faster and not break.'
      };
    }
    postMessage({
      good: false,
      err: err.message || ''+err
    });
  }
  close();
}