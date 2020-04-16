import memoize from "memoize-one";

import peg from './parser.pegjs';

export default function makeParser(startRule) {
  return memoize((text) => {
    let parsed = null, error = null;
    try {
      parsed = peg.parse(text, {startRule});
    } catch(e) {
      error = e;
    }
    return {parsed, error};
  });
}

makeParser.initSt = {
  parsed: null,
  error: null
};
