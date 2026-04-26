// Encodes a parsed FRACTRAN program + initial state into the whitespace-
// separated wire format consumed by Fractran.Runtime.JsBridge.fractranRunStr.

import { factorize } from './factor.ts';
import { parse, type ParseResult } from './parser.gen.js';

function encodeRegMap(factors: Array<[bigint, bigint]>): string {
  const parts: string[] = [factors.length.toString()];
  for (const [p, e] of factors) {
    parts.push(p.toString(), e.toString());
  }
  return parts.join(' ');
}

function parseProgram(src: string): Array<[bigint, bigint]> {
  const result: ParseResult = parse(src, { startRule: 'ProgFracs' });
  if (!Array.isArray(result)) {
    throw new Error('expected program (fraction list)');
  }
  return result;
}

function parseInputToFactors(src: string): Array<[bigint, bigint]> {
  const result: ParseResult = parse(src, { startRule: 'ProgInput' });
  if (Array.isArray(result)) {
    throw new Error('unexpected fraction list in input field');
  }
  if (result.kind === 'pairs') return result.pairs;
  return factorize(result.value);
}

export interface BuildWireOptions {
  cyclen: bigint;
  programSrc: string;
  inputSrc: string;
}

export function buildWireInput(opts: BuildWireOptions): string {
  const fractions = parseProgram(opts.programSrc);
  const init = parseInputToFactors(opts.inputSrc);

  const tokens: string[] = [
    opts.cyclen.toString(),
    fractions.length.toString(),
  ];
  for (const [num, den] of fractions) {
    tokens.push(encodeRegMap(factorize(num)));
    tokens.push(encodeRegMap(factorize(den)));
  }
  tokens.push(encodeRegMap(init));
  return tokens.join(' ');
}
