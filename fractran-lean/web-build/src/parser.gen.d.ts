// Type declarations for the peggy-generated parser.
// Source grammar: src/parser.peggy. Regenerate via `pnpm parser:build`.

export type ParseResult =
  | Array<[bigint, bigint]>                                    // ProgFracs
  | { kind: 'value'; value: bigint }                           // ProgInput (single value)
  | { kind: 'pairs'; pairs: Array<[bigint, bigint]> };         // ProgInput (pair list)

export interface ParseOptions {
  startRule?: 'ProgFracs' | 'ProgInput';
}

export class SyntaxError extends Error {
  location: {
    start: { offset: number; line: number; column: number };
    end: { offset: number; line: number; column: number };
  };
  expected: unknown;
  found: unknown;
}

export function parse(input: string, options?: ParseOptions): ParseResult;
