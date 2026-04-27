// Demo programs for the web UI. Each pairs a FRACTRAN program (commas or
// newlines as fraction separators) with an initial state expression.
//
// Fraction separator is `/` (the parser also accepts `%` for backwards
// compatibility). Initial state is a factored prime-power expression like
// `2^7 * 3^4`; the parser also still accepts the older `[prime, exp]` pair
// list form.

export interface Example {
  name: string;
  program: string;
  input: string;
}

const hamming = `3*11 / 2^2*5
5 / 11
13 / 2*5
1 / 5
2 / 3
2*5 / 7
7 / 2`;

const fibFr = `17 / 65
133 / 34
17 / 19
23 / 17
2233 / 69
23 / 29
31 / 23
74 / 341
31 / 37
41 / 31
129 / 287
41 / 43
13 / 41
1 / 13
1 / 3`;

const fibIn = (n: number) => `2 * 3 * 13 * 5^(${n}-1)`;

export const examples: Example[] = [
  {
    name: 'Hamming weight (small)',
    program: hamming,
    // popcount(0b1100001) = popcount(97) = 3
    input: '2^1100001b',
  },
  {
    name: 'Hamming weight (large)',
    program: hamming,
    // popcount(2^256 - 1) = 256
    input: '2^(2^256-1)',
  },
  {
    name: 'Add two numbers',
    program: '5 / 2\n5 / 3',
    input: '2^123 * 3^111',
  },
  {
    name: 'Multiply two numbers',
    program: '455 / 33\n11 / 13\n1 / 11\n3 / 7\n11 / 2\n1 / 3',
    input: '2^500 * 3^600',
  },
  {
    name: 'Infinite loop',
    program: '2 / 3\n3 / 2',
    input: '2',
  },
  {
    name: 'Calculate 7th fibonacci',
    program: fibFr,
    input: fibIn(7),
  },
  {
    name: 'Calculate 99th fibonacci',
    program: fibFr,
    input: fibIn(99),
  },
];

export const DEFAULT_EXAMPLE = 'Hamming weight (large)';
