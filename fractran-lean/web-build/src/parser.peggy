// FRACTRAN program + input grammar.
//
// Two start rules:
//   ProgFracs - parses a list of fractions (commas and/or newlines as separators).
//               Returns Array<[bigint, bigint]> ([numerator, denominator] pairs).
//   ProgInput - parses initial state. Either a single integer expression
//               (which the caller will factorize), or a list of [prime, value]
//               pairs (which the caller uses directly as register init).
//               Returns { kind: 'value', value: bigint }
//                    or { kind: 'pairs', pairs: Array<[bigint, bigint]> }.
//
// All arithmetic uses native BigInt. Only integer division is allowed; non-
// integer division throws.

ProgFracs
  = _ head:Frac tail:(FracSep Frac)* _ { return [head, ...tail.map(t => t[1])]; }

// Fractions are separated by ',' and/or one or more newlines.
FracSep
  = _ "," _ ([\r\n] _)* { return null; }
  / _ [\r\n] _ ([\r\n] _)* { return null; }

Frac
  = n:Calc "%" d:Calc {
      if (d <= 0n) throw new Error('fraction denominator must be positive');
      if (n <= 0n) throw new Error('fraction numerator must be positive');
      return [n, d];
    }

ProgInput
  = pairs:PairList { return { kind: 'pairs', pairs }; }
  / v:Calc { return { kind: 'value', value: v }; }

PairList
  = _ head:Pair tail:(_ "," _ Pair)* _ { return [head, ...tail.map(t => t[3])]; }

Pair
  = "[" _ p:Calc _ "," _ v:Calc _ "]" { return [p, v]; }

Calc
  = _ e:Expression _ { return e; }

Expression
  = head:Term tail:(_ ("+" / "-") _ Term)* {
      return tail.reduce(
        (acc, t) => (t[1] === '+' ? acc + t[3] : acc - t[3]),
        head,
      );
    }

Term
  = head:Pow tail:(_ ("*" / "/") _ Pow)* {
      return tail.reduce((acc, t) => {
        if (t[1] === '*') return acc * t[3];
        if (t[3] === 0n) throw new Error('division by zero');
        if (acc % t[3] !== 0n) throw new Error('non-integer division');
        return acc / t[3];
      }, head);
    }

// Right-associative: 2^3^4 = 2^(3^4).
Pow
  = head:Factor tail:(_ "^" _ Factor)* {
      if (tail.length === 0) return head;
      const exp = tail.reduceRight((res, el) => el[3] ** res, 1n);
      return head ** exp;
    }

Factor
  = "(" _ e:Expression _ ")" { return e; }
  / Integer

Integer "integer"
  = bin:[01]+ "b" { return BigInt('0b' + bin.join('')); }
  / hex:[0-9a-fA-F]+ "h" { return BigInt('0x' + hex.join('')); }
  / num:[0-9]+ { return BigInt(num.join('')); }

_ "spaces"
  = [ \t]*
