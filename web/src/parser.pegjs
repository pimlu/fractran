{
  const BN = require('bn.js');
  window.BN = BN;
}

ProgInput = Calc
  / head:Pair tail:(_ "," Pair)* _ {
    return `[${[head, ...tail.map(e => e[2])]}]`;
  }

ProgFracs = W head:Frac _ tail:(((_ ","? (_ "\n" _)*)/",") Frac)* W {
  return `[${[head, ...tail.map(e => e[1])]}]`;
}

Frac = n:Calc "%" d:Calc {
  return n + '%' + d;
}

Pair
  = _ "[" f:Integer _ "," v:Calc "]" {
    return `(${f},${v})`;
  }

Calc
  = _ expr:Expression _ {
      return expr.toString();
    }

Expression
  = head:Term tail:(_ ("+" / "-") _ Term)* {
      return tail.reduce(function(res, el) {
        if (el[1] === "+") { return res.iadd(el[3]); }
        if (el[1] === "-") { return res.isub(el[3]); }
      }, head);
    }

Term
  = head:Pow tail:(_ ("*" / "/") _ Pow)* {
      return tail.reduce(function(res, el) {
        if (el[1] === "*") { return res.imul(el[3]); }
        if (el[1] === "/") { return res.div(el[3]); }
      }, head);
    }

Pow
  = head:Factor tail:(_ "^" _ Factor)* {
      return head.pow(tail.reduceRight(function(res, el) {
        return el[3].pow(res);
      }, new BN(1)));
  }

Factor
  = "(" _ expr:Expression _ ")" { return expr; }
  / Integer

Integer "integer"
  =  _ bin:([01]+) "b" { return new BN(bin.join(''), 2)}
  / _ hex:([0-9a-fA-F]+) "h" { return new BN(hex.join(''), 16)}
  / _ [0-9]+ { return new BN(text()); }


_ "spaces"
  = [ \t]*

W "whitespace"
  = [ \t\r\n]*