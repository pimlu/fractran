// Trial division factorizer using a precomputed small-prime table.
// Sufficient for the small denominators / numerators that appear in typical
// FRACTRAN programs. For huge initial register values, callers should use
// the [prime, exponent] pair-list syntax instead.

const PRIME_LIMIT = 10_000;

const SMALL_PRIMES: bigint[] = (() => {
  const sieve = new Array<boolean>(PRIME_LIMIT + 1).fill(true);
  sieve[0] = false;
  sieve[1] = false;
  for (let i = 2; i * i <= PRIME_LIMIT; i++) {
    if (!sieve[i]) continue;
    for (let j = i * i; j <= PRIME_LIMIT; j += i) sieve[j] = false;
  }
  const out: bigint[] = [];
  for (let i = 2; i <= PRIME_LIMIT; i++) if (sieve[i]) out.push(BigInt(i));
  return out;
})();

const PRIME_LIMIT_BIG = BigInt(PRIME_LIMIT);
const PRIME_LIMIT_SQ = PRIME_LIMIT_BIG * PRIME_LIMIT_BIG;

export function factorize(n: bigint): Array<[bigint, bigint]> {
  if (n <= 0n) throw new Error(`factorize requires n > 0 (got ${n})`);
  const factors: Array<[bigint, bigint]> = [];
  let m = n;
  for (const p of SMALL_PRIMES) {
    if (m === 1n) break;
    if (p * p > m) break;
    if (m % p !== 0n) continue;
    let e = 0n;
    while (m % p === 0n) {
      m /= p;
      e++;
    }
    factors.push([p, e]);
  }
  if (m > 1n) {
    if (m > PRIME_LIMIT_SQ) {
      throw new Error(
        `couldn't factorize ${n}: residue ${m} exceeds small-prime table; ` +
          `use [prime, exponent] pair syntax for register init`,
      );
    }
    // m is prime: it has no factor ≤ PRIME_LIMIT and m ≤ PRIME_LIMIT^2.
    factors.push([m, 1n]);
  }
  return factors;
}
