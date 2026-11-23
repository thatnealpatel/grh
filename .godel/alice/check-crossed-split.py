"""Check the split rule on complete residue squares, not just on actual splits."""

from fractions import Fraction
from math import gcd, prod


def admitted_count(T):
    left = T
    density = Fraction(1, T)
    for p in range(2, T + 1):
        t = 0
        while left % p == 0:
            left //= p
            t += 1
        if t:
            unit = Fraction(p - 1, p)
            density *= 2 * unit + (t - 1) * unit**2
    return density * T**2


def check(T):
    # An algebraic fixture, not a constructed smooth endpoint. Both u_i
    # satisfy the row congruences mod d and run over all residues mod T.
    d, q, c, F1, F2, f = 101, 1009, 13, 7, 11, 3
    factors = [(h, T // h) for h in range(1, T + 1) if T % h == 0]

    def lifts(F):
        A = F * T * c
        r = A * pow(q, -1, d) % d
        for i in range(T):
            u = r + d * (i - T // 2)
            w, rem = divmod(A - q * u, d)
            assert rem == 0 and gcd(T, w) == gcd(T, u)
            yield u

    us, vs = list(lifts(F1 * f)), list(lifts(F2))
    count = 0
    for u in us:
        for v in vs:
            splits = [(h, k) for h, k in factors
                      if u % h == v % k == 0
                      and gcd(k, u // h) == gcd(h, v // k) == 1]
            predicted = (gcd(T, u), gcd(T, v))
            assert splits == ([predicted] if prod(predicted) == T else [])
            count += len(splits)
    assert count == admitted_count(T)
    return count


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without -O to check assertions.')
    trials = range(1, 97)
    admitted = sum(check(T) for T in trials)
    print(f'{admitted} admitted of {sum(T**2 for T in trials)} residue pairs')
