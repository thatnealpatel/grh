"""Check delayed output-divisor tests on a finite arithmetic box, not a prefix graph."""
from math import gcd, prod

assert __debug__
d, Z, q = 12, 24, 101
x1, x2 = 11, 13


def factors(n):
    out = []
    for p in (2, 3, 5, 7):
        while n % p == 0:
            out.append(p)
            n //= p
    return out


full = [a for a in range(36, 7 * 36 + 1) if prod(factors(a)) == a]


def witnesses(R, c, v1, v2):
    n1, n2 = c*x1 - q*R*v1, c*x2 - q*R*v2
    if min(n1, n2) <= 0 or n1 % d or n2 % d:
        return set()
    return {(R, c, a, b) for a in full if (n1//d) % a == 0
            for b in full if (n2//d) % b == 0 and gcd(a, b) == 1}


def lift(B, m, D):
    # Last convergent of B/m through denominator 2D.
    n, s = B, m
    k0, k, r0, r = 0, 1, 1, 0
    while s:
        u, t = divmod(n, s)
        if r0 + u*r > 2*D:
            break
        k0, k, r0, r = k, k0 + u*k, r, r0 + u*r
        n, s = s, t
    return r, B*r - m*k


total = large_R = shares_d = 0
for D in (1, 2, 4):
    box = {(R, c) for R in range(D, 2*D) for c in range(1, Z+1)
           if gcd(R, c) == gcd(c, d) == 1}
    seeds = set()
    for a in full:
        f = 1
        for p in factors(a):
            f *= p
            if d*f > 4*D*Z:
                break
        assert d*f > 4*D*Z and a % f == 0
        seeds.add(f)
    for v1 in range(-199, 8):
        if gcd(v1, d*x1) != 1:
            continue
        # Recovery does not use v2. Some candidates will have no witness.
        candidates = {lift(q*v1*pow(x1, -1, d*f) % (d*f), d*f, D) for f in seeds} & box
        for v2 in range(-199, 8):
            if gcd(v2, d*x2*v1) != 1 or (v1*x2 - v2*x1) % d:
                continue
            direct = set().union(*(witnesses(R, c, v1, v2) for R, c in box))
            delayed = set().union(*(witnesses(R, c, v1, v2) for R, c in candidates))
            assert direct == delayed
            total += len(direct)
            large_R += sum(R > 1 for R, c, a, b in direct)
            shares_d += sum(gcd(a, d) > 1 for R, c, a, b in direct)

# Slots separately pass at different c for the same direction, not jointly.
v1, v2, R = -193, -179, 1
one = {c for c in range(1, Z+1) if (c*x1 - q*R*v1) % (d*40) == 0}
two = {c for c in range(1, Z+1) if (c*x2 - q*R*v2) % (d*63) == 0}
assert one == {17} and two == {5} and not (one & two)
assert (total, large_R, shares_d) == (114, 26, 81)
print('Identical witness sets: 114 tuples, 26 at R>1, 81 with gcd(a,d)>1. Disjoint marginal lifts confirmed.')
