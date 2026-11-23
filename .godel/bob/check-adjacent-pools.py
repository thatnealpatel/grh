"""Certificate for adjacent-signed-pools.md. Python 3, no dependencies."""
from fractions import Fraction as F
from itertools import combinations
from math import factorial, isqrt, prod

q, d, t0 = 100000007, 6, 126191
assert t0**5 < 32*q**3 < (t0+1)**5
P = {61,677,821,1063,131,191,251,367,307,613,733,1013,433,503,557,877}
Q = (P - {61}) | {947}
pi0 = F(314159, 100000)


def prime(p):
    return p > 1 and all(p % k for k in range(2, isqrt(p)+1))


def block(plus, u, v):
    # u/v is the ratio for this orientation. Test EACH designated positive.
    m = 0
    for p in plus:
        den = v*(p+d)-u*p
        m += den > 0 and 2*abs(d*u*p-p*den) < den
        assert den <= 0 or 2*abs(d*u*p-p*den) != den
    h = F(u-v, v)
    assert abs(h)*(t0+1) < 8
    a = t0*(h-h*h/2)
    return a, max(0, 1-abs(a)/(2*pi0)), m


def cosine(z):
    # Truncate at degree 64 at a rounded argument. Error < 0.000051.
    x = F(round(z*10000), 10000)
    assert abs(x) < 14 and F(14**65, factorial(65)) < F(1, 10**8)
    return sum((-1)**i*x**(2*i)/factorial(2*i) for i in range(33))


def certify(pool):
    S = sorted(pool)
    assert min(y-x for x, y in zip(S, S[1:])) >= 50
    assert all(prime(p) and prime(p+d) for p in S)
    nd = {s: (prod(p+d for p in s), prod(s)) for s in combinations(S, 4)}

    def candidate(A, B):
        na, da = nd[A]; nb, db = nd[B]
        u, v = na*db, da*nb
        if 19000*abs(u-v) <= min(u, v):
            return [block(A, u, v), block(B, v, u)]

    count = err = total = 0
    for A in nd:
        if S[0] not in A:
            continue
        for B in combinations(sorted(pool.difference(A)), 4):
            one = candidate(A, B)
            if not one:
                continue
            rest = sorted(pool.difference(A, B))
            for C in combinations(rest, 4):
                if rest[0] not in C:
                    continue
                E = tuple(sorted(set(rest).difference(C)))
                two = candidate(C, E)
                if not two:
                    continue
                count += 1
                for a, T, i in one:
                    for b, U, j in two:
                        total += i*j*T*U*cosine(a-b)
                        err += F(i*j, 5000)
    return count, total-err, total+err


assert prime(q)
for pool, expected, lower, upper in [(P, 1, 59, 60), (Q, 7, -15, -14)]:
    count, lo, hi = certify(pool)
    assert count == expected and lower < lo <= hi < upper
    print(f'{count} unordered split(s) passing the integer filter; certified total in ({lower}, {upper})')
