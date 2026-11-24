"""Arithmetic controls for partial scalar classes, not an incidence sampler."""
from collections import Counter
from functools import cache
from itertools import product
from math import gcd

assert __debug__
q, F1, F2 = 101, 5, 7
# F1*p + F2*r = 1. For the lattice F2*n1-F1*n2=d*t,
# (t,l) are integral coordinates even when the modulus meets d.
p, r = 3, -2
assert F1*p + F2*r == 1


def crt(a, u, b, v):
    return (a + u*((b-a)*pow(u, -1, v) % v)) % (u*v)


classes = nonunit = partial = physical = 0
for d, (f1, f2) in product((6, 8, 9, 11, 12), ((2, 3), (4, 9), (7, 5))):
    e = f1*f2
    hist = Counter()
    for t, ell in product(range(-e, 0), range(e)):
        n1, n2 = F1*ell+r*d*t, F2*ell-p*d*t
        k = crt(q*n1*pow(F1, -1, f1), f1, q*n2*pow(F2, -1, f2), f2)
        hist[t % e, k] += 1
        for b in range(1, e+1):
            if e % b:
                continue
            u, v = gcd(b, f1), gcd(b, f2)
            # Reconstruct the physical vector mod b from t mod e, k mod b.
            a1 = F1*k*pow(q, -1, b)
            a2 = F2*k*pow(q, -1, b)
            rho1 = crt(a1, u, a1+d*t*pow(F2, -1, v), v)
            rho2 = crt(a2-d*t*pow(F1, -1, u), u, a2, v)
            assert (rho1, rho2) == (n1 % b, n2 % b)
            c0 = (d*(t % e) - F2*rho1 + F1*rho2)//b
            assert F2*((n1-rho1)//b) - F1*((n2-rho2)//b) == c0 + d*(e//b)*(t//e)
            partial += 1
    assert len(hist) == e*e and set(hist.values()) == {1}
    classes += len(hist)
    nonunit += (gcd(d, e) > 1)*len(hist)
    # Forgetting t: Multiplication by e loses the gcd with d.
    d0 = d//gcd(d, e)
    assert sum((F2*a-F1*z) % d0 == 0 for a, z in product(range(d0), repeat=2)) == d0
    for a, z in product(range(-8, 9), repeat=2):
        assert ((e*(F2*a-F1*z)) % d == 0) == ((F2*a-F1*z) % d0 == 0)
        physical += 1
print(f'{classes} full classes ({nonunit} at noncoprime moduli), {partial} partial reconstructions, {physical} difference tests')

# Compare the last gcd test with intersection of the actual divisor keys
# for a small signed row equation. No prefix graph or richness hypothesis.
q, d, F1, F2, Q, X = 11, 7, 3, 5, 3, 5
rows = []
ys = sorted({2**i * 3**j * 5**k for i, j, k in product(range(9), range(6), range(5))
             if 3 <= 2**i * 3**j * 5**k < 500})
for c, h1, h2 in product(range(1, 25), range(1, 6), range(1, 6)):
    if gcd(c, d*q) > 1 or gcd(h1, h2) > 1:
        continue
    def outputs(x):
        return [y for y in ys if gcd(c*x, d*y) == 1 and (c*x-d*y) % q == 0]
    for y1, y2 in product(outputs(F1*h1), outputs(F2*h2)):
        del1 = (c*F1*h1 - d*y1)//q
        del2 = (c*F2*h2 - d*y2)//q
        if del1*del2 == 0 or gcd(del1, del2) != 1:
            continue
        Y2 = y2
        while (g := gcd(y1, Y2)) > 1:
            Y2 //= g
        t = (F1*h1*y2-F2*h2*y1)//q
        keys = {(a, b, t % (a*b), c*h1*h2 % a) for a, b in product(range(Q, X*Q+1), repeat=2)
                if y1 % a == Y2 % b == 0}
        rows.append((y1, Y2, t, h2*del1, keys))
passing = 0
for (y, Y, t, n, keys), (yy, YY, tt, nn, others) in product(rows, repeat=2):
    hit = gcd(y, yy, t-tt, n-nn) >= Q and gcd(Y, YY, t-tt) >= Q
    assert hit == bool(keys & others)
    passing += hit
assert len(rows) < passing < len(rows)**2
print(f'{len(rows)**2} ordered row-pair tests, {passing} with a shared partial key')

# Replay on exactly those ordered pairs, with the first row as reference.
# Wtoy bounds |t| on this grid only. The finite test is integer-only.


@cache
def menu(S):
    cap = X**2 * Q**3
    steps = {1}
    for prime in S:
        for seed in list(steps):
            while seed * prime <= cap:
                seed *= prime
                steps.add(seed)
    return [(e, b) for e in steps for b in steps if e % b == 0 and e*b <= cap]


def supported(n, S):
    assert n > 0
    rest = n
    for prime in S:
        while rest % prime == 0:
            rest //= prime
    return n//rest


Wtoy = max(abs(row[2]) for row in rows)
projected = enlarged = mixed = 0
for (y, Y, t, n, keys), (yy, YY, tt, nn, others) in product(rows, repeat=2):
    S = tuple(p for p in (2, 3, 5) if y*Y % p == 0)
    z, v = tt-t, nn-n
    assert (F2*v-d*z) % F1 == 0
    w = (F2*v-d*z)//F1
    proj = any(z % (a*b) == v % a == w % a == 0 for a, b, _, _ in keys)
    assert not keys & others or proj
    m = gcd(z, v, w)
    hit = z == 0 or abs(z)*Q**3 <= 2*Wtoy*supported(abs(z), S)*supported(m, S)
    assert not proj or hit
    # Independent finite menu: No use of the factorization of the difference.
    assert hit == any(z % e == v % b == w % b == 0 and abs(z)*Q**3 <= 2*Wtoy*e*b
                      for e, b in menu(S))
    projected += proj
    enlarged += hit
    if z and t and tt and hit and not proj and abs(z)*Q**3 > 2*Wtoy*supported(abs(z), S):
        mixed += 1
assert passing < projected < enlarged < len(rows)**2 and mixed > 0
print(f'{projected} in reference-key cosets, {enlarged} in weighted windows, '
      f'{mixed} outside both the cosets and determinant-only windows with both t nonzero')
