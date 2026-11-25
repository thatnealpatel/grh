#!/usr/bin/env python3
"""Replay the local gap-mask indices and the resulting count exponents."""

from fractions import Fraction as Q
from itertools import product
from math import gcd


def val(n, p, cap):
    """Valuation truncated at cap, including when n is zero."""
    i = 0
    while i < cap and n % p == 0:
        i += 1
        n //= p
    return i


def check_fresh():
    cases = 0
    positive_direction_credit = set()
    depth = 3
    for p in (2, 3, 5):
        mod = p**depth
        pairs = [(x, y, (x, y, x - y)) for x, y in product(range(mod), repeat=2)]
        for r in range(depth + 1):
            for delta in range(depth + 1 - r):
                for direction in (range(3) if delta else (0,)):
                    powers = [p**r] * 3
                    powers[direction] *= p**delta
                    mask = [(x, y) for x, y, gaps in pairs
                            if all(gap % power == 0 for gap, power in zip(gaps, powers))]
                    assert len(mask) * p**(2*r + delta) == mod**2
                    for alpha, b, c in product(range(1, depth + 1), range(-2, 3), range(-2, 3)):
                        if gcd(p, b, c) != 1:
                            continue
                        a = p**alpha
                        image = {(b*x + c*y) % a for x, y in mask}
                        intersection = sum((b*x + c*y) % a == 0 for x, y in mask)
                        s = val((c, b, b + c)[direction], p, delta)
                        j = min(alpha, r + s)
                        i = 2*r + delta - j
                        assert len(image) * p**j == a
                        assert intersection * p**i == mod**2 // a
                        assert i >= r and j - 2*i <= min(alpha, s) - r
                        if j - 2*i > 0:
                            positive_direction_credit.add(direction)
                        cases += 1
    assert positive_direction_credit == {0, 1, 2}
    print(f'{cases} fresh-prime index cases; positive credit in all three directions')


def check_denominators():
    cases = 0
    q, F = 7, 11
    for p, u, alpha in product((2, 3), (1, 2), (1, 2)):
        a, d = p**alpha, p**u
        mod = a*d
        for v, b, c in product(range(u + 1), range(-2, 3), range(-2, 3)):
            if gcd(p, b, c) != 1:
                continue
            e = G = p**v
            plane = []
            for x, z in product(range(mod), repeat=2):
                y = x - G*z
                m, rem = divmod(-b*x - c*y, a)
                if rem == 0 and (F*m - q*x) % d == (F*m - q*y) % e == 0:
                    plane.append((x, z, y))
            if not any(x % p for x, _, _ in plane):
                continue
            N = q*a + F*(b + c)
            assert c % p and N % e == 0
            slope_mod = mod // e
            slope = (N // e) * pow(F*c, -1, slope_mod) % slope_mod
            assert len(plane) * slope_mod == mod**2
            assert all((z - slope*x) % slope_mod == 0 for x, z, _ in plane)
            for direction in ((1,) if v else (1, 2)):
                for t in range(1, alpha + u + 1):
                    masked = [row for row in plane if row[direction] % p**t == 0]
                    if not any(x % p for x, _, _ in masked):
                        continue
                    phi_slope = slope if direction == 1 else 1 - G*slope
                    L_p = u + alpha - v
                    assert phi_slope % p**min(t, L_p) == 0
                    assert len(masked) * p**max(0, t - L_p) == len(plane)
                    cases += 1
    assert cases > 0
    print(f'{cases} occupied denominator-prime mask-index cases')


def check_prices():
    base = (Q('1.720') + Q('.390')) / 2
    outer = Q('.470') - Q('.160')
    gate = Q('.011')
    assert base + outer / 4 == Q('1.1325')
    assert base + (outer + gate) / 4 == Q('1.13525') < Q('1.1354')
    print('count exponents: no new direction 1.1325; gated interior 1.13525')


if __name__ == '__main__':
    check_fresh()
    check_denominators()
    check_prices()
