#!/usr/bin/env python3
"""Replay the prices and residual tests in effective-gap-normals.md."""

from fractions import Fraction as Q
from math import gcd, lcm


def check_prices():
    v, h_bound = Q('1.720'), Q('.390')
    base = (v + h_bound) / 2
    t0, t1 = Q('.160'), Q('.470')
    outer = t1 - t0
    gate = Q('.011')
    cutoff = outer + gate
    cheap = cutoff / 2
    assert base == Q('1.055')
    assert outer == Q('.310')
    assert base + outer / 4 == Q('1.1325')
    assert cutoff == Q('.321') and cheap == Q('.1605')
    assert base + cheap / 2 == Q('1.13525') < Q('1.1354')
    residual = 2 * h_bound - cutoff - cheap
    assert residual == Q('.2985')
    print(f'empty={base + outer / 4}, gated={base + cutoff / 4}, '
          f'residual cap={residual}')

    # An exponent tuple satisfies the necessary inequalities simultaneously.
    # This does NOT assert that a corresponding plane or triple exists.
    gcd_de, lam_over_gcd, index, h = map(Q, ('.050', '.120', '.020', '.010'))
    xi, masked_occ, mask_over_gcd, overlap = map(
        Q, ('.322', '.211', '.280', '.130'))
    lam = gcd_de + lam_over_gcd
    a = h + xi + 2 * index
    c_over_d = index + lam + a - gcd_de - mask_over_gcd
    assert xi > cutoff and masked_occ > gcd_de + cheap
    assert lam + masked_occ + index + a < 2 * h_bound
    assert c_over_d < outer - 3 * gcd_de / 2
    assert h + lam_over_gcd + 3 * index + 2 * gcd_de < residual
    assert mask_over_gcd - index <= h + lam_over_gcd + overlap
    assert gate + 2 * index + 3 * gcd_de / 2 < overlap
    assert xi < outer + overlap - 2 * index - 3 * gcd_de / 2
    print('necessary residual inequalities are compatible as exponents')


def check_normal_indices():
    q, F = 101, 103
    count = 0
    for d in range(2, 29):
        for e in range(2, 29):
            G = gcd(d, e)
            rx = F * pow(q, -1, d) % d
            ry = F * pow(q, -1, e) % e
            # CRT basis: (1,rx,ry), (0,d,0), (0,0,e).
            for a in range(1, 5):
                for b in range(-3, 4):
                    for c in range(-3, 4):
                        if gcd(a, b, c) != 1:
                            continue
                        g = gcd(a + b * rx + c * ry, b * d, c * e)
                        lam = d * e // g
                        A, B = g // gcd(g, e), g // gcd(g, d)
                        assert lcm(d, e) % g == lam % G == 0
                        assert (q*a + F*(b+c)) % g == 0
                        assert c % A == b % B == 0
                        assert gcd(A, B) == gcd(a, A * B) == 1
                        assert A * B == g // gcd(g, G)
                        count += 1
    assert count == 123201
    print(f'{count} finite primitive-normal index checks')


if __name__ == '__main__':
    check_prices()
    check_normal_indices()
