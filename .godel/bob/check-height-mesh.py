#!/usr/bin/env python3
"""Check a safe centered sampling mesh and an alias on the one-copy fixture."""
from bisect import bisect_left, bisect_right
from fractions import Fraction
from itertools import combinations
from math import factorial, prod
from pathlib import Path
from runpy import run_path


def main():
    m = run_path(str(Path(__file__).with_name('check-complete-shift.py')))
    m['certified_geometry']()
    I, t, twopi = m['I'], m['T'], m['TAU']
    d, h = 26, m['HPLUS']
    _, _, starts, _ = m['plan'](d)
    w = m['weights'](starts, d)
    edge = {p: Fraction(p+d, p) for p in starts}
    # Mesh 2*pi/log(base) locks the phase of the least start.
    base = edge[starts[0]]
    omega = m['rational'](base).log()
    bits = {p: 1 << j for j, p in enumerate(starts)}
    vals = []
    for a in combinations(starts, h):
        if any(y-x < 50 for x, y in zip(a, a[1:])):
            continue
        mask = sum(bits[p] for p in a)
        vals.append((prod(edge[p] for p in a), mask, a))
    vals.sort()
    ratios = [r for r, _, _ in vals]
    assert len(ratios) == 80331 and ratios[0] < ratios[-1]
    # Bounds every cross-quartet difference even before the conflict test.
    radius = m['rational'](ratios[-1]/ratios[0]).log()
    assert (radius + twopi/t).hi < (I(2)*omega).lo
    # If |t log(x)| < 2*pi, then |log(x)| < 7/126191 and
    # 1/cap <= x <= cap by exp(u) <= 1/(1-u) for 0 <= u < 1.
    assert twopi.hi < 7 and (twopi/t).hi < omega.lo
    cap = Fraction(m['T0'], m['T0']-7)
    near = {p: sum(1 << j for j, q in enumerate(starts) if abs(p-q) < 50)
            for p in starts}
    weights = {}

    def weight(a):
        if a not in weights:
            weights[a] = prod((w[p] for p in a), start=I(1))
        return weights[a]

    total = I(0)
    count = 0
    for small, _, a in vals:
        banned = near[a[0]] | near[a[1]] | near[a[2]] | near[a[3]]
        center = small*base
        for i in range(bisect_left(ratios, center/cap), bisect_right(ratios, center*cap)):
            large, mask, b = vals[i]
            if banned & mask:
                continue
            z = t*m['rational'](large/center).log()
            hat = (I(1)-abs(z)/twopi).positive_part()
            if hat.hi == 0:
                continue
            assert hat.lo > 0  # No ambiguous membership on this fixture.
            count += 1
            total += hat*m['trig'](z, True)*weight(a)*weight(b)
    total *= I(factorial(h)**2)
    assert count == 8387
    v = total*I(10**12)
    assert -2723 < v.lo <= v.hi < -2722
    print('First alias: 8387 separated splits; -2723 < 10^12 Im(C) < -2722')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run without -O for certificate checks')
    main()
