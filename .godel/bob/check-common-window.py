#!/usr/bin/env python3
"""Finite joint-separation counterexample to a common sharp window. No -O."""

from bisect import bisect_left
from fractions import Fraction
from functools import cache
from itertools import combinations
from math import prod
from pathlib import Path
from runpy import run_path


def main():
    b = run_path(str(Path(__file__).with_name('check-complete-shift.py')))
    I, one, tau = b['I'], b['ONE'], b['TAU']
    q, d = 1532161, 24
    t5 = 32*q**3
    t = I(2)*(I(3)*I(q).log()/I(5)).exp()
    logxroot = I(3)*(t/I(2)).log()
    X = logxroot*logxroot
    D = X.log()
    L, gamma = t.log()/D, one/I(1000)
    h = (I(2)+gamma)*L
    assert b['prime'](q) and 2 < h.lo <= h.hi < 3 and d < (I(5)*D).lo
    assert 657 < X.lo <= X.hi < 658 and (I(-8).exp()*X).hi < 1
    assert 42 < (D*D).lo <= (D*D).hi < 43
    assert (D*gamma/(I(16)*(I(2)+gamma))).exp().hi < 2
    assert ((one+gamma)*L).hi < 6 and ((I(3)+gamma)*L).lo > 0
    # Joint gap >=43 makes every slot private and the old near count zero.
    starts = [p for p in range(2, 658-d) if b['prime'](p) and b['prime'](p+d)]
    weights = {p: (X/I(p)).log()*I(p).log()*I(p+d).log()/X for p in starts}
    assert len(starts) == 56 and sum(weights.values(), I(0)).lo > 2
    after = [bisect_left(starts, p+43) for p in starts]

    def pools(i, k, prefix):
        if not k:
            yield prefix
            return
        for j in range(i, len(starts)):
            if starts[j]+43*(k-1) > starts[-1]:
                break
            yield from pools(after[j], k-1, prefix+(starts[j],))

    @cache
    def phases(block):
        result = []
        for plus in combinations(block, 3):
            minus = tuple(p for p in block if p not in plus)
            u = prod(p+d for p in plus)*prod(minus)
            v = prod(p+d for p in minus)*prod(plus)
            if not b['fits_y'](u-v, v, t5):
                continue
            g = b['rounded_count'](plus, u, v, d)
            if not g:
                continue
            # Rounding to a start implies x in [X_min/2,2X] here.
            e = b['rational'](Fraction(u-v, v))
            a = t*e*(one-e/I(2))
            if abs(a).lo > tau.hi:
                continue  # in no translated window, including its endpoints
            assert abs(a).hi < tau.lo
            result.append((a, g))
        return result

    H = common = I(0)
    total = survivors = disjoint_windows = far_angles = 0
    for pool in pools(0, 12, ()):
        total += 1
        if not b['possible_min_block'](pool, d, 3, t5)[1]:
            continue
        survivors += 1
        for five in combinations(pool[1:], 5):
            left = (pool[0],)+five
            for a, g in phases(left):
                for c, j in phases(tuple(p for p in pool if p not in left)):
                    # Both orders; per designated label 2!3! permutations.
                    w = I(2*12**2*g*j)*prod((weights[p] for p in pool), start=one)
                    delta = a-c
                    cosine = b['trig'](delta, 0)
                    H += w*(one-abs(a)/tau)*(one-abs(c)/tau)*cosine
                    # Measure of (a,a+tau] intersect (c,c+tau] in [0,tau],
                    # divided by tau. Endpoints do not affect this average.
                    span = (abs(a)+abs(c)+abs(delta))/I(2)  # diameter of {0,a,c}
                    common += w*(one-span/tau).positive_part()*cosine
                    if abs(delta).lo > tau.hi:
                        disjoint_windows += 1  # cannot both be in a window of length tau
                    else:
                        assert (tau/I(4)).hi < abs(delta).lo <= abs(delta).hi < (tau/I(2)).lo
                        far_angles += 1  # never in the added arc for v <= pi/2
    scale = X/D/I(16**6)/t
    ratio = H/(scale*scale)
    assert (total, survivors) == (39369, 66)
    assert (disjoint_windows, far_angles) == (2, 2)
    assert 53 < ratio.lo <= ratio.hi < 54
    common_ratio = common/(scale*scale)
    assert -22 < common_ratio.lo <= common_ratio.hi < -21
    print(f'Common-location mean cosine / S in {common_ratio}')
    print(f'{total} pools, {survivors} survive the unsigned bound; H_r/S in {ratio}')
    print(f'{disjoint_windows} rows cannot share a window; {far_angles} cannot enter the added arc.')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run without -O to check certificate assertions')
    main()
