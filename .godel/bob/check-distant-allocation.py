#!/usr/bin/env python3
"""Certify exclusive allocation between net signed pools at q=100000007, d=26."""

from fractions import Fraction
from pathlib import Path
from runpy import run_path


def unused(supply, capacity, neighbors):
    """Maximum weighted Hall deficiency over all subsets of the supply side."""
    best = Fraction(0)
    unions = [0]
    weights = [Fraction(0)]
    sums = {0: Fraction(0)}
    for subset in range(1, 1 << len(supply)):
        bit = subset & -subset
        i = bit.bit_length()-1
        prior = subset ^ bit
        union = unions[prior] | neighbors[i]
        demand = weights[prior] + supply[i]
        if union not in sums:
            sums[union] = sum(c for j, c in enumerate(capacity) if union & (1 << j))
        unions.append(union)
        weights.append(demand)
        best = max(best, demand - sums[union])
    return best


def main():
    b = run_path(str(Path(__file__).with_name('check-complete-shift.py')))
    b['certified_geometry']()
    count, d, starts, after = b['plan'](26)
    pools = b['family'](starts, after, count)
    rows = [p for p in pools if b['possible_min_block'](p, d)[1]]
    assert count == 28592 and len(rows) == 720
    pos, neg = [], []
    for row, (counts, total) in zip(rows, b['evaluate'](starts, rows, d, b['weights'](starts, d)), strict=True):
        # Work in exact rational units of 10^-21 from the outward endpoints.
        lo, hi = (Fraction(x)*10**21 for x in (total.lo, total.hi))
        if lo > 0:
            pos.append((set(row), lo, hi))
        elif hi < 0:
            neg.append((set(row), -hi, -lo))
        else:
            assert counts[2] == 0 and lo == hi == 0
    assert len(pos) == 21 and len(neg) == 11
    plo, phi = [[w[i] for w in pos] for i in (1, 2)]
    nlo, nhi = [[w[i] for w in neg] for i in (1, 2)]
    assert sum(plo) > sum(nhi)
    # k=8: pay all negative masses, even for the least favorable endpoints.
    # k=9..12: integer hundredth-of-a-percent enclosures for usable fraction.
    for k, percent in [(8, 10000), (9, 9133), (10, 5112), (11, 1418), (12, 590), (13, 0)]:
        adj = [sum(1 << j for j, (p, _, _) in enumerate(pos) if len(q-p) >= k) for q, _, _ in neg]
        low = unused(nlo, phi, adj)
        high = unused(nhi, plo, adj)
        if k == 8:
            assert high == 0
            print('k=8: all negative supply usable')
        elif k == 13:
            assert not any(adj)
            print('k=13: no edge')
        else:
            # Deficiency is increasing in supply and decreasing in capacity.
            assert percent < 10000*(1-high/sum(nlo)) <= 10000*(1-low/sum(nhi)) < percent+1
            print(f'k={k}: usable percentage in ({percent/100:.2f}, {(percent+1)/100:.2f})')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run without -O to check certificate assertions')
    main()
