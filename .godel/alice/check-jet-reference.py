#!/usr/bin/env python3
"""Check the reference-disk thresholds from the cubic quotient data."""

from fractions import Fraction as Q
from math import comb
from pathlib import Path
from runpy import run_path

cubic_exponent = run_path(str(Path(__file__).with_name('check-jet-axis-lcm.py')))['cubic_exponent']


def check():
    m, r = 10000, 1200
    V, row, b, K = cubic_exponent(m, r)
    S = comb(m + 2, 3) - comb(m - 1, 3) - comb(r + 1, 3) + comb(r, 3)
    L = comb(r + 1, 2) * (m - r + 1) - comb(r, 2) * (m - r - 1)
    Z = 2 * S - L - 3 * b
    assert Z == 138734399 and 0 < Z < 2 * V
    assert Q('.33453') < Q(Z, V) < Q('.33454')
    assert Q('2.81605006') < Q(Z, b) < Q('2.81605007')
    tau = Q('.0207')
    one = K - tau * V
    two = K - tau * (2 * V + row)
    assert one / V == Q(759153473, 33444000000)
    assert two / V == Q(284262863, 1036764000000)
    assert Q('.0669') < Q('.1348') - one / Z < Q('.0670')
    assert Q('.000819') < two / Z < Q('.000820')
    assert Q('.860') + 2 * (Q('.1276') + tau / 2) == Q('1.1359')


if __name__ == '__main__':
    check()
    print('reference-disk thresholds verified')
