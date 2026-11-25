#!/usr/bin/env python3
"""Check the threshold balance for the projected-factor erasure code."""

from fractions import Fraction as Q


C, inputs, p, s = map(Q, ('1.055', '.860', '.22', '.28'))
small, large, target = map(Q, ('1.300', '1.475', '1.1354'))
A = Q(671, 900) * C
old_small = max(A, C - s / (s + 2 * p) * (C - small / 2))
old_large = Q(50989, 54800)
assert old_small == Q('.897500')
assert target - old_small == Q('.237900')


def threshold(height, radius):
    cap = ((p * C / s + C - height / 4 + (C + inputs / p) / 2)
           / (1 + p / s + 1 / (2 * p)))
    m = (C - cap) / s
    b_cross = C - (cap - inputs) / p
    b_no_cross = C - (cap - radius / 2) / p + m
    assert max(A, inputs) < cap < old_large
    assert b_no_cross < b_cross
    # At w >= height/2-b_cross, the upper bound for the positive
    # part uses a strictly positive width deficit at that lower floor.
    assert 0 < height / 2 - b_cross < 2 * C
    assert p * m + max(Q(0), 2 * C - height / 2 + b_cross) / 2 == cap
    return cap


for eta, height, cap, loss, gain, deletion in (
    ('.160', '2.430', '.926088', '.209312', '.028588', '1.135'),
    ('.272', '2.654', '.9122896', '.2231104', '.0147896', '1.191'),
):
    eta, height, cap, loss, gain, deletion = map(
        Q, (eta, height, cap, loss, gain, deletion)
    )
    assert 2 * C + 2 * eta == height
    assert C + eta / 2 == deletion
    assert threshold(height, large) == cap
    assert target - cap == loss
    assert cap - old_small == gain
    assert (deletion < target) == (eta == Q('.160'))

print('projected erasure ledger verified')
