#!/usr/bin/env python3
"""Check the exact coefficient and same-target ledgers for singleton erasure."""

from fractions import Fraction as F


C, target = F('1.055'), F('1.1354')
pivot, saving = F('.22'), F('.28')
moving, reference = F(7, 18), F(11, 18)
assert moving + reference == 1
assert moving * pivot == reference * saving / 2 == F(77, 900)
A = reference * (1 + pivot) * C
assert A == F(671, 900) * C
assert 2 * (A - reference * C) / moving == F(121, 175) * C


def J(radius):
    return reference * C + moving * radius / 2


def weight(radius):
    return (C - radius / 2) / (2 * pivot + saving)


r, s = F('1.300'), F('1.475')
assert (J(r), J(s)) == (F(359, 400), F(6707, 7200))
assert J(s) - J(r) == F(49, 1440)
assert (target - J(r), target - J(s)) == (F('.2379'), F(36697, 180000))
assert (weight(r), weight(s)) == (F(9, 16), F(127, 288))
assert max(A, r / 2 + 2 * pivot * weight(s)) == F(6077, 7200)
assert max(A, C - saving * weight(r)) == J(r) < J(s)
assert r / 2 + F('.220') < J(r) and s / 2 + F('.220') > J(s)

for radius, expected in ((r, F('.86285')), (s, F(325571, 360000))):
    x = weight(radius)
    assert radius / 2 + 2 * pivot * x == C - saving * x == J(radius)
    old_min_heavier_weight = F(61, 36) * (C - radius / 2)
    assert max(A, C - saving * old_min_heavier_weight) == expected < J(radius)

print('singleton erasure coefficients and paired-radius thresholds verified')
