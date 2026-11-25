#!/usr/bin/env python3
"""Exact arithmetic for the first-gap power-kernel deletion."""
from fractions import Fraction as F

inputs, columns, gaps, target = map(F, (".860", "1.055", ".390", "1.1354"))
prefix, cofactor = map(F, (".5275", ".665"))
assert prefix + cofactor / 2 == inputs
assert inputs + gaps / 2 == columns

for m, first_cut, first_expected, second_cut, second_expected in (
    (2, F(".020"), F("1.135"), F(".017"), F(9079, 8000)),
    (3, F(".049"), F(6809, 6000), F(".044"), F(3403, 3000)),
    (4, F(".059"), F(63531, 56000), F(".055"), F(25411, 22400)),
):
    delta = F(1, 2 * m)
    split = (columns - inputs - gaps * delta) / (1 - delta)
    small = inputs + 2 * gaps * delta + split * (1 - 2 * delta)
    large = columns + gaps * delta - split * delta
    base = columns + (columns - inputs) / (2 * m - 1)
    assert 0 < split < gaps
    assert small == large == base

    # Second-row cofactor bins maximize at the upper endpoint.
    l_slope = F(1, 2) - 2 * delta
    l_price = 2 * cofactor * delta + cofactor * l_slope
    assert l_slope >= 0
    assert prefix + l_price + 2 * gaps * delta + split * (1 - 2 * delta) == base
    assert prefix + l_price + gaps * (F(1, 2) + delta) - split * delta == base
    first = base + first_cut * (1 - delta)
    second = base + second_cut * (1 - delta / 2)
    assert first == first_expected <= F("1.135") < target
    assert second == second_expected <= F("1.135") < target
    print(f"m={m}: split={split}, first={first}, second={second}")
