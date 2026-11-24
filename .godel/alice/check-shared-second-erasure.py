#!/usr/bin/env python3
"""Check exact bin and capture prices in shared-second-erasure.md."""

from fractions import Fraction as F

rankin = F('.22')
smooth = F('.50')
width = F('2.110')
row = width / 2
saved = smooth - rankin
moving_weight = 1 - 2 * rankin / smooth
fixed_weight = 1 - moving_weight
assert (moving_weight, fixed_weight) == (F('.12'), F('.88'))

# Coefficients of (1, r, x, y) in the two bin prices.
moving = (F(0), smooth, rankin, rankin)
fixed = (row, F(0), rankin, -saved)
combined = tuple(
    moving_weight * a + fixed_weight * b for a, b in zip(moving, fixed)
)
assert combined == (F('.9284'), F('.06'), rankin, -rankin)

fraction = F('.1185')
short_subsets = F('.50') * (F('1.44') - 1)
assert short_subsets == F('.220')

for radius, hits, complement, short_complement in (
    ('1.300', '1.0064', '1.1249', '.9885'),
    ('1.475', '1.0169', '1.1354', '1.076'),
):
    r = F(radius)
    x = y = width - r
    assert 0 <= x <= width
    assert smooth * r + rankin * (x + y) == row - saved * y + rankin * x
    assert smooth * r + rankin * (x + y) == combined[0] + combined[1] * r
    assert combined[0] + combined[1] * r == F(hits)
    assert F(hits) + fraction == F(complement)
    assert smooth * r + short_subsets + fraction == F(short_complement)

assert F('1.475') / 2 + short_subsets == F('.9575')
assert F('1.135') < F('1.1354') < F('1.136')
assert (F('1.136') - fraction - combined[0]) / combined[1] == F('1.485')

print('Checked the shared-erasure bin prices and capture budgets.')
