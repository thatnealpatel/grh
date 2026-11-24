#!/usr/bin/env python3
"""Check the bin combinations and radius ledger in fixed-input-erasure.md."""

from fractions import Fraction as F

C, rankin, saving = map(F, ('1.055', '.22', '.28'))
half = F(1, 2)
lam, mu = F(671, 900), F(429, 625)

# Coefficients of (C, u, x, y), after dropping nonpositive slack.
moving = (0, half, rankin, rankin)
symmetric = (1 + rankin, -rankin / 2, -saving / 2, -saving / 2)
zero_local = (1, 0, 0, -saving)
reverse_direct = (1, 0, -saving, rankin)


def combine(weights, *prices):
    assert sum(weights) == 1 and min(weights) > 0
    return tuple(sum(w * c for w, c in zip(weights, terms)) for terms in zip(*prices))


assert combine((F(7, 18), F(11, 18)), moving, symmetric) == (
    lam, (1 - lam) / 2, 0, 0
)
assert combine(
    tuple(F(n, 625) for n in (196, 275, 154)), moving, zero_local, reverse_direct
) == (mu, (1 - mu) / 2, 0, 0)
assert 0 < mu < lam < 1
assert (1 + rankin) / (2 * rankin + saving) == F(61, 36)


def hits(r):
    return r / 2 + lam * (C - r / 2)


target = F('1.1354')
old_loss = F('.1185')
for r, hit, loss, old_total, pivot in (
    (F('1.300'), F('.95195'), F('.18345'), F('1.07045'), F('.68625')),
    (
        F('1.475'), F(350717, 360000), F(58027, 360000), F(393377, 360000),
        F(7747, 14400),
    ),
):
    assert r < 2 * C and hits(r) == hit
    assert target - hit == loss and hit + old_loss == old_total
    assert r / 2 + F('.220') < hit < F('.9284') + F('.06') * r
    a_h = a_k = r / 2
    x = y = F(61, 36) * (C - r / 2)
    assert x == pivot and 0 <= C - a_h <= x <= 2 * C
    assert x + a_h <= 2 * C and y + a_k <= 2 * C
    assert r / 2 + rankin * (x + y) == hit
    assert C - saving * y + rankin * min(x, C - a_h) == hit
    assert C - saving * x + rankin * min(y, C - a_k) == hit

assert hits(F('1.475')) - hits(F('1.300')) == F(1603, 72000)
print('Checked the fixed-input erasure prices, saddles, and capture budgets.')
