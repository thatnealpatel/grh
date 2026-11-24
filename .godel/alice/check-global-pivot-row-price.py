#!/usr/bin/env python3
"""Check the exact rates in global-pivot-row-price.md."""

from fractions import Fraction as F

S = F('.22')
H = F('.390')
WIDTH = F('2.110')
GLOBAL = WIDTH / 2 + H / 2
GAP = F(1, 2) - S
TAIL = GLOBAL - GAP * H
C_W = (F('2.890') - F('1.904')) / 2
C_D = F('.118') / 2 + H
SELECT = F('1.136')

assert GLOBAL == F('1.250') and TAIL == F('1.1408')
assert C_W == F('.493') and C_D == F('.449')


def row_pair(t):
    return max(GLOBAL - GAP * t, TAIL - GAP * t / 2)


def a_cross(c, r):
    switch = 2 * (TAIL - c - (S + GAP / 2) * 2 * H)
    if r <= switch:
        t = (TAIL - c - r / 2) / (S + GAP / 2)
        assert t >= 2 * H
        closed = (7 * c + 11 * TAIL) / 18 + 7 * r / 36
    else:
        t = (GLOBAL - c - r / 2) / (S + GAP)
        assert t <= 2 * H
        closed = F('.56') * c + F('.44') * GLOBAL + GAP * r
    assert 0 <= t <= WIDTH
    if c == C_W:
        assert t <= F('1.904') - r
    assert c + r / 2 + S * t == row_pair(t) == closed
    return closed


def b_cross(r):
    y = (GLOBAL - r / 2) / (S + GAP / 2)
    assert 0 <= y <= 2 * WIDTH
    value = S * y + r / 2
    assert value == GLOBAL - GAP * y / 2 == F(55, 72) + 7 * r / 36
    assert GLOBAL - GAP * WIDTH <= value
    return value


def prices(r_w, r_s, r_d):
    return a_cross(C_W, F(r_w)), b_cross(F(r_s)), a_cross(C_D, F(r_d))


for c, switch, end in [(C_W, '.734', '1.105'), (C_D, '.822', '1.193')]:
    for r in map(F, ('0', switch, end)):
        a_cross(c, r)
b_cross(F(0))

old = prices('.530', '.530', '.530')
assert old == (F(14879, 15000), F(3121, 3600), F(43867, 45000))
assert max(old) + F('.030') == F(15329, 15000)
end = prices('1.105', '1.912', '1.193')
assert end == (F('1.13548'), F(3407, 3000), F('1.13548'))
assert max(end) < SELECT
assert max(prices('1.105', '1.105', '1.105')) == F('1.13548')

new = prices('.658', '1.300', '.746')
assert new == (F(45757, 45000), F(61, 60), F(45757, 45000))
assert max(new) < F('1.0170')
assert F('1.0170') + F('.1185') == F('1.1355') < SELECT

short = F('.50') * (F('1.44') - 1)
assert short == F('.220')
small_span = (C_W + F('.530') / 2, F('.530') / 2, C_D + F('.530') / 2)
assert small_span == (F('.758'), F('.265'), F('.714'))
assert max(small_span) + short == F('.978')
assert F('.978') + F('.030') == F('1.008')
assert F('1.300') / 2 + short == F('.870')
assert F('.870') + F('.1185') == F('.9885')

print('Checked the pivot-row intersections, radii, and capture budgets.')
