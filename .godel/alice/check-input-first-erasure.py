#!/usr/bin/env python3
"""Check the exact ledger for buying the input before the singleton row."""

from fractions import Fraction as Q


C, inputs, pivot, saving = map(Q, ('1.055', '.860', '.22', '.28'))
target, small, large = map(Q, ('1.1354', '1.300', '1.475'))
lam = saving / (saving + 2 * pivot)
A = Q(671, 900) * C


def J(u):
    return C - lam * (C - u / 2)


def crossing(u):
    return inputs + pivot * (C - u / 2)


w_star = (C - inputs) / (lam + pivot)
u_star = 2 * (C - w_star)
cap = J(u_star)
assert small < u_star == Q(5033, 3425) < large
assert cap == crossing(u_star) == Q(50989, 54800)
assert crossing(large) == Q('.929850') < cap < J(large)
assert w_star / (2 * pivot + saving) == Q(975, 2192)
assert cap - inputs == Q(3861, 54800)
assert (cap - u_star / 2) / Q('.44') == Q(975, 2192)

# Noncrossing: M <= C-(1-pivot)w+pivot*m and D=C-saving*m.
intersection = (1 - pivot) / (pivot + saving)
coefficient = intersection * saving
assert intersection == Q('1.56')
assert coefficient == Q('.4368') > lam
assert C - coefficient * (C - large / 2) == Q('.916316') < cap
assert A < J(small) == Q('.897500')
assert target - J(small) == Q('.237900')
assert target - cap == Q(280773, 1370000)
assert target - J(large) == Q(36697, 180000)
assert cap + target - J(large) == Q(27972539, 24660000) < target
assert cap - J(small) == Q(903, 27400)

print('input-first erasure ledger verified')
