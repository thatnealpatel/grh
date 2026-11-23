"""Exact scalar comparisons in two-hit-sum.md. Run with python3, no -O."""

from fractions import Fraction as Q


def atan_bounds(x):
    # Alternating series, ending with a negative term for the lower sum.
    lo = sum((-1)**k * x**(2*k + 1) / (2*k + 1) for k in range(8))
    return lo, lo + x**17 / 17


assert __debug__
a, A = atan_bounds(Q(1, 5))
b, B = atan_bounds(Q(1, 239))
pi_lo, pi_hi = 16*a - 4*B, 16*A - 4*b  # Machin's identity
r = Q('1.4142136')
assert r**2 > 2
m = 2*r / pi_lo  # upper bound
h = Q(8, 9)
for F, b0, d in [(m, Q('.75173'), Q('1.293')),
                 (m + (m - 1/r)/145, Q('.72411'), Q('2.211'))]:
    assert F > h
    c = 1 - r*(F - h)  # lower bound (also valid if the true loss is zero)
    assert c > 0 and 2*c*c - 1 > 0
    assert 2*(2*c*c - 1)**2 - 1 > b0
    assert 2*b0*b0 - 1 > 1 / (1 + 4*d*d)

v = Q(37, 40)  # cos(2t) in the separating control
assert v*2/pi_hi > Q('.587') and 2/pi_hi > Q('.60429')
assert 2*v*v - 1 == Q('.71125') < Q('.72411')
assert m*m*(1+v)/2 < h*h
print('Both sum-height thresholds, diameter bounds, and control comparisons pass.')
