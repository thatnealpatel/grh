"""Check the scalar enclosures in dilated-first-ramp.md with SageMath 10.9."""
from sage.all import RealBallField

F = RealBallField(128)
m = F(8) / 9


def prices(h):
    # E = integral_0^infty exp(-v)/(v+h) dv.
    E = h.exp() * F(0).gamma_inc(h)
    L = 1 - h + h**2 * E
    dL = -1 - h + (2*h + h**2) * E
    r = (h/2).exp()
    P = 2*m**2/(r*L)
    return P-r, -P*(F(1)/2 + dL/L) - r/2, m/L


B, _, _ = prices(F(1)/20)
assert B > F('0.58603136')
assert B - F(1).cosh()/3 > F('0.07167115')
assert 3*B > F('1.164426').cosh()
lo, hi = '0.0507336319726', '0.0507336319728'
assert prices(F(lo))[1] > 0 and prices(F(hi))[1] < 0
B, _, A = prices(F('0.0507336319727 +/- 0.00000000000011'))
assert F('0.58603230294') < B and B < F('0.58603230297')
assert F('0.9298') < A and A < F('0.9300')
print('Fixed dilation, stationary bracket, price, and profile bounds passed.')
