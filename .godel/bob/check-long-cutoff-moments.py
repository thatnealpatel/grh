"""Replay the finite spline identities and strict prices. Run with SageMath Python."""
from sage.all import QQ, PolynomialRing, RealBallField, binomial, factorial

if not __debug__:
    raise SystemExit('Run without -O.')

# r measures distance below the leading endpoint; D is the knot spacing.
ring = PolynomialRing(QQ, names=('r', 'D'))
r, D = ring.gens()
for j in range(1, 16):
    h = sum((-1)**l * binomial(j-1, l) * r**(j-l) / factorial(j-l)
            for l in range(j))
    assert sum((-1)**k * binomial(j+1, k) * h(r-k*D, D)
               for k in range(j+2)) == 0
    # Multiply the one-sided Laplace transform by w^(j+1), using r as w.
    assert sum(h.monomial_coefficient(r**k) * factorial(k) * r**(j-k)
               for k in range(j+1)) == (1-r)**(j-1)

F = RealBallField(128)
p = F(47)/81
for depth, lower, upper in [('1.50', '-3.36', '-.31'), ('1.54', '-3.64', '-.066')]:
    c = F(depth)
    a, b = 3*p/c.cosh(), (2*c).cosh()/3
    assert 0 < a < 1 and F(lower) < -b and -b*(2*a*a-1) < F(upper)
    print('Depth, limiting lower and upper prices:', depth, -b, -b*(2*a*a-1))

v = [1, 2, 2, 2, 1]
coeff = [(1 if k == 0 else 2)*sum(i*j for i, j in zip(v, v[k:]))
         for k in range(len(v))]
assert coeff == [14, 24, 16, 8, 2]
price = F(coeff[0])/3 - coeff[1]*p/F('1.75').cosh()
assert price < F('-.03139')
print('Four-length upper price:', price)

# Finite-order decision: strict separation and failure at the preceding
# order for both constructions. pi() and trigonometric operations are Arb.
pi = F.pi()

def b(n):
    return 1/(2*(pi/(n+2)).cos())

for depth, n, equal_n in [('1.54', 2, 3), ('1.67', 3, 4), ('1.75', 4, 6),
                          ('1.80', 5, 9), ('1.81', 6, 10), ('1.90', 15, 54)]:
    a = 3*p/F(depth).cosh()
    assert b(n) < a < b(n-1)
    assert 2*a*(equal_n-1)/equal_n < 1 < 2*a*equal_n/(equal_n+1)
    if n == 15:
        assert (1-a/b(n))/3 < F('-.0004360')

for n in range(2, 6):
    for h in range(1, n):
        retained = b(h)
        for r in range(h+2, n+2):
            retained *= (pi/(2*r)).cos()
        assert retained > b(n)
assert b(5)*(pi/14).cos() < b(6)  # First unproved sparse comparison.
assert 3*p/F('1.75').cosh() < F(3)/5 < (pi/4).cos()*(pi/6).cos()
print('Finite cutoff brackets, signed price, and sparse comparisons passed.')
