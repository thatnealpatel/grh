"""SageMath Python, without -O: Common short-phase floor at t and 3t."""
from sage.all import QQ, RealBallField

if not __debug__:
    raise SystemExit('Run without -O.')
F = RealBallField(128)
q = QQ
a, d = q(2885)/10000, q(48)/10000


def mask(h, b, weight):
    return [(i*h+b, weight*q(6-abs(i))/36 * F(-(i*h+b)/2).exp()) for i in range(-5, 6)]


f = mask(q(1)/10, q(1)/25, a)
g = mask(q(1)/5, q(7)/25, d)
N = 1024
u = [F(j)/N for j in range(N+1)]
t2 = [2*x*x-1 for x in u]
t6 = [4*t*t*t-3*t for t in t2]


def lower(p, r, v):
    # p*T2 - r*T6 - v*u, p,r nonnegative; -T6'' <= 252/5.
    return F(min((p*t-r*s-v*x).lower() for x, t, s in zip(u, t2, t6))) - (4*p+51*r)/(8*N*N)


def ramp(z, coeffs):
    return sum(A*max(0, z+s) for s, A in coeffs)


mesh = sorted({q(j)/100 for j in range(-128, 801)} | {-s for s, _ in f+g})
assert mesh[0] == -max(s for s, _ in f+g) and mesh[-1] > -min(s for s, _ in f+g)
vals = [lower(ramp(z, f), ramp(z, g), F(max(0, z))) for z in mesh]
price = F(q(8)/9)
for x, y, l, r in zip(mesh, mesh[1:], vals, vals[1:]):
    h = F(y-x)
    m = 1-(-h).exp()
    price += F(-x).exp()*(l*m+(r-l)*(m/h-(-h).exp()))
price += F(-mesh[-1]).exp()*(vals[-1] + lower(sum(A for _, A in f), sum(A for _, A in g), F(1)))


def I(h):
    return sum(q(6-abs(i))/36 * F(-abs(i)*h/2).exp() for i in range(-5, 6))


def C(n):
    return F('1.95').cosh()/(6*(F.pi()/(n+2)).cos())


print('first-price floor:', price)
for n, m, ceiling in [(10, 3, '-.000012'), (11, 2, '-.00042')]:
    gap = a*C(n)*I(q(1)/10) + d*C(m)*I(q(1)/5) - price
    print((n, m), 'upper price:', gap)
    assert gap < F(ceiling)
