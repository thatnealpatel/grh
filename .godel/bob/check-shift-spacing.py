"""Certify the scalar and lattice second-shift tests. Run with sage at repo root."""
from collections import defaultdict
import runpy
from sage.all import QQ, RealIntervalField

if not __debug__:
    raise SystemExit('Run with assertions enabled.')
raw = runpy.run_path('.godel/bob/check-single-shift-10-2.py')
F, points, C = (raw[k] for k in ('F', 'points', 'C1'))
I = RealIntervalField(128)
# W(d) = exp(-d/2) + sum_p h[p] (2+|d-p|)exp(-|d-p|/2), d>=0.
h = defaultdict(lambda: F(0))
for z, b in points:
    for t, a in points:
        h[z-t] -= 2*b*a/C**2
knots = sorted(h)
assert -24 <= knots[0] < 0 < 7 <= knots[-1] <= 24 and 1 in knots
# After p<=d is swept left, exp(d/2)W(d)=A+B*d+(E+J*d)exp(d).
A, B, E, J = F(1), F(0), F(0), F(0)
for p in knots:
    v = h[p]*F(-p/2).exp()
    E += v*(2+p)
    J -= v
W0 = 1-2*raw['L0']/C**2
assert W0 > F('0.01148')
M = QQ(38)/100
eta = QQ(1)/10**6
nboxes = 0
for p, q in zip(knots, knots[1:]+[None]):
    v = h[p]*F(-p/2).exp()
    u = h[p]*F(p/2).exp()
    A += u*(2-p)
    B += u
    E -= v*(2+p)
    J += v
    if p < 0:
        continue
    if q is None:
        # The right sum is identically empty here. Don't propagate rounded zeros.
        assert abs(A) < M and abs(B) < eta
        break
    if p == 0:
        assert (A+E-W0).contains_zero()
    if p == 1:
        W1 = (A+B+(E+J)*F(1).exp())*F(-QQ(1)/2).exp()
    stack = [(p, q)]
    while stack:
        a, b = stack.pop()
        x = F(I(a,b))
        T = A+B*x+(E+J*x)*x.exp()
        # From 0 to the first positive knot, bound by the value at 0.
        below = (B+(E+J+J*x)*x.exp() < 0) if p == 0 else (T < W0)
        if abs(T) < M and below:
            nboxes += 1
        else:
            assert b-a > QQ(1)/10**9, (a,b,T)
            mid = (a+b)/2
            stack.extend([(a,mid),(mid,b)])
# Beyond 24 only the absolute envelope was tested. Its product with exp(-d/2)
# is decreasing. This bound also gives |W(d)|<W(0) for d>=7.
assert (M+7*eta)*F(-QQ(7)/2).exp() < W0
# For any d>=17/2 sum the envelope on nonzero multiples kd. Each term decreases.
d = QQ(17)/2
r = F(-d/2).exp()
assert 2*(M*r/(1-r)+eta*d*r/(1-r)**2) < W0
# Direct Cauchy majorant for the positive mask with shifts 0 and 1.
mass = (1+W0)/2
rho = (F(-QQ(1)/2).exp()+W1)/2
capacity = (2*mass*(mass+rho)).sqrt()
center = sum((a-b)/C**2 for a,b in (raw['energies'](s) for s in (0,1)))
assert capacity < F('.853') and center > F('.915')
print('W(0), W(1), finite envelope boxes:', W0, W1, nboxes)
print('0,1 positive mask: capacity upper bound, center:', capacity, center)

# S(s)=integral exp(isx)m^2 dmu. Group by p=-z-t, and sweep the
# switch in K(s-p) from an exponential to exponential times quadratic.
coef = {-p: v/C**2 for p, v in raw['sum_weights'].items()}
knots = sorted(coef)
P, K, lam, shift = QQ(476)/1000, QQ(7)/10, QQ(48)/100, QQ(2)/5
T = sum(v*F(-p/2).exp() for p, v in coef.items())
assert knots[0] < -2 and knots[-1] > 2
p = knots[0]
# Left of all knots the product with exp(lam*|x-shift|) increases.
assert abs(T)*F(p/2).exp() < P
assert abs(T)*F(p/2+lam*(shift-p)).exp() < K
A, B, E = F(0), F(0), F(0)
sboxes = 0
for p, q in zip(knots, knots[1:]+[None]):
    v = coef[p]*F(p/2).exp()
    A += v*(1-p+p**2/2)
    B += v*(1-p)
    E += v/2
    T -= coef[p]*F(-p/2).exp()
    if q is None:
        # On s=p+y, bound each y^j exp(-a*y) by j!/a^j.
        for a, fac, bound in [(QQ(1)/2,F(1),P), (QQ(1)/2-lam,F(-lam*shift).exp(),K)]:
            price = abs(A+B*p+E*p**2)+abs(B+2*E*p)/a+2*abs(E)/a**2
            assert fac*F(-a*p).exp()*price < bound
        break
    stack = [(p,q)]
    while stack:
        a, b = stack.pop()
        x = F(I(a,b))
        S = (A+B*x+E*x**2)*(-x/2).exp()+T*(x/2).exp()
        if abs(S) < P and abs(S)*(lam*abs(x-shift)).exp() < K:
            sboxes += 1
        else:
            assert b-a > QQ(1)/10**9, (a,b,S)
            mid = (a+b)/2
            stack.extend([(a,mid),(mid,b)])
# On an arbitrary D-separated set the two one-sided tails are geometric.
D = QQ(19)/2
assert F(K/P).log()/lam < D/2
r, q = F(-lam*D).exp(), F(-D/2).exp()
center_sum = P+K*r/(1-r)*(P/K+K/P)
off_diag = (1+M)*q/(1-q)+eta*D*q/(1-q)**2
endpoint = 2*K*F(-lam*D/2).exp()/(1-r)
assert endpoint < center_sum and center_sum+off_diag < mass
print('Separated set: sum of centers, Gram off-diagonal, diagonal, sum-kernel boxes:',
      center_sum, off_diag, mass, sboxes)
