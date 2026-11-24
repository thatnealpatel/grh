"""Certify the shift range for the accepted raw (10,2) mixture (SageMath 10.9)."""
from bisect import bisect_right
from functools import cache
import runpy
from sage.all import QQ, RealBallField

if not __debug__:
    raise SystemExit('Run with assertions enabled.')
F = RealBallField(128)
raw = runpy.run_path('.godel/bob/check-raw-10-2.py')
jumps = sorted((z, j) for z, j in raw['jumps'].items() if j)
L, limit = raw['L'], raw['limit']
# r=-(z_i+z_k); c_r is the sum of the unweighted jump products.
groups = {}
for i, (z, j) in enumerate(jumps):
    for k, (w, l) in enumerate(jumps[:i+1]):
        r = -z-w
        groups[r] = groups.get(r, 0)+j*l*(1 if i == k else 2)
knots = sorted(groups)
# For r<=s the term is c_r exp(r-s/2) [1+(s-r)+(s-r)^2/2].
# For r>s it is c_r exp(s/2). Prefix sums evaluate S in logarithmic time.
sums = [(F(0), F(0), F(0), sum(groups.values()))]
for r in knots:
    a, b, c, d = sums[-1]
    v = groups[r]*F(r).exp()
    sums.append((a+v*(1-r+r*r/2), b+v*(1-r), c+v/2, d-groups[r]))


@cache
def S(s):
    a, b, c, d = sums[bisect_right(knots, s)]
    e = F(s/2).exp()
    return (a+s*(b+s*c))/e + d*e


assert all((S(QQ(i))-v).contains_zero() for i, v in enumerate(raw['S']))
M = sum(abs(j)*F(-z/2).exp() for z, j in jumps)**2
T = 2*limit-L
# On either tail |s-r|>=64, and (1+v+v^2/2)exp(-v/2) decreases for v>=64.
assert knots[0] >= -32 and knots[-1] <= 32
assert M*(1+64+64**2//2)*F(-32).exp() < T


def check(a, b, ok):
    # |S''| <= integral x^2 |G|^2 dmu <= M. The extremal chord error is M h^2/8.
    pending = [(a, b)]
    while pending:
        a, b = pending.pop()
        err = M*(b-a)**2/8
        if ok and max(abs(S(a)), abs(S(b)))+err < T:
            continue
        if not ok and min(S(a), S(b))-err > T:
            continue
        assert b-a > QQ(1)/10**9, (a, b, ok)
        m = (a+b)/2
        pending.extend([(a, m), (m, b)])


p, q, u, v = [QQ(i)/10**5 for i in (1653, 1654, 186812, 186813)]
check(QQ(-96), p, True)
check(q, u, False)
check(v, QQ(96), True)
# Endpoint signs above and strict monotonicity certify exactly one crossing
# in each remaining box. S stays positive throughout each box.
for a, b, sign in [(p, q, 1), (u, v, -1)]:
    assert min(S(a), S(b))-M*(b-a)**2/8 > 0
    assert sign*(S(b)-S(a))/(b-a) > M*(b-a)
print('Raw mixture fails exactly between crossings in', (p, q), 'and', (u, v))
