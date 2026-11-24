"""Ball-arithmetic certificate for the complementary right-sector law (SageMath)."""
from argparse import ArgumentParser
from bisect import bisect_right
from functools import lru_cache
from math import comb, factorial
from pathlib import Path

from sage.all import ComplexBallField, QQ, RealBallField

if not __debug__:
    raise SystemExit('Run with assertions enabled.')
F = RealBallField(128)
K = ComplexBallField(128)

parser = ArgumentParser(description=__doc__)
parser.add_argument('--point-only', action='store_true',
                    help='Check the caps, angular mean, and reported residual only.')
parser.add_argument('--rectangle', type=QQ, nargs=4, metavar=('S_LO', 'S_HI', 'D_LO', 'D_HI'),
                    default=[QQ(-9)/50, QQ(1)/2, QQ(6)/5, QQ(2)],
                    help='All-orientation direction certificate on a rational rectangle.')
parser.add_argument('--baseline', choices=('midgap-sector', 'hard-pair'),
                    help='Check only the negative residual of an existing profile.')
args = parser.parse_args()
name = args.baseline or 'right-sector'
DATA = Path('.godel/bob') / (name+'-10-2.txt')
ZDEN, NSLABS, ZLO = (128, 416, -12) if name == 'hard-pair' else (64, 248, -10)
SCALE = 10**8
z, laws = [], []
for line in DATA.read_text().splitlines():
    line = line.split('#', 1)[0].strip()
    if not line:
        continue
    knot, *fields = map(int, line.split())
    assert fields and len(fields) % 2 == 0
    atoms, masses = fields[::2], fields[1::2]
    assert all(-SCALE <= a <= SCALE for a in atoms)
    assert all(p > 0 for p in masses) and sum(masses) == SCALE
    z.append(QQ(knot)/ZDEN)
    laws.append([(QQ(a)/SCALE, QQ(p)/SCALE) for a, p in zip(atoms, masses)])
assert len(z) == NSLABS and z[0] == ZLO
assert 0 in z and z[-1] == 16
assert all(l < r for l, r in zip(z, z[1:]))

A = [sum(p*a for a, p in law) for law in laws]
B = [sum(p*(4*a**3-3*a) for a, p in law) for law in laws]
U = [sum(p*F((1+a)/2).sqrt() for a, p in law) for law in laws]
assert all(-1 <= y <= 1 for y in A+B)
wt = [(1+t)*F(-t).exp() if t >= 0 else F(1) for t in z] + [F(0)]
mean_margin = sum((l-r)*u for l, r, u in zip(wt, wt[1:], U))-F(QQ(8)/9)
assert mean_margin > F(QQ(1)/(10**8))
print('Angular surplus:', mean_margin, flush=True)

c = F(QQ(39)/20)
C1 = c.cosh()/3
C10 = C1/(2*(F.pi()/12).cos())
cap_A = QQ(618660)/10**6
cap_B = QQ(119516)/10**5
assert cap_A < C10 and cap_B < C1


def jump_terms(profile, knots=z):
    return [(t, F(y-v)*F(-t/2).exp()) for t, y, v in zip(knots, profile, [QQ(0)]+profile)
            if y != v]


def certify_cap(label, profile, cap, knots=z):
    points = jump_terms(profile, knots)
    cap = F(cap)
    # Center the numerator polynomial at -2, changing it by a unit phase only.
    times = [t+2 for t, _ in points]
    jump = [b for _, b in points]
    Bk = [sum(abs(b)*F(abs(t)**k) for t, b in zip(times, jump)) for k in range(5)]
    X = QQ(64)
    assert Bk[0]/X < cap

    def phases(x):
        return [K(0, -t*x).exp() for t in times]

    # Direct integration of the slabs and the original first representer.
    for x in (QQ(0), QQ(17)/4, QQ(13)):
        w = K(QQ(1)/2, x)
        edges = [(-w*t).exp() for t in knots]+[K(0)]
        slab = sum(y*(l-r) for y, l, r in zip(profile, edges, edges[1:]))/w
        via_jumps = K(0, 2*x).exp()*sum(b*p for b, p in zip(jump, phases(x)))/w
        G = sum(b*K(0, t*x).exp() for t, b in points)/w
        tol = F(QQ(1)/10**29)
        assert abs(slab-via_jumps) < tol
        assert abs(G-(w.conjugate()/w)*slab.conjugate()) < tol

    # Taylor bound for Q=|N|^2-cap^2*(1/4+x^2), with global |Q''''| <= M4.
    M4 = sum(comb(4, j)*Bk[j]*Bk[4-j] for j in range(5))
    coef = [[K(b)*K(0, -t)**k for t, b in zip(times, jump)] for k in range(4)]

    def passes(mid, radius):
        p = phases(mid)
        nd = [sum(b*v for b, v in zip(row, p)) for row in coef]
        nc = [v.conjugate() for v in nd]
        rad = [F(QQ(1)/4+mid**2), F(2*mid), F(2), F(0)]
        q = [sum(comb(k, j)*(nd[j]*nc[k-j]).real() for j in range(k+1))
             -cap**2*rad[k] for k in range(4)]
        r = F(radius)
        upper = q[0]+sum(abs(q[k])*r**k/factorial(k) for k in range(1, 4))
        return upper+M4*r**4/24 < 0

    stack, boxes = [(QQ(0), X, 0)], 0
    while stack:
        lo, hi, depth = stack.pop()
        mid = (lo+hi)/2
        if passes(mid, (hi-lo)/2):
            boxes += 1
        else:
            assert depth < 24, (label, lo, hi)
            stack.extend([(lo, mid, depth+1), (mid, hi, depth+1)])
    print(label, 'cap:', cap, '; finite boxes:', boxes, '; tail bound at', X, ':', Bk[0]/X,
          flush=True)


if not args.baseline:
    certify_cap('A', A, cap_A)
    certify_cap('B', B, cap_B)

# Coefficients for S(t)=Re int e^{itx}m^2 dmu, E(t)=int cos(tx)|m|^2 dmu.
points = [(t, b/C1) for t, b in jump_terms(B)]
weights_s, weights_e = {}, {}
for t, a in points:
    for v, b in points:
        weights_s[t+v] = weights_s.get(t+v, F(0))+a*b
        weights_e[t-v] = weights_e.get(t-v, F(0))+a*b


def prefix_kernel(weights, neg, pos):
    """Evaluate sum w_h * exp(-|t+h|/2) * p_sign(t+h) at a rational t."""
    h = sorted(weights)
    def columns(poly, sign):
        vals = [weights[v]*F(sign*v/2).exp() for v in h]
        cols = [[F(0)] for _ in poly]
        for v, b in zip(h, vals):
            for j, col in enumerate(cols):
                col.append(col[-1]+b*F(v)**j)
        return cols
    lo = columns(neg, 1)
    hi = columns(pos, -1)

    def evaluate(t):
        i = bisect_right(h, -t)
        u = F(t)
        def translate(poly):
            return [sum(poly[k]*comb(k, j)*u**(k-j) for k in range(j, len(poly)))
                    for j in range(len(poly))]
        a, b = translate(neg), translate(pos)
        return ((u/2).exp()*sum(a_j*col[i] for a_j, col in zip(a, lo))
                +(-u/2).exp()*sum(b_j*(col[-1]-col[i]) for b_j, col in zip(b, hi)))
    return evaluate


S = prefix_kernel(weights_s, [1], [1, 1, QQ(1)/2])
E = lru_cache(maxsize=None)(prefix_kernel(weights_e, [2, -1], [2, 1]))
S = lru_cache(maxsize=None)(S)
V0 = 1-E(0)
# T = int x^2 |m|^2 dmu, bounding the second derivatives of S and E.
T = sum(b*F(QQ(1)/2-abs(t)/4)*F(-abs(t)/2).exp() for t, b in weights_e.items())
assert 0 < T < 3
print('Energy E(0), angular-frequency moment T:', E(0), T, flush=True)

@lru_cache(maxsize=None)
def binomial_price_data(q, n):
    # |1+q exp(idx)| is the squared modulus of its square-root series.
    assert 0 <= q < 1 and n > 0
    u = [F(1)]
    for j in range(1, n+1):
        u.append(u[-1]*((QQ(3)/2-j)*q/j))
    delta = q**(n+1)/(1-q)
    assert delta < 1
    # Uniform squared-series error after division by 1+q and integration
    # against the positive capacity measure (whose mass is <=1).
    c = [sum(a*b for a, b in zip(u, u[j:])) for j in range(n+1)]
    return c, 3*delta


@lru_cache(maxsize=None)
def binomial_capacity(d, q, n):
    c, _ = binomial_price_data(q, n)
    return (c[0]*V0+2*sum(v*(F(-j*d/2).exp()-E(j*d))
                         for j, v in enumerate(c[1:], 1)))/(1+q)


# The first weight is 3/5 (earlier shift); use q=(1-a)/a.
s0, d0, a0 = QQ(0), QQ(32)/25, QQ(3)/5
q0 = (1-a0)/a0
point_price = abs(a0*S(s0)+(1-a0)*S(s0+d0))
point_capacity = binomial_capacity(d0, q0, 128)
_, point_error = binomial_price_data(q0, 128)
point_slack = point_capacity-point_price + F(0, F(point_error).upper())
if args.baseline:
    assert point_slack < 0, (name, point_slack)
else:
    assert point_slack > 0, point_slack
print(name, 'residual (s,d,a) =', (s0,d0,a0), 'capacity:', point_capacity,
      'price:', point_price, 'normalized slack:', point_slack, flush=True)
if args.point_only or args.baseline:
    raise SystemExit

# Balanced capacity: the cosine series has an exponentially small tail
# after integration against the capacity measure, uniformly over d >= 1.
D = max(weights_e)
TV = sum(abs(b) for t, b in points)
N = 96
u = QQ(N+1)
assert u > D and 2+u+D > 6
err = (4/F.pi())/(4*u*u-1)*(F(-u/2).exp()/(1-F(-QQ(1)/2).exp())
        +TV**2*(2+u+D)*F(-(u-D)/2).exp()/(1-F(-QQ(1)/3).exp()))
assert err < F(QQ(1)/10**12)
coef = [QQ((-1)**(k-1))/(4*k*k-1) for k in range(1,N+1)]
C2 = 4/F.pi()*sum(abs(b)*k*k*(T+F(-QQ(k)/2).exp()/4)
                    for k,b in enumerate(coef,1))


@lru_cache(maxsize=None)
def R(u):
    return F(-u/2).exp()-E(u)


@lru_cache(maxsize=None)
def balanced(d):
    return (2*V0+4*sum(b*R(k*d) for k,b in enumerate(coef,1)))/F.pi()


etas = [QQ(x) for x in ('0', '1/8', '3/16', '1/4', '5/16', '3/8', '1/2', '3/4', '1')]
ratios = [(1-h)/(1+h) for h in etas[1:]]
M = 128


@lru_cache(maxsize=None)
def capacities(d):
    return [balanced(d)]+[binomial_capacity(d,q,M) for q in ratios]


@lru_cache(maxsize=None)
def lower(s,d):
    p, q = S(s), S(s+d)
    b = QQ((abs(p-q)/2).upper())
    center = F((abs(p+q)/2).upper())
    caps = [QQ(v.lower()) for v in capacities(d)]
    lo = []
    for l,r,cl,cr in zip(etas,etas[1:],caps,caps[1:]):
        # Capacity is concave as a function of eta^2. The chord through
        # capacities at l,r (before the uniform tail loss) is a lower proxy.
        g = (cr-cl)/(r*r-l*l)
        u = max(l,min(r,b/(2*g))) if g>0 else r
        lo.append(cl+g*(u*u-l*l)-b*u)
    return F(min(lo))-center


# At each fixed eta use the proxy interpolated between adjacent Fourier
# truncations. Derivative bounds interpolate too. Bound each signed center
# branch before taking its infimum, avoiding differentiation of |.|.
Ms = T
Md = C2+T
for q in ratios:
    c, tail = binomial_price_data(q,M)
    assert tail < QQ(1)/10**12
    bound = (2*(F(QQ(1)/4)+T)*sum(n*n*abs(v) for n,v in enumerate(c[1:],1)))/(1+q)+T
    Md = F(max(Md.upper(),bound.upper()))
err = F(QQ(1)/10**12)
floor = F(QQ(1)/100000)
slo, shi, dlo, dhi = args.rectangle
assert slo < shi and 1 <= dlo < dhi
stack = [(slo, shi, dlo, dhi)]
count = 0
min_margin = F(1).lower()
while stack:
    a, b, l, r = stack.pop()
    es, ed = Ms*(b-a)**2/8, Md*(r-l)**2/8
    margin = min(lower(s,d).lower() for s in (a,b) for d in (l,r))
    bound = F(margin)-es-ed-err
    if bound > floor:
        count += 1
        min_margin = min(min_margin, bound.lower())
    elif es > ed:
        assert b-a > QQ(1)/4096, (a,b,l,r,margin)
        m = (a+b)/2
        stack.extend(((a,m,l,r), (m,b,l,r)))
    else:
        assert r-l > QQ(1)/4096, (a,b,l,r,margin)
        m = (l+r)/2
        stack.extend(((a,b,l,m), (a,b,m,r)))
print(f'All like signs, s in [{slo},{shi}], d in [{dlo},{dhi}]:', count,
      'boxes; certified normalized slack >', min_margin, '; tail <=', err)
