"""Certify the common two-term mask law; run from the repo root with SageMath."""
from bisect import bisect_right
from functools import lru_cache
from math import comb, factorial
from os import environ
from pathlib import Path

from sage.all import ComplexBallField, QQ, RealBallField

if not __debug__:
    raise SystemExit('Run with assertions enabled.')
F = RealBallField(128)
K = ComplexBallField(128)

# Right-continuous slab laws for X=cos(theta); X=0 to the left of z[0].
case = environ.get('TWO_TERM_LAW', 'regional')
if case not in ('regional', 'hard-pair'):
    raise SystemExit('TWO_TERM_LAW must be regional or hard-pair.')
hard_pair = case == 'hard-pair'
DATA = Path('.godel/bob/hard-pair-10-2.txt' if hard_pair else '.godel/bob/two-term-10-2.txt')
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
    z.append(QQ(knot)/(128 if hard_pair else 64))
    laws.append([(QQ(a)/SCALE, QQ(p)/SCALE) for a, p in zip(atoms, masses)])
assert len(z) == (416 if hard_pair else 228) and z[0] == (-12 if hard_pair else -8)
assert 0 in z and z[-1] == 16
assert all(l < r for l, r in zip(z, z[1:]))

A = [sum(p*a for a, p in law) for law in laws]
B = [sum(p*(4*a**3-3*a) for a, p in law) for law in laws]
U = [sum(p*F((1+a)/2).sqrt() for a, p in law) for law in laws]
assert all(-1 <= y <= 1 for y in A+B)
wt = [(1+t)*F(-t).exp() if t >= 0 else F(1) for t in z] + [F(0)]
mean_margin = sum((l-r)*u for l, r, u in zip(wt, wt[1:], U))-F(QQ(8)/9)
assert mean_margin > F(QQ(1)/(10**8 if hard_pair else 10**6))
print('Angular surplus:', mean_margin, flush=True)

c = F(QQ(39)/20)
C1 = c.cosh()/3
C10 = C1/(2*(F.pi()/12).cos())
cap_A = (QQ(6186603)/10**7 if hard_pair else QQ(618660)/10**6)
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


def binomial_gap(s, d, q):
    return binomial_capacity(d, q, 80)-abs(S(s)+q*S(s+d))/(1+q)


def certify_hard_box():
    ss = [QQ(j)/80 for j in range(-4, 29)]     # [-.05, .35]
    ds = [QQ(j)/80 for j in range(70, 87)]     # [.875, 1.075]
    qs = [QQ(j)/100 for j in range(54, 62)]    # [.54, .61]
    # Interpolate in a=1/(1+q), not in q. The second a derivative of
    # |a+(1-a)e^(idx)| is <=4/min(2a-1). The signed price is affine in a.
    M_a = 4*V0/(2/(1+qs[-1])-1)
    es = T*F((ss[1]-ss[0])**2/8)
    floor = F(1).lower()
    for p, q in zip(qs, qs[1:]):
        ea = M_a*F((1/(1+p)-1/(1+q))**2/8)
        for x in (p, q):
            c, tail = binomial_price_data(x, 80)
            M_d = (2*(F(QQ(1)/4)+T)*sum(j*j*abs(v) for j,v in enumerate(c[1:],1))
                   +x*T)/(1+x)
            ed = M_d*F((ds[1]-ds[0])**2/8)
            # Apply s,d chord errors to each signed branch at this ratio
            # endpoint; the a error uses the true capacity curvature.
            for s in ss:
                for d in ds:
                    bound = binomial_gap(s, d, x)-es-ed-ea-tail
                    assert bound > F(QQ(1)/1000), (s,d,x,bound)
                    floor = min(floor, bound.lower())
    boxes = (len(ss)-1)*(len(ds)-1)*(len(qs)-1)
    print('Hard-pair box:', (ss[0], ss[-1]), (ds[0], ds[-1]), (qs[0], qs[-1]),
          '; normalized slack at least', floor, '; mesh boxes:', boxes, flush=True)


s_h, d_h = QQ(4)/25, QQ(1)
q_h = QQ(5809242445)/10180116210
_, error_h = binomial_price_data(q_h, 80)
gap_h = binomial_gap(s_h, d_h, q_h)
print('Dual hard-pair normalized gap:', gap_h, '; capacity tail <=', F(error_h), flush=True)
if hard_pair:
    assert F(QQ(242)/10**5) < gap_h-error_h
    assert gap_h+error_h < F(QQ(243)/10**5)
    certify_hard_box()
else:
    assert F(-QQ(282)/10**5) < gap_h-error_h
    assert gap_h+error_h < F(-QQ(281)/10**5)


N = 140
DMIN = QQ(7)/8
ETA = QQ(1)/20
D = max(weights_e)
assert D == z[-1]-z[0] and min(weights_e) == -D
TV = sum(abs(b) for t, b in points)

# For k >= N+1, kd >= u0 > D. The envelope (2+u+D)e^{-(u-D)/2}
# is decreasing at least as fast as exp(-(u-u0)/3).
u0 = (N+1)*DMIN
assert u0 > D and 2+u0+D > 6
E_tail = TV**2*F(2+u0+D)*F(-(u0-D)/2).exp()/(1-F(-DMIN/3).exp())
mu_tail = F(-u0/2).exp()/(1-F(-DMIN/2).exp())
tail = (4/F.pi())*(mu_tail+E_tail)/(4*(N+1)**2-1)
assert tail < F(QQ(1)/10**19)

# C(d)=int |cos(dx/2)| (1-|m|^2) dmu. Compute its truncated cosine
# series. Bound the second derivative of the truncated function only.
q0 = F(-DMIN/2).exp()
cap_curv = (4/F.pi())*sum(QQ(k*k)/(4*k*k-1)*(q0**k/4+T)
                         for k in range(1, N+1))


@lru_cache(maxsize=None)
def capacity(d):
    q = F(-d/2).exp()
    return (2*V0+4*sum(QQ((-1)**(k-1))/(4*k*k-1)*(q**k-E(k*d))
                         for k in range(1, N+1)))/F.pi()


def price(s, d):
    u, v = S(s), S(s+d)
    return (abs(u+v)+ETA*abs(u-v))/2


slack = F(QQ(1)/10**5)


def certify_joint_pair(s):
    # Fix d=1. Any normalized coefficients, up to global sign and
    # either orientation, are (a, +/- (1-a)), a in [1/2,1].
    d = QQ(1)
    R = F(-d/2).exp()-E(d)
    grid = [QQ(j)/100 for j in range(52, 101)]
    floor_same = floor_opp = F(1).lower()
    for u, v in ((S(s), S(s+d)), (S(s+d), S(s))):
        def same(a):
            return abs(a*u+(1-a)*v)
        for a in (QQ(1)/2, grid[0]):
            bound = capacity(d)-tail-same(a)
            assert bound > slack, (s,a,bound)
            floor_same = min(floor_same, bound.lower())
        for a, b in zip(grid, grid[1:]):
            er = 4*V0/(2*a-1)*F((b-a)**2/8)
            for x in (a, b):
                q = (1-x)/x
                _, series_tail = binomial_price_data(q, 160)
                bound = binomial_capacity(d, q, 160)-series_tail-same(x)-er
                assert bound > slack, (s,x,bound)
                floor_same = min(floor_same, bound.lower())
        # Opposite signs: capacity >= a*V0-(1-a)*R by real part.
        # Subtract each signed price branch, which is affine in a.
        for a in (QQ(1)/2, QQ(1)):
            bound = a*V0-(1-a)*R-abs(a*u-(1-a)*v)
            assert bound > slack, (s,a,bound)
            floor_opp = min(floor_opp, bound.lower())
    # Quantitative extension: for |delta d|,|delta s| <= h, factor
    # the larger coefficient and split the Cauchy integral at 2/h.
    h = QQ(1)/2500
    R_cut = 2/h
    loss_capacity = (F(h)*F(1+4*R_cut**2).log()/2+F(2/R_cut))/(2*F.pi())
    loss_price = F(2*h)*(E(0)*T).sqrt()
    near = F(min(floor_same, floor_opp))-loss_capacity-loss_price
    assert near > F(QQ(7)/10000)
    print('Joint pair:', (s,s+d), '; same/opposite sign slack at least',
          floor_same, floor_opp, '; neighborhood radius', h, 'slack', near, flush=True)


def certify_box(a, b, l, r):
    # The scalar mask gap is bounded below by C(d)-price(s,d). For each
    # choice of sign and endpoint eta, interpolate the corresponding smooth
    # gap at the four corners; price itself need not be differentiable.
    stack = [(a, b, l, r, 0)]
    checked = 0
    while stack:
        a0, b0, l0, r0, depth = stack.pop()
        es = T*F((b0-a0)**2/8)
        ed = (cap_curv+(1+ETA)*T/2)*F((r0-l0)**2/8)
        if all(capacity(d)-price(s, d)-tail-es-ed > slack
               for s in (a0, b0) for d in (l0, r0)):
            checked += 1
        else:
            assert depth < 25, (a0, b0, l0, r0)
            if es > ed:
                s = (a0+b0)/2
                stack += [(a0, s, l0, r0, depth+1), (s, b0, l0, r0, depth+1)]
            else:
                d = (l0+r0)/2
                stack += [(a0, b0, l0, d, depth+1), (a0, b0, d, r0, depth+1)]
    print('Mask box:', (a, b), (l, r), (-ETA, ETA), '; slack >', slack,
          '; certified boxes:', checked, flush=True)


def finite_sup(f, a, b):
    """Bound |f| by its grid chord and the second derivative bound T."""
    n = int((b-a)*64)
    assert n > 0
    h = (b-a)/n
    return F(max(abs(f(a+j*h)).upper() for j in range(n+1)))+T*F(h*h/8)


def exponential_tail(f, a, quadratic):
    """Bound |f(a+v)| for v>=0 when e^(v/2) f(a+v) is polynomial."""
    p0 = f(a)
    p1 = F(QQ(1)/2).exp()*f(a+1)
    p2 = (F(1).exp()*f(a+2)-2*p1+p0)/2 if quadratic else F(0)
    # v^j exp(-v/2) <= (2j/e)^j <= (2j)^j for j>0.
    return abs(p0)+2*abs(p1-p0-p2)+16*abs(p2)


# S(t) is a pure exponential to the left of -2*z[-1], and an
# exponential times a quadratic to the right of -2*z[0]. E is even,
# and an exponential times a linear polynomial to the right of D.
left, right = -2*z[-1], -2*z[0]
s_left = abs(S(left))
s_right = exponential_tail(S, right, True)
e_right = exponential_tail(E, D, False)


def S_sup(a):
    if a == 0:
        v = finite_sup(S, left, right)
    else:
        v = max(finite_sup(S, left, -a).upper(), finite_sup(S, a, right).upper())
    return max(F(v).upper(), s_left.upper(), s_right.upper())


S_all, S_5, S_14 = (S_sup(QQ(a)) for a in (0, 5, 14))
E_10 = max(finite_sup(E, QQ(10), D).upper(), e_right.upper())
print('Supremum bounds |S| (all, |s|>=5, |s|>=14), |E| (t>=10, tail):',
      S_all, S_5, S_14, E_10, e_right, '; E tail starts at', D, flush=True)
assert V0-F(S_all) > F(QQ(1)/1000)

# Any d>=10 puts at least one of s,s+d outside (-5,5). Use the
# sum of the absolute nonconstant Fourier coefficient factors, 1/2.
C_far = (2/F.pi())*(V0-F(-5).exp()-F(E_10))
assert C_far-((1+ETA)*F(S_all)+(1-ETA)*F(S_5))/2 > slack

# For d>=28, for BOTH signs and ANY coefficient ratio, place the
# larger absolute coefficient first and normalize a+|b|=1. The
# capacity is >= a*V0-|b|*|exp(-d/2)-E(d)| by |a+b*exp(idx)| >=
# a+b*cos(dx). At least one translate has absolute value >=14.
assert QQ(28) >= D
assert (V0-F(S_all)-F(-14).exp()-e_right-F(S_14))/2 > slack

# For d in [11/5,10] and s outside [-15,5], both translates are
# outside (-5,5). This coarse capacity bound uses only the k=0 term
# minus the absolute sum, with |E(t)| bounded on [11/5,infinity).
d0, d1 = QQ(11)/5, QQ(10)
# A simple alternative for this tail is |cos| >= cos^2, and
# int cos^2(dx/2) (1-|m|^2) dmu >= (V0-|E(d)|)/2.
E_d0 = max(finite_sup(E, d0, D).upper(), e_right.upper())
assert (V0-F(E_d0))/2-F(S_5) > slack

if hard_pair:
    certify_joint_pair(QQ(0))
    certify_joint_pair(QQ(4)/25)
else:
    certify_box(-QQ(1)/20, QQ(1)/20, DMIN, d0)
certify_box(-QQ(15), QQ(5), d0, d1)
print('Capacity nodes:', capacity.cache_info().currsize, '; Fourier tail:', tail, flush=True)
