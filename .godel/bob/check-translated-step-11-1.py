"""Replay with `sage .godel/bob/check-translated-step-11-1.py` (no -O)."""
from math import comb, factorial
from pathlib import Path

from sage.all import ComplexBallField, QQ, RealBallField

if not __debug__:
    raise SystemExit('Run without -O.')

F = RealBallField(128)
K = ComplexBallField(128)
S = 10**10


def load_laws():
    path = Path('.godel/bob/translated-step-11-1.txt')
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        knot, *fields = map(int, line.split())
        assert fields and len(fields) % 2 == 0
        xs, ps = fields[::2], fields[1::2]
        assert all(-S <= x <= S for x in xs)
        assert all(p > 0 for p in ps) and sum(ps) == S
        yield QQ(knot)/1024, [(QQ(x)/S, QQ(p)/S) for x, p in zip(xs, ps)]


z, laws = map(list, zip(*load_laws()))
assert z[0] == -8 and 0 in z and z[-1] == 16
assert all(l < r for l, r in zip(z, z[1:]))

# Before the first knot, take the point mass at zero. On every slab,
# derive both profiles and the failure mean from the same law.
A = [sum(p*x for x, p in law) for law in laws]
B = [sum(p*(4*x**3-3*x) for x, p in law) for law in laws]
assert all(-1 <= v <= 1 for v in A+B)
U = [sum(p*F((1+x)/2).sqrt() for x, p in law) for law in laws]
weight_tail = [(1+t)*F(-t).exp() for t in z] + [F(0)]
weights = [weight_tail[j]-weight_tail[j+1] if t >= 0 else F(0)
           for j, t in enumerate(z)]
mean_margin = sum(w*u for w, u in zip(weights, U))-F(QQ(8)/9)
assert mean_margin > F(QQ(7)/10**5)
print('angular mean minus 8/9:', mean_margin, flush=True)
third = sum(w*b for w, b in zip(weights, B))
print('unshifted short third-harmonic price:', third, flush=True)


def certify_cap(label, profile, rational_cap, cutoff):
    cap = F(rational_cap)
    slack = cutoff - cap
    assert slack > 0
    b = [(v-u)*F(-t/2).exp() for t, v, u in zip(z, profile, [QQ(0)]+profile)]
    # Center the jump polynomial at z=-2, up to a unit phase.
    times = [t+2 for t in z]
    Bk = [sum(abs(v)*F(abs(t)**k) for t, v in zip(times, b)) for k in range(5)]
    X = QQ(64)
    assert Bk[0]/X < cap

    def phases(x):
        return [K(0, -t*x).exp() for t in times]

    for x in (QQ(0), QQ(17)/4, QQ(13)):
        w = K(QQ(1)/2, x)
        edges = [(-w*t).exp() for t in z] + [K(0)]
        slab = sum(v*(l-r) for v, l, r in zip(profile, edges, edges[1:]))/w
        jump = K(0, 2*x).exp()*sum(v*p for v, p in zip(b, phases(x)))/w
        assert abs(slab-jump) < F(QQ(1)/10**30)

    # Fourth derivative of Q=|N|^2-cap^2*(1/4+x^2), via the product rule.
    M4 = sum(comb(4, k)*Bk[k]*Bk[4-k] for k in range(5))
    coeffs = [[K(v)*K(0, -t)**k for t, v in zip(times, b)] for k in range(4)]
    cap2 = cap**2

    def passes(mid, radius):
        p = phases(mid)
        nd = [sum(v*w for v, w in zip(row, p)) for row in coeffs]
        nc = [v.conjugate() for v in nd]
        radial = [F(QQ(1)/4+mid**2), F(2*mid), F(2), F(0)]
        q = [sum(comb(k, j)*(nd[j]*nc[k-j]).real() for j in range(k+1))
             - cap2*radial[k] for k in range(4)]
        r = F(radius)
        upper = q[0] + sum(abs(q[k])*r**k/factorial(k) for k in range(1, 4))
        return upper + M4*r**4/24 < 0

    stack = [(QQ(0), X, 0)]
    boxes = 0
    while stack:
        lo, hi, depth = stack.pop()
        mid = (lo+hi)/2
        if passes(mid, (hi-lo)/2):
            boxes += 1
        else:
            assert depth < 24, (label, lo, hi)
            stack.extend([(lo, mid, depth+1), (mid, hi, depth+1)])
    print(label, 'jump tail bound at', X, ':', Bk[0]/X, flush=True)
    print(label, 'all-frequency cap:', cap, '; finite boxes:', boxes, flush=True)
    print(label, 'depth-1.95 cutoff slack:', slack, flush=True)


c = F(QQ(39)/20)
cap_A = QQ(615455)/10**6
cap_B = QQ(119512)/10**5
assert cap_A < QQ(615464415)/10**9 and cap_B < QQ(1195160275)/10**9
certify_cap('A', A, cap_A, c.cosh()/(6*(F.pi()/13).cos()))
certify_cap('B', B, cap_B, c.cosh()/3)
