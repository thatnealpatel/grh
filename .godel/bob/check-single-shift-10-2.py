"""Replay the common all-single-shift witness with `sage .godel/bob/check-single-shift-10-2.py`."""
from math import comb, factorial
from pathlib import Path

from sage.all import ComplexBallField, QQ, RealBallField

if not __debug__:
    raise SystemExit('Run with assertions enabled.')
F = RealBallField(128)
K = ComplexBallField(128)

# Right-continuous slab laws for X=cos(theta); X=0 to the left of z[0].
DATA = Path('.godel/bob/single-shift-10-2.txt')
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
    z.append(QQ(knot)/64)
    laws.append([(QQ(a)/SCALE, QQ(p)/SCALE) for a, p in zip(atoms, masses)])
assert len(z) == 152 and z[0] == -8 and 0 in z and z[-1] == 16
assert all(l < r for l, r in zip(z, z[1:]))

A = [sum(p*a for a, p in law) for law in laws]
B = [sum(p*(4*a**3-3*a) for a, p in law) for law in laws]
U = [sum(p*F((1+a)/2).sqrt() for a, p in law) for law in laws]
assert all(-1 <= y <= 1 for y in A+B)
wt = [(1+t)*F(-t).exp() if t >= 0 else F(1) for t in z] + [F(0)]
mean_margin = sum((l-r)*u for l, r, u in zip(wt, wt[1:], U))-F(QQ(8)/9)
assert mean_margin > F(QQ(652)/10**8)
print('Angular surplus:', mean_margin, flush=True)

c = F(QQ(39)/20)
C1 = c.cosh()/3
C10 = C1/(2*(F.pi()/12).cos())
cap_A, cap_B = QQ(61864)/10**5, QQ(96)/100
assert cap_A < C10 and cap_B < C1


def jump_terms(profile):
    return [(t, F(y-v)*F(-t/2).exp()) for t, y, v in zip(z, profile, [QQ(0)]+profile)
            if y != v]


def certify_cap(label, profile, cap):
    points = jump_terms(profile)
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
        edges = [(-w*t).exp() for t in z]+[K(0)]
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

# Integrate |G_B|^2 using the difference kernel. Collect sum-kernel weights
# separately to make pointwise energy evaluation at any rational s reusable.
L0 = F(0)
sum_weights = {}
points = jump_terms(B)
for i, (t, b) in enumerate(points):
    for j, (v, d) in enumerate(points[:i+1]):
        p = b*d*(1 if i == j else 2)
        h = abs(t-v)
        L0 += p*F(2+h)*F(-h/2).exp()
        sum_weights[t+v] = sum_weights.get(t+v, F(0))+p


def energies(s):
    """Return enclosing balls for the real and imaginary energies at rational shift s."""
    s = QQ(s)
    total = F(0)
    for t, b in sum_weights.items():
        v = t+s
        up = max(v, QQ(0))
        total += b*F(1+up+up**2/2)*F(-abs(v)/2).exp()
    return (L0+total)/2, (L0-total)/2


energy_cutoff = C1**2/2
assert L0 < F(QQ(70601)/10**5) < energy_cutoff
print('Total energy, both-energy cutoff, guaranteed slack:', L0, energy_cutoff,
      energy_cutoff-L0)
print('Real and imaginary energies at s=1:', *energies(1))
