"""Price the fixed long-cutoff witness: sage .godel/bob/check-five-shift-long-cutoff.py.

Inputs: single-shift-10-2.txt (slab law) and joint-refit-10-2.txt (five
measured terms at 3t). Values are for the limiting comparison, under the
specified second-endpoint completion, not for actual failure conductors.
"""
from bisect import bisect_right
from collections import defaultdict
from functools import cache
from pathlib import Path

from sage.all import CyclotomicField, PolynomialRing, QQ, RealBallField, ZZ

if not __debug__:
    raise SystemExit('Run with assertions enabled.')
base = Path('.godel/bob')
F = RealBallField(128)
c = QQ(39)/20
C1, C2 = F(c).cosh()/3, F(2*c).cosh()/3


def rows(name):
    for line in (base/name).read_text().splitlines():
        if line := line.split('#', 1)[0].strip():
            yield list(map(int, line.split()))


# At t, write r=|m|. Before rotation, the j-th moment is the first
# sum below plus r times the second, both divided by 12. Rotation only
# multiplies this by a unit phase to power j. The accepted cap allows this
# law; no numerical evaluation of m or of the finite t masks is necessary.
zeta = CyclotomicField(24).gen()
roots = [zeta**(2*k+1) for k in range(12)]
for j in range(11):
    assert sum(v**j for v in roots) == (12 if j == 0 else 0)
    assert -sum(v**j*(v+1/v) for v in roots) == (-12 if j == 1 else 0)
print('Q_t = 0 exactly (all nine retained moment orders vanish).')

# B=E[4X^3-3X] with B=0 below -8 and the last slab extended to +infinity.
# Store the levels with a common integer denominator for exact convolution.
knots, levels = [], []
M = 10**8
scale = ZZ(M)**4
for knot, *fields in rows('single-shift-10-2.txt'):
    assert fields and len(fields) % 2 == 0
    atoms, masses = fields[::2], fields[1::2]
    assert all(-M <= a <= M for a in atoms)
    assert all(p > 0 for p in masses) and sum(masses) == M
    knots.append(knot)
    levels.append(ZZ(sum(p*(4*a**3-3*a*M**2) for a, p in zip(atoms, masses))))
assert len(knots) == 152 and knots[0] == -512 and knots[-1] == 1024
assert all(i < j for i, j in zip(knots, knots[1:]))

# Fourier method: with w=1/2+ix, G_B=sum(Delta B_j exp(-z_j/2)
# exp(i z_j x))/w, and S_s=Re int exp(isx) G_B^2 dmu. The kernel of
# w^(-3)*conj(w)^(-1) is (1+v_++v_+^2/2)exp(-|v|/2).
jumps = [(k, v-u) for k, v, u in zip(knots, levels, [0]+levels) if v != u]
pair = defaultdict(ZZ)
for i, (j, b) in enumerate(jumps):
    for k, b_other in jumps[:i+1]:
        pair[j+k] += (1 if j == k else 2)*b*b_other


@cache
def decay(x):
    return F(-x).exp()


def fourier(s):
    total = F(0)
    for grid, weight in pair.items():
        t = QQ(grid)/64
        v = t+s
        up = max(v, QQ(0))
        total += F(weight/scale**2*(1+up+up**2/2))*decay((t+abs(v))/2)
    # P_{2,3t}(exp(isx)): minus the C2-weighted moment m^2, m=-G_B/C1.
    return -C2/C1**2*total


# Physical method: refine the original slabs, not their jumps, to cells
# of length d. For a cell pair of indices i,j, the overlap length at
# r=2*start+n*d+v (0<=v<=d) is v if i+j=n, d-v if i+j=n-1, and 0
# otherwise. Thus the product of the two level lists gives the exact
# affine B*B on each cell, including any cell crossed by the ramp knot.
d = QQ(1)/64
start, end = 2*knots[0]*d, 2*knots[-1]*d
N = ZZ((end-start)/d)
R = PolynomialRing(ZZ, 'T')
cell = R([levels[bisect_right(knots, knots[0]+i)-1] for i in range(N+1)])
conv = cell**2
p = PolynomialRing(QQ, 'v').gen()
prev = ZZ(0)
segments = []
for n in range(N):
    b = conv[n]
    segments.append((start+n*d, (prev*d+(b-prev)*p)/scale**2))
    prev = b

# Beyond end=32 the compact part on [-8,16) has no self-overlap.
# The two compact x constant terms integrate over the whole compact part;
# constant x constant gives the linear term. Integrate this tail to infinity.
area = sum(v*(j-i)*d for v, i, j in zip(levels, knots, knots[1:]))
tail = (2*levels[-1]*area+levels[-1]**2*p)/scale**2
assert tail(0) == prev*d/scale**2
assert tail.derivative()(0) == (conv[N]-prev)/scale**2


def primitive_poly(poly):
    # -exp(-r)*(P+P'+P''+P''')(r-a) integrates exp(-r)*P(r-a).
    return poly + poly.derivative() + poly.derivative(2) + poly.derivative(3)


def physical(s):
    """Unscaled translate integral of h2(r+s) against the endpoint profile."""
    total = F(0)
    for a, density in segments:
        lo = max(0, -s-a)
        if lo >= d:
            continue
        u = a+s+p
        A = primitive_poly(density*(u**2/2-u))
        total += F(A(lo))*decay(a+lo)-F(A(d))*decay(a+d)
    assert end+s > 0
    u = end+s+p
    A = primitive_poly(tail*(u**2/2-u))
    total += F(A(0))*decay(end)
    return -C2/C1**2*total


support = [(l, h) for l, _, _, h in rows('joint-refit-10-2.txt') if h]
assert support == [(-9, -3586236), (5, -5334370), (19, -4303249),
                   (33, -4283501), (55, 1317896)]
q_fourier, q_physical = F(0), F(0)
tol = F(QQ(1)/10**32)
for l, h_int in support:
    s, h_l = QQ(l)/25, QQ(h_int)/10**10
    norm = decay(s/2)  # e^{-l/50}, used exactly once for the physical spline.
    multiplier = -C1/C2*h_l
    spline = multiplier*norm
    trace, radial = fourier(s), physical(s)
    assert abs(trace-norm*radial) < tol, (l, trace, norm*radial, trace-norm*radial)
    term, term_physical = multiplier*trace, spline*radial
    assert term*h_l > 0 and term_physical*h_l > 0
    q_fourier += term
    q_physical += term_physical
    print(f'l={l:3d}  shift={s}  10^10*h_l={h_int}  spline coefficient={spline}')
    print(f'  P2 Fourier={trace}  P2 normalized physical={norm*radial}')
    print(f'  Q_3 term Fourier={term}  physical={term_physical}')

assert abs(q_fourier-q_physical) < tol
lo = QQ(-886217000725063753759034113045)/10**33
hi = lo+QQ(1)/10**33
assert lo < q_fourier < hi and lo < q_physical < hi
assert hi < -QQ(884)/10**8
print('Q_3 Fourier:', q_fourier)
print('Q_3 physical:', q_physical)
print('Fourier and physical agree within 1e-32 at all five shifts; Q_t+Q_3 < -8.84e-6.')
