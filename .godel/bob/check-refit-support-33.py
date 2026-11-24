"""Spend the all-slabs price once, allowing the refit to choose its changed slabs."""
from hashlib import sha256
import json
from pathlib import Path
from runpy import run_path

import numpy as np
from sage.all import QQ

base = Path(__file__).resolve().parent
laws = base / 'deletion-laws'
cert = run_path(str(base / 'check-tail-deletion-33.py'))
F = cert['F']
assert __debug__
# The unaltered all-slabs price at these exact inputs is < P (6662ffc0).
P = QQ(5849)/10**12
ref = (laws / 'delete-33-tail-baseline.txt').read_bytes()
rows = (laws / 'delete-33-all-slabs-dual.json').read_bytes()
assert sha256(ref).hexdigest() == '7be0449af83f2b264894d0b0074108139ada0badc0c34a26edc6731d81baaa5c'
assert sha256(rows).hexdigest() == 'c42c34963cd2bdd081bdf9e0a2d004e4dc81211a7776472aaaa7d02b8bbfde11'
z, A, B, U = cert['unfold']['lattice']['prime_rows'](ref.decode())
assert len(z) == 1257 and z[0] == -QQ(144)/25 and z[-1] == QQ(29)/5
radii = (0, QQ(1)/1000, QQ(1)/20, QQ(1)/2)
losses = {r: [] for r in radii}
ug = np.linspace(0, 1, 10001)
xg = 2*ug**2-1
tg = 4*xg**3-3*xg


def hull(lo, hi):
    return F(lo).union(F(hi))


def bmax(a, b):
    return hull(max(a.lower(), b.lower()), max(a.upper(), b.upper()))


def bmin(a, b):
    return -bmax(-a, -b)


def T(x):
    return 4*x**3-3*x


def f(q):
    assert -1 <= q <= 1
    if q == 1:
        return F(1)
    if q == -1:
        return F(1)/2
    return (F(q).arccos()/3).cos()


def section_upper(a, beta, b0, rho):
    """Ball enclosing max(-a A-beta B), for |B-b0|<=rho in the law hull.

    b0 and rho are exact; the ball's upper endpoint is a certified price.
    """
    a, beta = F(a), F(beta)
    b0, rho = QQ(b0), QQ(rho)
    assert -1 <= b0 <= 1 and rho >= 0
    lo, hi = max(QQ(-1), b0-rho), min(QQ(1), b0+rho)
    assert lo <= b0 <= hi

    def branch(s):
        # A=s f(s B); q=s B and x=f(q). Score is C*x-d*T(x).
        C, d = -s*a, s*beta
        ql, qh = (lo, hi) if s == 1 else (-hi, -lo)
        xl, xh = f(ql), f(qh)
        gl, gh = C*xl-d*F(ql), C*xh-d*F(qh)
        if ql == qh:
            return gl
        if d > 0:
            # Concave cubic on [1/2,1]; clip its maximizer there and
            # then to the admissible x interval (also handles endpoint ties).
            ratio = bmax(F(0), bmin(F(9), C/d))
            critical = ((3+ratio)/12).sqrt()
            x = bmax(xl, bmin(xh, critical))
            return C*x-d*T(x)
        if d < 0 or d.is_zero():
            return bmax(gl, gh)  # Convex (affine if exact zero).
        # If d's sign is unresolved, the true max differs from the d=0
        # max by at most |d|, since |T(x)|<=1 on this interval.
        base, err = bmax(C*xl, C*xh), abs(d)
        return hull((base-err).lower(), (base+err).upper())

    if a < 0:
        return branch(1)
    if a > 0:
        return branch(-1)
    return bmax(branch(1), branch(-1))


# At B=0 the extreme A is sqrt(3)/2; with B free the cubic can
# also peak in the interior at X=3/4. Check both orientations.
for sign in (-1, 1):
    assert (section_upper(sign*2, 0, 0, 0)-F(3).sqrt()).contains_zero()
    assert (section_upper(sign*15, -sign*4, 0, 1)-QQ(27)/2).contains_zero()
negative = {r: [] for r in radii}


def slab_check(t, upper, a, b, m, b0):
    if t < 0:
        assert m.is_zero() and t == z[len(negative[0])]
        for r in radii:
            section = upper-section_upper(a, b, b0, r)
            bound = max(0, section.lower().exact_rational())
            negative[r].append(bound)
            losses[r].append(bound)
        return
    # The float grid only nominates a tilt h at fixed B; ANY rational h is valid.
    g = float(m)*ug-float(a)*xg-float(b)*tg
    v = tg-float(b0)
    lo, hi = -4., 4.
    for _ in range(44):
        mid = (lo+hi)/2
        if v[np.argmax(g-mid*v)] > 0:
            lo = mid
        else:
            hi = mid
    h = QQ(round(mid*10**16))/10**16
    shifted = cert['bern_upper'](a, b+h, m, F('1e-14'))
    drop = upper-shifted-h*b0
    for r in radii:
        # Exact rational lower endpoints. Zero means keep the old enclosure.
        bound = max(0, (drop-abs(h)*r).lower().exact_rational())
        losses[r].append(bound)


offset, gain, _ = cert['price'](z, A, B, U, json.loads(rows, parse_float=str),
                                 omit={z[-1]}, slab_check=slab_check)
# From the three den=4800 continuous_tail enclosures in all-slabs-deletion-33.md.
# Verify P with the very Bernstein uppers from which this run subtracted savings.
tail_upper = QQ(125112963)/10**15
assert gain[2] == 0 and offset + sum(gain) + tail_upper < F(P)


def required(savings):
    spent = 0
    for i, s in enumerate(sorted(savings)):
        spent += s
        if spent > P:
            # Even freezing the i+1 cheapest slabs within r uses too much budget.
            break
    else:
        raise AssertionError('no exclusion')
    return len(savings)-i


for r in radii:
    assert len(negative[r]) == 494 and len(losses[r]) == 1256
    nneg, nall = required(negative[r]), required(losses[r])
    print('Radius, required negative count, required overall count:', r, nneg, nall)
    assert nall >= {0: 646, QQ(1)/1000: 401, QQ(1)/20: 174, QQ(1)/2: 46}[r]
    assert nneg >= {0: 181, QQ(1)/1000: 101, QQ(1)/20: 82, QQ(1)/2: 35}[r]

# Localization is a separate test: The global counts do not force a
# change in any specified pool. The eight are from the original nine.
panel = [-880, -1072, -1312, -896, -1168, -1152, -1184, -1456,
         -1472, -1296, -1120, -684, -686, -912]
for n, count in ((8, 1), (11, 2), (14, 3)):
    assert required([negative[QQ(1)/2][z.index(QQ(t)/400)] for t in panel[:n]]) >= count
