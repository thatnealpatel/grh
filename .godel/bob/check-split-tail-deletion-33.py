"""Ball-arithmetic dual prices for the six-pair family at depth 39/20."""
from pathlib import Path
from runpy import run_path

from sage.all import QQ

if not __debug__:
    raise SystemExit('Run with assertions enabled.')
base = Path(__file__).resolve().parent
old = run_path(str(base/'check-unfolded-deletion-33.py'))
F, K, Ct, jumps, step = (old[k] for k in ('F', 'K', 'Ct', 'jumps', 'step'))
laws = base/'deletion-laws'
z, A, B, U = old['lattice']['prime_rows']((laws/'delete-33-unfolded-seed.txt').read_text())

# Rational nominations (lambda, frequency, Re p, Im p) from a tangent-cut LP.
# There is no assumption of dual feasibility, unit length, or exact optimality.
UNSPLIT = '''
.054838140373 0 1 0
.040002757263 .6 .999768850999 -.021499873792
.008433803348 1.7 .997943943699 -.064092786139
.016406097067 1.687927413947 .997975240819 -.063603606132
.025368662005 .608598101173 .999762413343 -.021797175654
'''
SPLIT = '''
.029335140908 .25 .999960069632 -.008936394205
.012865685032 .9 .999470029486 -.032552421715
.005487635215 1.85 .997528879059 -.070257636189
.060466485853 .226715358878 .999967260446 -.008091849967
.025382199230 .925337899475 .999438513356 -.033506089313
.011863104419 1.863318925490 .997489844884 -.070809669910
'''


def harmonic(u):
    x = 2*u*u-1
    return x, 4*x**3-3*x


def mass(l, r):
    return step(l, 0)-(0 if r is None else step(r, 0))


def directions(split):
    ans = []
    seen = set()
    rows = (laws/'delete-33-six.pairs').read_text().splitlines()
    assert len(rows) == 6 and z[0] == -QQ(112)/25 and z[-1] == QQ(22)/5
    for row in rows:
        knot, i, j, _ = map(int, row.split())
        assert 0 <= i < j <= 10**9 and knot not in seen
        seen.add(knot)
        l = QQ(knot)/400
        k = z.index(l)
        i, j = QQ(i)/10**9, QQ(j)/10**9
        x, b = harmonic(i)
        y, d = harmonic(j)
        p = (B[k]-d)/(b-d)
        assert 0 <= p <= 1 and p*b+(1-p)*d == B[k]
        da = p*x+(1-p)*y-A[k]
        du = p*i+(1-p)*j-U[k]
        if k < len(z)-1:
            assert z[k+1] <= 0
            ans.append((l, z[k+1], da, du))
        elif split is None:
            ans.append((l, None, da, du))
        else:
            assert l < split
            ans.extend([(l, split, da, du), (split, None, da, du)])
    return ans


def price(split, cuts, upper):
    ds = directions(split)
    residual = [mass(l, r)*du for l, r, _, du in ds]
    surplus = sum(mass(l, r)*u for l, r, u in zip(z, z[1:]+[None], U))-F(8)/9
    coeff = jumps(z, A, Ct)
    for line in cuts.strip().splitlines():
        lam, x, c, s = map(F, line.split())
        assert lam >= 0
        p = K(c, s)
        w = K(QQ(1)/2, x)
        seed_field = sum(v*K(0, x*t).exp() for t, v in zip(z, coeff))/w
        surplus += lam*(abs(p)-(p.conjugate()*seed_field).real())
        for j, (l, r, da, _) in enumerate(ds):
            outer = 0 if r is None else (-w.conjugate()*r).exp()
            response = F(da)*((-w.conjugate()*l).exp()-outer)/(w*Ct)
            residual[j] -= lam*(p.conjugate()*response).real()
    # For arbitrary fractions q_j in [0,1], a residual r_j costs at most max(0,r_j).
    correction = sum(max(0,r.upper()) for r in residual)
    print('Split:', split, 'Residual allowance:', correction, 'Upper surplus:', surplus+F(correction),flush=True)
    assert surplus+F(correction) < F(upper)


if __name__ == '__main__':
    price(None, UNSPLIT, '-.0000026734')
    price(QQ(27)/5, SPLIT, '-.0000026688')
