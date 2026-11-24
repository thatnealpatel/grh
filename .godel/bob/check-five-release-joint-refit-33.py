"""Bracket one moved-cut price on the five measurable delete-33 releases."""
import argparse
from hashlib import sha256
import json
from itertools import combinations
from pathlib import Path
from runpy import run_path

from sage.all import QQ

base = Path(__file__).resolve().parent
p = run_path(str(base/'refined-prices-33.py'))
z, s, F = (p[k] for k in ('z', 's', 'F'))
DEN = 25600
SITES = (0, 2, 4, 6, 16)
TAIL = [*range(2320, 5200), *range(5200, 8800, 2),
        *range(8800, 12800, 4), *range(12800, 16000, 8),
        *range(16000, 22400, 16), 22400]
EPS = F('1e-17')


def support(a, b, m):
    # bern_upper stores a lower value at an actual evaluated atom and
    # returns that value + eps after proving the upper via subdivision.
    upper = s['bern_upper'](a, b, m, EPS)
    return upper-EPS, upper


def mesh_brackets(data, center, constant):
    # All unchanged finite slabs and the step tail through 56 share their
    # primitive evaluations. Only the five finite releases change mesh.
    base_pts = [int(t*400) for t in z[:-1]]+TAIL
    points = [j for k in SITES for j in range(k*(DEN//400)+1, (k+2)*(DEN//400))]
    pts = {}
    for mesh, den in ((base_pts, 400), (points, DEN)):
        a, b, *_ = s['tail_data'](z, center, data, sorted(mesh), den, primitive=True)
        pts.update((j*(DEN//den), (aa, bb, s['step'](QQ(j)/den, 0)))
                   for j, aa, bb in zip(sorted(mesh), a, b))

    def integrate(nodes):
        lo, hi = F(0), F(0)
        for l, r in zip(nodes, nodes[1:]):
            v, w = support(*(x-y for x, y in zip(pts[l], pts[r])))
            lo += v
            hi += w
        return lo, hi

    fixed = [j*(DEN//400) for j in base_pts]
    # After 56 both laws here are the SAME reference step law. In
    # particular, the coarse upper is for this fixed remote law only.
    A, B, U = s['unfold']['lattice']['prime_rows'](p['ref'].decode())[1:]
    a, b, m = pts[fixed[-1]]
    offset = constant+m*U[-1]-a*A[-1]-b*B[-1]
    for den in (3200, DEN):
        step = DEN//den
        nodes = sorted(fixed+[j for k in SITES
                              for j in range(k*(DEN//400)+step, (k+2)*(DEN//400), step)])
        lo, hi = integrate(nodes)
        print('Mesh bracket', den, offset+lo, offset+hi, flush=True)
        if den == 3200:
            assert F('-1.6223e-10') < offset+lo and offset+hi < F('-1.6214e-10')
        else:
            assert F('6.2475e-10') < offset+lo and offset+hi < F('6.2485e-10')

    for k in SITES:
        l, r = k*(DEN//400), (k+2)*(DEN//400)
        a, b = integrate(range(l, r+1, DEN//3200))
        c, d = integrate(range(l, r+1))
        print('Gain on refinement', k, c-b, d-a, flush=True)
    return {k: tuple((x-y)*200 for x, y in zip(pts[k*(DEN//400)],
                                                pts[(k+2)*(DEN//400)]))
            for k in SITES}


def control(a, b, c):
    return 2*b-(a+c)/2


def release_prices(data, center, means):
    den = 12800
    h = QQ(1)/den
    assert den % 400 == 0  # All kernel branch points are on the original lattice.
    nodes = {k: range(2*k*(den//400), 2*(k+2)*(den//400)+1) for k in SITES}
    pts = sorted(set(j for span in nodes.values() for j in span))
    a, b, *_ = s['tail_data'](z, center, data, pts, 2*den)
    m = [F(j)/(2*den)*(-F(j)/(2*den)).exp() for j in pts]
    values = dict(zip(pts, zip(a,b,m)))
    neg = p['neg']
    scale = neg['curved_error'](z, center, data, den)/(2*((-F(z[0])/2).exp()-1))
    scale += 3*h**3*F(h/2).exp()/192
    out = []
    for k, span in nodes.items():
        _, bv, mv = means[k]
        rem = 2*scale*((-F(k)/800).exp()-(-F(k+2)/800).exp())
        data0 = [values[j] for j in span]
        row = []
        # Flatten one coefficient at a time. The same error envelope
        # works: The constant coefficient has vanishing derivatives.
        for samples in (data0, [(a,bv,m) for a,b,m in data0],
                        [(a,b,mv) for a,b,m in data0]):
            ends = [support(*v)[1] for v in samples[::2]]
            controls = [support(*(control(*v) for v in zip(*samples[j-1:j+2])))[1]
                        for j in range(1,len(samples),2)]
            row.append(h*(2*sum(ends)-ends[0]-ends[-1]+sum(controls))/3+rem)
        out.append(row)
        print('Free, mean B, mean U', k, *row, flush=True)
    return list(zip(*out))


def self_test():
    for l, r in ((QQ(-2), QQ(1)), (QQ(2)/3, QQ(7)/8)):
        f = lambda x: x*x-x+1
        assert (f(l)+control(f(l),f((l+r)/2),f(r))+f(r))*(r-l)/3 == (
            (r**3-l**3)/3 - (r**2-l**2)/2+r-l)
    # A realizing law with u=0 then u=1 on the two halves of [0,1].
    # The signed covariance with density t is negative for -bB,
    # positive for mU, and zero for the constant profile.
    spans = [(QQ(0), QQ(1)/2, QQ(0)), (QQ(1)/2, QQ(1), QQ(1))]
    change = lambda g: sum(((r*r-l*l)/2-(r-l)/2)*g(u) for l, r, u in spans)
    assert change(lambda u: -(2*u*u-1)) == -QQ(1)/4
    assert change(lambda u: u) == QQ(1)/8
    assert change(lambda _: QQ(1)) == 0
    # Endpoint and interior optima, including the actual nonmonotone T.
    for a, b, m, exact in [(F(3), F(0), F(0), F(3)),
                           (F(-1), F(1), F(0), 8/(3*F(3).sqrt())),
                           (F(1), F(0), F(2), F(3)/2)]:
        lo, hi = support(a, b, m)
        assert lo-EPS < exact < hi+EPS and abs(hi-lo-EPS) < F('1e-35')
    print('Interpolation, signed covariance, and atom bracket checks passed', flush=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--self-test', action='store_true')
    opt = ap.parse_args()
    self_test()
    if opt.self_test:
        return
    raw = (p['laws']/'delete-33-five-release-joint-refit.json').read_bytes()
    assert sha256(raw).hexdigest() == '0b288072bc772e52fc7fb42aea4ca8544cc2d5e40d90e19d1d18e2de47bb54e2'
    cert = json.loads(raw, parse_float=str)
    old = p['load_certificate']('eight-knots')
    assert [r[:2] for r in cert['cuts'] if len(r)==5] == [r[:2] for r in old['cuts'] if len(r)==5]
    assert [r[:2] for r in cert['cuts'] if len(r)==3] == [r[:2] for r in old['cuts'] if len(r)==3]
    assert all(t+QQ(2)/400 in z and z[z.index(t)+1]==t+QQ(2)/400 for t in (QQ(k)/400 for k in SITES))
    data, center, _, constant = p['tangent_data'](cert)
    means = mesh_brackets(data, center, constant)
    _, original, old, _ = p['mesh_prices'](data, center, constant, 400, [], 60, tail_den=800)
    outside = original-sum(old[QQ(k)/400] for k in SITES)
    free, fixed_b, fixed_u = release_prices(data, center, means)
    upper = outside+sum(free)
    print('Full measurable upper', upper, flush=True)
    assert upper < F('7.2e-10')

    base_b = outside+sum(fixed_b)
    print('All B coefficients flattened', base_b, flush=True)
    assert base_b < F('-6.5e-10')
    for j, k in enumerate(SITES):
        bound = upper-free[j]+fixed_u[j]
        print('One U flattened', k, bound, flush=True)
        assert bound < F('-1.7e-8')
    for size in (1, 2):
        for js in combinations(range(len(SITES)), size):
            bound = base_b+sum(free[j]-fixed_b[j] for j in js)
            ks = tuple(SITES[j] for j in js)
            print('Only these B coefficients unflattened', ks, bound, flush=True)
            if ks != (4, 6):
                assert bound < 0
            else:
                assert bound < F('8e-11')


if __name__ == '__main__':
    main()
