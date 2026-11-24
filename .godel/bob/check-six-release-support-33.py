"""Replay the inherited-price obstruction for one signed six-release mask."""
import argparse
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction
import gzip
from hashlib import sha256
import json
from pathlib import Path
from runpy import run_path

from sage.all import QQ


base = Path(__file__).resolve().parent
checks = run_path(str(base/'check-five-release-disk-price-33.py'))
p, s, F = (checks[k] for k in ('p', 's', 'F'))
z, K = p['z'], s['K']
SITES = (-216, 0, 2, 4, 6, 8)
DEN = 1600
SCALE = 10**12
TAIL = [*range(2320, 5200, 8), *range(5200, 8800, 16),
        *range(8800, 12800, 32), *range(12800, 16000, 64),
        *range(16000, 22400, 128), 22400]
DIGESTS = {
    'five-release-disk-price-k8': '4150ddbca857c6d79966354328bdb8791a3818a12e8506a9aafd844e8a9cc2ee',
    'five-release-disk-price': '47a17eb53b3ec4867e3a3953a713c6978887dc4fe2632907d86a241c012e3211',
    'five-release-joint-refit': '0b288072bc772e52fc7fb42aea4ca8544cc2d5e40d90e19d1d18e2de47bb54e2',
    'five-release-pair': '595e14a39f60cf01cdf8094774bd163d94c41ba185a28fdca14bb4bc695dcdb8',
}
ANCHOR = 'five-release-disk-price-k8'
CASES = (ANCHOR, 'five-release-disk-price', 'eight-knots', 'five-releases',
         'five-release-joint-refit', 'five-release-pair', 'independent', 'recentered')


def price_data(case):
    if case in ('independent', 'recentered'):
        result = checks['r']['moved_tangent'](case == 'recentered')
    else:
        if case in DIGESTS:
            raw = (p['laws']/f'delete-33-{case}.json').read_bytes()
            assert sha256(raw).hexdigest() == DIGESTS[case]
            cert = json.loads(raw, parse_float=str)
        else:
            cert = p['load_certificate'](case)
        result = p['tangent_data'](cert)
    tests = checks['tests_of']({'cuts': result[0]})
    assert tests == checks['tests_of'](p['load_certificate']('eight-knots'))
    assert sum(j == 0 for j, _ in tests[0]) == 581
    assert sum(j == 1 for j, _ in tests[0]) == 62
    assert (0, Fraction(0)) in tests[0]
    return result


def meshes():
    assert all(t*400 == int(t*400) for t in z)
    right = dict(zip(z, z[1:]))
    assert all(right[QQ(k)/400] == QQ(k+2)/400 for k in SITES)
    assert z[-1] == QQ(TAIL[0])/400
    coarse = [int(t*400) for t in z[:-1]]+TAIL
    fine = [i for k in SITES for i in range(k*(DEN//400)+1, (k+2)*(DEN//400))]
    nodes = sorted([j*(DEN//400) for j in coarse]+fine)
    assert len(nodes) == len(set(nodes))
    return coarse, fine, nodes


def disk_vectors(data):
    W = {}
    total = F(0)
    for j, f, re, im, w in (row for row in data if len(row) == 5):
        k, u, w = (j, Fraction(f)), K(F(re), F(im)), F(w)
        W[k] = W.get(k, K(0))+w*u/abs(u)
        total += w
    return W, total


def on_profile(case):
    data, center, sigma, constant = price_data(case)
    coarse, fine, nodes = meshes()
    with gzip.open(p['laws']/'delete-33-six-release-support-witness.json.gz', 'rt') as f:
        numerators = json.load(f)
    assert len(numerators) == len(nodes)-1
    assert all(type(n) is int and 0 <= n <= SCALE for n in numerators)
    U = [QQ(n)/SCALE for n in numerators]
    X = [2*u*u-1 for u in U]
    Y = [(4*x*x-3)*x for x in X]
    ts = [QQ(j)/DEN for j in nodes]
    m = [s['step'](t, 0) for t in ts]
    assert all(v == 1 for t, v in zip(ts, m, strict=True) if t <= 0)
    if case == ANCHOR:
        e = [2*(-F(t)/2).exp() for t in ts]
        V0 = sum((a-b)*x for a, b, x in zip(e[:-1], e[1:], X, strict=True))/s['Ct']
        print('Witness A(0):', V0, flush=True)
        assert V0 > F('2.8')
    coeff = {}
    for mesh, den in ((coarse, 400), (fine, DEN)):
        a, b, *_ = s['tail_data'](z, center, data, mesh, den, primitive=True)
        coeff.update((j*(DEN//den), (x, y)) for j, x, y in zip(mesh, a, b, strict=True))
    # After 56 take delta_(1/sqrt(2)): Both field moments vanish.
    value = constant + m[-1]/F(2).sqrt()
    for i, (l, r) in enumerate(zip(nodes, nodes[1:])):
        a, b = coeff[l]
        c, d = coeff[r]
        value += (m[i]-m[i+1])*U[i]-(a-c)*X[i]-(b-d)*Y[i]
    W, total = disk_vectors(data)
    lam = list(map(F, next(row[1] for row in data if len(row) == 3)))
    return value, W, total, center, F(sigma), lam


def lower(jobs):
    with ProcessPoolExecutor(max_workers=jobs) as pool:
        rows = list(pool.map(on_profile, CASES))
    _, W0, _, Z0, _, lam = rows[0]
    assert all(abs(w) > 0 for w in W0.values())
    q = s['second_majorant'](lam)
    for case, (value, W, total, center, sigma, _) in zip(CASES, rows, strict=True):
        assert W.keys() == W0.keys()
        # Linearize each disk norm at the anchor. For center variance,
        # evaluating squared distances at Z0 bounds the optimal discount.
        disk_loss = total-sum((W[k]*w.conjugate()).real()/abs(w) for k, w in W0.items())
        J = s['jumps'](z, [x-y for x, y in zip(center, Z0, strict=True)], s['C'])
        _, G = s['second_tangent'](z, J, lam, q)
        quad_loss = sigma*sum(x*y for x, y in zip(J, G, strict=True))
        bound = value-disk_loss-quad_loss
        print(case, 'raw', value, 'disk and Q debits', disk_loss, quad_loss,
              'lower', bound, flush=True)
        assert bound > F('2.6e-8')


def upper():
    data, center, _, constant = price_data(ANCHOR)
    meshes()
    _, ordinary, old, _ = p['mesh_prices'](data, center, constant, 400, [], 60, tail_den=800)
    inc = p['costs']['release_costs'](z, center, data, old, den=DEN,
                                     sites={QQ(k)/400 for k in SITES})
    assert len(inc) == len(SITES)
    bound = ordinary+sum(inc)
    print('Ordinary upper', ordinary, 'release increments', tuple(map(float, inc)),
          'six-release upper', bound, flush=True)
    assert bound < F('3.36e-8')


def self_test():
    p['neg']['self_test']()
    a, b = s['step'](-QQ(216)/400, 0), s['step'](-QQ(214)/400, 0)
    assert (a-b).is_zero()
    assert s['step'](QQ(0), 0) > s['step'](QQ(2)/400, 0)
    W, total = disk_vectors([[0, '1', '3', '4', '5'], [0, '1.0', '0', '-1', '4']])
    assert len(W) == 1 and abs(W[0, Fraction(1)]-K(3)) < F('1e-35') and total == 9
    meshes()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--self-test', action='store_true')
    ap.add_argument('--jobs', type=int, default=1)
    args = ap.parse_args()
    self_test()
    if not args.self_test:
        lower(args.jobs)
        upper()


if __name__ == '__main__':
    assert __debug__
    main()
