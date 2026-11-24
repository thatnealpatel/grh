"""Check a common lower witness against weighted frontier tangent prices."""
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
from runpy import run_path

import numpy as np
from sage.all import QQ


p = run_path(str(Path(__file__).with_name('refined-prices-33.py')))
z, s, F = (p[k] for k in ('z', 's', 'F'))
SETS = (tuple((0, 2, 4, 6, k) for k in range(8, 17, 2))
        + ((0, 2, 4, 8, 10), (0, 2, 4, 8, 12)))
CASES = ('eight-knots', 'six-knots', 'seven-two-negative', 'seven-minus-216',
         'seven-minus-2304', 'seven-nonnegative', 'five-releases',
         'five-release-minus-216', 'five-release-minus-2304')
DEN = 6400
TAIL = [*range(2320, 5200, 2), *range(5200, 8800, 4),
        *range(8800, 12800, 8), *range(12800, 16000, 16),
        *range(16000, 19200, 32), 19200]
BASE = [int(t*400) for t in z[:-1]] + TAIL
SPANS = {int(400*t): range(int(DEN*t)+1, int(DEN*r))
         for t, r in zip(z, z[1:]) if any(int(400*t) in row for row in SETS)}
EXTRA = sorted(j for span in SPANS.values() for j in span)
BASE_FINE = [j*(DEN//400) for j in BASE]


def primitives(case):
    data, center, _, constant = p['tangent_data'](p['load_certificate'](case))
    coeff = {}
    for mesh, den in ((BASE, 400), (EXTRA, DEN)):
        a, b, *_ = s['tail_data'](z, center, data, mesh, den, primitive=True)
        coeff.update((j*(DEN//den), (a0, b0)) for j, a0, b0 in zip(mesh, a, b))
    # U=1/sqrt(2) and A=B=0 after the last knot.
    return constant+s['step'](QQ(BASE[-1])/400, 0)/F(2).sqrt(), coeff


def atom(a, b, m):
    # Floating point only selects an atom. The actual test evaluates the
    # resulting rational on the rigorous primitive differences below.
    a, b, m = float(a), float(b), float(m)
    roots = np.roots([-192*b, 0, 192*b, 0, -4*a-36*b, m])
    sites = [0., 1.]+[v.real for v in roots if abs(v.imag)<1e-8 and 0<v.real<1]

    def score(u):
        x = 2*u*u-1
        return m*u-a*x-b*x*(4*x*x-3)

    u = QQ(round(max(sites, key=score)*10**12))/10**12
    assert 0 <= u <= 1
    x = 2*u*u-1
    return u, x, x*(4*x*x-3)


def witnesses(coeff):
    xs = tuple(QQ(w)/1000 for w in (399, 250, 351))
    assert sum(xs) == 1
    shifts = ((QQ(1)/10**14, 0), (QQ(1)/10**14, -QQ(1)/10**15),
              (QQ(31623)/10**18, -QQ(1)/10**14))
    result = []
    for row in SETS:
        nodes = sorted(BASE_FINE + [j for k in row for j in SPANS[k]])
        assert len(nodes) == len(set(nodes))
        a, b = zip(*(coeff[j] for j in nodes))
        m = [s['step'](QQ(j)/DEN, 0) for j in nodes]
        w = [2*(-F(j)/(2*DEN)).exp() for j in nodes]
        terms = []
        for i, (l, r) in enumerate(zip(nodes, nodes[1:])):
            dm = m[i]-m[i+1]
            dw = w[i]-w[i+1]
            da, db = a[i]-a[i+1], b[i]-b[i+1]
            atoms = [atom(da+pa*dw/s['Ct'], db+pb*dw/s['C'], dm)
                     for pa, pb in shifts]
            u, x, y = (sum(p*v for p, v in zip(xs, values)) for values in zip(*atoms))
            terms.append((l, r, dm*u, dw, x, y))
        result.append(terms)
    return result


def prices(table, profiles):
    c, coeff = table
    return [c+sum(m-(coeff[l][0]-coeff[r][0])*x-(coeff[l][1]-coeff[r][1])*y
                  for l, r, m, _, x, y in terms) for terms in profiles]


if __name__ == '__main__':
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--jobs', type=int, default=1)
    args = parser.parse_args()
    with ProcessPoolExecutor(max_workers=args.jobs) as pool:
        tables = list(pool.map(primitives, CASES))
    profiles = witnesses(tables[0][1])
    # The common profiles satisfy both first caps at zero, but do not
    # satisfy the continuous cap. Test the A field at frequency one.
    K = s['K']
    for row, terms in zip(SETS, profiles):
        a0 = sum(dw*x for _, _, _, dw, x, _ in terms)/s['Ct']
        b0 = sum(dw*y for _, _, _, dw, _, y in terms)/s['C']
        v = K(-QQ(1)/2, 1)
        h = [K(v*QQ(j)/DEN).exp() for j in [terms[0][0]]+[t[1] for t in terms]]
        a1 = abs(sum((p-q)*x for p, q, (_, _, _, _, x, _) in zip(h, h[1:], terms))
                 /(-v*s['Ct']))
        print('First fields: A(0), B(0), |A(1)|', row, a0, b0, a1, flush=True)
        assert abs(a0) < 1 and abs(b0) < 1 and a1 > 1
    for case, table in zip(CASES, tables):
        row = prices(table, profiles)
        print(case, *row, flush=True)
        assert all(v > QQ(5)/10**10 for v in row)
