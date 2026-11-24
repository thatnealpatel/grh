"""Certify simultaneous real motion and full refits of the 426 seed slabs."""
import argparse
from bisect import bisect_right
from functools import cache
from pathlib import Path
from runpy import run_path

from sage.all import QQ

if not __debug__:
    raise SystemExit('Run with assertions enabled.')
base = Path(__file__).resolve().parent
mesh = run_path(str(base/'check-mesh-deletion-33.py'))
F, K, P, C, Ct = (mesh[k] for k in ('F', 'K', 'P', 'C', 'Ct'))
seed = [QQ(k)/400 for k in mesh['seed']]
maximum = mesh['maximum']
sites = [-112, 96, 304]


@cache
def primitives():
    """Return the exact-function enclosures, constant surplus price, and third bounds."""
    cuts = []
    q = {}
    cost = F(0)
    for line in (base/'deletion-laws/delete-33-mesh.dual').read_text().splitlines()[1:]:
        tag, *data = line.split()
        if tag == 'F':
            j, i, a, b = map(int, data)
            d = K(a, -b)/10**13
            w = K(F(1)/2, F(i)/10**9)
            cuts.append((j, -w.conjugate(), d/(w*[Ct, C][j])))
            cost += abs(d)
        else:
            assert tag == 'Q'
            k, a = map(int, data)
            assert k not in q
            q[k] = F(a)/10**13
    assert sorted(q) == mesh['seed'] and len(seed) == 426 and 0 in seed
    cs, lam, rhs = mesh['majorant']()
    m = len(cs)-1
    first = min(q)-208*m
    p = P({208*(m+j): cs[abs(j)] for j in range(-m, m+1)})
    diff = (P({k-min(q): v for k, v in q.items()})*p).list()
    summ = {}
    for k, v in q.items():
        for s, l in zip(sites, lam):
            r = -k-s
            summ[r] = summ.get(r, F(0))+l*v
    assert first <= min(summ) <= max(summ) < first+len(diff)

    # At integer breakpoint k, put r=k/400, d=diff weight, b=sum weight.
    # Add this row to the left polynomial times exp(-t) if t>=r;
    # otherwise add the right affine polynomial. Store genuine suffix sums
    # to avoid subtracting exponentially large totals.
    left, right = [(F(0),)*3], [(F(0),)*2]
    rows = []
    for i, d in enumerate(diff, first):
        r = F(i)/400
        h = (r/2).exp()
        b = summ.get(i, F(0))
        rows.append(((2*d-r*d+b*(1-r+r*r/2))*h, (d+b*(1-r))*h, b*h/2,
                     (d*(2+r)+b)/h, -d/h))
    for a, b, c, _, _ in rows:
        x, y, z = left[-1]
        left.append((x+a, y+b, z+c))
    for _, _, _, a, b in reversed(rows):
        x, y = right[-1]
        right.append((x+a, y+b))
    right.reverse()

    def probe(t, order=0):
        i = int((400*t).floor())-first+1
        assert 0 <= i <= len(rows)
        a, b, c = left[i]
        d, e = right[i]
        x = F(t)
        y = (-x).exp()
        p0, p1 = a+x*(b+x*c), b+2*x*c
        return (y*p0+d+x*e, y*(p1-p0)+e, y*(2*c-2*p1+p0))[order]

    # This is evaluated at the original probe sites, not the moved knots.
    qs = sum(v*probe(QQ(k)/400)*(F(k)/800).exp() for k, v in q.items())
    assert qs > 0
    price = cost+(rhs*qs).sqrt()-F(8)/9
    third = [sum(abs(d)*abs(w)**3 for j, w, d in cuts if j == jj) for jj in (0, 1)]
    third[1] += (2*sum(map(abs, diff))+4*sum(map(abs, summ.values())))/C

    @cache
    def phi(t, order=0):
        assert order in (0, 1, 2)
        x = F(t)
        a, b = F(0), probe(t, order)/C
        field = [a, b]
        for j, w, d in cuts:
            field[j] += (d*w**order*(w*x).exp()).real()
        if t <= 0:
            W = F(int(order == 0))
        else:
            W = (-x).exp()*[1+x, -x, x-1][order]
        return (W, *field)

    return phi, price, third


def smoke(phi, price):
    """Compare with the original, independent lattice convolution and cap sums."""
    (fa, fb), cost, q = mesh['first_and_probe']()
    lin, q_price = mesh['quadratic'](q)
    tol = F('1e-24')
    assert abs(price-(cost+q_price-F(8)/9)) < tol
    for k in (mesh['lo'], 0, mesh['hi']):
        i = k-mesh['lo']
        x = F(k)/400
        W, a, b = phi(QQ(k)/400)
        z = max(x, F(0))
        assert abs(W-(1+z)*(-z).exp()) < tol
        assert abs(a-fa[i]) < tol
        assert abs(b-(fb[i]+lin[i]*(-x/2).exp()/C)) < tol
    edges = [(phi(x), phi(y)) for x, y in zip(seed, seed[1:])]
    edges.append((phi(seed[-1]), (F(0),)*3))
    fixed = price+sum(maximum(*(a-b for a, b in zip(p, q))) for p, q in edges)
    assert -F('1.85e-6') < fixed < -F('1.83e-6')
    print('fixed seed upper price', fixed, flush=True)


def path_upper(radius, cells, phi, price, third):
    assert radius > 0 and cells >= 1
    # If two windows touch, equality is a zero-width slab, with zero price.
    assert all(b-a >= 2*radius for a, b in zip(seed, seed[1:]))
    h = 2*radius/cells
    grid = [[phi(z-radius+i*h) for i in range(cells+1)] for z in seed]
    D = F(0)
    for z in seed:
        W, a, b = phi(z, 2)
        if z+radius <= 0:
            dw = F(0)
        elif z-radius <= 0:
            dw = F(1)
        else:
            dw = abs(W)+3*F(radius)
        D += dw+2*(abs(a)+abs(b)+F(radius)*(third[0]+third[1])*F((radius-z)/2).exp())
    error = D*F(h)**2/8
    scores = [F(0)]*(cells+1)
    for lo, hi in zip(grid, grid[1:]+[[(F(0),)*3]]):
        next_scores = []
        # Visit the best previous scores first to get useful pruning bounds.
        sources = sorted(zip(lo, scores), key=lambda pair: pair[1].upper(), reverse=True)
        for t in hi:
            incumbent = None
            for s, prev in sources:
                value = maximum(*(a-b for a, b in zip(s, t)), offset=prev, incumbent=incumbent)
                incumbent = value.upper()
            next_scores.append(F(incumbent))
        scores = next_scores
    return price+scores[0], error


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--radius', type=QQ, default=QQ(1)/200)
    parser.add_argument('--cells', type=int, default=40)
    parser.add_argument('--threshold', type=QQ, default=QQ(0))
    args = parser.parse_args()
    phi, price, third = primitives()
    smoke(phi, price)
    grid, error = path_upper(args.radius, args.cells, phi, price, third)
    upper = grid+error
    print(f'radius={args.radius}, cells={args.cells}, grid={grid}, chord={error}, surplus<={upper}', flush=True)
    assert upper < F(args.threshold)


if __name__ == '__main__':
    main()
