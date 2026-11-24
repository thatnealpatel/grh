"""Increase E[u] on nonnegative slabs without changing the two trace inputs."""
import argparse
from fractions import Fraction
from math import lcm
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

UNIT = 10**9


def moments(site):
    x = 2 * Fraction(site, UNIT)**2 - 1
    return x, 4*x**3 - 3*x


def improve(pairs):
    atoms, counts = pairs[::2], pairs[1::2]
    vals = [moments(i) for i in atoms]
    den = sum(counts)
    a, b = (sum(w*v[t] for w, v in zip(counts, vals))/den for t in (0, 1))
    old_mean_site = Fraction(sum(i*w for i, w in zip(atoms, counts)), den)
    sites = np.unique([*(np.arange(2001)*500000), *atoms])
    u = sites/UNIT
    x = 2*u*u-1
    opt = linprog(-u, A_eq=np.array([np.ones_like(x), x, 4*x**3-3*x]),
                  b_eq=[1, float(a), float(b)], method='highs')
    ix = np.flatnonzero(opt.x > 0) if opt.success else []
    if len(ix) != 3:
        return pairs
    # Use the LP only to nominate three sites. Solve the mass, first,
    # and cubic equalities again with rational arithmetic.
    i, j, k = map(int, sites[ix])
    (x, y), (X, Y), (s, t) = map(moments, (i, j, k))
    det = (x-s)*(Y-t)-(X-s)*(y-t)
    if not det:
        return pairs
    p = ((a-s)*(Y-t)-(b-t)*(X-s))/det
    q = ((b-t)*(x-s)-(a-s)*(y-t))/det
    r = 1-p-q
    if min(p, q, r) < 0 or p*i+q*j+r*k <= old_mean_site:
        return pairs
    assert p*x+q*X+r*s == a and p*y+q*Y+r*t == b
    den = lcm(p.denominator, q.denominator, r.denominator)
    return [i, int(den*p), j, int(den*q), k, int(den*r)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('table', type=Path)
    parser.add_argument('out', type=Path)
    args = parser.parse_args()
    primes, second = args.table.read_text().split('# Second:')
    rows = []
    for line in primes.splitlines():
        if line and not line.startswith('#'):
            z, *pairs = map(int, line.split())
            if z >= 0:
                line = ' '.join(map(str, [z, *improve(pairs)]))
        rows.append(line)
    args.out.write_text('\n'.join(rows)+'\n# Second:'+second)


if __name__ == '__main__':
    main()
