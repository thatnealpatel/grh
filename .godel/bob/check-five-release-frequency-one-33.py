"""Verify a serialized common witness for nine prices and three point caps."""
from concurrent.futures import ProcessPoolExecutor
import gzip
import json
from pathlib import Path
from runpy import run_path

from sage.all import QQ


base = Path(__file__).resolve().parent
p = run_path(str(base/'check-five-release-linear-lower-33.py'))
s, F, DEN = (p[k] for k in ('s', 'F', 'DEN'))
SET = (0, 2, 4, 6, 16)
SCALE = 10**12


def primitives(case):
    return p['primitives'](case)


def profile():
    # Store the atoms so the check need not reproduce floating nomination.
    with gzip.open(base/'deletion-laws/delete-33-five-release-frequency-one.json.gz', 'rt') as f:
        law = json.load(f)
    nodes = sorted(p['BASE_FINE'] + [j for k in SET for j in p['SPANS'][k] if j % 2 == 0])
    assert len(set(nodes)) == len(nodes)
    assert len(law['weights']) == len(law['atoms']) == 4
    assert sum(law['weights']) == SCALE
    assert all(type(w) is int and 0 < w <= SCALE for w in law['weights'])
    weights = [QQ(w)/SCALE for w in law['weights']]
    assert all(len(a) == len(nodes)-1 for a in law['atoms'])
    ts = [QQ(j)/DEN for j in nodes]
    e = [2*(-F(t)/2).exp() for t in ts]
    mass = [s['step'](t, 0) for t in ts]
    terms = []
    for i, sites in enumerate(zip(*law['atoms'])):
        assert all(type(u) is int and 0 <= u <= SCALE for u in sites)
        u = [QQ(x)/SCALE for x in sites]
        x = [2*v*v-1 for v in u]
        y = [v*(4*v*v-3) for v in x]
        U, A, B = (sum(w*v for w, v in zip(weights, values)) for values in (u, x, y))
        terms.append((nodes[i], nodes[i+1], (mass[i]-mass[i+1])*U, e[i]-e[i+1], A, B))
    return ts, terms


def field(ts, vals, freq, norm):
    v = s['K'](QQ(1)/2, -freq)
    h = [(-v*t).exp() for t in ts]
    return sum((p-q)*z for p, q, z in zip(h, h[1:], vals))/(v*norm)


if __name__ == '__main__':
    import argparse

    if not __debug__:
        raise SystemExit('Run with assertions enabled.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--jobs', type=int, default=1)
    args = parser.parse_args()
    ts, law = profile()
    A, B = zip(*(row[-2:] for row in law))
    A0 = field(ts, A, 0, s['Ct'])
    B0 = field(ts, B, 0, s['C'])
    A1 = field(ts, A, 1, s['Ct'])
    print('|V_A(0)|, |V_B(0)|, |V_A(1)|:', *(abs(f) for f in (A0, B0, A1)), flush=True)
    assert all(abs(f) < QQ(91)/100 for f in (A0, B0, A1))
    for name, vals, freq, norm, bound in (
            ('A', A, QQ(611)/10, s['Ct'], QQ(388)/100),
            ('B', B, QQ(2)/5, s['C'], QQ(23)/10)):
        mod = abs(field(ts, vals, freq, norm))
        print(f'|V_{name}({freq})|:', mod, flush=True)
        assert mod > bound
    with ProcessPoolExecutor(max_workers=args.jobs) as pool:
        tables = list(pool.map(primitives, p['CASES']))
    for case, table in zip(p['CASES'], tables):
        value, = p['prices'](table, [law])
        print(case, value, flush=True)
        assert value > QQ(35)/10**12
