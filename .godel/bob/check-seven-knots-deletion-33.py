"""Cover seven arbitrary added real knots by five delete-33 tangents."""
import argparse
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
from runpy import run_path

from sage.all import QQ


UNIT = 10**16
CUTOFF = -10**6  # Prove a uniform upper bound of -1e-10.
CASES = [('six-knots', 1600, 48), ('seven-two-negative', 3200, 56),
         ('seven-minus-216', 3200, 56), ('seven-minus-2304', 3200, 56),
         ('seven-nonnegative', 3200, 60)]


def case_price(case):
    name, split_den, tail_end = case
    p = run_path(str(Path(__file__).resolve().with_name('refined-prices-33.py')))
    data, center, _, constant = p['tangent_data'](p['load_certificate'](name))
    z = p['z']
    _, original, old, _ = p['mesh_prices'](data, center, constant, 400, [], tail_end)
    release = p['costs']['release_costs'](z, center, data, old)
    split, _ = p['single_knot_costs'](z, center, data, old, release, QQ(15)/10**9, split_den)
    # Round each term independently upward before using integer arithmetic.
    base = int((original.upper().exact_rational()*UNIT).ceil())
    return base, {int(400*t): (0, int((e*UNIT).ceil()), int((d*UNIT).ceil()))
                  for t, e, d in zip(z[:-1], split, release)}


def unpaid_patterns(base, costs, budget):
    """Yield all slab assignments not excluded below CUTOFF."""
    items = sorted(costs.items(), key=lambda kv: max(2*kv[1][1], kv[1][2]), reverse=True)
    n = len(items)
    suffix = [[0]*(budget+1) for _ in range(n+1)]
    for i in reversed(range(n)):
        _, (_, e, d) = items[i]
        a = suffix[i+1]
        suffix[i] = [max(a[k], e+a[k-1] if k >= 1 else 0,
                         d+a[k-2] if k >= 2 else 0) for k in range(budget+1)]

    def visit(i, k, value, pattern):
        if value >= CUTOFF:
            yield pattern
        if k == 0:
            return
        for j in range(i, n):
            if value+suffix[j][k] < CUTOFF:
                break  # Suffix bounds are nonincreasing in j.
            t, price = items[j]
            for c in range(1, min(2,k)+1):
                v = value+price[c]
                if v+suffix[j+1][k-c] >= CUTOFF:
                    yield from visit(j+1, k-c, v, pattern+((t,c),))

    yield from visit(0, budget, base, ())


def check(prices):
    base, costs = prices[0]
    pending = list(unpaid_patterns(base, costs, 7))
    print(CASES[0][0], 'unpaid:', len(pending), flush=True)
    for (name, _, _), (other_base, other_costs) in zip(CASES[1:], prices[1:]):
        assert costs.keys() == other_costs.keys()
        pending = [p for p in pending if other_base+sum(other_costs[t][c] for t,c in p) >= CUTOFF]
        print(name, 'unpaid:', len(pending), flush=True)
    assert not pending, pending
    print('Seven real knots: surplus <', QQ(CUTOFF)/UNIT, flush=True)


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run with assertions enabled.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--jobs', type=int, default=1)
    args = parser.parse_args()
    if args.jobs == 1:
        check(list(map(case_price, CASES)))
    else:
        with ProcessPoolExecutor(max_workers=args.jobs) as pool:
            check(list(pool.map(case_price, CASES)))
