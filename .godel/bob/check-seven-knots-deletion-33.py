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


def unpaid_patterns(base, costs, budget, choices=(1, 2)):
    """Yield all slab assignments not excluded below CUTOFF."""
    items = sorted(costs.items(),
                   key=lambda kv: max(2*kv[1][c]//c for c in choices), reverse=True)
    n = len(items)
    suffix = [[0]*(budget+1) for _ in range(n+1)]
    for i in reversed(range(n)):
        _, price = items[i]
        a = suffix[i+1]
        suffix[i] = [max([a[k]] + [price[c]+a[k-c] for c in choices if c <= k])
                     for k in range(budget+1)]

    def visit(i, k, value, pattern):
        if value >= CUTOFF:
            yield pattern
        if k == 0:
            return
        for j in range(i, n):
            if value+suffix[j][k] < CUTOFF:
                break  # Suffix bounds are nonincreasing in j.
            t, price = items[j]
            for c in choices:
                if c > k:
                    continue
                v = value+price[c]
                if v+suffix[j+1][k-c] >= CUTOFF:
                    yield from visit(j+1, k-c, v, pattern+((t,c),))

    yield from visit(0, budget, base, ())


def screen(prices, budget, choices=(1, 2), report=False):
    base, costs = prices[0]
    pending = list(unpaid_patterns(base, costs, budget, choices))
    if report:
        print(CASES[0][0], 'unpaid:', len(pending), flush=True)
    for (name, _, _), (other_base, other_costs) in zip(CASES[1:], prices[1:]):
        assert costs.keys() == other_costs.keys()
        pending = [p for p in pending if other_base+sum(other_costs[t][c] for t,c in p) >= CUTOFF]
        if report:
            print(name, 'unpaid:', len(pending), flush=True)
    return pending


def check_frontier(prices):
    releases = [(b, {t: (0, d) for t, (_, _, d) in c.items()}) for b, c in prices]
    for label, tables, budget, choices, count, max_negative, exceptions in (
        ('eight knots', prices, 8, (1, 2), 1289, 2, {
            (-2304, -216, 0, 2, 6, 8, 10, 12),
            (-216, 0, 2, 6, 8, 10, 12, 14),
            (-2304, 0, 2, 6, 8, 10, 12, 14),
        }),
        ('five measurable releases', releases, 5, (1,), 14, 1, {
            (0, 2, 6, 8, 10),
        }),
    ):
        pending = screen(tables, budget, choices)
        assert len(pending) == count
        skips_third = set()
        for p in pending:
            sites = dict(p)
            assert sum(sites.values()) == budget and {0, 2} <= sites.keys()
            assert sum(c for t, c in p if t < 0) <= max_negative
            if 4 not in sites:
                assert all(c == 1 for c in sites.values())
                skips_third.add(tuple(sorted(sites)))
        assert skips_third == exceptions
        print(label, 'unpaid:', count, '; omitting slab 4:', sorted(skips_third), flush=True)


def check(prices, frontier):
    pending = screen(prices, 7, report=True)
    assert not pending, pending
    print('Seven real knots: surplus <', QQ(CUTOFF)/UNIT, flush=True)
    if frontier:
        check_frontier(prices)


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run with assertions enabled.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--jobs', type=int, default=1)
    parser.add_argument('--frontier', action='store_true',
                        help='also localize the eight-knot and five-release gaps')
    args = parser.parse_args()
    if args.jobs == 1:
        check(list(map(case_price, CASES)), args.frontier)
    else:
        with ProcessPoolExecutor(max_workers=args.jobs) as pool:
            check(list(pool.map(case_price, CASES)), args.frontier)
