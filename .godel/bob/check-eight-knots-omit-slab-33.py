"""Price the two eight-knot assignments omitting the slab at 4/400."""
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
from runpy import run_path

from sage.all import QQ


p = run_path(str(Path(__file__).with_name('refined-prices-33.py')))
z = p['z']
CASES = (
    ('seven-two-negative', (-2304, -216, 0, 2, 6, 8, 10, 12), 400),
    ('five-release-minus-216', (-216, 0, 2, 6, 8, 10, 12, 14), 800),
)


def price(job):
    case, sites, tail_den = job
    indices = [i for i, t in enumerate(z[:-1]) if int(400*t) in sites]
    assert len(indices) == len(sites) == 8
    data, center, _, constant = p['tangent_data'](p['load_certificate'](case))
    _, base, old, _ = p['mesh_prices'](data, center, constant, 400, [], 60,
                                      tail_den=tail_den)
    # The sentinel requests a direct shared-coordinate bound rather than
    # capping it by a precomputed release bound. Check it was not used.
    extra = [int(i in indices) for i in range(len(z)-1)]
    split, _ = p['single_knot_costs'](z, center, data, old, extra, 0, 6400)
    assert all(split[i] < 1 for i in indices)
    return base+sum(split[i] for i in indices)


if __name__ == '__main__':
    with ProcessPoolExecutor(max_workers=2) as pool:
        for (_, sites, _), value in zip(CASES, pool.map(price, CASES)):
            print(sites, value, flush=True)
            assert value < -QQ(1)/10**10
