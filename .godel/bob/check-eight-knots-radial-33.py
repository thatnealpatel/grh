"""Radially reprice the checked 155-mask delete-33 eight-knot frontier."""
import argparse
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
from runpy import run_path

from sage.all import QQ


base = Path(__file__).resolve().parent
frontier = run_path(str(base/'check-refined-frontier-33.py'))
p, z, UNIT, CUTOFF = (frontier[key] for key in ('p', 'z', 'UNIT', 'CUTOFF'))


def checked_masks(path):
    raw = path.read_bytes()
    # Exact canonical --write-eight output of the preceding ball checker.
    assert sha256(raw).hexdigest() == 'b198276408fadb7f791d3ef68a16eee27ae1fd1ebc9773276de30bbb684003ed'
    return json.loads(raw)


def radial_certificate():
    raw = (p['laws']/'delete-33-five-release-disk-price-k8.json').read_bytes()
    assert sha256(raw).hexdigest() == '4150ddbca857c6d79966354328bdb8791a3818a12e8506a9aafd844e8a9cc2ee'
    cert = json.loads(raw, parse_float=str)
    patch = json.loads((p['laws']/'delete-33-k8-radial-deltas.json').read_bytes())
    disks = [row for row in cert['cuts'] if len(row) == 5]
    assert len(patch) == len({i for i, _ in patch}) == 42
    for i, n in patch:
        assert type(i) is type(n) is int and 0 <= i < len(disks) and n != 0
        w = Fraction(disks[i][-1])+Fraction(n, 10**20)
        assert w > 0
        disks[i][-1] = QQ(w)
    return cert


def check(eight):
    data, center, _, constant = p['tangent_data'](radial_certificate())
    _, original, old, _ = p['mesh_prices'](data, center, constant, 400, [], 60, tail_den=800)
    single_sites, double_sites = ({k for row in eight for k, c in row if c == n} for n in (1, 2))
    # Select the needed single-split calculations with a sentinel. Check
    # the resulting direct bounds are strictly smaller than the sentinel.
    extra = [int(int(400*t) in single_sites) for t in z[:-1]]
    assert sum(extra) == len(single_sites)
    split, _ = p['single_knot_costs'](z, center, data, old, extra, 0, 12800)
    assert all(v < 1 for v in split)
    costs = {(int(400*t), 1): int((v*UNIT).ceil()) for t, v, chosen in
             zip(z[:-1], split, extra, strict=True) if chosen}
    costs.update({(k, 2): v for k, v in frontier['double_costs'](center, data, double_sites).items()})
    b = frontier['rounded'](original)
    prices = [b+sum(costs[k, c] for k, c in row) for row in eight]
    nonnegative = [v for row, v in zip(eight, prices, strict=True) if all(k >= 0 for k, _ in row)]
    assert nonnegative == [-1885403]
    assert max(v for v in prices if v < CUTOFF) == -1139268
    residual = frontier['screen'](eight, b, costs)
    assert len(residual) == 137
    assert sum(any(c == 2 for _, c in row) for row in residual) == 13
    groups = {}
    for row in residual:
        key = tuple(k for k, c in row if k < 0 for _ in range(c))
        groups[key] = groups.get(key, 0)+1
    assert groups == {(-2304,): 21, (-216,): 71, (-2304, -216): 41,
                      (-2288, -216): 2, (-322, -216): 2}
    print('Radial prices in 1e-16 units: all-nonnegative', nonnegative[0],
          '; worst paid', max(v for v in prices if v < CUTOFF), flush=True)
    print('Radial frontier: 137 unpaid; 13 with a double slab; negative starts', groups, flush=True)
    return residual


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('frontier', type=Path, help='canonical JSON from the refined-frontier checker')
    parser.add_argument('--write-eight', type=Path, help='export the radial residual masks as JSON')
    args = parser.parse_args()
    residual = check(checked_masks(args.frontier))
    if args.write_eight:
        args.write_eight.write_text(json.dumps(residual, separators=(',', ':'))+'\n')
