"""Replay a joint upper price with every original slab independently free."""
import argparse
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
from runpy import run_path

from sage.all import QQ


def main():
    base = Path(__file__).resolve().parent
    laws = base / 'deletion-laws'
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('dual', type=Path, nargs='?',
                   default=laws / 'delete-33-all-slabs-dual.json')
    p.add_argument('--den', type=int, default=4800)
    p.add_argument('--upper', default='1.4e-8',
                   help='required strict upper bound (use 0 to test exclusion)')
    p.add_argument('--check-pre', nargs=2, metavar=('FRACTION', 'UPPER'),
                   help='also check the bound with this pre-tail replacement cap')
    p.add_argument('--regional', action='store_true',
                   help='price three local third-moment changes on the reference mesh')
    args = p.parse_args()
    assert __debug__ and args.den > 0 and args.den % 400 == 0

    tail = run_path(str(base / 'check-tail-deletion-33.py'))
    z, A, B, U = tail['unfold']['lattice']['prime_rows'](
        (laws / 'delete-33-tail-baseline.txt').read_text())
    assert len(z) == 1257 and z[0] == -QQ(144)/25 and z[-1] == QQ(29)/5
    assert z[494] == 0 and all(t < s for t, s in zip(z, z[1:]))

    payload = args.dual.read_bytes()
    data = json.loads(payload, parse_float=str)
    assert isinstance(data, list) and data
    for row in data:
        assert isinstance(row, list) and len(row) in (3, 5)
        assert type(row[0]) is int and row[0] in (0, 1)
        assert Fraction(row[-1]) >= 0
        if len(row) == 5:
            f, re, im = map(Fraction, row[1:-1])
            assert f >= 0 and (re != 0 or im != 0)
        else:
            assert row[0] == 1 and len(row[1]) == 3
            tuple(map(Fraction, row[1]))
    print('Cut list:', args.dual, 'sha256:', sha256(payload).hexdigest(), flush=True)
    print('Tail mesh denominator:', args.den, flush=True)

    # The last reference half-line is omitted from the fixed-slab gains.
    # Replace its price, including its remote remainder, by continuous_tail.
    F = tail['F']
    tilts, loss, weight = {}, {}, {}
    if args.regional:
        for line in (laws / 'delete-33-regional-tilts.txt').read_text().splitlines():
            name, k, n = line.split()
            t, h = QQ(k)/400, QQ(n)/10**16
            assert t in z[:-1] and t not in tilts
            tilts[t] = name, h
            loss[name] = F(0)
            weight[name] = weight.get(name, 0) + abs(h)

        masks = [('negative', z[0], 0, 9), ('early', 0, 1, 32),
                 ('late', 1, z[-1], 21)]
        assert set(loss) == {name for name, *_ in masks}
        for name, lo, hi, n in masks:
            knots = [t for t, (g, _) in tilts.items() if g == name]
            assert len(knots) == n and all(lo <= t < hi for t in knots)

    def slab_check(t, upper, a, b, m, w):
        if t in tilts:
            name, h = tilts[t]
            shifted = tail['bern_upper'](a, b+h, m, F('1e-13'))
            loss[name] += upper - shifted - h*w

    off, gain, _ = tail['price'](z, A, B, U, data, omit={z[-1]},
                                   slab_check=slab_check if args.regional else None)
    assert gain[2] == 0
    bound = off + gain[0] + gain[1] + tail['continuous_tail'](
        z, A, B, U, data, den=args.den)
    print('All original slabs free, measurable tail:', bound, flush=True)
    if args.regional:
        for name, radius in [('negative', '0.5'), ('early', '0.001'), ('late', '0.06')]:
            limit = bound - loss[name] + F(radius)*weight[name]
            print(name, 'loss', loss[name], 'weight', weight[name], 'upper at radius', limit)
            assert limit < F('-6.58e-10')
        assert loss['negative'] - bound > F('7.275e-9')
        print('Combined signed score required:', sum(loss.values()) - bound)
        assert sum(loss.values()) - bound > F('2.80009e-8')
    if args.check_pre:
        frac, limit = args.check_pre
        eta = QQ(frac)
        assert 0 <= eta <= 1
        restricted = bound - (1 - eta)*gain[1]
        print('Pre-tail replacement at most', eta, ':', restricted, flush=True)
        assert restricted < tail['F'](limit)
    assert bound < tail['F'](args.upper)


if __name__ == '__main__':
    main()
