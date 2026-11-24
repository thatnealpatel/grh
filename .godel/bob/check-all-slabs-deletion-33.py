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
    off, gain, _ = tail['price'](z, A, B, U, data, omit={z[-1]})
    assert gain[2] == 0
    bound = off + gain[0] + gain[1] + tail['continuous_tail'](
        z, A, B, U, data, den=args.den)
    print('All original slabs free, measurable tail:', bound, flush=True)
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
