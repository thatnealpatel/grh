"""Replay a combined disk-normal price over all five-release assignments."""
import argparse
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
from runpy import run_path

from sage.all import QQ

base = Path(__file__).resolve().parent
r = run_path(str(base/'check-five-release-independent-price-33.py'))
p, s, F = (r[k] for k in ('p', 's', 'F'))
TARGET = (0, 2, 4, 8, 10)
LIMITS = {TARGET: '-3.0e-10', (0, 2, 4, 6, 14): '-1.5e-9',
          (0, 2, 4, 6, 16): '-3.8e-9', (0, 2, 4, 8, 12): '-3.6e-9'}


def tests_of(cert):
    disks, quadratic = set(), []
    for row in cert['cuts']:
        if len(row) == 5:
            j, f, re, im, w = row
            assert Fraction(w) > 0 and (Fraction(re) or Fraction(im))
            disks.add((j, Fraction(f)))
        else:
            j, lam, sigma = row
            assert j == 1 and Fraction(sigma) > 0
            quadratic.append(tuple(map(Fraction, lam)))
    return disks, quadratic


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--self-test', action='store_true')
    args = ap.parse_args()
    r['j']['self_test']()
    raw = (p['laws']/'delete-33-five-release-disk-price.json').read_bytes()
    assert sha256(raw).hexdigest() == '47a17eb53b3ec4867e3a3953a713c6978887dc4fe2632907d86a241c012e3211'
    cert = json.loads(raw)
    disks, quadratic = tests_of(cert)
    assert (disks, quadratic) == tests_of(p['load_certificate']('eight-knots'))
    assert sum(j == 0 for j, _ in disks) == 581
    assert sum(j == 1 for j, _ in disks) == 62
    assert len(cert['cuts']) == len(disks)+1
    assert TARGET in r['ASSIGNMENTS']
    assert r['release_spans'](12800)[10] == range(640, 769)
    # A nonunit stored normal with a nonzero imaginary part. Test both
    # branches against the signed real values at t=0.
    z, center = [QQ(0), QQ(1)/400], [0, 0]
    for primitive, exact in ((True, -2), (False, -5)):
        a, b, *_ = s['tail_data'](z, center, [[0, '1', '3', '4', '5']],
                                  [0], 400, primitive=primitive)
        assert abs(a[0]*s['Ct']-exact) < F('1e-34') and b == [F(0)]
    data, center, _, constant = p['tangent_data'](cert)
    if args.self_test:
        return
    bounds = r['measurable_uppers'](data, center, constant)
    for ks, bound in bounds.items():
        print('Full measurable upper', ks, bound, flush=True)
    for ks, limit in LIMITS.items():
        assert bounds[ks] < F(limit)


if __name__ == '__main__':
    assert __debug__
    main()
