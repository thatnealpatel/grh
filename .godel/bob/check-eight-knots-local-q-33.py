"""Restore the local quadratic loss on the delete-33 eight-knot frontier."""
import argparse
from collections import Counter
from hashlib import sha256
import json
from math import comb
from pathlib import Path
from runpy import run_path

from sage.all import PolynomialRing, QQ


radial = run_path(str(Path(__file__).resolve().with_name('check-eight-knots-radial-33.py')))
p, z, UNIT, CUTOFF = (radial[k] for k in ('p', 'z', 'UNIT', 'CUTOFF'))
F, s = p['F'], p['s']
rounded, double_costs = (radial['frontier'][k] for k in ('rounded', 'double_costs'))
DIGEST = '34df5c789255c8c519db79ca76f915eb2461b44e8b60c332f696e7bcb8ea1ef8'
SITE, DEN = -2304, 6400
LFT, RGT = QQ(SITE)/400, QQ(-2288)/400
H0 = QQ(13)/25
SHIFTS = tuple(QQ(j)/25 for j in (-7, 6, 19))
GROUPS = {(-2304,): 21, (-2304, -216): 41, (-216,): 71, (-2288, -216): 2,
          (-322, -216): 2}
EPS = F('1e-14')
AREA = QQ(1)/2
I = (QQ(13)/35, QQ(6)/5, QQ(12))


def E(t):
    return (-F(t)/2).exp()


def cubic(v):
    return 1-3*v*v+2*v*v*v


def probe(left, right, q0):
    c = (left+right)/2
    lengths = (c-LFT, RGT-c)
    assert LFT <= left < right <= RGT and min(lengths) > 0
    v = (right-left)/(2*min(lengths))
    assert 0 < v <= 1
    a = q0*E(right)*cubic(v)
    den = q0*sum(QQ(comb(2, j))/4**(2-j)*I[j]*h**(1-2*j)
                 for j in range(3) for h in lengths)
    assert den > 0
    return a, den


def fee(beta, a, den, err, C, sigma):
    cap = (2*beta).upper()
    if not a > 0:
        return cap
    return min(cap, (beta*err/a+(beta*C/a)**2*den/(4*sigma)).upper())


def tilted_upper(left, right, beta):
    # The support is for -a*A-b*B+m*U; the tilt is -beta*(B_L-B_R).
    a, b, m = left
    u, v, n = right
    return p['upper'](a, b+beta, m)+p['upper'](u, v-beta, n)


def excluded(value):
    return value < CUTOFF


def edges(totals):
    def count(values):
        return next((i for i, value in enumerate(values) if not excluded(value)), len(totals))
    return count(totals), count(reversed(totals))


def reference():
    P = PolynomialRing(QQ, 'v')
    shape = cubic(P.gen())
    assert (shape(0), shape(1), shape.derivative()(0), shape.derivative()(1)) == (1, 0, 0, 0)
    integral = lambda pol: pol.integral()(1)-pol.integral()(0)
    assert integral(shape) == AREA
    assert tuple(integral(shape.derivative(j)**2) for j in range(3)) == I
    # At a cell touching the probe support boundary the minimum is exactly zero.
    a, den = probe(LFT, RGT, F(2))
    h = QQ(1)/50
    norm = 4*(QQ(13)/560*h+QQ(3)/5/h+12/h**3)
    assert a == 0 and abs(den-norm) < F('1e-28')
    assert probe(LFT, LFT+QQ(1)/DEN, F(1))[0] == 0
    beta, err, C, sigma = map(F, (1, 1, 2, 1))
    assert fee(beta, F(0), den, err, C, sigma) == 2
    assert fee(beta, F(4), F(2), err, C, sigma) == QQ(3)/8
    assert fee(beta, F(1)/4, F(2), err, C, sigma) == 2
    left, right = (F(0), F(-1), F(0)), (F(0), F(1), F(0))
    for sign, expected in ((1, 0), (0, 2), (-1, 4)):
        assert abs(tilted_upper(left, right, F(sign))-expected) < F('3e-14')
    assert CUTOFF == -1000000 and UNIT == 10**16
    assert excluded(CUTOFF-1) and not excluded(CUTOFF) and not excluded(CUTOFF+1)
    assert edges([CUTOFF+j for j in (-1, 0, 1, -1, -2)]) == (1, 2)
    print('Reference controls: cubic, fee branches, tilt sign and strict cutoff passed', flush=True)


def negative(row):
    return tuple(k for k, n in row if k < 0 for _ in range(n))


def has_double(row):
    return any(n == 2 for _, n in row)


def contamination(center, data, active_sites, slabs):
    assert z[:2] == [LFT, RGT] and z[-1] == QQ(29)/5 and RGT-LFT < H0
    assert all(2*RGT+t < 0 for t in SHIFTS)
    assert all(400*t == int(400*t) for t in (*z, H0, *SHIFTS)) and DEN % 400 == 0
    assert -RGT-SHIFTS[0] >= z[-1]

    def check_unsplit(a, b):
        assert any(t <= a < b <= r for t, r in slabs.items())
        assert all(slabs[QQ(k)/400] <= a or b <= QQ(k)/400 for k in active_sites)

    for m in range(1, 8):
        check_unsplit(LFT+m*H0, RGT+m*H0)
    for t in SHIFTS[1:]:
        check_unsplit(-RGT-t, -LFT-t)
    second = [row for row in data if len(row) == 3]
    assert len(second) == 1 and second[0][0] == 1 and len(second[0][1]) == len(SHIFTS)
    lam = list(map(F, second[0][1]))
    q = s['second_majorant'](lam)
    assert len(q) == 193 and q[0] > 0 and s['C'] > 0
    mass = AREA*(RGT-LFT)
    refl = [abs(v)*E(-RGT-t) for t, v in zip(SHIFTS, lam, strict=True)]
    derivative = sum(abs(q[m])*E(LFT+m*H0) for m in range(8, len(q)))+refl[0]
    err = F(1+max(map(abs, center)))*(derivative*(2+mass/2)+2*mass*sum(refl))
    assert err > 0
    return q[0], err


def local_prices(center, data, unsplit, q0, err, sigma):
    lo, hi = int(2*DEN*LFT), int(2*DEN*RGT)
    assert (lo, hi, hi-lo) == (2*DEN*LFT, 2*DEN*RGT, 512)
    aa, bb, _, _, curv = s['tail_data'](z, center, data, range(lo, hi+1), 2*DEN, primitive=True)
    samples = list(zip(aa, bb, strict=True))
    assert len(samples) == 513 and RGT < 0
    controls = [v if i % 2 == 0 else tuple(2*y-(x+t)/2 for x, y, t in
                zip(samples[i-1], v, samples[i+1], strict=True)) for i, v in enumerate(samples)]

    def support(v, beta):
        # The mass primitive is constant here, so both signed differences are zero.
        left = (*(a-b for a, b in zip(samples[0], v, strict=True)), F(0))
        right = (*(a-b for a, b in zip(v, samples[-1], strict=True)), F(0))
        return tilted_upper(left, right, beta).upper()

    rem = curv*E(LFT)/(DEN**3*72*F(3).sqrt())
    betas = [F(QQ(j)/(2*10**9)) for j in range(45)]
    table = [[support(v, beta) for v in controls] for beta in betas]
    plain, paid = [], []
    for i in range(0, len(controls)-2, 2):
        left = QQ(lo+i)/(2*DEN)
        a, den = probe(left, left+QQ(1)/DEN, q0)
        candidates = [(F(max(row[i:i+3]))+F(fee(beta, a, den, err, s['C'], sigma))).upper()
                      for row, beta in zip(table, betas, strict=True)]
        plain.append(rounded(F(max(table[0][i:i+3]))+rem-unsplit+EPS))
        paid.append(rounded(F(min(candidates))+rem-unsplit+EPS))
    assert len(plain) == len(paid) == 256 and all(a <= b for a, b in zip(paid, plain, strict=True))
    return plain, paid


def check(masks):
    slabs = dict(zip(z[:-1], z[1:], strict=True))
    sites = {int(400*t) for t in slabs}
    assert len(sites) == len(slabs) and len(masks) == len({tuple(map(tuple, r)) for r in masks}) == 137
    for row in masks:
        assert all(type(k) is type(n) is int and k in sites and n in (1, 2) for k, n in row)
        assert [k for k, _ in row] == sorted(set(k for k, _ in row))
        assert sum(n for _, n in row) == 8 and {0, 2, 4} <= dict(row).keys()
        assert sum(n == 2 for _, n in row) <= 1
    assert Counter(map(negative, masks)) == GROUPS and sum(map(has_double, masks)) == 13
    active = [row for row in masks if SITE in dict(row)]
    assert len(active) == 62 and all(dict(row)[SITE] == 1 for row in active)
    single, double = ({k for row in active for k, n in row if n == c and k != SITE} for c in (1, 2))

    data, center, sigma, constant = p['tangent_data'](radial['radial_certificate']())
    sigma = F(sigma)
    disks = [row for row in data if len(row) == 5]
    assert sigma > 0 and all(F(row[-1]) > 0 for row in disks)
    assert Counter(row[0] for row in disks) == {0: 581, 1: 62} and len(data) == len(disks)+1
    q0, err = contamination(center, data, single | double | {SITE}, slabs)
    print('Local unscaled contamination upper:', err.upper(), flush=True)

    _, original, old, _ = p['mesh_prices'](data, center, constant, 400, [], 60, tail_den=400)
    extra = [int(int(400*t) in single) for t in z[:-1]]
    split, _ = p['single_knot_costs'](z, center, data, old, extra, 0, DEN)
    assert sum(extra) == len(single) and all(0 <= v < 1 for v in split)
    costs = {(int(400*t), 1): int((v*UNIT).ceil()) for t, v, chosen in
             zip(z[:-1], split, extra, strict=True) if chosen}
    doubled = double_costs(center, data, double)
    assert {k for k, _ in costs} == single and doubled.keys() == double
    costs.update({(k, 2): v for k, v in doubled.items()})
    b0 = rounded(original)
    plain, paid = local_prices(center, data, old[LFT], q0, err, sigma)

    rest = lambda row: b0+sum(costs[k, n] for k, n in row if k != SITE)
    best_cell = max(paid)
    checked = [(row, rest(row), rest(row)+best_cell) for row in active]
    limits = {(-2304,): (-161601452, 112823619, -64289659, 0, 0, (256, 256)),
              (-2304, -216): (-31387539, 243037532, 65924254, 5, 74, (4, 176))}
    for key, expected in limits.items():
        group = [(base, total) for row, base, total in checked if negative(row) == key]
        worst_rest = max(base for base, _ in group)
        totals = [worst_rest+cell for cell in paid]
        actual = (worst_rest, worst_rest+max(plain), max(totals),
                  sum(not excluded(total) for _, total in group),
                  sum(not excluded(v) for v in totals), edges(totals))
        print(key, 'complement / plain / paid / masks / cells / edges:', actual, flush=True)
        assert actual == expected
    removed_prices = [total for _, _, total in checked if excluded(total)]
    removed = {tuple(map(tuple, row)) for row, _, total in checked if excluded(total)}
    residual = [row for row in masks if tuple(map(tuple, row)) not in removed]
    assert (len(removed), len(residual)) == (57, 80)
    assert dict(Counter(map(negative, residual))) == {(-216,): 71, (-2304, -216): 5,
                                                       (-2288, -216): 2, (-322, -216): 2}
    least_paid = max(removed_prices)
    doubles_left = sum(map(has_double, residual))
    assert least_paid < CUTOFF and doubles_left + sum(
        has_double(row) for row, _, total in checked if excluded(total)) == 13
    print('Least negative excluded:', least_paid, '; residual:', len(residual),
          '; residual double slabs:', doubles_left, flush=True)
    return residual


if __name__ == '__main__':
    assert __debug__
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('masks', type=Path, nargs='?', help='canonical export of the radial checker')
    parser.add_argument('--reference', action='store_true', help='only run small reference controls')
    parser.add_argument('--write-eight', type=Path, help='export the remaining masks as JSON')
    args = parser.parse_args()
    reference()
    if not args.reference:
        if args.masks is None:
            parser.error('the radial frontier is required unless only running controls')
        raw = args.masks.read_bytes()
        assert sha256(raw).hexdigest() == DIGEST
        residual = check(json.loads(raw))
        if args.write_eight:
            args.write_eight.write_text(json.dumps(residual, separators=(',', ':'))+'\n')
