"""Price the A drop at -216 on the canonical signed Delete-33 frontier."""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
from runpy import run_path

from sage.all import QQ


local_q = run_path(str(Path(__file__).resolve().with_name('check-eight-knots-local-q-33.py')))
p, s, z, F, UNIT, CUTOFF = (local_q[key] for key in ('p', 's', 'z', 'F', 'UNIT', 'CUTOFF'))
E, rounded, negative = (local_q[key] for key in ('E', 'rounded', 'negative'))
DIGEST = 'b15f16a1fc3662d4187dbbec71ec0cde6a77579b5fa015d34f5397b04ea4e31f'
SITE, END = -216, -214
DEN = 3200
GROUPS = {(-216,): 71, (-2304, -216): 5, (-2288, -216): 2, (-322, -216): 2}
# Plain and best complement integer maxima for the four groups.
MAXIMA = {(-216,): (-161601452, -161601452), (-2304, -216): (-71217256, -248330434),
          (-2288, -216): (-274454489, -274454489), (-322, -216): (-280686259, -280686259)}
FLAT = [[k, 1] for k in (SITE, 0, 2, 4, 6, 8, 10, 12)]
DELTA_UP, DELTA_DOWN = QQ(2096)/10**11, QQ(25)/10**13
TARGET = QQ(3)/4
EPS = F('1e-14')


def controls(left, middle, right):
    return left, 2*middle-(left+right)/2, right


def correction(cap):
    assert 0 <= cap <= 2
    return max(cap*DELTA_UP, 2*DELTA_DOWN)


def conditional_units(base, cap):
    return base+int((UNIT*correction(cap)).ceil())


def drop_floor(base):
    # For a frontier law the negative-delta branch cannot pay this gap.
    gap = QQ(CUTOFF-base)/UNIT
    return gap/DELTA_UP if gap > 2*DELTA_DOWN else None


def moments(u):
    assert 0 <= u <= 1
    x = 2*u*u-1
    return x, (4*x*x-3)*x


def encloses(ball, value):
    return ball.lower().exact_rational() <= value <= ball.upper().exact_rational()


def reference():
    assert F.precision() == 128 and UNIT == 10**16 and CUTOFF == -1000000
    assert controls(*map(F, (0, 1, 0))) == (0, 2, 0)
    assert controls(*map(F, (0, -1, 0))) == (0, -2, 0)
    # Signed primitive increments: a toy decomposition with opposite A and B jumps.
    c_a, c_b, a, b = map(F, (4, 8, 3, 2))
    theta, delta = b/c_b, a-c_a/c_b*b
    left, right = (F(1), F(-1)), (F(-1)/2, F(1))
    direct = a*left[0]+b*left[1]+(c_a-a)*right[0]+(c_b-b)*right[1]
    mix = tuple(theta*y+(1-theta)*v for y, v in zip(left, right, strict=True))
    assert direct == c_a*mix[0]+c_b*mix[1]+delta*(left[0]-right[0]) == QQ(13)/2
    assert correction(QQ(0))*UNIT == 50000 and correction(TARGET)*UNIT == 157200000
    assert rounded(F(QQ(1)/(4*UNIT))) == 1 and rounded(F(-QQ(1)/(4*UNIT))) == 0
    tie = CUTOFF-157200000
    assert conditional_units(tie-1, TARGET) < CUTOFF == conditional_units(tie, TARGET)
    assert drop_floor(tie-1) > TARGET == drop_floor(tie)
    assert drop_floor(CUTOFF-50000) is None and drop_floor(CUTOFF-50001) > 0
    assert moments(QQ(1)) == (1, 1) and moments(QQ(1)/2) == (-QQ(1)/2, 1)
    out, atom = s['bern_upper'](F(1), F(0), F(2), EPS, witness=True)
    assert atom == QQ(1)/2 and (out-EPS).lower() <= QQ(3)/2 < out
    assert encloses(out-p['upper'](F(1), F(0), F(2)), 0)
    # Exercise both child stacks, not just the initial midpoint.
    for mass, expected, score in ((1, QQ(1)/4, QQ(9)/8), (3, QQ(3)/4, QQ(17)/8)):
        out, atom = s['bern_upper'](F(1), F(0), F(mass), EPS, witness=True)
        assert atom == expected and (out-EPS).lower() <= score < out
    # The endpoint choices and the interior midpoint may all witness lower bounds.
    for sign, expected in ((1, 0), (-1, 1)):
        out, atom = s['bern_upper'](F(sign), F(0), F(0), EPS, witness=True)
        assert atom == expected and (out-EPS).lower() <= 1 < out
    # A different, low-mass flat-B splice satisfies all caps and the quadratic test.
    l, r = QQ(SITE)/400, QQ(END)/400
    assert all(E(l)*(r-l)/s[name] < QQ(1)/80 for name in ('Ct', 'C'))
    assert QQ(2)/80**2 < 1 and 1/F(2).sqrt() < QQ(8)/9+QQ(CUTOFF)/UNIT
    print('Reference controls: projection, Bernstein signs, ceil, cutoff, atoms and cap-only splice passed',
          flush=True)


def checked_masks(path, slabs):
    raw = path.read_bytes()
    assert sha256(raw).hexdigest() == DIGEST
    masks = json.loads(raw)
    assert len(slabs) == 1256 and slabs[SITE] == END
    assert len(masks) == len({tuple(map(tuple, row)) for row in masks}) == 80
    for row in masks:
        assert all(type(k) is type(n) is int and k in slabs and n in (1, 2) for k, n in row)
        assert [k for k, _ in row] == sorted(set(k for k, _ in row))
        assert sum(n for _, n in row) == 8 and {0, 2, 4} <= dict(row).keys()
        assert dict(row)[SITE] == 1 and sum(n == 2 for _, n in row) <= 1
    assert Counter(map(negative, masks)) == GROUPS
    assert sum(map(local_q['has_double'], masks)) == 10 and FLAT in masks
    print('Canonical scope:', dict(Counter(map(negative, masks))), '; 10 double slabs', flush=True)
    return masks


def geometry(center, data):
    l, r = QQ(SITE)/400, QQ(END)/400
    den = 2*DEN
    assert den % 400 == 0 and r < 0
    assert all(400*t == int(400*t) for t in (*z, local_q['H0'], *local_q['SHIFTS']))
    i, j = int(den*l), int(den*r)
    assert (i, j, j-i) == (den*l, den*r, 32)
    points = range(i, j+1)
    a, b, _, _, curv = s['tail_data'](z, center, data, points, den, primitive=True)
    _, rho, _, _, rho_curv = s['tail_data'](z, center, data, points, den)
    assert len(a) == len(b) == len(rho) == len(points)
    # B primitive is the integral to infinity. Negative density makes it increasing.
    rho_lo, rho_hi = min(v.lower() for v in rho), max(v.upper() for v in rho)
    secant_err = rho_curv*E(l)/(8*den**2)
    assert QQ(-402265)/10**9 < F(rho_lo) and F(rho_hi) < QQ(-397641)/10**9
    assert secant_err < QQ(3084)/10**11 and F(rho_hi)+secant_err < 0
    c_b = b[-1]-b[0]
    assert c_b > 0
    ratio = (a[-1]-a[0])/c_b
    delta = [(v-a[0])-ratio*(w-b[0]) for v, w in zip(a, b, strict=True)]
    delta[0] = delta[-1] = F(0)  # exact algebraic endpoint values
    table = [v for k in range(0, len(delta)-2, 2) for v in controls(*delta[k:k+3])]
    assert len(table) == 3*16 and s['step'](l, 0) == s['step'](r, 0) == 1
    rem = (1+abs(ratio))*curv*E(l)/(DEN**3*72*F(3).sqrt())
    lo, hi = min(v.lower() for v in table), max(v.upper() for v in table)
    assert lo >= 0 and F(hi) < QQ(2094704)/10**14 and rem < QQ(2473)/10**15
    assert F(lo)-rem > -DELTA_DOWN and F(hi)+rem < DELTA_UP
    print('B density samples:', rho_lo, rho_hi,
          '; secant error upper:', secant_err.upper(), flush=True)
    print('A/B ratio:', ratio, '; delta controls:', lo, hi,
          '; interpolation error upper:', rem.upper(), flush=True)
    print('A-drop geometry: theta in [0,1]; delta in', (-DELTA_DOWN, DELTA_UP), flush=True)


def complements(masks, slabs, data, center, sigma, constant):
    _, original, old, _ = p['mesh_prices'](data, center, constant, 400, [], 60, tail_den=400)
    single, double = ({k for row in masks for k, n in row if n == c and k != SITE} for c in (1, 2))
    extra = [int(int(400*t) in single) for t in z[:-1]]
    split, _ = p['single_knot_costs'](z, center, data, old, extra, 0, 2*DEN)
    assert sum(extra) == len(single) and all(0 <= v < 1 for v in split)
    costs = {(int(400*t), 1): int((v*UNIT).ceil()) for t, v, chosen in
             zip(z[:-1], split, extra, strict=True) if chosen}
    doubled = local_q['double_costs'](center, data, double)
    assert {k for k, _ in costs} == single and doubled.keys() == double
    costs.update({(k, 2): v for k, v in doubled.items()})
    baseline = rounded(original)
    assert baseline == -2187294957
    plain = [baseline+sum(costs[k, n] for k, n in row if k != SITE) for row in masks]
    print('Rounded unsplit base:', baseline, '; complement sites single/double:', len(single), len(double),
          flush=True)

    first = local_q['SITE']
    paid_rows = [row for row in masks if first in dict(row)]
    assert len(paid_rows) == 5 and all(dict(row)[first] == 1 for row in paid_rows)
    area = {QQ(k)/400: QQ(v)/400 for k, v in slabs.items()}
    active = {k for row in paid_rows for k, _ in row}
    q0, err = local_q['contamination'](center, data, active, area)
    _, paid_cells = local_q['local_prices'](center, data, old[QQ(first)/400], q0, err, sigma)
    paid = max(paid_cells)
    assert (costs[first, 1], paid) == (274424971, 97311793)
    improvement = costs[first, 1]-paid
    assert improvement > 0
    print('First-slab increment plain/paid in 1e-16 units:', costs[first, 1], paid, flush=True)
    return plain, [b-(improvement if first in dict(row) else 0)
                   for b, row in zip(plain, masks, strict=True)]


def report(masks, plain, best):
    for key, n in GROUPS.items():
        rows = [(row, a, b) for row, a, b in zip(masks, plain, best, strict=True) if negative(row) == key]
        assert len(rows) == n
        print('Group', key, 'count', n, flush=True)
        for col, name in enumerate(('plain', 'best'), 1):
            base = [row[col] for row in rows]
            assert max(base) == MAXIMA[key][col-1]
            at_cap = [conditional_units(b, TARGET) for b in base]
            pos = sum(conditional_units(b, QQ(0)) < CUTOFF for b in base)
            forced = sum(v < CUTOFF for v in at_cap)
            unconditional = sum(conditional_units(b, QQ(2)) < CUTOFF for b in base)
            expected_forced = 0 if col == 1 and key == (-2304, -216) else n
            assert (pos, forced, unconditional) == (n, expected_forced, 0)
            assert forced == sum(f is not None and f > TARGET for f in map(drop_floor, base))
            print(name, 'complement min/max:', min(base), max(base), '; capped min/max:',
                  min(at_cap), max(at_cap), '; forces >0 / >3/4 / >2:', pos, forced, unconditional,
                  '; common drop floor:', drop_floor(max(base)), flush=True)


def disk_violation(pieces, data):
    # Independently test the explicit witness at one original A disk.
    # Atoms with X=0 outside these pieces contribute zero to either moment.
    x = '0.2424456471998'
    assert any(len(row) == 5 and row[0] == 0 and row[1] == x for row in data)
    edges = [a for a, _, _ in pieces]+[pieces[-1][1]]
    wbar = s['K'](F(1)/2, -F(x))
    exp = [(-wbar*(QQ(t)/400)).exp() for t in edges]
    area = sum((a-b)*moments(u)[0] for a, b, (_, _, u) in
               zip(exp[:-1], exp[1:], pieces, strict=True))/wbar
    norm = abs(area)/s['Ct']
    assert norm > QQ(136308)/10**5
    print('Flat witness violates A disk (x, norm lower):', x, norm.lower(), flush=True)


def flat_witness(slabs, data, center, constant):
    assert all(slabs[k] == k+2 for k, _ in FLAT)
    tail = range(int(400*z[-1]), 48*400+1)
    split = {k for k, _ in FLAT}
    points = sorted(slabs.keys() | {k+1 for k in split} | set(tail))
    a, b, *_ = s['tail_data'](z, center, data, points, 400, primitive=True)
    primitive = {k: (x, y, s['step'](QQ(k)/400, 0)) for k, x, y in zip(points, a, b, strict=True)}
    cells = []
    for l, r in slabs.items():
        edges = (l, l+1, r) if l in split else (l, r)
        cells.extend(zip(edges[:-1], edges[1:], strict=True))
    assert len(cells) == 1256+8
    cells.extend(zip(tail[:-1], tail[1:], strict=True))
    assert cells[0][0] == int(400*z[0]) and cells[-1][1] == 48*400
    assert all(b == c for (_, b), (c, _) in zip(cells[:-1], cells[1:], strict=True))
    score = constant
    pieces = []
    for l, r in cells:
        a, b, m = (x-y for x, y in zip(primitive[l], primitive[r], strict=True))
        if l in (SITE, SITE+1):
            u = QQ(1) if l == SITE else QQ(1)/2
            x, y = moments(u)
            assert m == 0 and y == 1
            score += -a*x-b*y
        else:
            upper, u = s['bern_upper'](a, b, m, EPS, witness=True)
            score += upper-EPS  # best is a lower bound for this particular atom
        pieces.append((l, r, u))
    by_start = {l: u for l, _, u in pieces}
    assert all(by_start[k] != by_start[k+1] for k, _ in FLAT)
    # Past 48 use X=0, i.e. u=1/sqrt(2), with nonnegative mass contribution.
    print('Flat-B raw tangent lower:', score.lower(), '; priced finite/tail pieces:',
          1256+8, len(cells)-(1256+8), flush=True)
    assert score > QQ(147577)/10**13
    disk_violation(pieces, data)


def main(path):
    slabs = {int(400*t): int(400*r) for t, r in zip(z[:-1], z[1:], strict=True)}
    masks = checked_masks(path, slabs)
    data, center, sigma, constant = p['tangent_data'](local_q['radial']['radial_certificate']())
    disks = [row for row in data if len(row) == 5]
    assert Counter(row[0] for row in disks) == {0: 581, 1: 62} and len(data) == len(disks)+1
    sigma = F(sigma)
    assert sigma > 0 and all(F(row[-1]) > 0 for row in disks)
    geometry(center, data)
    report(masks, *complements(masks, slabs, data, center, sigma, constant))
    flat_witness(slabs, data, center, constant)


if __name__ == '__main__':
    assert __debug__
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('masks', type=Path, nargs='?', help='canonical --write-eight output of local-q checker')
    parser.add_argument('--reference', action='store_true', help='only run small reference controls')
    args = parser.parse_args()
    reference()
    if not args.reference:
        if args.masks is None:
            parser.error('the local-q frontier is required unless only running controls')
        main(args.masks)
