"""Price oriented third-moment jumps on the canonical 80 Delete-33 masks."""
import argparse
from fractions import Fraction
from pathlib import Path
from runpy import run_path

from sage.all import PolynomialRing, QQ

prior = run_path(str(Path(__file__).resolve().with_name('check-eight-knots-a-drop-33.py')))
p, s, z, F, UNIT, CUTOFF = (prior[k] for k in ('p', 's', 'z', 'F', 'UNIT', 'CUTOFF'))
local = prior['local_q']
E, rounded, negative = (prior[k] for k in ('E', 'rounded', 'negative'))
FIRST = local['SITE']
DEN = 3200
# Thousandths, used only to bracket an exact stationary atom.
ROOTS = dict(zip((*range(6, 36, 2), *range(38, 54, 2)),
                 (170, 207, 241, 271, 299, 324, 347, 369, 389, 407, 425, 441, 457,
                  472, 486, 512, 525, 536, 548, 559, 569, 579, 589), strict=True))
EXEMPT = {FIRST, -2288, -322, -216, 0, 2, 4, 36, 184}
CHANGED = (6, 8, 10, 12)
HALF_JUMP = QQ(1)/40
# Maximal passing grid numerators with zero or one arbitrary free slab.
CAPS = {(-216,): (412, 368), (-2304, -216): (462, 429),
        (-2288, -216): (480, 458), (-322, -216): (485, 465)}


def D(v):
    return 4*v*(12*(2*v*v-1)**2-3)


def shape(u, v):
    return 16*(u+v)**2*(2*u*u+4*v*v-3)


def atom(k, a, b, m):
    seed = QQ(ROOTS[k])/1000
    l, r = seed-QQ(1)/1000, seed+QQ(1)/1000
    assert 0 < l < r < 1

    def derivative(v):
        return m-4*v*a-D(v)*b

    assert derivative(l) > 0 and derivative(r) < 0
    for _ in range(36):
        mid = (l+r)/2
        value = derivative(mid)
        if value > 0:
            l = mid
        elif value < 0:
            r = mid
        else:
            break  # The enclosing sign bracket remains valid.
    return F(l).union(F(r))


def jump_bounds(slabs, center, data):
    den = 2*DEN
    pts = sorted({i for k in ROOTS for i in range(den*k//400, den*slabs[k]//400+1)})
    ap, bp, *_, curv = s['tail_data'](z, center, data, pts, den, primitive=True)
    ad, _, *_, dcurv = s['tail_data'](z, center, data, pts, den)
    ap, bp, ad = (dict(zip(pts, values, strict=True)) for values in (ap, bp, ad))
    mp = {i: s['step'](QQ(i)/den, 0) for i in pts}
    md = {i: F(QQ(i)/den)*(-F(QQ(i)/den)).exp() for i in pts}
    uboxes = [F(QQ(i)/32).union(F(QQ(i+1)/32)) for i in range(32)]
    prices = {}
    for k in ROOTS:
        l, r = den*k//400, den*slabs[k]//400
        assert 0 < l < r and l % 2 == r % 2 == 0
        a, b, m = (v[l]-v[r] for v in (ap, bp, mp))
        v = atom(k, a, b, m)
        divisor = D(v)
        assert (divisor > 0 if k < 36 else divisor < 0)
        ratio = 4*v/divisor
        weight = E(QQ(l)/den)
        ae, me = dcurv*weight/(8*den**2), 2*weight/(8*den**2)
        for i in range(l, r):
            acell = ad[i].union(ad[i+1])+(-ae).union(ae)
            mcell = md[i].union(md[i+1])+(-me).union(me)
            bc = (mcell-4*v*acell)/divisor
            # This is the divided difference after enforcing stationarity.
            assert all(-bc*shape(u, v)-mcell/(2*v) < 0 for u in uboxes), (k, i)

        # P integrates b - b*, from the left endpoint of this original slab.
        P = {i: bp[l]-bp[i]-((mp[l]-mp[i])/divisor-ratio*(ap[l]-ap[i]))
             for i in range(l, r+1)}
        P[l] = P[r] = F(0)  # exact stationarity of the original integral
        ctr = [q for i in range(l, r, 2)
               for q in prior['controls'](P[i], P[i+1], P[i+2])]
        rem = ((1+abs(ratio))*curv+2/abs(divisor))*weight/(DEN**3*72*F(3).sqrt())
        down = max(0, rounded(F(max((-q).upper() for q in ctr))+rem))
        up = max(0, rounded(F(max(q.upper() for q in ctr))+rem))
        major, reverse = (up, down) if k < 36 else (down, up)
        assert major > reverse >= 0, (k, major, reverse)
        prices[k] = major, reverse
    print('Per-unit (favored, reverse) jump prices, in 1e-16 units:', prices, flush=True)
    return prices


def base_prices(masks, slabs, data, center, sigma, constant):
    _, original, old, _ = p['mesh_prices'](data, center, constant, 400, [], 60, tail_den=400)
    single, double = ({k for row in masks for k, n in row if n == c} for c in (1, 2))
    extra = [int(int(400*t) in single) for t in z[:-1]]
    split, _ = p['single_knot_costs'](z, center, data, old, extra, 0, 2*DEN)
    assert sum(extra) == len(single) and all(0 <= v < 1 for v in split)
    costs = {(int(400*t), 1): int((v*UNIT).ceil()) for t, v, chosen in
             zip(z[:-1], split, extra, strict=True) if chosen}
    costs.update({(k, 2): v for k, v in local['double_costs'](center, data, double).items()})
    assert rounded(original) == -2187294957
    assert costs.keys() == {(k, n) for row in masks for k, n in row}
    first_rows = [row for row in masks if FIRST in dict(row)]
    assert len(first_rows) == 5 and all(dict(row)[FIRST] == 1 for row in first_rows)
    q0, err = local['contamination'](center, data, {k for row in first_rows for k, _ in row},
                                      {QQ(k)/400: QQ(r)/400 for k, r in slabs.items()})
    _, paid = local['local_prices'](center, data, old[QQ(FIRST)/400], q0, err, sigma)
    assert max(paid) == 97311793 < costs[FIRST, 1] == 274424971
    costs[FIRST, 1] = max(paid)
    return rounded(original), costs


def charge(cost, n, oriented, prices):
    major, reverse = prices
    assert 0 <= oriented <= 2*n
    return min(cost, int((oriented*major).ceil())+2*n*reverse)


def budget(row, base, raw, jump, cap, free):
    """Cap favorable variation per tested slab, except on at most `free` slabs."""
    excess = []
    for k, n in row:
        full = raw[k, n]
        if k in jump:
            clipped = charge(full, n, cap, jump[k])
            excess.append(full-clipped)
            base += clipped
        else:
            base += full
    return base+sum(sorted(excess, reverse=True)[:free])


def reference():
    assert F.precision() == 128 and UNIT == 10**16 and CUTOFF == -1000000
    ring = PolynomialRing(QQ, names=('u', 'v', 'b', 'm'))
    u, v, b, m = ring.gens()
    T = lambda u: 32*u**6-48*u**4+18*u*u-1
    assert T(v).derivative(v) == D(v)
    # Clear the denominator in a=(m-D(v)b)/(4v).
    def score(u):
        return 4*v*(m*u-b*T(u))-(m-D(v)*b)*(2*u*u-1)
    assert score(u)-score(v) == (u-v)**2*(-4*v*b*shape(u, v)-2*m)
    # Piecewise values 1,-1,0: signed residual is -2P_1+P_2.
    assert -((b-0)*1+(m-b)*(-1)+(0-m)*0) == -2*b+m
    row = [(6, 2), (8, 1), (36, 1)]
    raw = {(6, 2): 15, (8, 1): 10, (36, 1): 2}
    price = {6: (8, 1), 8: (2, 0)}
    assert [budget(row, -1, raw, price, QQ(1)/3, j) for j in range(3)] == [9, 18, 26]
    assert budget(row, -1, raw, price, QQ(2), 0) == 20
    print('Reference controls: Exact atom factor, jump sign, ceil, reverse fee, and free-slab selection passed',
          flush=True)


def b_completion(data, center, sigma, jump, base, raw, masks):
    # Restore the B disks and the full B loss, without requiring a matching A.
    mask = prior['FLAT']
    changed = set(CHANGED)
    assert mask in masks and changed == dict(mask).keys()-EXEMPT
    assert all(dict(mask)[k] == 1 for k in changed)
    zz, yy, cc = [], [], []
    for i, (t, b, c) in enumerate(zip(z, p['B'], center, strict=True)):
        zz.append(t)
        cc.append(c)
        if int(400*t) in changed:
            assert 400*t == int(400*t) and z[i+1]-t == QQ(1)/200
            zz.append(t+QQ(1)/400)
            cc.append(c)
            yy.extend([b-HALF_JUMP, b+HALF_JUMP])
        else:
            yy.append(b)
    assert all(-1 < b < 1 for b in yy)
    K, C = s['K'], s['C']
    J = s['jumps'](zz, yy, C)
    residual = s['jumps'](zz, [y-c for y,c in zip(yy, cc, strict=True)], C)
    norms, disk_loss = [], F(0)
    for _, x, u, v, w in (row for row in data if len(row) == 5 and row[0] == 1):
        x, u, v, w = map(F, (x,u,v,w))
        gamma = K(u, v)
        gamma /= abs(gamma)
        value = sum(a*K(0, x*t).exp() for t,a in zip(zz, J, strict=True))/K(F(1)/2, x)
        norms.append(abs(value))
        disk_loss += w*(1-(gamma.conjugate()*value).real())
    lam, = [list(map(F, row[1])) for row in data if len(row) == 3 and row[0] == 1]
    majorant = s['second_majorant'](lam)

    def quadratic(j):
        d, v = s['second_tangent'](zz, j, lam, majorant)
        return d, sum(a*b for a,b in zip(j, v, strict=True))

    d, q = quadratic(J)
    _, distance = quadratic(residual)
    loss = disk_loss+F(sigma)*(d-q+distance)
    # Use the field's actual oriented variation and zero reverse variation.
    # This is a necessary screen, not a B-fixed support optimization.
    allowance = base-CUTOFF
    for k, n in mask:
        cost = raw[k, n]
        if k in changed:
            cost = min(cost, int((2*HALF_JUMP*jump[k][0]).ceil()))
        allowance += cost
    assert len(norms) == 62 and all(v < F('.999976') for v in norms)
    assert d-q > F('4.8e-6') and F(0) < loss < F('1.04e-8')
    assert loss < QQ(allowance)/UNIT, (loss, allowance)
    print('B-only completion: max disk, Q slack, total B loss, allowance units:',
          max(v.upper() for v in norms), d-q, loss, allowance, flush=True)


def a_screen():
    # Restore the accepted A-only affine test for negative slabs plus 0 free.
    # Its global baseline deficit is already certified in third-moment-band-33.
    band = run_path(str(Path(__file__).resolve().with_name('check-third-moment-band-33.py')))
    releases, _, _, gap = band['CASES'][1]
    assert releases == band['NEGATIVE'] | {0} and not releases.intersection(CHANGED)
    pts = sorted({j for k in CHANGED for j in range(2*k, 2*k+5)})
    prices, *_ = s['tail_data'](z, p['B'], band['disk_rows'](), pts, 800)
    prices = dict(zip(pts, (-v for v in prices), strict=True))
    mass = {j: F(j)/800*(-F(j)/800).exp() for j in pts}
    signal = F(0)
    for k in CHANGED:
        i = z.index(QQ(k)/400)
        assert z[i+1] == QQ(k+2)/400
        b = F(p['B'][i])
        for panel, change in ((k, -HALF_JUMP), (k+1, HALF_JUMP)):
            j = 2*panel
            ajs, mjs = (prior['controls'](*(p[j+q] for q in range(3))) for p in (prices, mass))
            for a, m in zip(ajs, mjs, strict=True):
                _, slope = band['priced_control'](a, m, b)
                signal += slope*change/1200  # (panel width)/3
    assert F('9.13e-8') < signal < F('9.14e-8') < gap
    print('A-only witness signal, certified necessary signal:', signal, gap, flush=True)


def main(path):
    slabs = {int(400*t): int(400*r) for t, r in zip(z[:-1], z[1:], strict=True)}
    masks = prior['checked_masks'](path, slabs)
    assert EXEMPT | ROOTS.keys() == {k for row in masks for k, _ in row}
    assert not EXEMPT & ROOTS.keys()
    assert all(400*t == int(400*t) for t in (*z, local['H0'], *local['SHIFTS']))
    data, center, sigma, constant = p['tangent_data'](local['radial']['radial_certificate']())

    def tests(cuts):
        disks = {(row[0], Fraction(row[1])) for row in cuts if len(row) == 5}
        quads = [(row[0], tuple(map(Fraction, row[1]))) for row in cuts if len(row) == 3]
        return disks, quads

    assert tests(data) == tests(p['load_certificate']('eight-knots')['cuts'])
    disks = [row for row in data if len(row) == 5]
    assert sum(row[0] == 0 for row in disks) == 581 and len(disks) == 643
    assert F(sigma) > 0 and all(F(row[-1]) > 0 for row in disks)
    jump = jump_bounds(slabs, center, data)
    base, raw = base_prices(masks, slabs, data, center, F(sigma), constant)
    assert CAPS.keys() == prior['GROUPS'].keys()
    for key, caps in CAPS.items():
        rows = [row for row in masks if negative(row) == key]
        for free, i in enumerate(caps):
            lo, hi = (max(budget(row, base, raw, jump, QQ(j)/10000, free) for row in rows)
                      for j in (i, i+1))
            assert lo < CUTOFF <= hi, (key, free, i, lo, hi)
            print('Best grid cap: group, free, cap, passing/failing maxima:',
                  key, free, QQ(i)/10000, lo, hi, flush=True)
    b_completion(data, center, sigma, jump, base, raw, masks)
    a_screen()


if __name__ == '__main__':
    assert __debug__
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('masks', type=Path, nargs='?', help='canonical local-Q checker export')
    parser.add_argument('--reference', action='store_true', help='only run small reference controls')
    args = parser.parse_args()
    reference()
    if not args.reference:
        if args.masks is None:
            parser.error('the local-Q frontier is required unless only running controls')
        main(args.masks)
