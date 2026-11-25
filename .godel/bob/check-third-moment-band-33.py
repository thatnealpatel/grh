"""Delete-33: Price measurable laws near the baseline third moment."""
import argparse
from collections import defaultdict
from fractions import Fraction
from math import sqrt
from pathlib import Path
from runpy import run_path

from sage.all import QQ

base = Path(__file__).resolve().parent
r = run_path(str(base/'check-eight-knots-radial-33.py'))
p, z = (r[k] for k in ('p', 'z'))
s, B = (p[k] for k in ('s', 'B'))
F, Ct = s['F'], s['Ct']
NEGATIVE = frozenset((-2304, -2288, -322, -216))
CASES = ((NEGATIVE, QQ(1)/30000, F('-2e-8'), F('2.20e-7')),
         (NEGATIVE | {0}, QQ(1)/50000, F('-2e-8'), F('1.50e-7')),
         (NEGATIVE | {2}, QQ(1)/10**6, F('-1e-8'), F('1.90e-8')))
TAGS = frozenset().union(*(sites for sites, *_ in CASES))
EPS = F('1e-11')


def controls(left, mid, right):
    return left, 2*mid-(left+right)/2, right


def third(x):
    return (4*x*x-3)*x


def maximizing_u(a, beta, m):
    # Only proposes a dual tilt. The ball polynomial check trusts none of
    # these floating roots or the maximizing-atom and bisection decisions.
    d, c = 192*beta, 36*beta+4*a
    def derivative(u):
        v = u*u
        return m+u*(c+d*v*(v-1))
    breaks = [0.0]
    if d:
        det = .09-c/(5*d)
        if det > 0:
            sd = sqrt(det)
            breaks.extend(sqrt(v) for v in (.3-sd, .3+sd) if 0 < v < 1)
    breaks.append(1.0)
    atoms = [0.0, 1.0]
    for l, h in zip(breaks[:-1], breaks[1:], strict=True):
        if derivative(l) <= 0 or derivative(h) >= 0:
            continue
        for _ in range(32):
            u = (l+h)/2
            if derivative(u) > 0:
                l = u
            else:
                h = u
        atoms.append((l+h)/2)
    def score(u):
        x = 2*u*u-1
        return a*x+beta*third(x)+m*u
    return max(atoms, key=score)


def trial_beta(a, m, b):
    a, m, b = map(float, (a, m, b))
    hi = 10000*(abs(a)+m)
    lo = -hi
    for _ in range(56):
        beta = (lo+hi)/2
        u = maximizing_u(a, beta, m)
        if third(2*u*u-1) > b:
            hi = beta
        else:
            lo = beta
    return F((lo+hi)/2)


def priced_control(a, m, b):
    # Return intercept and slope for a tangent upper at baseline b. For
    # zero mass the outer inverse root of T3 gives the supporting tangent.
    if m == 0:
        if not (a >= 0 or a <= 0):
            return abs(a), F(0)
        sign = 1 if a >= 0 else -1
        x = ((sign*b).arccos()/3).cos()
        derivative = 12*x*x-3
        assert derivative > 0
        return abs(a)*x, sign*abs(a)/derivative
    assert m > 0
    beta = trial_beta(a, m, b)
    return s['bern_upper'](-a, -beta, m, EPS)-beta*b, -beta


def free_control(a, m):
    return abs(a) if m == 0 else s['bern_upper'](-a, F(0), m, EPS)


def disk_rows():
    cuts = [row for row in r['radial_certificate']()['cuts'] if len(row) == 5 and row[0] == 0]
    inherited = {Fraction(row[1]) for row in p['load_certificate']('eight-knots')['cuts']
                 if len(row) == 5 and row[0] == 0}
    assert len(cuts) == len(inherited) == 581
    assert {Fraction(row[1]) for row in cuts} == inherited
    return cuts


def reference():
    assert F.precision() == 128
    assert controls(*map(F, (0, 1, 0))) == (0, 2, 0)
    assert controls(*map(F, (0, 1, 2))) == (0, 1, 2)
    # Integral of the absolute cubic nodal product divided by 3!, width 1.
    assert 2*(QQ(1)/16-QQ(1)/16+QQ(1)/64)/6 == QQ(1)/192
    for sign in (-1, 1):
        v, slope = priced_control(F(sign), F(0), F(sign)/2)
        assert v > QQ(9)/10 and v < 1
        assert abs(sign*slope*(12*v*v-3)-1) < F('1e-30')
    assert maximizing_u(0., 0., 1.) == 1.
    assert abs(maximizing_u(-1., 0., 2.)-.5) < 1e-9
    a, m, b = map(F, (-1, 2, 1))
    # Here u=1/2 has B=1 and also maximizes the unrestricted score.
    assert QQ(3)/2 < free_control(a, m) < F('1.50000000002')
    v, _ = priced_control(a, m, b)
    assert QQ(3)/2 < v < F('1.50000000002')
    v, slope = priced_control(F(0), F(1), F(0))
    exact = (F.pi()/12).cos()
    assert exact < v < exact+2*EPS and F('.04') < slope < F('.05')
    a0, b0, *_ = s['tail_data']([QQ(0), QQ(1)/400], [0, 0],
                                [[0, '1', '3', '4', '5']], [0], 400)
    assert abs(a0[0]*Ct+5) < F('1e-34') and b0 == [F(0)]
    disk_rows()
    print('Reference controls: Bernstein, both outer branches, positive-mass tilt, and disk phase passed', flush=True)


def check_b_only_witness(sites, cuts):
    # Dilution pays for a dip on an unchanged original slab, including
    # the cross term with the baseline in the quadratic form.
    k = sites.index(36)
    assert sites[k:k+2] == [36, 38] and 36 not in TAGS
    y = [value*(1-QQ(1)/10**5) for value in B]
    y[k] -= QQ(1)/200
    assert all(-1 < value < 1 for value in y)
    b = s['jumps'](z, y, s['C'])
    s['cap'](z, b, F('.99998'))  # All real frequencies, not just the 62 disks.
    rows = p['load_certificate']('eight-knots')['cuts']
    lam, = [row[1] for row in rows if len(row) == 3 and row[0] == 1]
    lam = list(map(F, lam))
    d, v = s['second_tangent'](z, b, lam, s['second_majorant'](lam))
    slack = d-sum(x*t for x, t in zip(b, v, strict=True))
    assert slack > F('1.18e-5')

    # The outer root gives one common-atom lift with high mass, but this
    # lift grossly violates an inherited A disk. It is not a feasible law.
    X = [(F(value).arccos()/3).cos() for value in y]
    U = [((1+x)/2).sqrt() for x in X]
    cumulative = [s['step'](t, 0) for t in z]+[F(0)]
    surplus = sum((a-b)*u for a, b, u in zip(cumulative[:-1], cumulative[1:], U, strict=True))-F(8)/9
    assert any(Fraction(row[1]) == 0 for row in cuts)
    a0 = 2*abs(sum(s['jumps'](z, X, Ct)))
    assert surplus > F('.0225') and a0 > 49
    print('B-witness quadratic slack, lifted surplus, A norm at zero:', slack, surplus, a0, flush=True)
    return y


def main():
    assert all(-1 < b < 1 for b in B)
    sites = [int(400*t) for t in z]
    assert z == [QQ(t)/400 for t in sites] and (sites[0], sites[-1]) == (-2304, 2320)
    assert len(sites) == 1257 and TAGS <= set(sites[:-1])
    cuts = disk_rows()
    y = check_b_only_witness(sites, cuts)
    assert all(F(w) > 0 and F(f) >= 0 and (F(re)**2+F(im)**2) > 0
               for _, f, re, im, w in cuts)
    constant = sum(F(row[-1]) for row in cuts)-F(8)/9
    third_a = sum(F(row[-1])*(F(1)/4+F(row[1])**2)**(QQ(3)/2) for row in cuts)/Ct
    # Panel edges in /400 units, all nodes (including midpoints) in /800.
    edges = (list(range(-2304, 4800))+list(range(4800, 8000, 4))
             +list(range(8000, 24000+1, 16)))
    assert set(sites) <= set(edges) and len(edges)-1 == 8904
    panels = list(zip(edges[:-1], edges[1:], strict=True))
    points = [j for l, h in panels for j in (2*l, l+h)]+[2*edges[-1]]
    a, *_ = s['tail_data'](z, B, cuts, points, 800)
    a = [-v for v in a]
    t = [QQ(j)/800 for j in points]
    mass = [F(v)*(-F(v)).exp() if v > 0 else F(0) for v in t]
    decay = [(-F(t[2*i])/2).exp() for i in range(len(panels))]
    price, slopes, free = (defaultdict(lambda: F(0)) for _ in range(3))
    signal, witness_price = (defaultdict(lambda: F(0)) for _ in range(2))
    error, j = F(0), 0
    for i, (l, h) in enumerate(panels):
        if j+1 < len(sites) and l == sites[j+1]:
            j += 1
        assert sites[j] <= l and (j+1 == len(sites) or h <= sites[j+1])
        key, b, d = sites[j], F(B[j]), QQ(h-l)/400
        for v, w in zip(controls(*a[2*i:2*i+3]), controls(*mass[2*i:2*i+3]), strict=True):
            intercept, slope = priced_control(v, w, b)
            price[key] += d/3*intercept
            slopes[key] += d/3*abs(slope)
            signal[key] += d/3*slope*F(y[j]-B[j])
            witness_price[key] += d/3*priced_control(v, w, F(y[j]))[0]
            if key in TAGS:
                free[key] += d/3*free_control(v, w)
        e = decay[i]
        third_m = (3+QQ(h)/400)*e**2 if l >= 0 else F(0)
        error += d**4/192*(third_a*e+third_m)
    assert j == len(sites)-1 and set(free) == TAGS
    remote = s['step'](QQ(60), 0)+2*sum(F(row[-1]) for row in cuts)/Ct*F(-30).exp()
    fixed = constant+sum(price.values())+error+remote
    assert error < F('4e-9') and remote < F('1e-12')
    assert fixed < F('-2.30e-7') and sum(slopes.values()) < F('.0057')
    print('A-only measurable fixed-B upper, interpolation, remote, band slope:',
          fixed, error, remote, sum(slopes.values()), flush=True)
    for releases, eps, target, required_signal in CASES:
        released = sum(free[k]-price[k] for k in sorted(releases))
        penalty = eps*sum(v for k, v in slopes.items() if k not in releases)
        upper = fixed+released+penalty
        print('Released slabs, band, release price, band price, upper:',
              sorted(releases), eps, released, penalty, upper, flush=True)
        assert upper < target
        gap = -F('1e-10')-fixed-released
        sig = sum(v for k, v in signal.items() if k not in releases)
        repriced = constant+error+remote+sum(free[k] if k in releases else v
                                             for k, v in witness_price.items())
        print('B-witness signal, affine threshold, repriced upper:', sig, gap, repriced, flush=True)
        assert gap > required_signal and sig > gap and sig > F('2.65e-7')
        assert repriced < F('-9e-8')


if __name__ == '__main__':
    assert __debug__
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reference', action='store_true', help='only run small reference controls')
    args = parser.parse_args()
    reference()
    if not args.reference:
        main()
