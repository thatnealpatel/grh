"""Price the released and coupled third-moment support on cap completions."""
import argparse
from fractions import Fraction
from pathlib import Path
from runpy import run_path

from sage.all import QQ


def atoms(a, m, b, maximize):
    """Propose rational common atoms; the lower bound needs no oracle proof."""
    a, m, t = float(a), float(m), float(b)
    hi = 10000*(abs(a)+m)
    lo = -hi
    for _ in range(52):
        beta = (hi+lo)/2
        u = maximize(a, beta, m)
        x = 2*u*u-1
        if (4*x*x-3)*x > t:
            hi = beta
        else:
            lo = beta
    den = 10**13
    return sorted({QQ(0), QQ(1)/2, QQ(1)} | {
        QQ(round(den*maximize(a, beta, m)))/den for beta in (lo, hi)
    })


def lower(a, m, b, ctx):
    F, maximize = ctx['F'], ctx['maximizing_u']
    if m == 0:
        if b is None:
            return abs(a)
        sign = 1 if float(a) >= 0 else -1
        return sign*a*((sign*F(b)).arccos()/3).cos()
    assert m > 0
    if b is None:
        u = QQ(round(10**13*maximize(float(a), 0., float(m))))/10**13
        assert 0 <= u <= 1
        return (2*u*u-1)*a+u*m
    candidates = []
    for u in atoms(a, m, b, maximize):
        assert 0 <= u <= 1
        x = 2*u*u-1
        candidates.append((ctx['third'](x), a*x+m*u))
    choices = [v for t, v in candidates if t == b]
    for t, v in candidates:
        for w, g in candidates:
            if t < b < w:
                lam = (b-t)/(w-t)
                assert 0 < lam < 1 and (1-lam)*t+lam*w == b
                choices.append((1-lam)*v+lam*g)
    return max(choices, key=float)


def reference(ctx):
    F = ctx['F']
    v = lower(F(-1), F(2), QQ(1), ctx)
    assert abs(v-QQ(3)/2) < F('1e-20')
    assert abs(lower(F(-1), F(2), None, ctx)-QQ(3)/2) < F('1e-16')
    assert abs(lower(F(-2), F(0), QQ(-1), ctx)-2) < F('1e-30')
    u = lower(F(0), F(1), QQ(0), ctx)
    assert F('.9659258262') < u < F('.9659258264')
    print('Reference: endpoints, released atom, negative branch, and rational mixture passed', flush=True)


def fields(ctx, sites):
    B = ctx['B']
    N = ctx['NEGATIVE']
    eps = QQ(1)/10**10
    # B = clip((1+scale) B0, -1+eps, 1-eps) plus five exact bumps.
    specs = (
        (0, QQ(12)/10**5, (-2512873400, 2577509911, 20411426, 97089221, 72361935365)),
        (2, QQ(6)/10**5, (-1321918706, 1363000165, 80403002, 157076197, 35687656197)),
    )
    for last, scale, bump in specs:
        R = N | {last}
        y = [min(1-eps, max(-1+eps, (1+scale)*b)) for b in B]
        for k, n in zip(sorted(R), bump, strict=True):
            y[sites.index(k)] += QQ(n)/10**12
        assert all(-1 < b < 1 for b in y)
        yield R, y


def caps(ctx, y, rows, lam, majorant):
    s, z, F = (ctx[k] for k in ('s', 'z', 'F'))
    K = s['K']
    b = s['jumps'](z, y, s['C'])
    norms = []
    for freq in rows:
        w = K(QQ(1)/2, -freq)
        norms.append(abs(sum(v*K(0, freq*t).exp() for t, v in zip(z, b, strict=True))/w))
    d, v = s['second_tangent'](z, b, lam, majorant)
    gap = d-sum(x*t for x, t in zip(b, v, strict=True))
    print('Inherited B-disk max upper and Q slack:', max(t.upper() for t in norms), gap, flush=True)
    # These bounds certify the 62 inherited disks, not the full-line cap.
    assert all(t < F('.99999975') for t in norms) and gap > F('2.8e-7')


def main(ctx):
    s, z, B, F, Ct = (ctx[k] for k in ('s', 'z', 'B', 'F', 'Ct'))
    cuts = ctx['disk_rows']()
    rows = ctx['p']['load_certificate']('eight-knots')['cuts']
    freqs = [QQ(Fraction(row[1])) for row in rows if len(row) == 5 and row[0] == 1]
    assert len(freqs) == len(set(freqs)) == 62
    lam, = [list(map(F, row[1])) for row in rows if len(row) == 3 and row[0] == 1]
    majorant = s['second_majorant'](lam)
    sites = [int(400*t) for t in z]
    assert z == [QQ(t)/400 for t in sites] and sites[-1] == 2320
    witnesses = list(fields(ctx, sites))
    for R, y in witnesses:
        print('Check release set', sorted(R), flush=True)
        caps(ctx, y, freqs, lam, majorant)

    weights = [F(row[-1]) for row in cuts]
    constant = sum(weights)-F(8)/9
    third_a = sum(F(row[-1])*(F(1)/4+F(row[1])**2)**(QQ(3)/2) for row in cuts)/Ct
    edges = (list(range(-2304, 4800))+list(range(4800, 8000, 4))
             +list(range(8000, 24001, 16)))
    assert set(sites) <= set(edges)
    panels = list(zip(edges[:-1], edges[1:], strict=True))
    points = [j for l, h in panels for j in (2*l, l+h)]+[2*edges[-1]]
    density, *_ = s['tail_data'](z, B, cuts, points, 800)
    integral, *_ = s['tail_data'](z, B, cuts, edges, 400, primitive=True)
    t = [QQ(v)/800 for v in points]
    mass = [F(v)*(-F(v)).exp() if v > 0 else F(0) for v in t]
    cum = [s['step'](QQ(v)/400, 0) for v in edges]
    remote_a = 2*sum(weights)/Ct*F(-30).exp()
    remote_m = cum[-1]
    lo = [constant-remote_a for _ in witnesses]
    hi = [constant+remote_a+remote_m for _ in witnesses]
    hi_N = hi.copy()
    error, j = F(0), 0
    for i, (l, h) in enumerate(panels):
        if j+1 < len(sites) and l == sites[j+1]:
            j += 1
        assert sites[j] <= l and (j+1 == len(sites) or h <= sites[j+1])
        # The primitive is the integral of the disk price before the
        # sign reversal in a. Candidate laws are constant on each panel.
        a_int, m_int = integral[i+1]-integral[i], cum[i]-cum[i+1]
        a = ctx['controls'](*[-x for x in density[2*i:2*i+3]])
        m = ctx['controls'](*mass[2*i:2*i+3])
        width = QQ(h-l)/400
        is_N = sites[j] in ctx['NEGATIVE']
        nfree = width/3*sum(ctx['free_control'](x,w) for x,w in zip(a, m, strict=True)) if is_N else None
        for k, (R, y) in enumerate(witnesses):
            lo[k] += lower(a_int, m_int, None if sites[j] in R else y[j], ctx)
            fixed = width/3*sum(ctx['priced_control'](x, w, F(y[j]))[0]
                                for x, w in zip(a, m, strict=True))
            hi[k] += fixed
            hi_N[k] += nfree if is_N else fixed
        e = (-F(l)/800).exp()
        third_m = (3+QQ(h)/400)*e**2 if l >= 0 else F(0)
        error += width**4/192*(third_a*e+third_m)
    for (R, _), l, h, n in zip(witnesses, lo, hi, hi_N, strict=True):
        print('Release set, true released lower, full and N-only upper:',
              sorted(R), l, h+error, n+error, flush=True)
        assert l > F('1.4e-7') and h+error < F('-2.4e-7')
        assert n+error < F('-2.4e-7')


if __name__ == '__main__':
    assert __debug__
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reference', action='store_true')
    args = parser.parse_args()
    ctx = run_path(str(Path(__file__).with_name('check-third-moment-band-33.py')))
    reference(ctx)
    if not args.reference:
        main(ctx)
