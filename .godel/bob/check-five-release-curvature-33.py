"""Check five point caps, two quadratic losses, and a uniform loss budget."""
from concurrent.futures import ProcessPoolExecutor
from functools import cache
from pathlib import Path
from runpy import run_path

from sage.all import QQ

base = Path(__file__).resolve().parent
w = run_path(str(base/'check-five-release-frequency-one-33.py'))
p, s, F = (w[k] for k in ('p', 's', 'F'))
r = p['p']
P = s['P']


def moments(poly, offset, den, degree, queries):
    """Return lower (+ exponent) and upper (- exponent) kernel moments."""
    coeff = poly.list()
    splits = {x: max(0, min(len(coeff), -x-offset)) for x in queries}
    pts = sorted({0, len(coeff)} | set(splits.values()))
    # At a split index i, (i+offset+x)/den is nonnegative. The two
    # exponential moments supply the kernel on opposite sides of zero.
    sums = {1: [F(0)]*(degree+1), -1: [F(0)]*(degree+1)}
    prefixes = {}
    previous = 0
    for end in pts:
        for i in range(previous, end):
            v = coeff[i]
            if v.is_zero():
                continue
            t = F(i+offset)/den
            e = (t/2).exp()
            plus, minus = v*e, v/e
            for j in range(degree+1):
                sums[1][j] += plus
                sums[-1][j] += minus
                plus *= t
                minus *= t
        prefixes[end] = (tuple(sums[1]), tuple(sums[-1]))
        previous = end
    for x in queries:
        left, right = prefixes[splits[x]]
        yield left, tuple(a-b for a, b in zip(sums[-1], right))


def quadratic(ts, B, lam, q):
    """Unfolded Gram form on the difference field (not a tangent)."""
    den = 3200
    mesh = [int(t*den) for t in ts]
    assert len(mesh) == len(B) and all(i == t*den for i, t in zip(mesh, ts))
    assert all(i < j for i, j in zip(mesh, mesh[1:]))
    lo, hi = mesh[0], mesh[-1]
    b = s['jumps'](ts,B,s['C'])
    bp = P({i-lo: v for i,v in zip(mesh,b)})
    br = P({hi-i: v for i,v in zip(mesh,b)})
    shifts = [j*13*den//25 for j in range(len(q))]
    assert all(i*25 == j*13*den for j,i in enumerate(shifts))
    d = []
    for x, ((l0,l1), (r0,r1)) in zip(shifts, moments(bp*br, lo-hi, den, 1, shifts)):
        t = F(x)/den
        e = (t/2).exp()
        d.append(e*((2-t)*l0-l1)+((2+t)*r0+r1)/e)
    shifts = [j*den//25 for j in s['unfold']['S']]
    z = []
    for x, ((l0,_,_), (r0,r1,r2)) in zip(shifts, moments(bp*bp, 2*lo, den, 2, shifts)):
        t = F(x)/den
        e = (t/2).exp()
        z.append(e*l0+((1+t+t*t/2)*r0+(1+t)*r1+r2/2)/e)
    toeplitz = q[0]*d[0]+2*sum(a*b for a, b in zip(q[1:], d[1:]))
    return toeplitz+sum(a*b for a, b in zip(lam, z))


def check_kernel(lam, q):
    # Independent ordered-pair sum on an asymmetric mesh, with both
    # signs of the shifted arguments and with a nonzero final level.
    ts = [QQ(k)/400 for k in (-289, -208, -9, 7, 208, 921)]
    B = [QQ(k)/7 for k in (2, 3, -5, 2, 4, -1)]
    b = s['jumps'](ts, B, s['C'])

    def d(x):
        return (2+abs(x))*(-F(abs(x))/2).exp()

    def h(x):
        u = max(x, QQ(0))
        return (1+u+u*u/2)*(-F(abs(x))/2).exp()

    def kernel(t, v):
        modes = (a*(d(t-v+j*QQ(13)/25)+d(t-v-j*QQ(13)/25))
                 for j, a in enumerate(q[1:], 1))
        hankel = sum(a*h(t+v+QQ(j)/25) for j, a in zip(s['unfold']['S'], lam))
        return q[0]*d(t-v)+sum(modes)+hankel

    direct = sum(bi*bj*kernel(t, v) for t, bi in zip(ts, b) for v, bj in zip(ts, b))
    assert abs(quadratic(ts, B, lam, q)-direct) < QQ(1)/10**20


def loss_budget():
    data, center, sigma, constant = r['tangent_data'](r['load_certificate']('eight-knots'))
    z = r['z']
    # The best scalar floor using just Q(V_B) <= d and the radius of Z
    # is too small to close even the checked positive raw lower price.
    _, lam, _ = next(row for row in data if len(row) == 3)
    q = s['second_majorant'](list(map(F, lam)))
    d = q[0]+2*sum(a*(-F(j)*13/50).exp() for j, a in enumerate(q[1:], 1))
    qc = (constant+F(8)/9-sum(F(row[-1]) for row in data if len(row) == 5))/F(sigma)-d
    radial_floor = F(sigma)*(d.sqrt()-qc.sqrt())**2
    print('Radial second-slack floor:', radial_floor, flush=True)
    assert radial_floor < QQ(11)/10**16

    _, original, old, _ = r['mesh_prices'](data, center, constant, 400, [], 60,
                                            tail_den=800)
    sites = {QQ(k)/400 for k in w['SET']}
    bound = original+sum(r['costs']['release_costs'](z, center, data, old, 6400, sites))
    print('Uniform raw upper price:', bound, flush=True)
    assert bound < QQ(107)/10**11
    radius = QQ(13)/10**4
    assert QQ(107)/10**11+QQ(1)/10**10 < F(sigma)*radius**2


@cache
def profiles():
    return [w['profile'](name) for name in ('frequency-one','five-caps')]


def check_case(case):
    cert = r['load_certificate'](case)
    data, center, _, _ = r['tangent_data'](cert)
    _, lam, sigma = next(row for row in data if len(row) == 3)
    lam = list(map(F,lam))
    q = s['second_majorant'](lam)
    if case == 'eight-knots':
        check_kernel(lam, q)
    table = p['primitives'](case)
    result = []
    for ts, terms in profiles():
        cen = []
        j = 0
        for t in ts:
            while j+1<len(r['z']) and r['z'][j+1] <= t:
                j += 1
            cen.append(center[j])
        # After the law's last knot, B=0, but the center continues at
        # its final level. Include the jump at the cutoff and that tail.
        B = [term[-1]-v for term, v in zip(terms, cen)]+[-cen[-1]]
        loss = F(sigma)*quadratic(ts,B,lam,q)
        raw, = p['prices'](table,[terms])
        result.append((raw, loss, raw-loss))
    return result


if __name__ == '__main__':
    import argparse

    if not __debug__:
        raise SystemExit('Run with assertions enabled.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--jobs', type=int, default=1)
    args = parser.parse_args()
    for i, (ts, terms) in enumerate(profiles()):
        A, B = zip(*(row[-2:] for row in terms))
        caps = [(A,0,s['Ct']), (B,0,s['C']), (A,1,s['Ct'])]
        if i:
            caps.extend([(A,QQ(611)/10,s['Ct']), (B,QQ(2)/5,s['C'])])
        fields = [abs(w['field'](ts, vals, freq, norm)) for vals,freq,norm in caps]
        print('Point moduli:', *fields, flush=True)
        assert all(v<1 for v in fields)
    with ProcessPoolExecutor(max_workers=args.jobs) as pool:
        budget = pool.submit(loss_budget)
        for case, values in zip(p['CASES'], pool.map(check_case, p['CASES'])):
            print(case, '(raw, loss, corrected)', *values, flush=True)
            assert all(raw > QQ(35)/10**12 for raw, _, _ in values)
            assert all(corrected < -QQ(33)/10**4 for _, _, corrected in values)
        budget.result()
