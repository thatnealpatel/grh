"""Check the rounded joint recovery and price local freezes of its seed."""
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
from runpy import run_path
import sys

from sage.all import QQ

base = Path(__file__).resolve().parent
r = run_path(str(base/'check-five-release-recovery-33.py'))
c = run_path(str(base/'check-five-release-joint-refit-33.py'))
p, s, F, K, DEN = (r[k] for k in ('p', 's', 'F', 'K', 'DEN'))
laws = p['laws']
SLOPE_DEN = 10**20
RAW_UPPER = QQ(72)/10**11  # Full measurable bound, replayed by c['main'].
TARGET = -QQ(1)/10**10


def freeze_lower(a, b, m, j, delta, seed):
    # The original support minus the corrected support. The corrected
    # score is the original score minus delta*(field-seed).
    lo, _ = c['support'](a, b, m)
    _, hi = c['support'](a+(delta if j == 0 else 0),
                         b+(delta if j == 1 else 0), m)
    return (lo-hi-delta*seed).lower().exact_rational()


def remaining(bounds, free):
    return sum(bounds)-sum(max(0,b) for b in sorted(bounds, reverse=True)[:free])


def self_test():
    r['self_test']()
    # The A correction changes 3X to -X-4, with maxima 3 and -3.
    a = freeze_lower(F(-3), F(0), F(0), 0, QQ(4), QQ(-1))
    assert QQ(599)/100 < a <= QQ(6)
    # The B correction changes -2T(X) to T(X)-3, with maxima 2 and -2.
    b = freeze_lower(F(0), F(2), F(0), 1, QQ(-3), QQ(1))
    assert QQ(399)/100 < b <= QQ(4)
    assert remaining([a, b, QQ(1)], 1) == b+1
    assert remaining([a, -b, QQ(-1)], 2) == -b-1


def prices(cert, comparison):
    data, center, _, _ = p['tangent_data'](cert)
    z = p['z']
    points = [int(400*t) for t in z]
    a, b, *_ = s['tail_data'](z, center, data, points, 400, primitive=True)
    m = [s['step'](t, 0) for t in z]
    cells = dict(zip(points, zip(a, b, m)))
    index = dict(zip(points, range(len(points))))
    old_k, *old = r['data'](laws/'delete-33-five-release-recovery.json.gz')
    old_idx = {k: i for i, k in enumerate(old_k)}
    new_k, *new = comparison
    assert new_k == old_k
    # Loss from just the ordinary constant slabs of the rounded trial.
    # The maximal raw price is separable across ordinary and released slabs.
    loss_by_side = [F(0), F(0)]
    for k, e in zip(points, points[1:]):
        if k in c['SITES']:
            continue
        i = old_idx[k*(DEN//400)]
        assert old_k[i+1] == e*(DEN//400)
        a, b, m = (x-y for x,y in zip(cells[k], cells[e]))
        lo, _ = c['support'](a,b,m)
        loss_by_side[k>=0] += lo-(m*new[2][i]-a*new[0][i]-b*new[1][i])
    print('Ordinary slab deficits (negative, nonnegative):', loss_by_side, flush=True)
    assert sum(loss_by_side) > F('8.2e-10')
    rows_b = [tuple(map(int, line.split())) for line in
              (laws/'delete-33-five-release-B-slopes.txt').read_text().splitlines()]
    assert len(rows_b) == len({k for k, _ in rows_b}) == 386
    for j, rows in enumerate(([(-320, 3538379393184)], rows_b)):
        reductions, changes, slopes = [], [], []
        for k, q in rows:
            assert k in index and index[k]+1 < len(points)
            assert k < 2320 and k not in c['SITES']
            e = points[index[k]+1]
            i = old_idx[k*(DEN//400)]
            assert old_k[i+1] == e*(DEN//400)
            delta = QQ(q)/SLOPE_DEN
            abc = [a-b for a,b in zip(cells[k], cells[e])]
            loss = freeze_lower(*abc, j, delta, old[j][i])
            assert loss > 0
            reductions.append(loss)
            changes.append(new[j][i]-old[j][i])
            slopes.append(delta)
        if j == 0:
            assert delta > 0
            move = (TARGET-RAW_UPPER+reductions[0])/delta
            print('Necessary A increase at -320/400:', F(move),
                  '; rounded trial change:', F(changes[0]), flush=True)
            assert move > QQ(4)/1000
        else:
            eps = QQ(1)/10**6
            need = TARGET-RAW_UPPER+sum(reductions)
            earned = sum(slope*change for slope,change in zip(slopes,changes))
            net = [lo-eps*abs(slope) for lo,slope in zip(reductions,slopes)]
            residue = remaining(net, 40)
            bound = RAW_UPPER-residue
            print('Necessary signed B displacement:', F(need),
                  '; rounded trial displacement:', F(earned), flush=True)
            print('B reduction after freeing best 40 with tolerance:', F(residue),
                  '; raw upper:', F(bound), flush=True)
            print('B moves beyond tolerance on rounded trial:',
                  sum(abs(x)>eps for x in changes), flush=True)
            assert need > QQ(126)/10**11 and bound < TARGET


def check_law(cert):
    ks,A,B,U = r['data'](laws/'delete-33-five-release-joint-recovery.json.gz')
    assert len(ks) == 2702
    ts = [QQ(k)/DEN for k in ks]
    ms = [s['step'](t,0) for t in ts]+[F(0)]
    mass = sum((a-b)*u for a,b,u in zip(ms,ms[1:],U))-QQ(8)/9
    print('Surplus:',mass,flush=True)
    assert F('-5.547e-8') < mass < F('-5.546e-8')
    J = [s['jumps'](ts,Y,d) for Y,d in zip((A,B),(s['Ct'],s['C']))]

    def first(j, f):
        return sum(b*K(0,f*t).exp() for b,t in zip(J[j],ts))/K(QQ(1)/2,f)

    V = {}
    first_loss = F(0)
    for j,f,re,im,w in (row for row in cert['cuts'] if len(row)==5):
        key = j, QQ(Fraction(f))
        if key not in V:
            V[key] = first(*key)
        gamma = K(F(re),F(im))
        first_loss += F(w)*(1-(gamma.conjugate()*V[key]).real()/abs(gamma))
    for j, count, bound in ((0,581,'0.999999999991'), (1,62,'0.99999966')):
        out = [abs(v) for (k,_),v in V.items() if k == j]
        assert len(out) == count
        worst = F(max(v.upper() for v in out))
        print('Inherited maximum:', j, worst, flush=True)
        assert worst < F(bound)
    badf = QQ(16377)/1000
    assert (0,badf) not in V
    bad = abs(first(0,badf))
    print('Off-list A modulus at 16.377:',bad,flush=True)
    assert bad > 1

    _, la, sig = next(row for row in cert['cuts'] if len(row)==3)
    lam, sigma = list(map(F,la)), F(sig)
    q = s['second_majorant'](lam)
    d = q[0]+2*sum(a*(-F(k)*13/50).exp() for k,a in enumerate(q[1:],1))
    form = r['quadratic']
    err = form(ks,J[1],lam,q)-d
    print('Full Q-d:',err,flush=True)
    assert F('-5.58e-7') < err < F('-5.56e-7')
    bump = {QQ(k)/400:QQ(Fraction(v)) for k,v in cert['jumps']}
    assert len(bump) == len(cert['jumps']) and bump.keys() <= set(p['z'])
    shift, center = QQ(0), []
    for t,b in zip(p['z'],p['B']):
        shift += bump.get(t,0)
        center.append(b+shift)
    ctr = dict(zip(p['z'],s['jumps'](p['z'],center,s['C'])))
    assert ctr.keys() <= set(ts)
    dist = form(ks,[v-ctr.get(t,0) for t,v in zip(ts,J[1])],lam,q)
    raw = mass+first_loss+sigma*(dist-err)
    print('First slack:',first_loss,'; Q center distance squared:',dist,
          '; raw price:',raw,flush=True)
    assert F('-4.117e-8') < raw < F('-4.115e-8')
    return ks,A,B,U


def main():
    assert __debug__
    self_test()
    if sys.argv[1:] == ['--self-test']:
        return
    assert not sys.argv[1:]
    raw = (laws/'delete-33-five-release-joint-refit.json').read_bytes()
    assert sha256(raw).hexdigest() == '0b288072bc772e52fc7fb42aea4ca8544cc2d5e40d90e19d1d18e2de47bb54e2'
    cert = json.loads(raw,parse_float=str)
    prices(cert,check_law(cert))


if __name__ == '__main__':
    main()
