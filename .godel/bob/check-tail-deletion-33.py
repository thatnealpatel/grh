"""Ball checks for the split-tail and joint-refit upper price at c=39/20."""
import argparse
import json
from math import comb
from pathlib import Path
from runpy import run_path

from sage.all import QQ

base = Path(__file__).resolve().parent
unfold = run_path(str(base/'check-unfolded-deletion-33.py'))
F, K, P = (unfold[k] for k in ['F', 'K', 'P'])
C, Ct = unfold['C'], unfold['Ct']
fft, jumps, cap, complete = (unfold[k] for k in ['fft', 'jumps', 'cap', 'complete'])
step = unfold['step']
knots = [2340,2360,2400,2480,2560,2720,2880,3200,4000,4800]


def bern_upper(a, b, mass, eps):
    # Upper-bound max_{0<=u<=1} mass*u - a*(2u^2-1) - b*(32u^6-48u^4+18u^2-1).
    q = [a+b,mass,-2*a-18*b,F(0),48*b,F(0),-32*b]
    beta = [sum(q[j]*QQ(comb(k,j))/comb(6,j) for j in range(k+1)) for k in range(7)]
    best = max(beta[0].lower(),beta[-1].lower())
    stack = [beta]
    while stack:
        beta = stack.pop()
        if all(v < F(best)+eps for v in beta):
            continue
        le, ri = [], []
        while beta:
            le.append(beta[0]); ri.append(beta[-1])
            beta = [(x+y)/2 for x,y in zip(beta,beta[1:])]
        best = max(best,le[-1].lower())
        stack.extend([le,ri[::-1]])
    return F(best)+F(eps)


def second_majorant(lam):
    # q is a globally positive Laurent majorant of |L|. Its addition
    # as the coefficient of |V_B|^2 makes the disk test convex.
    N, D = 1024, 192
    vals = [abs(lam[0]*v.conjugate()+lam[1]+lam[2]*v)
            for v in (K(0,2*F.pi()*j/N).exp() for j in range(N))]
    a = [v.real()/N for v in fft(vals)[:D+1]]
    p = P(a[:0:-1]+a)
    # If |cos(theta)|>.9 use Re L, otherwise use Im L. The test
    # bounds either part away from zero, without evaluating a grid.
    assert F('.9')*abs(lam[0]+lam[2])-abs(lam[1]) > F('.1')
    assert F('.19').sqrt()*abs(lam[0]-lam[2]) > F('.1')
    e = sum(abs(v) for v in (p*p-P.gen()**(2*D-2)*P(lam)*P(lam[::-1])).list())
    assert e < F('1e-8') and p(F(1)) > 0
    a[0] += 10*e  # p > 0 and p+|L| > .1 everywhere
    return a


def second_tangent(z, b, lam, a):
    D = len(a)-1
    dh = 208
    k = [int(t*400) for t in z]
    J = k[-1]-k[0]
    assert all(t*400 == j for t,j in zip(z,k))
    tv = [F(i)/400 for i in range(J+D*dh+1)]
    df = [(2+t)*(-t/2).exp() for t in tv]
    kd = [a[0]*df[i]+sum(a[j]*(df[i+j*dh]+df[abs(i-j*dh)]) for j in range(1,D+1))
          for i in range(J+1)]
    def f(i):
        t = F(i)/400
        u = max(i,0)/QQ(400)
        return (1+u+u*u/2)*(-abs(t)/2).exp()
    ks = [sum(h*f(i+j*16) for h,j in zip(lam,[-7,6,19]))
          for i in range(2*k[0],2*k[-1]+1)]
    bp = P(dict(zip([i-k[0] for i in k],b)))
    br = P(dict(zip([k[-1]-i for i in k],b)))
    dprod = bp*P(kd[:0:-1]+kd)
    sprod = br*P(ks)
    v = [dprod[J+i-k[0]]+sprod[J+i-k[0]] for i in k]
    d = a[0]+2*sum(a[j]*(F(-j*dh)/800).exp() for j in range(1,D+1))
    return d,v


def tail_data(z, B, data, points, den, *, primitive=False):
    # First and tangent prices, or their integrals from each point to infinity.
    h = QQ(1)/den
    k = [int(t/h) for t in z]
    assert all(i*h == t for i,t in zip(k,z)) and den % 400 == 0
    bstar = [v for v in jumps(z,B,C)]
    lo, hi = points[0], points[-1]
    assert k[-1] <= lo
    x = [F(j)*h for j in points]
    w = [(-t/2).exp() for t in x]
    aa, bb = [F(0) for _ in x], [F(0) for _ in x]
    size, slope, curvature = F(0), F(0), F(0)  # weighted envelopes
    for row in data:
        j, scale = int(row[0]), F(row[-1])
        if len(row) == 5:
            f, re, im = map(F,row[1:-1])
            v = K(re,im)
            v /= abs(v)
            D = Ct if j == 0 else C
            wbar = K(F(1)/2,-f)
            coeff = scale/D*(1 if primitive else wbar)/wbar.conjugate()*v.conjugate()
            target = aa if j == 0 else bb
            for i,t in enumerate(x):
                target[i] += w[i]*(coeff*K(0,f*t).exp()).real()
            size += 2*scale/D
            slope += 2*scale/D*abs(wbar)
            curvature += 2*scale/D*(F(1)/4+f*f)
        else:
            lam = list(map(F,row[1]))
            q = second_majorant(lam)
            s = den//400
            dh = 208*s
            H = dh*(len(q)-1)
            J = k[-1]-k[0]
            ap = P(dict(zip(range(0,2*H+1,dh),q[:0:-1]+q)))
            bp = P(dict(zip([i-k[0] for i in k],bstar)))
            br = P(dict(zip([k[-1]-i for i in k],bstar)))
            dl, dr = lo-k[-1]-H, hi-k[0]+H
            kl, kr = lo+k[0], hi+k[-1]
            shifts = [s*i for i in (-112,96,304)]
            n = max(abs(dl),abs(dr),abs(kl+shifts[0]),abs(kr+shifts[-1]))
            E = [(F(-i)/(2*den)).exp() for i in range(n+1)]
            def d(j):
                return (2+abs(j)*h if primitive else 1+max(j,0)*h)*E[abs(j)]
            def g(j):
                u = max(j,0)*h
                return ((1+u if primitive else 0)+u*u/2)*E[abs(j)]
            dp = (bp*ap)*P([d(i) for i in range(dl,dr+1)])
            kp = br*P([sum(a*g(i+s) for s,a in zip(shifts,lam)) for i in range(kl,kr+1)])
            for i,p in enumerate(points):
                bb[i] += w[i]*2*scale/C*(dp[J+2*H+p-lo]+kp[J+p-lo])
            bnorm = sum(abs(b) for b in bstar)
            qnorm = abs(q[0])+2*sum(abs(a) for a in q[1:])
            lnorm = sum(abs(a) for a in lam)
            size += 8*scale/C*bnorm*(qnorm+lnorm)
            slope += 4*scale/C*bnorm*(qnorm+2*lnorm)
            curvature += 4*scale/C*bnorm*(qnorm+4*lnorm)
    return aa, bb, size, slope, curvature


def continuous_tail(z, A, B, U, data):
    den, lo, hi = 800, 4640, 38400
    h = QQ(1)/den
    points = range(lo,hi+1)
    aa, bb, size, _, curvature = tail_data(z,B,data,points,den)
    w = [(F(-i)*h/2).exp() for i in points]
    vals = []
    for i,(a,b,v) in enumerate(zip(aa,bb,w),lo):
        m = F(i)*h*v**2
        vals.append(bern_upper(a,b,m,F('1e-11'))-(m*U[-1]-a*A[-1]-b*B[-1]))
    trap = h*(sum(vals[1:-1])+(vals[0]+vals[-1])/2)
    error = h*h/8*(F(h).exp()*(step(lo*h,0)-step(hi*h,0))
                   + 2*curvature*F(h/2).exp()*(w[0]-w[-1]))
    remote = step(hi*h,0)+2*size*w[-1]
    print('Measurable intervals: grid',trap,'interpolation',error,'remote',remote,flush=True)
    return trap+error+remote


def moving_tail(z, A, B, U, data, den, radius, R):
    # Optimize the score on the endpoint grid by dynamic programming.
    # Then interpolate in the boundary coordinates, keeping each law fixed.
    h = QQ(1)/den
    s = den//400
    bands = [list(range(j*s-radius,j*s+radius+1)) for j in knots]
    levels = [[int(z[-1]*den)]]+bands+[[None]]
    points = [k for m in levels[:-1] for k in m]
    aa, bb, size, slope, _ = tail_data(z,B,data,points,den,primitive=True)
    prim = {k:(step(k*h,0),a,b) for k,a,b in zip(points,aa,bb)}
    prim[None] = (F(0),)*3
    def increment(l,r):
        m,a,b = [x-y for x,y in zip(prim[l],prim[r])]
        return bern_upper(a,b,m,F('1e-12'))-(m*U[-1]-a*A[-1]-b*B[-1])
    dp = [F(0)]
    for prev,curr in zip(levels,levels[1:]):
        dp = [F(max((score+increment(l,r)).upper() for score,l in zip(dp,prev)))
              for r in curr]
    err = F(0)
    for band in bands:
        t = F(band[0])*h
        err += h*h/8*(t*(-t).exp()+slope*(-t/2).exp())
    remote = step(R,0)+2*size*(F(-R)/2).exp()
    print('Moving tail: radius',radius*h,'grid',dp[0],'interpolation',err,
          f'remote beyond {R}',remote,flush=True)
    return dp[0]+err+remote


def price(z, A, B, U, data, omit=()):
    bstar = jumps(z, B, C)
    az, bz = [F(0) for _ in z], [F(0) for _ in z]
    room, remote_density = F(0), F(0)
    for row in data:
        j, scale = int(row[0]), F(row[-1])
        assert j in (0, 1) and scale >= 0
        if len(row) == 5:
            x, r, i = map(F, row[1:-1])
            unit = K(r, i)
            unit /= abs(unit)  # Exactly unit modulus even after rounding.
            den = Ct if j == 0 else C
            phi = [(K(-F(t)/2, x*F(t)).exp()*unit.conjugate()/K(F(1)/2, x)).real()
                   for t in z]
            area = [scale*(u-v)/den for u, v in zip(phi, phi[1:]+[F(0)])]
            Y, target = (A, az) if j == 0 else (B, bz)
            room += scale-sum(a*y for a, y in zip(area, Y))
            remote_density += 2*scale/den
        else:
            assert len(row) == 3 and j == 1
            lam = list(map(F, row[1]))
            q = second_majorant(lam)
            d, v = second_tangent(z, bstar, lam, q)
            room += scale*(d-sum(a*b for a, b in zip(v, bstar)))
            phi = [a*(-F(t)/2).exp() for a, t in zip(v, z)]
            area = [2*scale*(a-b)/C for a, b in zip(phi, phi[1:]+[F(0)])]
            target = bz
            bnorm = sum(abs(b) for b in bstar)
            qnorm = abs(q[0])+2*sum(abs(a) for a in q[1:])
            remote_density += 8*scale/C*bnorm*(qnorm+sum(abs(a) for a in lam))
        for k, a in enumerate(area):
            target[k] += a
    mass = [step(t, 0)-step(s, 0) for t, s in zip(z, z[1:])]+[step(z[-1], 0)]
    ref = sum(m*u for m, u in zip(mass, U))-F(8)/9
    zonal = [F(0), F(0), F(0)]
    eps = F('1e-12')
    for t, a, b, m, u, y, w in zip(z, az, bz, mass, U, A, B):
        if t in omit:
            continue
        j = 0 if t < 0 else 1 if t < QQ(29)/5 else 2
        zonal[j] += bern_upper(a, b, m, eps)-(m*u-a*y-b*w)
    R = QQ(40)
    remote = step(R, 0)+2*remote_density*(F(-R)/2).exp()
    print('Baseline surplus:', ref, flush=True)
    print('Combined slack:', room, flush=True)
    print('Independent arbitrary-u gains (negative, pre-tail, tail):', zonal, flush=True)
    print('Uniform allowance beyond z=40:', remote, flush=True)
    return ref+room, zonal, remote


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--skip-baseline-check', action='store_true')
    p.add_argument('--probe-dual', type=Path)
    p.add_argument('--fine-tail', action='store_true', help='only with --probe-dual')
    p.add_argument('--movable', action='store_true')
    p.add_argument('--continuous', action='store_true')
    args = p.parse_args()
    assert not args.fine_tail or args.probe_dual
    tab = base/'deletion-laws/delete-33-tail-baseline.txt'
    z, A, B, U = unfold['lattice']['prime_rows'](tab.read_text())
    assert len(z) == 1257 and z[0] == QQ(-144)/25 and z[-1] == QQ(29)/5
    assert 0 in z
    if not args.skip_baseline_check:
        surplus = sum((step(t, 0)-step(s, 0))*u for t, s, u in zip(z, z[1:], U))+step(z[-1], 0)*U[-1]-F(8)/9
        print('Baseline: tail mass', step(z[-1], 0), 'last U', U[-1], 'surplus', surplus, flush=True)
        assert F('-6.608e-7') < surplus < F('-6.607e-7')
        cap(z, jumps(z, A, Ct), F('.9999998'))
        cap(z, jumps(z, B, C), F('.999975'))
        complete(z, jumps(z, B, C), list(map(F, ['113.71074849', '153.65856922', '156.52872908'])),
                 degree=256, grid_size=65536, min_slack='.0000014')
    read_dual = lambda p: json.loads(p.read_text(), parse_float=str)
    if args.continuous:
        data = read_dual(base/'deletion-laws/delete-33-continuous-tail-dual.json')
        off, gain, _ = price(z,A,B,U,data,omit={z[-1]})
        bound = off+gain[0]/4+continuous_tail(z,A,B,U,data)
        print('Measurable tail, quarter negative mix, unchanged pre-tail:',bound,flush=True)
        assert bound < F('-1e-8')
        return
    extra = knots
    if args.fine_tail:
        extra = sorted(set(knots+list(range(2330, 4801, 10))+list(range(4840, 9601, 40))))
    dual = args.probe_dual or base/'deletion-laws/delete-33-tail-dual.json'
    data = read_dual(dual)
    if args.movable:
        assert not args.fine_tail
        off, gain, _ = price(z,A,B,U,data,omit={z[-1]})
        for pre, den, rad, R in [(1,6400,1,48),(QQ(1)/4,3200,4,40)]:
            bound = off+gain[0]+pre*gain[1]+moving_tail(z,A,B,U,data,den,rad,QQ(R))
            print('Moving tail, full negative freedom, pre-tail replacement',pre,':',bound,flush=True)
            if not args.probe_dual:
                assert bound < F('-1e-8')
        return
    z += [QQ(k)/400 for k in extra]
    for Y in [A, B, U]:
        Y += [Y[-1]]*len(extra)
    off, gain, remote = price(z,A,B,U,data)
    bound = off+sum(gain)+remote
    print('Complete mesh upper plus remote:',bound,flush=True)
    if not args.probe_dual:
        assert bound < F('-1e-8')


if __name__ == '__main__':
    main()
