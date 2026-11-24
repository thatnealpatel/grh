"""Check the recovered five-release law and its fixed-field price."""
from bisect import bisect_right
from fractions import Fraction
import gzip
from hashlib import sha256
import json
from pathlib import Path
from runpy import run_path
import sys

from sage.all import QQ, matrix, vector

base = Path(__file__).resolve().parent
p = run_path(str(base/'refined-prices-33.py'))
s, F, z = (p[k] for k in ('s', 'F', 'z'))
K = s['K']
DEN, SCALE = 25600, 10**14
SITES = (0, 2, 4, 6, 16)


def quadratic(y, w, lam, q):
    """Evaluate the inherited jump-kernel form without a dense convolution."""
    # D uses x=t_i+h, with argument x-t_j. H uses x=t_i+h,
    # with argument x+t_j. Prefix/suffix sums are independent of h.
    E = [(F(t)/(2*DEN)).exp() for t in y]
    t = [F(j)/DEN for j in y]
    wp, wm = [a*b for a,b in zip(w,E)], [a/b for a,b in zip(w,E)]

    def sums(weights, k, reverse=False):
        result = [F(0)]
        for i in (range(len(y)-1, -1, -1) if reverse else range(len(y))):
            result.append(result[-1]+weights[i]*t[i]**k)
        return result[::-1] if reverse else result

    p0, p1 = [sums(wp, k) for k in range(2)]
    m0, m1 = [sums(wm, k, True) for k in range(2)]
    m2 = sums(wm, 2, True)

    def d(j, v):
        e = E[j]*v
        x = t[j]+vshift
        i = bisect_right(y, y[j]+shift)
        return ((2+x)*p0[i]-p1[i])/e+e*((2-x)*m0[i]+m1[i])

    def h(j, v):
        e = E[j]*v
        x = t[j]+vshift
        i = bisect_right(y, -y[j]-shift)
        return e*p0[i]+((1+x+x*x/2)*m0[i]+(1+x)*m1[i]+m2[i]/2)/e

    value = F(0)
    for j, coeff in enumerate(q):
        shift = j*13*DEN//25
        vshift = F(shift)/DEN
        e = (vshift/2).exp()
        value += (1 if j == 0 else 2)*coeff*sum(a*d(i,e) for i,a in enumerate(w))
    for j, coeff in zip((-7,6,19), lam):
        shift = j*DEN//25
        vshift = F(shift)/DEN
        e = (vshift/2).exp()
        value += coeff*sum(a*h(i,e) for i,a in enumerate(w))
    return value


def self_test():
    y = [-17408, -13312, -9, 7, 13312, 22464]
    w = list(map(F, [2, 3, -5, 2, 4, -1]))
    lam, q = list(map(F, [3, -2, 4])), list(map(F, [5, 2, -3, 1]))
    def d(t):
        return (2+abs(t))*(-abs(t)/2).exp()
    def h(t):
        u = max(t, F(0))
        return (1+u+u*u/2)*(-abs(t)/2).exp()
    v = F(0)
    for i,a in zip(y,w):
        for j,b in zip(y,w):
            x, t = F(i-j)/DEN, F(i+j)/DEN
            v += a*b*(q[0]*d(x)+sum(c*(d(x+k*F(13)/25)+d(x-k*F(13)/25))
                                    for k,c in enumerate(q[1:],1))
                      +sum(c*h(t+F(k)/25) for k,c in zip((-7,6,19),lam)))
    assert abs(v-quadratic(y,w,lam,q)) < QQ(1)/10**25


def data(path):
    with gzip.open(path,'rt') as f:
        rows=json.load(f)
    zz, ar, br, ur = s['unfold']['lattice']['prime_rows'](p['ref'].decode())
    ks = [row[0] for row in rows]
    assert all(type(k) is int for k in ks)
    assert all(a < b for a,b in zip(ks,ks[1:])) and ks[-1] == 56*DEN
    tk = [int(t*DEN) for t in zz]
    assert all(QQ(k)/DEN==t for k,t in zip(tk,zz))
    assert ks[0] == tk[0] and set(tk) <= set(ks)
    assert all(k in tk or k >= 2320*(DEN//400) or
               any(l*DEN <= 400*k <= (l+2)*DEN for l in SITES) for k in ks)
    assert rows[-1] == [56*DEN,SCALE]
    A,B,U = [],[],[]
    for k, base, *terms in rows:
        assert len(terms)%2==0 and all(type(v) is int for v in [base,*terms])
        assert 0<=base<=SCALE
        i = bisect_right(tk,k)-1
        atoms, weights = terms[::2],terms[1::2]
        assert all(0<=u<=SCALE for u in atoms) and all(w>0 for w in weights)
        assert base+sum(weights)==SCALE
        u = [QQ(t)/SCALE for t in atoms]
        x = [2*t*t-1 for t in u]
        for out,y,v in zip((A,B,U),(ar[i],br[i],ur[i]),(x,[(4*t*t-3)*t for t in x],u)):
            out.append((base*y+sum(w*t for w,t in zip(weights,v)))/SCALE)
    return ks,A,B,U


def check():
    ks,A,B,U = data(p['laws']/'delete-33-five-release-recovery.json.gz')
    ts = [QQ(k)/DEN for k in ks]
    ms = [s['step'](t,0) for t in ts]+[F(0)]
    mass = sum((a-b)*u for a,b,u in zip(ms,ms[1:],U))-QQ(8)/9
    print('surplus',mass,flush=True)
    assert F('-6.6e-8') < mass < F('-6.4e-8')
    raw = (p['laws']/'delete-33-five-release-joint-refit.json').read_bytes()
    assert sha256(raw).hexdigest() == '0b288072bc772e52fc7fb42aea4ca8544cc2d5e40d90e19d1d18e2de47bb54e2'
    cert = json.loads(raw,parse_float=str)
    J = [s['jumps'](ts,Y,c) for Y,c in zip((A,B),(s['Ct'],s['C']))]

    def first(j, f):
        return sum(b*K(0,f*t).exp() for b,t in zip(J[j],ts))/K(QQ(1)/2,f)

    V = {}
    for j, f, *_ in (r for r in cert['cuts'] if len(r)==5):
        key = (j, QQ(Fraction(f)))
        if key not in V:
            V[key] = first(*key)
    for j, count in enumerate((581,62)):
        out = [abs(v) for (k,_),v in V.items() if k==j]
        assert len(out)==count
        worst = max(v.upper() for v in out)
        print('Inherited max modulus',j,count,worst,flush=True)
        assert F(worst) < 1-F('1e-10')
    # A single rational frequency disproves the continuous cap, without
    # relying on peak finding or the maximum from a floating scan.
    bad = abs(first(0, QQ(16377)/1000))
    print('Off-list A modulus at 16.377:',bad,flush=True)
    assert (0,QQ(16377)/1000) not in V and bad > F('1.001')

    _, lam, sig = next(row for row in cert['cuts'] if len(row)==3)
    sigma = F(sig)
    lam = list(map(F,lam))
    q = s['second_majorant'](lam)
    d = q[0]+2*sum(a*(-F(k)*13/50).exp() for k,a in enumerate(q[1:],1))
    err = quadratic(ks,J[1],lam,q)-d
    print('Q-d:',err,flush=True)
    assert err < -F('1e-9')

    lo, hi = fiber(p['laws']/'delete-33-five-release-recovery.fiber.json.gz',
                   ks,A,B,U,ms,mass)
    assert lo > F('-6.09e-8') and hi < F('-5.76e-8')

    # Reconstruct the signed reference tangent center, which is not a law.
    bump = {QQ(k)/400:QQ(Fraction(v)) for k,v in cert['jumps']}
    assert len(bump)==len(cert['jumps']) and bump.keys()<=set(p['z'])
    ctr = {}
    prev = shift = QQ(0)
    for t, b in zip(p['z'],p['B']):
        shift += bump.get(t,0)
        ctr[t] = (F(b+shift-prev)*(-F(t)/2).exp()/s['C'])
        prev = b+shift
    dist = quadratic(ks,[b-ctr.get(t,0) for b,t in zip(J[1],ts)],lam,q)
    first_loss = [F(0),F(0)]
    for j, f, re, im, w in (r for r in cert['cuts'] if len(r)==5):
        gamma = K(F(re),F(im))
        v = V[j,QQ(Fraction(f))]
        first_loss[j] += F(w)*(1-(gamma.conjugate()*v).real()/abs(gamma))
    loss = sum(first_loss)+sigma*(dist-err)
    print('First losses:',first_loss, 'second slack loss:',-sigma*err,
          'second distance loss:',sigma*dist,flush=True)
    print('Polished law raw price is at least',lo+loss,
          '; fixed-field raw price upper',hi+loss,flush=True)
    assert F('1.5e-8') < loss < F('1.7e-8')
    assert hi+loss < F('-4.16e-8')


def fiber_weights(us, a, b):
    x = [2*u*u-1 for u in us]
    H = matrix(QQ, [[1]*3, x, [v*(4*v*v-3) for v in x]])
    if H.det() == 0:
        return None
    w = H.solve_right(vector(QQ,[1,a,b]))
    return w if min(w)>=0 else None


def fiber(path, ks, A, B, U, ms, mass):
    with gzip.open(path,'rt') as f:
        rows = json.load(f)
    # We apply pointwise atom upper bounds, so a measurable competitor
    # can have arbitrary laws inside any cell, with only A and B fixed.
    i0 = ks.index(0)
    assert [row[0] for row in rows] == ks[i0:-1]
    gain_upper = gain_lower = F(0)
    for i, (_, *row) in enumerate(rows, i0):
        m = ms[i]-ms[i+1]
        a, b, u = A[i], B[i], U[i]
        bound = ((F(a)+1)/2).sqrt()  # Jensen, including near-degenerate LP cells
        if row:
            ca, cb, *sites = row
            assert len(sites)<=3 and all(type(v) is int for v in row)
            ca, cb = [QQ(v)/10**12 for v in (ca, cb)]
            eps = F('1e-12')
            ub = s['bern_upper'](F(ca), F(cb), F(1), eps)+ca*a+cb*b
            if ub < bound:
                bound = ub
            assert all(0<=v<=SCALE for v in sites)
            if len(sites)==3:
                triple = [QQ(v)/SCALE for v in sites]
                w = fiber_weights(triple, a, b)
                if w is not None:
                    gain_lower += m*max(0,w.dot_product(vector(QQ,triple))-u)
        gain_upper += m*(bound-u)
    # Permit any law with these fields after 56 as well. On negative
    # slabs the mass density is zero, so no fiber change adds surplus.
    gain_upper += ms[-2]*(1-U[-1])
    print('fiber attainable surplus',mass+gain_lower,flush=True)
    print('fiber upper surplus',mass+gain_upper,flush=True)
    return mass+gain_lower, mass+gain_upper


if __name__ == '__main__':
    assert __debug__
    self_test()
    assert fiber_weights([QQ(0),QQ(1)/2,QQ(1)],-QQ(1)/6,QQ(1)/3)==vector(QQ,[QQ(1)/3]*3)
    assert fiber_weights([QQ(0),QQ(1)/2,QQ(1)],QQ(0),QQ(-1)) is None
    if sys.argv[1:] != ['--self-test']:
        assert not sys.argv[1:]
        check()
