"""A continuous upper bound for mobile knots of the delete-33 seed."""
from bisect import bisect_left, bisect_right
from functools import cache
from itertools import accumulate
from json import loads
from math import comb
from pathlib import Path
from runpy import run_path

from sage.all import PolynomialRing, QQ

base = Path(__file__).resolve().parent
u = run_path(str(base / 'check-unfolded-deletion-33.py'))
F, K, C, Ct = (u[k] for k in ('F', 'K', 'C', 'Ct'))
laws = base / 'deletion-laws'
z, A, B, U = u['lattice']['prime_rows'](
    (laws / 'delete-33-unfolded-seed.txt').read_text())
cert = loads((laws / 'delete-33-mobile-dual.json').read_text())


def jump(Y, D):
    return [F(y - prev) / D for y, prev in zip(Y, [0] + Y)]


def majorant():
    # p(theta)=sum p_j exp(i*j*theta), p_-j=p_j.
    lam = [QQ(x) / 10000 for x in (2685, 3623, 3692)]
    p = [QQ(x) / 10**15 for x in cert['majorant']]
    R = PolynomialRing(QQ, 'y')
    L = R(lam)
    Q = R(p[:0:-1] + p)
    err = sum(map(abs, (Q**2 - R.gen()**(2*len(p)-4)*L*R(lam[::-1])).list()))
    # For |cos(theta)|>.76 use the real part; otherwise use the imaginary part.
    lb = QQ(65) / 1000
    cut = QQ(76) / 100
    assert (lam[0] + lam[2])*cut - lam[1] > lb
    assert (lam[2] - lam[0])**2 * (1-cut**2) > lb**2
    assert err < lb**2 and Q(1) > 0
    pad = QQ(2) / 10**7
    assert err / lb < pad
    p[0] += pad
    print('Squared modulus coefficient error:', F(err), flush=True)
    return lam, p


def potential(d, lam, p):
    # For the seed m0, make g(t) with 2*sum deltaB/C*g(t) = DQ_{m0}[m].
    # Differentiate the same prefix/suffix formulas in t through order two.
    h = QQ(13)/25
    ps = [F(0)] + list(accumulate(d))
    pt = [F(0)] + list(accumulate(a*t for a,t in zip(d,z)))
    e = [a*(-F(t)).exp() for a,t in zip(d,z)]
    q0, q1, q2 = [list(accumulate(a*t**k for a,t in zip(e[::-1],z[::-1])))[::-1]
                  + [F(0)] for k in range(3)]
    plus = [(QQ(s)/25,F(a)) for s,a in zip(u['S'],lam)]
    diff = [(j*h,F(p[abs(j)])) for j in range(1-len(p),len(p))]
    plus, diff = ([ (s,a*(F(s)/2).exp(),a*(-F(s)/2).exp()) for s,a in seq]
                  for seq in (plus,diff))
    mass = sum(abs(a)*(-F(t)/2).exp() for a,t in zip(d,z))
    third = mass * (4*sum(map(abs,lam)) + 2*(abs(p[0]) + 2*sum(map(abs,p[1:]))))
    baseline = F(p[0]) + 2*sum(a*(-F(j*h)/2).exp() for j,a in enumerate(p[1:],1))

    def eval_at(t, em):
        g, dg, ddg = F(0), F(0), F(0)
        for s,a,b in plus:
            v = t+s
            j = bisect_left(z,-v)
            r = b*em
            poly2 = (v*v*q0[j]+2*v*q1[j]+q2[j])/2
            g += a*ps[j] + r*((1+v)*q0[j]+q1[j]+poly2)
            dg -= r*poly2
            ddg += r*(poly2-v*q0[j]-q1[j])
        for s,a,b in diff:
            v = t+s
            j = bisect_right(z,v)
            r = b*em
            poly1 = v*ps[j]-pt[j]
            g += r*(2*ps[j]+poly1) + a*((2-v)*q0[j]+q1[j])
            dg -= r*(ps[j]+poly1) + a*q0[j]
            ddg += r*poly1
        return g,dg,ddg

    return eval_at, third, baseline


def upper(v):
    return v.upper().exact_rational()


def lower(v):
    return v.lower().exact_rational()


def upper_on_box(eval_at, lo, hi, D3, tol):
    """Upper bound using quadratic Taylor boxes, with intermediate zero split."""
    assert lo < hi and D3 >= 0

    @cache
    def vals(t, positive):
        return eval_at(t,positive)

    def side(a,b,positive):
        if a == b:
            return upper(vals(a,positive)[0]), 1
        stack, n = [(a,b)], 0
        best = max(lower(vals(e,positive)[0]) for e in (a,b))
        while stack:
            l,r = stack.pop()
            x, h = (l+r)/2, (r-l)/2
            y, dy, ddy = vals(x,positive)
            best = max(best, lower(y))
            # Monotone on the box: it suffices to use one endpoint.
            err = abs(ddy)*h+D3*h*h/2
            if abs(dy)>err:
                e = r if dy>0 else l
                v = vals(e,positive)[0]
                best = max(best,lower(v))
                assert upper(v)-best < tol
            else:
                d, c = upper(abs(dy)), upper(ddy)/2
                if c<0 and d < -2*c*h:
                    inc = -d*d/(4*c)
                else:
                    # Use both ends of [0,h] if the vertex test is ambiguous.
                    inc = d*h + max(0,c)*h*h
                if upper(y + inc + D3*h**3/6) > best+tol:
                    assert h > QQ(1)/2**30
                    stack.extend([(l,x), (x,r)])
            n += 1
        return best+tol, n

    out = [side(lo,min(hi,QQ(0)),False)] if lo<0 else []
    if hi>0:
        out.append(side(max(lo,QQ(0)),hi,True))
    return F(max(v for v,_ in out)), sum(n for _,n in out)


def atom_allowance(caps, mult, eval_g, D3g, radius):
    # Node values of the scalar potentials multiplying U, -A and -B.
    N = 16
    cuts = [[(w,a/D) for w,a in rows] for rows,D in zip(caps,(Ct,C))]

    def coeffs(t):
        W = (1+t)*(-F(t)).exp() if t>0 else F(1)
        a, b = (sum((q*(w*t).exp()).real() for w,q in seq) for seq in cuts)
        b += 2*mult*eval_g(t,(-F(t)).exp())[0]/C
        return W, a, b

    def window(t):
        l, r = t-radius, t+radius
        em = (-F(l)/2).exp()
        d3a, d3b = [em*sum(abs(q)*abs(w)**3 for w,q in seq) for seq in cuts]
        d3b += em*2*mult*D3g/C
        a, b = (sum((q*w**2*(w*t).exp()).real() for w,q in seq) for seq in cuts)
        b += 2*mult*eval_g(t,(-F(t)).exp())[2]/C
        w2 = (F(0) if r<=0 else F(1) if l<=0 else
              abs((t-1)*(-F(t)).exp())+3*radius)
        D2 = w2 + 2*(abs(a)+abs(b)+(d3a+d3b)*radius)
        return [coeffs(l + j*2*radius/N) for j in range(N+1)], D2

    def split(row):
        l,r = [row[0]],[row[-1]]
        while len(row)>1:
            row = [(a+b)/2 for a,b in zip(row,row[1:])]
            l.append(row[0])
            r.append(row[-1])
        return l,r[::-1]

    def reduce(left, right, tol):
        # Bound max_u[max_left price(u) - min_right price(u)] over
        # all node pairs, with de Casteljau on the common u interval.
        stack = [(left,right,0)]
        best = QQ(0)  # Some atom attains >= its seed expectation, zero.
        while stack:
            l,r,depth = stack.pop()
            for j in (0,6):
                best = max(best, max(lower(v[j]) for v in l)-min(upper(v[j]) for v in r))
            if max(max(upper(v[j]) for v in l)-min(lower(v[j]) for v in r)
                   for j in range(7)) > best+tol:
                assert depth < 18
                ls, rs = [list(zip(*(split(row) for row in v))) for v in (l,r)]
                stack.extend((ll,rr,depth+1) for ll,rr in zip(ls,rs))
        return F(best+tol)

    # Bernstein coefficients on [0,1] of X=2u^2-1 and T=32u^6-48u^4+18u^2-1.
    X = [QQ(2*comb(j,2))/15-1 for j in range(7)]
    T = [32*comb(j,6)-QQ(48*comb(j,4))/15+QQ(18*comb(j,2))/15-1
         for j in range(7)]
    left = window(z[0])
    by_side = [F(0), F(0)]
    for i,t in enumerate(z):
        right = window(z[i+1]) if i+1<len(z) else ([(F(0),)*3], F(0))
        u = [QQ(j)/6-U[i] for j in range(7)]
        x, b = [e-A[i] for e in X], [e-B[i] for e in T]

        def bern(nodes):
            return [[w*uj-a*xj-d*bj for uj,xj,bj in zip(u,x,b)] for w,a,d in nodes]

        chord = (left[1]+right[1])*(2*radius/N)**2/8
        by_side[int(t>=0)] += reduce(bern(left[0]), bern(right[0]), QQ(3)/10**10) + chord
        left = right
    return by_side


def setup():
    lam, p = majorant()
    da, db, du = jump(A,Ct), jump(B,C), jump(U,1)
    eval_g, D3g, P = potential(db,lam,p)
    Q0 = sum(a*eval_g(t,(-F(t)).exp())[0] for a,t in zip(db,z))
    print('Seed quadratic price minus P:', Q0-P, flush=True)
    mult = QQ(cert['price'])/10**12
    assert mult>0
    cap_rhs = F(0)
    caps = [[], []]
    for f,i,a,b,c in cert['caps']:
        assert i in (0,1) and c>0 and a*a+b*b<=10**24
        w = K(QQ(1)/2,QQ(f)/100)
        caps[i].append((-w.conjugate(), K(a,b)*QQ(c)/10**24/w))
        cap_rhs += QQ(c)/10**12

    rhs = cap_rhs + mult*(P+Q0)
    return rhs, caps, mult, eval_g, D3g, da, db, du


def mobile_surplus(data, radius):
    rhs, caps, mult, eval_g, D3g, da, db, du = data
    total, boxes = F(0), 0
    for i,t in enumerate(z):
        d, e = da[i], db[i]
        rows = [(w,weight*m) for seq,m in zip(caps,(d,e)) for w,weight in seq]
        b = 2*mult*e

        def priced(t, positive):
            em = (-F(t)).exp()
            if positive:
                v, d1, d2 = du[i]*em*(1+t), -du[i]*em*t, du[i]*em*(t-1)
            else:
                v, d1, d2 = du[i], F(0), F(0)
            g, dg, ddg = eval_g(t,em)
            v-=b*g
            d1-=b*dg
            d2-=b*ddg
            for w,a in rows:
                v0 = a*(w*t).exp()
                v1 = w*v0
                v -= v0.real()
                d1 -= v1.real()
                d2 -= (w*v1).real()
            return v,d1,d2

        # The C^2 sum and difference kernels have a bounded piecewise third
        # derivative. At t=0 only the U-tail splits the Taylor interval.
        D3 = 3*abs(du[i]) + (-F(t-radius)/2).exp()*(abs(b)*D3g
             + sum(abs(a)*abs(w)**3 for w,a in rows))
        bound,n = upper_on_box(priced,t-radius,t+radius,D3,QQ(1)/10**10)
        total += bound
        boxes += n

    gap = rhs + total - F(8)/9
    print('Taylor boxes:', boxes, flush=True)
    print('Upper bound on fixed-law failure surplus:', gap, flush=True)
    return gap


if __name__ == '__main__':
    data = setup()
    radius = QQ(cert['radius'])
    assert len(z) == 426 and radius == QQ(1)/5 and z[0]+radius < 0
    assert mobile_surplus(data, radius) < -QQ(12055)/10**10
    near = QQ(1)/1000
    print('Joint price at radius', near, flush=True)
    base_gap = mobile_surplus(data, near)
    neg, pos = atom_allowance(*data[1:5], near)
    print('Negative and nonnegative atom allowances:', neg, pos, flush=True)
    gap = base_gap + neg/4 + pos
    print('Upper bound on joint failure surplus (one-quarter negative replacement):', gap, flush=True)
    assert gap < -QQ(3)/10**8
