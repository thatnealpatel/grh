"""Certify a fixed-B upper bound with arbitrary atom laws on a specified mesh."""
from math import comb
from pathlib import Path
from runpy import run_path

import numpy as np
from sage.all import QQ

if not __debug__:
    raise SystemExit('Run with assertions enabled.')
base = Path(__file__).resolve().parent
old = run_path(str(base/'check-unfolded-deletion-33.py'))
F, K, Ct, step = (old[k] for k in ('F', 'K', 'Ct', 'step'))
laws = base/'deletion-laws'
z, A, B, U = old['lattice']['prime_rows']((laws/'delete-33-unfolded-seed.txt').read_text())

# Float arrays only nominate a Lagrange multiplier and an upper bound for a
# polynomial. Both the full polynomial check and the final sum use balls.
u = np.linspace(0, 1, 4097)
x = 2*u*u-1
b = 4*x**3-3*x


def nominate(w, d, m):
    obj, dif = float(w)*u-float(d)*x, b-float(m)

    def sign(t):
        return dif[np.argmax(obj-t*dif)]

    l, r = -1., 1.
    for _ in range(40):
        if sign(l) >= 0 and sign(r) <= 0:
            break
        l, r = 2*l, 2*r
    else:
        raise ArithmeticError('sampled multiplier not bracketed')
    for _ in range(55):
        t = (l+r)/2
        if sign(t)>0:
            l = t
        else:
            r = t
    t = (l+r)/2
    return F(str(t)), F(str(max(obj-t*dif)))


def positive_slab(w, d, m):
    # For all u, w*u-d*X <= beta*(T(X)-m) + bound. The beta term
    # integrates to zero under ANY probability measure with E[T(X)]=m.
    beta, nomination = nominate(w, d, m)
    a = [d+beta*(1+m), w, -2*d-18*beta, F(0), 48*beta, F(0), -32*beta]
    bern = [sum(a[k]*QQ(comb(i,k))/comb(6,k) for k in range(i+1)) for i in range(7)]
    bound = nomination+F('1e-10')
    # Adapt the ceiling if the sampled peak was too low. A ceiling is
    # returned only if the Bernstein convex-hull tests cover [0,1].
    radius = F('1e-10')
    for _ in range(18):
        pending = [(bern, 0)]
        while pending:
            v, depth = pending.pop()
            if all(t < bound for t in v):
                continue
            if depth == 28 or any(t >= bound for t in (v[0],v[-1])):
                break
            left, right = [v[0]], [v[-1]]
            while len(v)>1:
                v = [(s+t)/2 for s,t in zip(v,v[1:])]
                left.append(v[0])
                right.append(v[-1])
            pending.extend(((left,depth+1),(right[::-1],depth+1)))
        else:
            return bound
        radius *= 2
        bound = nomination+radius
    raise ArithmeticError('could not bound the slab polynomial')


def extreme(m):
    # The top inverse branch of 4X^3-3X is increasing and concave:
    # it lies above all X at given T(X), hence above E[X] by Jensen.
    m = F(m)
    return (m.arccos()/3).cos()


def price(name, split=False):
    assert z[0] == -QQ(112)/25 and z[-1] == QQ(22)/5 and 0 in z
    knots = [z[0]-QQ(j)/10 for j in range(80,0,-1)]+z+[z[-1]+QQ(j)/5 for j in range(1,81)]
    bs = [QQ(0)]*80+B+[B[-1]]*80
    assert len(knots) == len(bs) == 586 and all(-1<m<1 for m in bs)
    if split:
        mesh = [(k,m) for k,m in zip(knots,bs)]
        mesh += [((l+r)/2,m) for l,r,m in zip(knots,knots[1:],bs) if l<0]
        knots,bs = map(list,zip(*sorted(mesh)))
        assert len(knots) == 868
    duals = []
    for line in (laws/f'delete-33-fixed-third-{name}.duals').read_text().splitlines():
        lam, xi, c, s = map(F, line.split())
        assert lam >= 0
        p = K(c,s)
        duals.append((lam, K(-QQ(1)/2, xi),
                      p.conjugate()/(Ct*K(QQ(1)/2, xi)), abs(p)))
    assert duals
    allowance = sum(lam*p for lam,_,_,p in duals)

    def primitive(t):
        return sum(lam*(p*(k*t).exp()).real() for lam,k,p,_ in duals)

    def negative_slab(d, m):
        return [d*extreme(-m), -d*extreme(m)]

    v = [primitive(t) for t in knots]+[0]
    prices = []
    half_gain = F(0)
    for l,r,m,d,e in zip(knots,knots[1:]+[None],bs,v,v[1:]):
        if l < 0:
            old = negative_slab(d-e,m)
            price = max(t.upper() for t in old)
            if not split:
                mid = primitive((l+r)/2)
                new = [negative_slab(d-mid,m), negative_slab(mid-e,m)]
                half_gain += sum(F(max(t.lower() for t in side)) for side in new)-F(price)
        else:
            w = step(l,0)-(step(r,0) if r is not None else 0)
            price = positive_slab(w,d-e,m)
        prices.append(F(price))
    bound = allowance+sum(prices)-F(8)/9
    print('Slabs:', len(prices), '; cap cuts:',len(duals), '; upper surplus:', bound,flush=True)
    if not split:
        print('Lower bound on negative-slab price increase after halving:', half_gain,flush=True)
        assert bound < F('-6.29e-7')
        assert half_gain > F('8.23e-6')
    else:
        assert bound < F('-1.22e-7')


def positive_without_t_cap():
    # An exact one-atom B-preserving replacement on the whole positive tail.
    a = extreme(B[-1])
    u = ((1+a)/2).sqrt()
    m = sum((step(l,0)-step(r,0))*v for l,r,v in zip(z,z[1:],U))
    surplus = m+step(z[-1],0)*u-F(8)/9
    print('Upper-branch tail atom surplus without the t cap:',surplus,flush=True)
    assert 0 < u < 1 and surplus > F('.0010795')
    h = sum((step(l,0)-step(r,0))*v for l,r,v in zip(z,z[1:],A))
    tests = [h+step(z[-1],0)*v for v in (A[-1],a)]
    assert F('.588277') < tests[0] < F('.588279')
    assert F('.592080') < tests[1] < F('.592082')
    assert all(abs(q)<Ct for q in tests)
    print('Exponential Hankel tests (seed, tail modification); required cap:',*tests,Ct,flush=True)


if __name__ == '__main__':
    price('left')
    price('halved', split=True)
    positive_without_t_cap()
