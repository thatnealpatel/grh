"""Reprice the historical grouped atom table without an optimizer."""
from bisect import bisect_right
import gzip
import json
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
from runpy import run_path
import sys

from sage.all import QQ

base = Path(__file__).resolve().parent
r = run_path(str(base/'check-five-release-recovery-33.py'))
p, s, F, K, DEN, SCALE = (r[x] for x in ('p', 's', 'F', 'K', 'DEN', 'SCALE'))
C = s['C']


def dot(a, b):
    return sum(x*y for x, y in zip(a, b, strict=True))


def prefixes(values):
    out = [F(0)]
    for v in values:
        out.append(out[-1]+v)
    return out


def potential(src, jump, dst, lam, q):
    """Bilinear kernel on unnormalized jumps, including both shift signs."""
    x = [F(k)/DEN for k in src]
    t = [F(k)/DEN for k in dst]
    decay = [(-u).exp() for u in t]
    w = [a*(-u).exp() for a, u in zip(jump, x)]
    p0, p1 = [prefixes(a*u**j for a, u in zip(jump, x)) for j in range(2)]
    m0, m1, m2 = [prefixes(a*u**j for a, u in zip(w[::-1], x[::-1]))[::-1]
                  for j in range(3)]
    out = [F(0) for _ in dst]
    for h in range(1-len(q), len(q)):
        k = h*13*DEN//25
        v = F(k)/DEN
        e = (-v/2).exp()
        a, b = q[abs(h)]*e, q[abs(h)]/e
        for i, (u, dd) in enumerate(zip(t, decay)):
            j = bisect_right(src, dst[i]+k)
            y = u+v
            out[i] += a*dd*((2+y)*p0[j]-p1[j])+b*((2-y)*m0[j]+m1[j])
    for h, a in zip((-7, 6, 19), lam):
        k = h*DEN//25
        v = F(k)/DEN
        e = (-v/2).exp()
        for i, (u, dd) in enumerate(zip(t, decay)):
            j = bisect_right(src, -dst[i]-k)
            y = u+v
            out[i] += a*(p0[j]/e+e*dd*((1+y+y*y/2)*m0[j]+(1+y)*m1[j]+m2[j]/2))
    return [v/C**2 for v in out]


def self_test():
    src = [-5*DEN, -DEN//2, 0, DEN//25, 2*DEN]
    jump = [2, 3, -5, 2, 4]
    lam, q = [3, -2, 4], [5, 2, -3, 1]
    dst = sorted(set(src+[DEN//25-13*DEN//25, -DEN//25-19*DEN//25]))
    tol = F('1e-28')
    val = potential(src, jump, dst, lam, q)
    for k, v in zip(dst, val):
        t = F(k)/DEN
        dense = F(0)
        for i, a in zip(src, jump):
            x = F(i)/DEN
            for h in range(1-len(q), len(q)):
                u = abs(t-x+F(13*h)/25)
                dense += a*q[abs(h)]*(2+u)*(-(t+x+u)/2).exp()
            for h, c in zip((-7, 6, 19), lam):
                u = t+x+F(h)/25
                y = max(u, F(0))
                dense += a*c*(1+y+y*y/2)*(-(t+x+abs(u))/2).exp()
        assert abs(v-dense/C**2) < tol
    normalized = [a*(-F(i)/(2*DEN)).exp()/C for i, a in zip(src, jump)]
    assert abs(dot(jump, [val[dst.index(i)] for i in src])
               -r['quadratic'](src, normalized, lam, q)) < tol


def main():
    laws = p['laws']
    def load(name, digest):
        path = laws/f'delete-33-five-release-{name}'
        assert sha256(path.read_bytes()).hexdigest() == digest
        return path

    cert = json.loads(load('joint-refit.json',
        '0b288072bc772e52fc7fb42aea4ca8544cc2d5e40d90e19d1d18e2de47bb54e2'
    ).read_bytes(), parse_float=str)
    with gzip.open(load('group12-price.json.gz',
        '9543c61b31c826c9d999263a295896b28df3de2ce5e2cb5e9ea520dadd6a8255'
    ), 'rt') as f:
        price = json.load(f)
    ks,A,B,U = r['data'](load('recovery.json.gz',
        '49ac43e9fa5a1421d1a9b597078cdcb63462f1664be3516820643f8da664315d'))
    unit = DEN//400
    zn = [int(a*DEN) for a in p['z']]
    breaks = (2320,5200,8800,12800,16000,22400)
    tail = {k*unit for a,b,d in zip(breaks,breaks[1:],(8,16,32,64,128))
            for k in range(a,b,d)} | {56*DEN}
    releases = {k for i in r['SITES'] for k in range(i*unit,(i+2)*unit+1)}
    assert ks == sorted(set(zn) | tail | releases)
    n = len(ks)-1
    assert n == 2701
    ends = [0]+price['group_ends']
    assert ends == sorted(set(range(0,n,12)) | {n} | {
        ks.index(k*(DEN//400)) for k in (0,2,4,6,8,16,18,2320,5200,8800,12800,16000)})
    assert len(ends) == 239
    modes = price['modes']
    assert len(modes) == 4 and all(len(row) == n for row in modes)
    assert all(type(x) is int and 0 <= x <= SCALE for row in modes for x in row)
    assert sum(len({tuple(row[l:h]) for row in modes})
               for l,h in zip(ends,ends[1:])) == 927

    x = [QQ(k)/DEN for k in ks]
    t = list(map(F, x))
    envelope = [(-a/2).exp() for a in t]
    W = [s['step'](a,0) for a in x]
    mass = [a-b for a,b in zip(W,W[1:]+[F(0)])]
    surplus = dot(mass,U)-QQ(8)/9
    assert F('-6.524e-8') < surplus < F('-6.523e-8')

    def jumps(v):
        return [a-b for a,b in zip(v,[0]+v[:-1])]

    J = [jumps(v) for v in (A,B)]
    nu = [[F(0) for _ in ks] for _ in range(2)]
    constant = surplus

    rows = [row for row in cert['cuts'] if len(row) == 5]
    weights = {}
    for j,f,_,_,w in rows:
        key = j,QQ(Fraction(f))
        weights[key] = max(weights.get(key,F(0)), F(w))
    assert len(weights) == 643
    directions = {}
    for i,w in price['inherited_direction_weights']:
        j,f,a,b,_ = rows[i]
        g = K(F(a), F(b))
        w = F(w)
        assert w > 0
        key = j,QQ(Fraction(f))
        directions[key] = directions.get(key,K(0))+w*g.conjugate()/abs(g)
        constant += w
    seed_weights = {(j,QQ(Fraction(f))): F(w) for j,f,w in price['seed_direction_weights']}
    assert all(w > 0 for w in seed_weights.values()) and seed_weights.keys() <= weights.keys()
    outside = []
    for j,f in directions.keys() | seed_weights.keys():
        rotation = directions.get((j,f),K(0))
        cf = F(f)
        scale = 1/(([s['Ct'],C][j])*K(F(1)/2,cf))
        # Periodic reanchoring bounds ball growth in repeated phasor products.
        steps, v = {}, []
        for i, (k,tt,e) in enumerate(zip(ks,t,envelope)):
            if i % 128 == 0 or k-ks[i-1] > 16:
                phase = K(0,cf*tt).exp()
            else:
                h = k-ks[i-1]
                if h not in steps:
                    steps[h] = K(0,cf*h/DEN).exp()
                phase *= steps[h]
            v.append(scale*e*phase)
        seed = dot(v,J[j])
        if abs(seed) < 1-F('2e-4') and weights[j,f] <= F('1e-8'):
            outside.append((j,f))
        if (j,f) in seed_weights:
            w = seed_weights[j,f]
            rotation += w*seed.conjugate()/abs(seed)
            constant += w
        nu[j] = [a+(rotation*b).real() for a,b in zip(nu[j],v)]
    assert len(outside) == 2
    print('Priced disk frequencies; outside initial subset:',
          len(directions.keys() | seed_weights.keys()), sorted(outside), flush=True)

    _, la, _ = next(row for row in cert['cuts'] if len(row) == 3)
    lam = list(map(F,la))
    q = s['second_majorant'](lam)
    d = q[0]+2*sum(a*(-F(j)*13/50).exp() for j,a in enumerate(q[1:],1))
    bump = {int(k)*unit: QQ(Fraction(v)) for k,v in cert['jumps']}
    assert bump.keys() <= set(zn)
    Jz = [a+bump.get(k,0) for a,k in zip(jumps(p['B']),zn)]
    anchors = [(zn,Jz), (ks,J[1])]
    for (src,jump), mu in zip(anchors,price['quadratic_weights'],strict=True):
        mu = F(mu)
        assert mu > 0
        v = potential(src,jump,ks,lam,q)
        q_anchor = dot(jump,[v[ks.index(k)] for k in src])
        const_check = r['quadratic'](src,[a*(-F(k)/(2*DEN)).exp()/C
                                         for a,k in zip(jump,src)],lam,q)
        assert abs(const_check-q_anchor) < F('1e-24')
        constant += mu*(d+q_anchor)
        nu[1] = [a+2*mu*b for a,b in zip(nu[1],v)]
    constant -= sum(dot(v,j) for v,j in zip(nu,J))

    # Subtract the chosen upper constraints and maximize the resulting
    # affine functional over each group simplex, including its seed vertex.
    delta_a, delta_b = ([b-a for a,b in zip(v,v[1:])] for v in nu)
    coeff = list(zip(delta_a,delta_b,mass[:-1],strict=True))
    seed = list(zip(A,B,U))
    upper = constant
    for l,h in zip(ends,ends[1:]):
        values = [F(0)]
        for row in modes:
            gain = F(0)
            for i in range(l,h):
                u = QQ(row[i])/SCALE
                a = 2*u*u-1
                atom = (a,(4*a*a-3)*a,u)
                gain += dot(coeff[i],[u-v for u,v in zip(atom,seed[i])])
            values.append(gain)
        upper += F(max(v.upper() for v in values).exact_rational())
    print('Seed surplus; grouped surplus upper:', surplus, upper, flush=True)
    assert upper < F('-4.54e-8')


if __name__ == '__main__':
    assert __debug__
    self_test()
    if sys.argv[1:] != ['--self-test']:
        main()
