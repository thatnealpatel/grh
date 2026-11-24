"""SageMath: Price all convex mixtures of five existing first laws on one triple."""
from collections import defaultdict
from functools import cache
from pathlib import Path
from sage.all import QQ, RealBallField

if not __debug__:
    raise SystemExit('Run with assertions enabled.')
F = RealBallField(128)
C = F(QQ(39)/20).cosh()/3
M = 10**8


def law(name):
    # Common knot unit 1/128, including the finer hard-pair input.
    zden = 128 if name == 'hard-pair' else 64
    prev = 0
    points = []
    for line in Path(f'.godel/bob/{name}-10-2.txt').read_text().splitlines():
        if not (line := line.split('#')[0].strip()):
            continue
        k, *row = map(int, line.split())
        assert len(row) % 2 == 0 and sum(row[1::2]) == M
        b = sum(p*(4*a**3-3*M*M*a) for a,p in zip(row[::2], row[1::2]))
        z = QQ(k)/zden
        if b != prev:
            points.append((k*(128//zden), F(QQ(b-prev)/M**4)*F(-z/2).exp()/C))
        prev = b
    return points


@cache
def E(q):
    return F(-abs(q)/2).exp()


@cache
def sum_kernel(k, s):
    q = QQ(k)/128+s
    v = max(q,0)
    return F(1+v+v*v/2)*E(q)


@cache
def diff_kernel(k, s):
    q = QQ(k)/128+s
    return F(2+abs(q))*E(q)


def kernels(P, T):
    plus, minus = defaultdict(lambda: F(0)), defaultdict(lambda: F(0))
    for k,b in P:
        for j,d in T:
            a = b*d
            plus[k+j] += a
            minus[k-j] += a
    def S(s):
        return sum(a*sum_kernel(k,s) for k,a in plus.items())
    def R(s):
        # Polarize the real density 1-Re(m_P conj(m_T)).
        return E(s)-sum(a*(diff_kernel(k,s)+diff_kernel(k,-s))/2 for k,a in minus.items())
    return S, R


def times(a,b):
    out = defaultdict(lambda: QQ(0))
    for i,v in a.items():
        for j,w in b.items():
            out[i+j] += v*w
    return out


hs = {-7: QQ(3)/12, 6: QQ(5)/12, 19: QQ(4)/12}
u = times(hs, {-k:v for k,v in hs.items()})  # |H|^2
z = {k:-v for k,v in u.items()}; z[0] += 1
# 1 - (1-u)/2 - (1-u)^2/8 majorizes sqrt(u) on [0,1].
major = {0: QQ(1)}
for poly, div in ((z,2), (times(z,z),8)):
    for k,v in poly.items():
        major[k] = major.get(k,0)-v/div
assert all(v == major[-k] for k,v in major.items())

names = ['single-shift', 'hard-pair', 'midgap-sector', 'right-sector', 'two-term']
laws = [law(name) for name in names]
for i,p in enumerate(laws):
    for j,q in enumerate(laws[:i+1]):
        S,R = kernels(p,q)
        entry = sum(a*R(QQ(k)/25) for k,a in major.items()) - sum(a*S(QQ(k)/25) for k,a in hs.items())
        print(names[i], names[j], entry, flush=True)
        assert entry < -F('0.00268')

# Same kernels, but now price the *actual* sparse measured masks and
# every disk completion of the original 152-slab first law.
S, R = kernels(laws[0],laws[0])
for table, count, low, high, cap in (
    ('four-shift-10-2',4,'-.000891398','-.000891397','-.00008175'),
    ('joint-refit-10-2',5,'-.000886218','-.000886216','-.00007548'),
):
    rows = [list(map(int,l.split())) for l in Path(f'.godel/bob/{table}.txt').read_text().splitlines()
            if l.strip() and not l.lstrip().startswith('#')]
    h = [(QQ(k)/25,QQ(b)/10**10) for k,_,_,b in rows if b]
    assert len(h) == count
    center = C*sum(b*S(s) for s,b in h)
    rad = C*(R(0)*sum(b*d*R(s-t) for s,b in h for t,d in h)).sqrt()
    assert F(low) < center < F(high) and center+rad < F(cap)
    print(table, 'center, radius upper bound, upper price:', center, rad, center+rad)
