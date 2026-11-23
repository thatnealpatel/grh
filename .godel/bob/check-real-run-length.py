"""Continuous fixed-label windows in the genuine cell, Sage interval replay."""
from bisect import bisect_right
from itertools import accumulate
from math import factorial
from sage.all import QQ, RealIntervalField, prime_range

if not __debug__:
    raise RuntimeError('run with assertions enabled')
R = RealIntervalField(160)
q, n, K = 2**127-1, 24, 61
t = 2*R(q)**(QQ(3)/5)


def cutoff(v):
    return (3*(v/2).log())**2


X = cutoff(t)
D = X.log()
ell = X/D/R(n).sqrt()
u = t+44*ell
x = cutoff(u+ell*R(0, 1)).union(X)
# All moving supports, trims, pressure radii, and orders are the same.
assert 8 < R(-8).exp()*x < 9 and 25107 < x < 25108
assert 10 < x.log() < 11 and 40 < 4*x.log() < 41 and 102 < x.log()**2 < 103
assert 11 < QQ(9)/4*R(t.lower(), (u+ell).upper()).log()/x.log() < 12
primes = set(int(p) for p in prime_range(9, 25108))
logs = {p: R(p).log() for p in primes}
N, tile = 8192, 32
step = ell/N
# Each fine row stores an enclosure on the whole closed subcell, not a node.
rows = [{} for j in range(N)]
positive_box = [R(0) for j in range(N)]
H = 4*x.log()
endpoint_cost = R(0)
dropped = []
for d in range(1, 41):
    ps = sorted(p for p in primes if p+d in primes)
    if not ps:
        assert d % 2 == 1
        continue
    ws = [(x/p).log()*logs[p]*logs[p+d]/x for p in ps]
    prefix = list(accumulate(ws, initial=R(0)))
    pressure = n*n*sum(w*(w+2*(prefix[bisect_right(ps, p+102)]-prefix[i+1]))
                       for i, (p, w) in enumerate(zip(ps, ws)))
    retained = d >= 11 and pressure < K
    if d >= 11 and not retained:
        assert pressure > K
        dropped.append(d)
    # For each evaluation, keep the weights at that height fixed when
    # expanding the cosines. The interval ws encloses all such choices.
    fs = [(1+R(d)/p).log() for p in ps]
    b = 2*(1-d/H)/H
    endpoint_cost += b*sum(f*logs[p]*logs[p+d]/x for p, f in zip(ps, fs))
    cs = [w*(u*f).cos() for f, w in zip(fs, ws)]
    ss = [w*(u*f).sin() for f, w in zip(fs, ws)]
    powers = [[(f**k)/factorial(k) for f in fs] for k in range(8)]
    radius = tile*step/2
    err = sum(w*(radius*f)**8 for f, w in zip(fs, ws))/factorial(8)
    delta = [step*R(j-tile//2, j+1-tile//2) for j in range(tile)]
    for left in range(0, N, tile):
        v = (left+tile//2)*step
        angles = [v*f for f in fs]
        cos = [a.cos() for a in angles]
        sin = [a.sin() for a in angles]
        re = [c*C-s*S for c, s, C, S in zip(cs, ss, cos, sin)]
        im = [c*S+s*C for c, s, C, S in zip(cs, ss, cos, sin)]
        coeff = [(-1)**((k+1)//2)*sum(a*b for a, b in zip(im if k%2 else re, powers[k]))
                 for k in range(8)]
        for j, h in enumerate(delta):
            p = coeff[-1]
            for c in reversed(coeff[:-1]):
                p = p*h+c
            value = p+R(-1, 1)*err
            if retained:
                rows[left+j][d] = value
            positive_box[left+j] += b*R(max(0, value.upper()))
assert dropped == [12, 24, 30, 36]
labels = sorted(rows[0])
a = QQ(1)/16
assert max(sum(v.upper() >= a for v in row.values()) for row in rows) <= 4
assert max(sum(abs(v).upper() >= a for v in row.values()) for row in rows) <= 8


def check(l, r, margin, positive, negative):
    for row in rows[l:r]:
        assert all(row[d] > margin for d in positive)
        assert all(row[d] < -margin for d in negative)


check(1728, 1750, QQ(64)/1000, [14, 20, 22, 34], [18, 32, 38, 40])
check(2366, 2386, QQ(1)/12, [14, 20, 22, 34], [18, 40])
# Price the longest six-label run, not a pointwise counting run. For
# the upper bound relax every straddling subcell in the label's favor.
def longest(possible):
    age = {d: 0 for d in labels}
    best = (0, 0, ())
    for j, row in enumerate(rows):
        for d in labels:
            v = abs(row[d])
            hit = v.upper() >= a if possible else v > a
            age[d] = age[d]+1 if hit else 0
        group = sorted(labels, key=age.get, reverse=True)[:6]
        length = age[group[-1]]
        if length > best[0]:
            best = length, j+1-length, tuple(sorted(group))
    return best


lo, hi = longest(False), longest(True)
print('six-label runs (cell count, left index, labels):', lo, hi)
print('lower and upper length enclosures:', lo[0]*step, hi[0]*step)
assert lo[0]*step > QQ(183)/10 and hi[0]*step < QQ(187)/10

# Finite layer-cake box bound for the full principal ramp. Use 9 as the
# layer floor (identical prime support to the moving clipped band).
tail = sum((x/p).log()*R(p).log()/x for p in [2, 3, 5, 7])
diag = sum((x/p).log()*logs[p]**2/x for p in primes)/H
area = (x-9+(H-9)*(x/9).log())/x
box = R(max(b.upper() for b in positive_box))
cap = tail+(area*(diag+box+endpoint_cost)).sqrt()
print('positive box, diagonal, endpoint correction, area, tail, cap:',
      box, diag, endpoint_cost, area, tail, cap)
assert box < QQ(26)/1000
assert cap < QQ(482)/1000
assert lo[:2] == (299, 2273) and hi[:2] == (302, 2271)
assert lo[2] == hi[2] == (14, 18, 20, 32, 34, 40)
