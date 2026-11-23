"""Finite signed dense-gap overlap certificate. Run with Sage Python, not -O."""
from bisect import bisect_right
from collections import Counter
from itertools import accumulate

from sage.all import ComplexIntervalField, QQ, RealIntervalField, prime_range

if not __debug__:
    raise RuntimeError('the certificate requires assertions')
R = RealIntervalField(192)
C = ComplexIntervalField(192)
q, gamma, n, K = 2**127-1, QQ(1)/4, 24, 61
a2 = QQ(1)/256
t = 2*R(q)**(QQ(3)/5)
X = (3*(t/2).log())**2
D = X.log()
L = X/D
ell = L/R(n).sqrt()
u = t+44*ell
M = X/(n*D**4)
assert 11 < (2+gamma)*t.log()/D < 12
assert t+ell < u < 5*t/4-ell and 0 < M < 1


def floor_cert(x):
    k = int(x.lower().floor())
    assert k <= x < k+1
    return k


def cis(y):
    return C(y.cos(), y.sin())


def shift_data(d):
    starts = [p for p in primes if p+d in support]
    weights = [(X/p).log()*logs[p]*logs[p+d]/X for p in starts]
    prefix = list(accumulate(weights, initial=R(0)))
    near = (w*(w+2*(prefix[bisect_right(starts, p+r)]-prefix[i+1]))
            for i, (p, w) in enumerate(zip(starts, weights)))
    pressure = n*n*sum(near, R(0))
    z = [w*cis(u*(1+R(d)/p).log()) for p, w in zip(starts, weights)]
    conj = [v.conjugate() for v in z]
    groups, counts = {}, Counter()
    for i, p in enumerate(starts):
        for j in range(bisect_right(starts, p+cut), len(starts)):
            g = starts[j]-p
            counts[g] += 1
            cross = 2*z[i]*conj[j]
            groups[g] = groups[g]+cross if g in groups else cross
    # All and only the nonempty far groups are dense on this fixture.
    assert groups.keys() == counts.keys() and all(m > M for m in counts.values())
    return pressure, groups, counts, dict(zip(starts, weights))


lo, hi = floor_cert(D)+1, floor_cert(4*D)
bottom, top = floor_cert(X*R(-8).exp())+1, floor_cert(X)
assert lo-1 < D and bottom-1 < X*R(-8).exp()
assert (lo, hi, bottom, top) == (11, 40, 9, 25107)
r, cut = floor_cert(D**2), floor_cert(n*D**2)
primes = [int(p) for p in prime_range(bottom, top+1)]
support = set(primes)
logs = {p: R(p).log() for p in primes}
pi = R.pi()
betas = (QQ(0), QQ(21)/256)  # beta/pi, shared by every shift


def phase(b, d, g):
    # Reduce exactly modulo one turn before taking interval trig values.
    turns = b*d*g
    return -2*pi*(turns-turns.floor())


def signed_sum(groups, b, d):
    if b == 0:
        return sum((P.real() for P in groups.values()), R(0))
    return sum(((cis(phase(b, d, g))*P).real() for g, P in groups.items()), R(0))


def bounds(x):
    return RealIntervalField(32)(x).str(style='brackets')


hits = [[], []]
removed_hits = [[], []]
removed, empty = [], []
ngaps = npairs = 0
assert min(primes) > 2
print('band, trim, strip cutoffs:', (bottom, top), (lo, hi), (r, cut))
print('beta/pi:', betas)
print('d retained n^2 C_d(D^2) B_d(0) B_d(21*pi/256)')
for d in range(lo, hi+1):
    pressure, groups, counts, w = shift_data(d)
    assert abs(pressure-K) > QQ(1)/5000
    if pressure > K:
        removed.append(d)
        target = removed_hits
    else:
        assert pressure <= K
        target = hits
    ngaps += len(groups)
    npairs += sum(counts.values())
    if d % 2:
        assert not w and not groups and pressure.is_zero()
        empty.append(d)

    if d == 18:
        assert QQ(6099)/100 < pressure < K
        assert len(groups) == 11141 and max(counts.values()) == 184
        # At gap 22688 the sole term starts at 11. Check the full complex
        # coefficient by the exact rational log defect, also after rotation.
        p, g = 11, 22688
        assert (g > cut and counts[g] == 1
                and [x for x in w if x+g in w] == [p])
        y = u*(1+R(QQ(d*g)/(p*(p+g+d)))).log()
        for b in betas:
            direct = 2*w[p]*w[p+g]*cis(y-2*pi*b*d*g)
            assembled = cis(phase(b, d, g))*groups[g]
            assert abs(direct-assembled) < QQ(1)/10**22

    row = [signed_sum(groups, b, d) for b in betas]
    if d == 18:
        assert QQ(16)/1000 < row[0] < QQ(17)/1000
    for value, out in zip(row, target):
        if value > a2:
            out.append(d)
        else:
            assert value <= a2
        assert abs(value-a2) > QQ(7)/10000
    if d % 2 == 0:
        print(d, target is hits, bounds(pressure), *(bounds(v) for v in row))

assert removed == [12, 24, 30, 36] and removed_hits == [[12], []]
assert empty == list(range(11, 41, 2))
assert hits == [[18, 20, 22, 40], [18, 22, 28, 32, 38, 40]]
print('odd shifts (retained, both sums exactly zero):', empty)
print('shifts, nonempty far groups, far pairs:', hi-lo+1, ngaps, npairs)
print('pressure deletions:', removed, 'raw exceedances there:', removed_hits)
print('retained hits:', hits, 'counts:', list(map(len, hits)))
