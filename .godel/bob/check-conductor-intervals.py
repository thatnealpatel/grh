"""Closed labeled-cell sweep, integer inverse, and a moving real-window witness."""
from sage.all import QQ, RealIntervalField, prime_range

if not __debug__:
    raise RuntimeError('run with assertions enabled')
R = RealIntervalField(160)
q0, u0, N, W, k = 100000007, 126192, 256, 4, 4
a = QQ(1)/16


def cutoff(u):
    return (3*(u/2).log())**2


X = cutoff(2*R(q0)**(QQ(3)/5))
primes = set(prime_range(1100))
assert 1099 < X < 1100 and X*R(-8).exp() < 1
assert 7 < X.log() < 8 and 28 < 4*X.log() < 29
labels = range(8, 29)


def edges(x, d, primes):
    return [((x/p).log()*R(p).log()*R(p+d).log()/x, (1+R(d)/p).log())
            for p in sorted(primes) if p+d in primes]


def amplitude(terms, u):
    return abs(sum((w*(u*f).cos() for w, f in terms), R(0)))


# These are marks on whole closed cells by convention, not interpolation bounds.
rows = [0]*N
for d in labels:
    terms = edges(X, d, primes)
    for j in range(N):
        s = amplitude(terms, u0+j)
        assert s > a or s < a
        if s > a:
            rows[j] |= 1 << d


def merge(pieces):
    runs = []
    for l, r in sorted(pieces):
        if runs and l <= runs[-1][1]:
            runs[-1] = (runs[-1][0], max(runs[-1][1], r))
        else:
            runs.append((l, r))
    return runs


def sweep(rows, labels, u0, w, k):
    events = {}
    for d in labels:
        for l, r in merge((u0+i, u0+i+1) for i, row in enumerate(rows) if row >> d & 1):
            if l+w <= r-w:
                events.setdefault(l+w, [0, 0])[0] += 1
                events.setdefault(r-w, [0, 0])[1] += 1
    active, prev, pieces = 0, None, []
    for t, (starts, ends) in sorted(events.items()):
        if active >= k:
            pieces.append((prev, t))
        active += starts
        if active >= k:
            pieces.append((t, t))
        active -= ends
        prev = t
    assert active == 0
    return merge(pieces)


def lower(t, strict=False):
    # First q >= 0 with 32 q^3 >= t^5 (or > if strict).
    lo, hi = -1, 1
    target = t**5 + int(strict)
    while 32*hi**3 < target:
        hi *= 2
    while hi-lo > 1:
        mid = (lo+hi)//2
        if 32*mid**3 >= target:
            hi = mid
        else:
            lo = mid
    return hi


def invert(runs, A=0, B=0):
    centers = merge((a-B, b-A) for a, b in runs)
    return [(l, r) for a, b in centers if (l := lower(a)) <= (r := lower(b, True)-1)]


# A perfect fifth power gives an integer center. Two different eroded
# runs just touch there; the sweep and inverse must keep the singleton.
z, qc = 2*8**3, 8**5
assert sweep([1, 1, 3, 3, 2, 2], [0, 1], z-3, 1, 2) == [(z, z)]
assert invert([(z, z)]) == [(qc, qc)]
# A common midpoint at z+2 is allowed at offset +2, including equality.
assert any(l <= qc <= r for l, r in invert([(z+2, z+2)], 1, 2))
# Each label has an eligible midpoint at offset 1 or 3, but not together.
separate = [1, 1, 2, 2]
for d in (0, 1):
    assert any(l <= qc <= r for l, r in invert(sweep(separate, [d], z, 1, 1), 1, 3))
assert not invert(sweep(separate, [0, 1], z, 1, 2), 1, 3)


# Independent truth from the masks on open cell interiors. A closed
# window of positive length is covered iff all interiors it meets carry
# the label: At an integer endpoint the adjacent interior supplies it.
def direct(i, integral):
    rr = rows[i-W:i+W+1-int(integral)]
    assert len(rr) == 2*W+1-int(integral)
    common = rr[0]
    for r in rr[1:]:
        common &= r
    return common.bit_count() >= k, min(r.bit_count() for r in rr) >= k


runs = invert(sweep(rows, labels, u0, W, k))
first, last = lower(u0+W), lower(u0+N-W, True)-1
j, ri, good, rotating = u0, 0, 0, 0
for q in range(first, last+1):
    v5 = 32*q**3
    while (j+1)**5 <= v5:
        j += 1
    fixed, pointwise = direct(j-u0, j**5 == v5)
    while ri < len(runs) and runs[ri][1] < q:
        ri += 1
    assert fixed == (ri < len(runs) and runs[ri][0] <= q)
    good += fixed
    rotating += pointwise
assert (last-first+1, good, rotating, len(runs)) == (327767, 64754, 303974, 16)
print('marked cells: domain, persistent, pointwise, compressed runs:', last-first+1, good, rotating, len(runs))

# Separate from the cell model: Classify the entire continuous moving
# window at this conductor by interval enclosures, not sampled counts.
q = 100277386
center = 2*R(q)**(QQ(3)/5)
band = cutoff(center+R(-W, W))
assert 1099 < band < 1100 and band*R(-8).exp() < 1
assert 7 < band.log() < 8 and 28 < 4*band.log() < 29
terms = {d: edges(band, d, primes) for d in labels}
remaining = set(labels)
least = len(labels)
for j in range(-64*W, 64*W):
    u = center + R(j, j+1)/64
    values = {d: amplitude(e, u) for d, e in terms.items()}
    least = min(least, sum(s > a for s in values.values()))
    # A whole subcell strictly below threshold suffices to kill persistence.
    remaining -= {d for d, s in values.items() if s < a}
assert least >= 5 and remaining <= {12, 18}
print('moving window: q, guaranteed pointwise count, possible persistent labels:', q, least, sorted(remaining))

# The flagged large-conductor node from quadratic-overlap.md. Search is
# unnecessary for replay. Use a common subinterval in its next grid cell.
q = 2**127-1
t = 2*R(q)**(QQ(3)/5)
X = cutoff(t)
D = X.log()
ell = X/D/R(24).sqrt()
u0 = t+44*ell
v = u0 + QQ(247)/512*ell + R(-1, 1)/2048
x = cutoff(v)
assert u0 < v < u0+ell < 5*t/4
assert 8 < x*R(-8).exp() < 9 and 25107 < x < 25108
assert 10 < x.log() < 11 and 40 < 4*x.log() < 41
primes = set(prime_range(9, 25108))
worst = max(amplitude(edges(x, d, primes), v).upper() for d in range(11, 41))
assert worst < QQ(61)/1000 < a
print('moving subinterval at flagged grid cell: largest absolute real part at most', worst)
