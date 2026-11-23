"""Certify the linear phase sweep and the untwisted dip tests. Use Sage Python, not -O."""
from bisect import bisect_right

from sage.all import ComplexIntervalField, QQ, RealIntervalField, prime_range

if not __debug__:
    raise RuntimeError('the certificate requires assertions')
R = RealIntervalField(192)
C = ComplexIntervalField(192)
pi = R.pi()
q, n, K, a = 2**127-1, 24, 61, QQ(1)/16
t = 2*R(q)**(QQ(3)/5)
X = (3*(t/2).log())**2
D = X.log()
assert 11 < 9*t.log()/(4*D) < 12


def floor_cert(x):
    k = x.lower().floor()
    assert k <= x and x < k+1
    return int(k)


bottom = floor_cert(X*R(-8).exp())+1
assert bottom-1 < X*R(-8).exp()
primes = list(prime_range(bottom, floor_cert(X)+1))
support = set(primes)
r = floor_cert(D**2)
retained, large, real = [], [], []
events = []
trim_real = []
for d in range(1, floor_cert(4*D)+1):
    starts = [p for p in primes if p+d in support]
    weights = [(X/p).log()*R(p).log()*R(p+d).log()/X for p in starts]
    prefix = [R(0)]
    for w in weights:
        prefix.append(prefix[-1]+w)
    pressure = n*n*sum((w*(w+2*(prefix[bisect_right(starts, p+r)]-prefix[i+1]))
                        for i, (p, w) in enumerate(zip(starts, weights))), R(0))
    if D <= d:
        assert pressure <= 128
    z = C(0)
    for p, w in zip(starts, weights):
        y = t*(1+R(d)/p).log()
        z += w*C(y.cos(), y.sin())
    if D <= d:
        if abs(z.real()) > a:
            trim_real.append(d)
        else:
            assert abs(z.real()) < a
    if pressure > K:
        continue
    assert pressure <= K
    retained.append(d)
    if abs(z) < a:
        continue
    assert abs(z) > a
    large.append(d)
    if abs(z.real()) > a:
        real.append(d)
    else:
        assert abs(z.real()) < a
    # x=alpha/pi in [0,1). Each of the d periods has one entry
    # (-theta) and one exit (+theta) of the strict superlevel set.
    theta = (R(a)/abs(z)).arccos()/pi
    phase = z.argument()/pi
    for side in (-1, 1):
        for j in range(d):
            x = (j + side*theta-phase)/d
            x -= floor_cert(x)
            assert 0 < x < 1
            events.append((x, -side))

# Midpoints propose an order; interval inequalities certify it.
events.sort(key=lambda event: event[0].center())
count = low = high = len(real)
previous = R(0)
for x, delta in events:
    assert previous < x
    previous = x
    count += delta
    low, high = min(low, count), max(high, count)
assert count == len(real)
# At a single strict crossing its value is the lesser adjacent count.
print('retained even shifts:', [d for d in retained if d % 2 == 0])
print('modulus hits:', large, 'genuine real hits:', real)
print('crossings, minimum, maximum:', len(events), low, high)
assert trim_real == [12, 24, 26, 34, 36] and 5 < D/2 < 6
assert large == [14, 18, 26, 34] and real == [26, 34]
assert (len(events), low, high) == (184, 0, 4)

# A different finite question: One moving ordinate, no retention cut,
# all shifts in the trim D(u) <= d <= 4 D(u), and no phase twist.
u = t + (QQ(5)/8)*X/D
Xu = (3*(u/2).log())**2
Du = Xu.log()
lo, hi = floor_cert(Xu*R(-8).exp())+1, floor_cert(Xu)
dlo, dhi = floor_cert(Du)+1, floor_cert(4*Du)
assert lo-1 < Xu*R(-8).exp() and dlo-1 < Du
assert (lo, hi, dlo, dhi) == (9, 25107, 11, 40)
ps = list(prime_range(lo, hi+1))
pset = set(ps)
modhits, realhits = [], []
for d in range(dlo, dhi+1):
    z = C(0)
    for p in ps:
        if p+d in pset:
            w = (Xu/p).log()*R(p).log()*R(p+d).log()/Xu
            y = u*(1+R(d)/p).log()
            z += w*C(y.cos(), y.sin())
    if abs(z) > a:
        modhits.append(d)
    else:
        assert abs(z) < a
    if abs(z.real()) > a:
        realhits.append(d)
    else:
        assert abs(z.real()) < QQ(562)/10000
assert len(modhits) == 11 and realhits == [12, 14]
assert len(realhits) < D/4 < len(modhits)
print('moving node modulus hits:', modhits, 'real hits:', realhits)

# Can the modulus test witness *any* dip on the smaller window? Enclose
# weights for every moving cutoff, then freeze each such weight vector
# when applying Taylor to its exponential sum. No derivative of a moving
# weight is needed. Dyadic coordinates below are exact rationals.
T = X/(16*D)
Y = (3*((t+R(-1, 1)*T)/2).log())**2
assert lo-1 < Y*R(-8).exp() < lo and hi < Y < hi+1
assert dlo-1 < Y.log() < dlo and dhi < 4*Y.log() < dhi+1
models = []
for d in range(dlo, dhi+1):
    edges = [((Y/p).log()*R(p).log()*R(p+d).log()/Y, (1+R(d)/p).log())
             for p in ps if p+d in pset]
    if edges:
        models.append((edges, sum(w*f*f for w, f in edges)))
stack = [(QQ(-1), QQ(1), 0)]
leaves = 0
while stack:
    left, right, depth = stack.pop()
    mid = t+T*(left+right)/2
    h = T*(right-left)/2
    hits = 0
    for edges, second in models:
        re = im = dr = di = R(0)
        for w, f in edges:
            y = mid*f
            c, s = w*y.cos(), w*y.sin()
            re += c
            im += s
            dr -= f*s
            di += f*c
        if abs(C(re, im))-h*abs(C(dr, di))-h*h*second/2 > a:
            hits += 1
            if hits == 6:
                break
    if hits == 6:
        leaves += 1
    else:
        assert depth < 16, 'undecided cell'
        m = (left+right)/2
        stack.extend([(left, m, depth+1), (m, right, depth+1)])
print('full-window cells with at least six modulus hits:', leaves)
