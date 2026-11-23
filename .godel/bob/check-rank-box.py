"""Certified triangular pair budgets at the named (not translated) height."""
from sage.all import QQ, RealIntervalField, prime_range

if not __debug__:
    raise RuntimeError('run with assertions enabled')
R = RealIntervalField(160)
t = 2*R(2**127-1)**(QQ(3)/5)
x = (3*(t/2).log())**2
H = 4*x.log()
assert 8 < x*R(-8).exp() < 9 and 25107 < x < 25108 and 40 < H < 41
ps = list(map(int, prime_range(9, 25108)))
ts = [R(p).log() for p in ps]
z = [(x/p).log() for p in ps]
tail = sum(R(p).log()*(x/p).log()/x for p in (2, 3, 5, 7))
diag = sum(a*a*b for a, b in zip(ts, z))/(x*H)
# Integrate the union of occupied boxes, adding primes in order of entry.
area1 = H*sum(z)/x
area0 = (H*z[0]+sum((H if b-a >= 41 else R(b-a))*f
                      for a, b, f in zip(ps, ps[1:], z[1:])))/x
ranks = [6, 7, 9, None]  # None is one block containing every prime.
sums = {k: [R(0) for _ in range(41)] for k in ranks}
raw = [R(0) for _ in range(41)]
for i, p in enumerate(ps):
    for j in range(i+1, len(ps)):
        d = ps[j]-p
        if d >= 41:
            break
        c = ts[i]*ts[j]*(t*(1+R(d)/p).log()).cos()/x
        raw[d] += c*z[i]
        for k in ranks:
            if k is None or j-i < k:
                sums[k][d] += c*z[j]*(1 if k is None else 1-QQ(j-i)/k)


def budget(terms):
    return sum(2*(1-d/H)/H*a.max(R(0)) for d,a in enumerate(terms) if d)


original = budget(raw)
print('original positive shift budget', original)
assert QQ(1200240)/10**8 < original < QQ(1200241)/10**8
# Resolve the threshold for each actual shift, not just its midpoint.
cut = QQ(1)/16
above = {d for d, a in enumerate(raw) if a > cut}
assert above == {12, 36}
assert all(a < cut or d in above for d, a in enumerate(raw))
small = budget([R(0) if d in above else a for d, a in enumerate(raw)])
assert QQ(69925)/10**7 < small < QQ(69926)/10**7
assert small > original/2
bounds = {6: (588638, 588639), 7: (572434, 572435),
          9: (550036, 550037), None: (461900, 461901)}
for k in ranks:
    area = area0 if k is None else area0+(area1-area0)/k
    b = budget(sums[k])
    cap = tail+(area*(diag+b)).sqrt()
    print(k, 'area, positive budget, cap', area, b, cap)
    lo, hi = bounds[k]
    assert QQ(lo)/10**6 < cap < QQ(hi)/10**6
    if k == 7:
        assert QQ(71606)/10**7 < b < QQ(71607)/10**7

# Lower constants in the asymptotic implication, without its o(1).
m = 1-9*R(-8).exp()
s = QQ(47)/81
for c, k, bound in [(4, 9, QQ(1405)/10**6), (400, 3, QQ(158)/10**8)]:
    assert (s-1+m)**2/(m*(1+QQ(c-1)/k))-m/c > bound

# The wide box at this same conductor: Do not mistake its asymptotic
# sufficient budget for a finite upper bound.
H = 400*x.log()
successors = {}
for i, p in enumerate(ps):
    for j in range(i+1, min(i+3, len(ps))):
        d = ps[j]-p
        assert d < H
        c = ts[i]*ts[j]*z[j]*(t*(1+R(d)/p).log()).cos()/x
        successors[d] = successors.get(d, R(0)) + (1-QQ(j-i)/3)*c
wide = sum(2*(1-d/H)/H*a.max(R(0)) for d, a in successors.items())
wide_signed = sum(2*(1-d/H)/H*a for d, a in successors.items())
assert QQ(45720)/10**9 < wide < QQ(45721)/10**9
assert -QQ(748)/10**9 < wide_signed < -QQ(747)/10**9

# Conditional endpoint test. Unweighted in gap for the chord statistic;
# triangular in gap and restricted to rank two for the positive budget.
Z = sum(z)
chord = R(0)
second = {}
H = 40*x.log()
for j in range(1, len(ps)):
    d = ps[j]-ps[j-1]
    co = (t*(1+R(d)/ps[j-1]).log()/2).cos()
    chord += z[j]*((1+abs(co))/2).sqrt()/Z
    if j < 2:
        continue
    d = ps[j]-ps[j-2]
    if d >= H:
        continue
    assert d < H
    co = (t*(1+R(d)/ps[j-2]).log()).cos()
    second[d] = second.get(d, R(0)) + z[j]*ts[j]*ts[j-2]*co/x
second_pos = budget([second.get(d, R(0)) for d in range(1+max(second))])
print('chord mean and length-40D rank-two positive budget', chord, second_pos)
assert QQ(899035)/10**6 < chord < QQ(899036)/10**6
assert QQ(14475)/10**7 < second_pos < QQ(14476)/10**7
# Uniform first-edge chord kernel, and the worst allowed deficit in (2).
assert 2*R(2).sqrt()/R.pi() < QQ(900317)/10**6
s0 = (QQ(8)/9-(1-m))/m
c = 1-R(2).sqrt()*(QQ(9005)/10000-s0)
b = 2*(2*c*c-1)**2-1
r = 2*b*b-1
assert 2*c*c-1 > 0 and b > 0 and r > QQ(9793)/10**5
assert 2*m/40*(r-QQ(2)/40) > QQ(2389)/10**6
