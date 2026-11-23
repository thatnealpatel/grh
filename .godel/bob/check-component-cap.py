"""Exact-support, interval replay of the relative-phase test at the named center."""
from sage.all import ComplexIntervalField, QQ, RealIntervalField, prime_range

if not __debug__:
    raise RuntimeError('run with assertions enabled')
R, C = RealIntervalField(160), ComplexIntervalField(160)
t = 2*R(2**127-1)**(QQ(3)/5)
x = (3*(t/2).log())**2
assert 25107 < x < 25108 and 40 < 4*x.log() < 41 and 8 < x*R(-8).exp() < 9
parts = []
for p in prime_range(2, 25108):
    # No ratio data on unclipped primes. In the clip two successive
    # primes are connected precisely when their gap is at most 40.
    if not parts or parts[-1][-1] < 9 or p-parts[-1][-1] > 40:
        parts.append([])
    parts[-1].append(p)
assert [(g[0], g[-1]) for g in parts[4:]] == [(11, 15683), (15727, 16141),
                                                (16183, 19609), (19661, 25097)]
assert [g[0] for g in parts[:4]] == [2, 3, 5, 7] and all(len(g) == 1 for g in parts[:4])
lengths, masses = [], []
for g in parts:
    s, m = C(0), R(0)
    for p in g:
        w = R(p).log()*(x/p).log()/x
        # Product of the edge phases along the path from the first prime.
        a = t*(R(p)/g[0]).log()
        s += w*C(a.cos(), a.sin())
        m += w
    lengths.append(abs(s))
    masses.append(m)

# Each component has one free rotation, independently of all other components.
print('Genuine center, sharp upper radius:', sum(lengths))
print('Aligned center, sharp lower and upper radii:', 2*masses[4]-sum(masses), sum(masses))
assert R('0.04136603') < sum(lengths) < R('0.04136604')
assert R('0.82034516') < 2*masses[4]-sum(masses) < R('0.82034517')
assert R('0.98429171') < sum(masses) < R('0.98429172')
