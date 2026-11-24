"""Run with SageMath Python. Replay the common filter, then change only its angular test."""
from pathlib import Path
from runpy import run_path

if not __debug__:
    raise SystemExit("Run without -O.")
base = run_path(str(Path(__file__).with_name('check-common-filter.py')))
F, QQ, shifts, I = (base[k] for k in ('F', 'QQ', 'shifts', 'I'))
a, lam = QQ(197)/200, QQ(171)/50
n = 1024
u = [QQ(i)/n for i in range(n+1)]
t2 = [2*v*v-1 for v in u]
basis = [a*t-(1-a)*(4*t**3-3*t) for t in t2]


def lower(f, r):
    # Minimize f*(a*T2-(1-a)*T6) - lam*r*u on [0,1].
    # Endpoints sampled; at an interior minimizer the first derivative vanishes.
    return (min(f*b-lam*r*v for b, v in zip(basis, u))
            - f*(4*a+51*(1-a))/(8*n*n))


mesh = [QQ(i)/80 for i in range(-48, 81)]
assert {-t for t, p in shifts} <= set(mesh) and 0 in mesh
assert mesh[0] == -max(t for t, p in shifts) and mesh[-1] == -min(t for t, p in shifts)
ends = [lower(sum(p*max(0, z+t) for t, p in shifts), max(0,z)) for z in mesh]
price = F(lam*8/9)
for x, y, left, right in zip(mesh, mesh[1:], ends, ends[1:]):
    # Exact integral of the lower chord against exp(-z), evaluated in balls.
    h = F(y-x)
    mass = 1-(-h).exp()
    first = mass-h*(-h).exp()
    price += F(-x).exp()*(left*mass+(right-left)*first/h)
price += F(-mesh[-1]).exp()*(ends[-1]+lower(1, 1))
assert price > F('.5602789')
print('Combined prime lower certificate:', price)
for c, d, margin in [('1.230', '1.230', '.0004804'), ('1.226', '1.50', '.0000929')]:
    gap = price - I*(a*F(c).cosh() + (1-a)*F(d).cosh())/3
    assert gap > F(margin)
    print('Depth pair and unsmoothed margin:', c, d, gap)
