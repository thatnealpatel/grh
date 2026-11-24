"""Price the positive half-line exactly for a localized first-cap test."""
from math import comb
from pathlib import Path
from runpy import run_path

from sage.all import QQ

base = Path(__file__).resolve().parent
laws = base/'deletion-laws'
tail = run_path(str(base/'check-tail-deletion-33.py'))
F, K, C = [tail[s] for s in ('F', 'K', 'C')]
z, _, B, _ = tail['unfold']['lattice']['prime_rows'](
    (laws/'delete-33-tail-baseline.txt').read_text())
rows = [list(map(int, line.split())) for line in
        (laws/'delete-33-early-refit.txt').read_text().splitlines()]
h = {QQ(k)/400: QQ(n)/10**16 for name, k, n in (line.split() for line in
     (laws/'delete-33-regional-tilts.txt').read_text().splitlines()) if name == 'negative'}
assert len(h) == 9 and set(h) <= set(z[:494])

def T(n):
    x = 2*(QQ(n)/10**9)**2-1
    return 4*x**3-3*x

Zref, Zdiff, score = K(0), K(0), QQ(0)
coeff = [K(0, F(j)*2/5*22/5).exp()*comb(4, j+2)/16 for j in range(-2,3)]

def primitive(t, carrier):  # integral from t to infinity, including 1/C
    out = K(0)
    for j, a in zip(range(-2,3), coeff):
        w = K(F(1)/2, -(carrier+F(2)*j/5))
        out += a*(-t*w).exp()/w
    return out/C

x = QQ(273)/8
p = primitive(z[0], x)
for i, ((k,*pairs), t, s, b) in enumerate(zip(rows, z[:494], z[1:], B)):
    assert k == 400*t and pairs and len(pairs)%2 == 0 and min(pairs[1::2]) > 0
    assert all(-2 <= n <= 10**9 for n in pairs[::2])
    # Both reference labels retain b, including the fixed-(A,B) fiber.
    db = QQ(999)/1000*sum(w*(T(n)-b) for n,w in zip(pairs[::2],pairs[1::2])
                           if n >= 0)/sum(pairs[1::2])
    q = primitive(s, x)
    Zref += (p-q)*b
    Zdiff += (p-q)*db
    score += h.get(t,0)*db
    p = q
assert i == 493 and s == 0
pos = primitive(0,0).real()
neg = primitive(z[0],0).real()-pos
probe = Zref+F('.55')*Zdiff
slope = (probe.conjugate()*Zdiff).real()/abs(probe)
weight = sum(map(abs,h.values()))
# From --regional: L_neg - P_full > 7.275e-9.
rho = F('.005')
lo = (F('7.275e-9')-rho*weight)/score
assert score > 0 and slope > 0
margin = abs(probe)+(lo-F('.55'))*slope-rho*neg-pos-1
print('Trial signed score, packet positive allowance, negative mass:', F(score), pos, neg)
print('Projected slope, necessary parameter, cap excess at radius .005:', slope, lo, margin)
assert margin > F('.01494')
