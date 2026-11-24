"""SageMath 10.9: Finite translated two-height separator at orders (10,2)."""
from pathlib import Path
from sage.all import QQ, RealBallField, ComplexBallField

if not __debug__:
    raise SystemExit('Run with assertions enabled.')
F = RealBallField(128)
K = ComplexBallField(128)
h, c = QQ(1)/25, QQ(39)/20
L, N = 256, 512
rows = [list(map(int, s.split())) for s in Path('.godel/bob/paired-10-2.txt').read_text().splitlines()
        if s.strip() and not s.startswith('#')]
assert len(set(l for l, a, b in rows)) == len(rows)
assert all(abs(l) < L and abs(l)+L-1 < N for l, a, b in rows)
cols = [{l: F(v)/10**7 for l, v in col} for col in
        ([(l, a) for l, a, b in rows], [(l, b) for l, a, b in rows])]

# Lower price. Use every knot and 0. Beyond the last cell, price the
# endpoint and the two slopes separately, with integral weights exp(-8).
weights = [{l: b*F(-l*h/2).exp() for l, b in col.items()} for col in cols]
M = 1024
u = [F(j)/M for j in range(M+1)]
A = [2*x*x-1 for x in u]
B = [4*x**3-3*x for x in A]


def lower(f, g, v):
    m = min((f*a+g*b-v*x).lower() for a, b, x in zip(A, B, u))
    return F(m) - (4*abs(f)+420*abs(g))/(8*M**2)


def price(z):
    return lower(*(sum(b*max(0, z+l*h) for l, b in col.items()) for col in weights), F(max(0, z)))


mesh = sorted({QQ(i)/100 for i in range(-160, 801)} | {-l*h for l, a, b in rows})
assert mesh[0] == min(-l*h for l, a, b in rows) and mesh[-1] == 8
vals = [price(z) for z in mesh]
floor = F(8)/9
for x, y, a, b in zip(mesh, mesh[1:], vals, vals[1:]):
    width = F(y-x)
    e = (-width).exp()
    mass = 1-e
    floor += F(-x).exp()*(mass*a+(mass/width-e)*(b-a))
floor += F(-8).exp()*(vals[-1]+lower(*(sum(col.values()) for col in weights), F(1)))

# Exact finite constant mask price, not quadrature for an L1 norm.
alpha = F.pi()/(L+1)
d = [((L-j)*(j*alpha).cos()+((j+1)*alpha).sin()/alpha.sin())/(L+1) for j in range(L)]
assert all(t > 0 for t in d)
roots = [K(0, F(2*j)*F.pi()/N).exp() for j in range(N)]
e = [d[j]*F(-j*h/2).exp() for j in range(1, L)]
C = [F(c).cosh()/(6*(F.pi()/(n+2)).cos()) for n in (10, 2)]
cost = F(0)
for p in range(N//2+1):
    I = 1+2*sum(w*roots[(j*p) % N].real() for j, w in enumerate(e, 1))
    assert I > 0
    mult = 1 if p in (0, N//2) else 2
    for cap, col in zip(C, cols):
        V = sum(b/d[abs(l)]*roots[(l*p) % N] for l, b in col.items())
        cost += mult*I*cap*abs(V)/N
print('First-price floor:', floor)
print('Combined shallow allowance:', cost)
print('Signed upper price:', cost-floor)
assert floor > F('0.16405490') and cost < F('0.16402944')
