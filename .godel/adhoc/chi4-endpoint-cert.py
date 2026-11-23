"""Sage 10.9 Python: Whole-window chi_4 lower bound, diameter 111/100.

Run with `sage -python chi4-endpoint-cert.py`. See chi4-window.md.
"""

from sage.all import ComplexBallField, QQ, RealBallField

R = RealBallField(100)
C = ComplexBallField(100)
D = QQ(111) / 100
a = QQ(9) / 20
N = 8192
step = R(D / N)
grid = [R(j * D / N) for j in range(N + 1)]
c = (C(QQ(3) / 4).psi() + (4 / C.pi()).log()).real()
cost = R(3).log() / R(3).sqrt()
assert R(3).log() < R(D) < 2 * R(3).log() and R(D) < R(5).log()

# f_j encloses t*w(t) at t=grid[j]. Both w and t*w are decreasing.
f = [R(1) / 2] + [t * (-t / 2).exp() / (2 * t.sinh()) for t in grid[1:]]
U = [R(0)]  # Cumulative left sums of t*w(t).
V = [R(0)]  # Cumulative lower sums of t*(t*w(t)).
for j in range(N):
    U.append(U[-1] + step * f[j])
    V.append(V[-1] + step * grid[j] * f[j + 1])

# T[j] bounds int_{grid[j]}^infty w from below, not from above.
T = [None] * (N + 1)
rates = [QQ(3) / 2 + 2 * k for k in range(16)]
T[N] = sum((-R(r * D)).exp() / R(r) for r in rates)
for j in reversed(range(N)):
    T[j] = T[j + 1] + step * f[j + 1] / grid[j + 1]

dr, ar = R(D), R(a)

def h(x):
    return 1 - ar * (1 - 2 * x / dr) ** 2

# Reflection handles the other half. Lower bound the potential separately
# on each closed cell. Treat an uncertain prime-overlap comparison as active.
for j in range(N // 2):
    l, r = grid[j : j + 2]
    val = c + T[j + 1] + T[N - j]
    val += 4 * ar / dr**2 * (V[j] + V[N - j - 1]) / h(r)
    val -= 4 * ar / dr * (1 - 2 * l / dr) * (U[N - j] - U[j]) / h(l)
    if not (l > dr - R(3).log()):
        val -= cost
    assert val > R(QQ(1) / 50), (j, val)

print('Verified every cell against the lower bound 1/50.')
