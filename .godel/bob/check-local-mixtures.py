"""SageMath: A finite dual obstruction for local mixtures of two tabulated laws."""
import ast
from pathlib import Path

from sage.all import QQ, RealBallField, ComplexBallField

if not __debug__:
    raise SystemExit('Run without -O.')
F = RealBallField(128)
K = ComplexBallField(128)
root = Path('.godel/bob')


def profile(xs, ps, scale):
    assert sum(ps) == scale and all(p >= 0 for p in ps)
    assert all(-1 <= x <= 1 for x in xs)
    p = [QQ(i)/scale for i in ps]
    return (F(sum(a*x for a, x in zip(p, xs))),
            F(sum(a*(4*x**3-3*x) for a, x in zip(p, xs))),
            sum(a*F((1+x)/2).sqrt() for a, x in zip(p, xs)))


# Read the two existing exact tables, without executing their checkers.
tree = ast.parse((root/'check-two-height-radial-witness.py').read_text())
(data,) = [ast.literal_eval(n.value) for n in tree.body if isinstance(n, ast.Assign)
           and any(isinstance(t, ast.Name) and t.id == 'DATA' for t in n.targets)]
left, right = {}, {}  # Keys are 1024*z.
for k, *law in data:
    us, ps = zip(*law)
    left[32*k] = profile([2*(QQ(i)/80)**2-1 for i in us], ps, 10**9)
for line in (root/'translated-step-11-1.txt').read_text().splitlines():
    if line.strip() and not line.startswith('#'):
        k, *fields = map(int, line.split())
        assert len(fields) % 2 == 0
        right[k] = profile([QQ(i)/10**10 for i in fields[::2]], fields[1::2], 10**10)

# (0: first height, 1: third height; 1000*frequency; 10^8 times real and
# imaginary parts of coefficient). Only this rational price is used below.
rows = [
    (0, 130, 16769546, 9256680),
    (0, 195, 17288754, 15690907),
    (0, 505, 168177, 22445106),
    (0, 790, -3510888, 7943283),
    (0, 1050, -5520953, 7328697),
    (0, 1515, -5206769, 4156281),
    (0, 2135, -3238167, 2308207),
    (0, 2620, -997341, 475175),
    (0, 3050, -1562361, 856282),
    (0, 3715, -824744, 373791),
    (0, 4230, -406870, 178223),
    (0, 4540, -342747, 76535),
    (0, 5435, -303577, 154001),
    (0, 6090, -5444, 3420),
    (0, 6715, -71944, 82876),
    (0, 7885, -2301, 15024),
    (0, 9215, 8193, 1636),
    (0, 10480, 1879, -1183),
    (0, 11095, 420, -988),
    (0, 15205, -301, 3545),
    (0, 21860, 330, -1421),
    (1, 0, -292837, 0),
    (1, 230, -269925, -298774),
    (1, 510, -58333, -414203),
    (1, 920, 82835, -133729),
    (1, 1190, 52434, -109453),
    (1, 2115, 18036, -56623),
    (1, 3565, -14706, -925),
    (1, 4820, -7437, 7760),
]
mu = QQ(3787499)/10**6
terms = [(j, K(QQ(1)/2, QQ(k)/1000), K(a, b)/10**8) for j, k, a, b in rows]
norm = [sum(abs(c) for j, _, c in terms if j == i) for i in (0, 1)]
curvature = sum(abs(c)*abs(w)**2 for j, w, c in terms)


def kernels(z):
    v = [F(0), F(0), -mu*max(0, z)*(-z).exp()]
    for j, w, c in terms:
        v[j] += (c*(-w*z).exp()).real()
    return v


def floor(v, p, q):
    return F(min(sum(a*b for a, b in zip(v, profile)).lower() for profile in (p, q)))


# One-sided values on each cell; a law can jump at either endpoint. For each
# smooth endpoint price the linear interpolation error is <= M*s*(h-s)/2.
# The minimum of two affine functions is concave and lies above its chord.
N, stop = 1024, 40
h = F(QQ(1)/N)
start = min(min(left), min(right))
assert start == -8*N and max(max(left), max(right)) < stop*N
p = q = (F(0), F(0), F(QQ(1)/2).sqrt())
a = kernels(F(QQ(start)/N))
total = F(0)
for k in range(start, stop*N):
    p, q = left.get(k, p), right.get(k, q)
    z = F(QQ(k)/N)
    b = kernels(z+h)
    M = curvature*(-z/2).exp()
    if k >= 0:
        M += mu*(z+h+2)*(-z).exp()  # |(s exp(-s))''| on [z,z+h].
    total += h*(floor(a, p, q)+floor(b, p, q))/2 - M*h**3/12
    a = b
# Left tail is zero. On the right use |A|, |B|, U <= 1.
total -= 2*sum(norm)*F(-QQ(stop)/2).exp() + mu*(1+stop)*F(-stop).exp()


def cap(n):
    return F(QQ(39)/20).cosh()/(6*(F.pi()/(n+2)).cos())


def gap(n, m):
    return total + mu*QQ(8)/9 - cap(n)*norm[0] - cap(m)*norm[1]


print('lower bound on the (10,2) dual gap:', gap(10, 2))
assert gap(10, 2) > QQ(149)/10**6
# Known compatible neighbors: The dual must not exclude either of these.
assert gap(10, 1) < 0 and gap(9, 2) < 0
