"""Check both bucket lengths against direct positive energies, with Sage intervals."""
from math import factorial
from sage.all import ComplexIntervalField, QQ, RealIntervalField, prime_range

if not __debug__:
    raise RuntimeError('run with assertions enabled')
R = RealIntervalField(160)
C = ComplexIntervalField(160)
pi = R.pi()


def cis(x):
    return C(x.cos(), x.sin())


def geom(z, m):
    a, b, w, v = C(1), C(0), z, C(1)
    while m:
        if m % 2:
            a, b = a*w, b+a*v
        m //= 2
        if m:
            w, v = w*w, v+w*v
    return b


def fft(a):
    if len(a) == 1:
        return a
    e, o = fft(a[::2]), fft(a[1::2])
    o = [v*cis(2*pi*j/len(a)) for j, v in enumerate(o)]
    return [x+y for x, y in zip(e, o)] + [x-y for x, y in zip(e, o)]


def buckets(terms, N, s, p, direct):
    B, F, J = N//s, 1 << (p-1).bit_length(), 32
    assert N % s == 0
    q, d = divmod(B, p)
    for length, rr in [(q+1, range(d)), (q, range(d, p))]:
        if not rr:
            continue
        bins = [[C(0) for _ in range(F)] for _ in range(J)]
        mass = R(0)
        for th, c in terms:
            x = F*s*th/(2*pi)
            k = int((x.center()+QQ(1)/2).floor())
            v = x-k
            assert abs(v) < QQ(3)/4
            z = c*geom(cis(s*p*th), length)*geom(cis(th), s)
            mass += abs(z)
            for j in range(J):
                bins[j][k % F] += z
                z *= C(0, 2*pi*v)/(j+1)
        transforms = [fft(a) for a in bins]
        # Real-argument integral Taylor remainder; r/F <= 1.
        tail = mass*(3*pi/2)**J/factorial(J)
        for r in rr:
            estimate = sum((a[r]*(QQ(r)/F)**j for j, a in enumerate(transforms)), C(0))
            truth = sum((direct[b*s+i] for b in range(r, B, p) for i in range(s)), R(0))
            assert abs(estimate-truth) + tail < QQ(1)/10**8


N, s, p = 256, 8, 7  # 32 = 4*7+4 blocks
q, d = 100000007, 26
t = 2*R(q)**(QQ(3)/5)
u0 = 126192
X = (3*(t/2).log())**2
assert u0-1 < t < u0 and 1099 < X < 1100 and 0 < X*R(-8).exp() < 1
primes = set(prime_range(1100))
starts = sorted(k for k in primes if k+d in primes)
assert len(starts) == 44
edges = []
for k in starts:
    th = (1+R(d)/k).log()
    w = (X/k).log()*R(k).log()*R(k+d).log()/X
    edges.append((th, w*cis(u0*th)))
terms = [(x-y, a*b.conjugate()) for x, a in edges for y, b in edges]
direct = [abs(sum((a*cis(j*x) for x, a in edges), C(0)))**2 for j in range(N)]
buckets(terms, N, s, p, direct)
# Synthetic real signal with a gridding tie at F*s*th/(2*pi)=1/2,
# zero frequency, and empty buckets when p exceeds the block count.
N, s, p = 32, 8, 7
th = pi/64
terms = [(R(0), C(2)), (th, C(1)), (-th, C(1))]
buckets(terms, N, s, p, [2+2*(j*th).cos() for j in range(N)])
print('Both bucket partitions agree with direct energies to < 1e-8.')
