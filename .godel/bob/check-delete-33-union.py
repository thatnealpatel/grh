"""Delete 33: certify the positive-index law and its missing t probe."""
from functools import cache
from pathlib import Path
from runpy import run_path

from sage.all import ComplexBallField, QQ, RealBallField

if not __debug__:
    raise SystemExit('Run with assertions enabled.')
F, K = RealBallField(512), ComplexBallField(512)
pi = F.pi()
r = (-F(1)/50).exp()
C = F(QQ(39)/20).cosh()/3
Ct = C/(2*(pi/12).cos())
delta = QQ(1)/10**6
unit = 10**9
base = Path(__file__).with_name('deletion-laws')
I = range(-192, 193)
P = range(193, 257)
E = range(-256, 257)
N = range(-256, -192)
S = [-7, 6, 19]


def pairs(row):
    assert row and len(row) % 2 == 0 and min(row[1::2]) > 0
    total = sum(row[1::2])
    return [(a, QQ(p)/total) for a, p in zip(row[::2], row[1::2])]


def input_tables():
    rows = [s for s in (base/'delete-33.txt').read_text().splitlines() if s and not s.startswith('#')]
    j = rows.index('trace')
    assert rows[0] == 'prime' and len(rows[j+1:]) == 512
    prime, trace = ([list(map(int, s.split())) for s in sub] for sub in (rows[1:j], rows[j+1:]))
    a, b = zip(*(tuple(map(int, s.split())) for s in (base/'delete-33.probe').read_text().splitlines()))
    assert len(a) == len(b) == 257
    h = dict.fromkeys(E, 0)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            h[i-j] += x*y
    return prime, trace, (a, b), h


@cache
def root(turn):
    return K(0, 2*pi*turn).exp()


@cache
def exp(q):
    return F(q).exp()


def step(k, start):
    """Original prime response to the step 1_[start,infinity)."""
    s = QQ(k)/25
    return exp(s/2) if start+s <= 0 else (1+start+s)*exp(-start-s/2)


def prime_answers(table):
    z = [QQ(row[0])/400 for row in table]
    assert z[0] == -QQ(192)/25 and sorted(set(z)) == z and 0 in z
    a, b, u = [], [], []
    for row in table:
        means = [QQ(0)]*3
        for h, p in pairs(row[1:]):
            assert 0 <= h <= unit
            radial = QQ(h)/unit
            x = 2*radial**2-1
            for j, v in enumerate((x, 4*x**3-3*x, radial)):
                means[j] += p*v
        for col, v in zip((a, b, u), means):
            col.append(v)
    def answer(col):
        jumps = [col[0]]+[y-x for x, y in zip(col, col[1:])]
        return {k: sum(d*step(k, x) for x, d in zip(z, jumps)) for k in E}
    # Integrate both the finite intervals and the final infinite interval.
    ends = [(1+x)*exp(-x) for x in z]+[F(0)]
    mean = sum(u[i]*(ends[i]-ends[i+1]) for i, x in enumerate(z) if x >= 0)
    return answer(a), answer(b), (1-delta)*mean+delta*(F(1)/2).sqrt()-QQ(8)/9


def cells():
    phi = [pi*(QQ(i)/512)**2 for i in range(513)]
    edges = [K(0, x).exp() for x in phi]
    d = [1+r*r-2*r*w.real() for w in edges]
    cdf = [F(0)]+[2/pi*((x/2).tan()/(F(1)/100).tanh()).arctan() for x in phi[1:-1]]+[F(1)]
    for i in range(512):
        mass = cdf[i+1]-cdf[i]
        j = [K(mass), K(((1+r*r)*mass-(1-r*r)*(phi[i+1]-phi[i])/pi)/(2*r),
                       (1-r*r)*(d[i+1]/d[i]).log()/(2*r*pi))]
        lo, hi = K(1), K(1)
        for k in range(1, 256):
            lo *= edges[i]
            hi *= edges[i+1]
            flat = (hi-lo)/K(0, k)
            j.append(((1+r*r)*j[-1]-(1-r*r)*flat/pi)/r-j[-2])
        yield [w.conjugate() for w in j[:0:-1]]+j


def trace_answers(table):
    t, m, n = [], [], []
    for x, y, *atoms in table:
        assert x*x+y*y <= unit**2
        t.append(K(x, y)/unit)
        law = [(root(QQ(h)/unit), p) for h, p in pairs(atoms)]
        m.append(sum(p*w for w, p in law))
        n.append(sum(p*w*w for w, p in law))
    J = list(cells())
    def answers(v, indices):
        return {k: sum((u*j[k+256]).real() for u, j in zip(v, J)) for k in indices}
    return answers(t, E), answers(m, E), answers(n, S)


def gram_inverse(v, indices):
    a = dict.fromkeys(indices, F(0))
    a[indices[0]] = v[indices[0]]
    for i, j in zip(indices, indices[1:]):
        q = r**(j-i)
        w = (v[j]-q*v[i])/(1-q*q)
        a[j] += w
        a[i] -= q*w
    for i in indices:
        assert abs(sum(c*r**abs(i-j) for j, c in a.items())-v[i]) < F('1e-70')
    return a


def old_repair(prime, tr, price):
    coeff = gram_inverse({k: prime[k]/price-tr[k] for k in I}, I)
    return coeff, sum(map(abs, coeff.values()))


def slab(k, j):
    if j > k:
        return F(0)
    a, b, s = -QQ(j)/25, -QQ(j-1)/25, QQ(k)/25
    return exp(-s/2)*(exp(-a)*(1+a+s)-exp(-b)*(1+b+s))


def positive_extension(prime, tr, price):
    # After extracting r^k each column is affine in k above its knot.
    # Two backward differences leave only the current and previous slabs.
    g = {191: F(0), 192: F(0)}
    a = {192: F(0)}
    prev = F(0)
    for k in P:
        d = price*(tr[k]-r**(k-192)*tr[192])+r**(k-192)*prime[192]-prime[k]
        g[k] = d/r**k
        diag = slab(k,k)/r**k
        assert diag > 0
        a[k] = (g[k]-2*g[k-1]+g[k-2]-prev*a[k-1])/diag
        prev = slab(k+1,k)/r**(k+1)-2*diag
    del a[192]
    return a


def cents(x, lo):
    """Assert an outward decimal enclosure [lo, lo+0.01]."""
    start = QQ(int(lo.replace('.', '')))/100
    assert F(start) < x < F(start+QQ(1)/100), (x, lo)


def baseline():
    prime, trace, columns, h = input_tables()
    A, B, surplus = prime_answers(prime)
    Lt, Lm, Ln = trace_answers(trace)
    qt, et = old_repair(A, Lt, Ct)
    q3, e3 = old_repair(B, Lm, C)
    q2 = gram_inverse({k: -Ln[k] for k in S}, S)
    e2 = sum(map(abs, q2.values()))
    assert (1-delta)*et < delta and 2*(1-delta)*(e3+e2) < delta
    assert F('0.00002413784023') < surplus < F('0.00002413784024')
    assert et < F('1.464e-8') and e3 < F('1.760e-8') and e2 < F('2.908e-10')
    a, b = positive_extension(A, Lt, Ct), positive_extension(B, Lm, C)
    gauge = max(((abs(2*a[j]+b[j])+2*abs(a[j]-b[j]))/3).upper() for j in P)
    assert gauge < QQ(156195265)/10**9
    # Recover the extended prime answers independently of the triangular solve,
    # evaluating the step functional on the two jumps of each slab.
    def completed(prime, extension, tr, q, price):
        ans, trace_ans = {}, {}
        for k in E:
            ans[k] = (1-delta)*(prime[k]+sum(x*(step(k,-QQ(j)/25)-step(k,-QQ(j-1)/25))
                                           for j,x in extension.items()))
            trace_ans[k] = (1-delta)*price*(tr[k]+sum(x*r**abs(k-i) for i,x in q.items()))
            if k >= -192:
                assert abs(ans[k]-trace_ans[k]) < F('1e-48'), (k, ans[k]-trace_ans[k])
        return ans, trace_ans
    p, ans = completed(A, a, Lt, qt, Ct)
    completed(B, b, Lm, q3, C)
    u = sum(h[k]*p[k] for k in N)
    v = sum(h[k]*ans[k] for k in N)
    old, pos = (sum(h[k]*ans[k] for k in band) for band in (I, P))
    pos_added = sum(h[k]*(p[k]-(1-delta)*A[k]) for k in P)
    head = old+pos
    diff = u-v
    trace_probe = sum(h[k]*ans[k] for k in E)
    prime_probe = sum(h[k]*p[k] for k in E)
    assert abs(prime_probe-trace_probe-diff) < F('1e-32')
    for x, lo in [(u, '527324409074.03'), (v, '465073773170.19'), (diff, '62250635903.84'),
                  (old, '60874450406804.82'), (pos, '524014906040.29'),
                  (pos_added, '-26691396721.36'), (head, '61398465312845.11'),
                  (trace_probe, '61863539086015.31'), (prime_probe, '61925789721919.15')]:
        cents(x, lo)
    print('surplus, old t/3t/second repair bounds, gauge:', surplus, et, e3, e2, gauge, flush=True)
    print('negative tail prime, baseline trace, residual:', u, v, diff, flush=True)
    print('matched old, matched positive, prime added on positive:', old, pos, pos_added, flush=True)
    print('matched head, full baseline trace, full fixed prime:', head, trace_probe, prime_probe, flush=True)
    return columns, h, diff, trace_probe, prime_probe


def price(columns, h, diff, trace_probe, prime_probe):
    def norm(v):
        return sum(x*y*r**abs(i-j) for i,x in enumerate(v) for j,y in enumerate(v)).sqrt()
    ideal_upper = Ct*norm(columns[0])*norm(columns[1])
    finite_t = run_path(str(Path(__file__).with_name('check-four-shift-10-2.py')))['finite_t']
    assert ideal_upper-trace_probe < diff/25
    bounds = [('Cauchy–Schwarz', ideal_upper, '61866026525025.04', '2487439009.73', '59763196894.10'),
              ('8192', finite_t(h, 8192), '61874265747026.86', '10726661011.55', '51523974892.29'),
              ('2048', finite_t(h, 2048), '62494696068706.82', '631156982691.51', '-568906346787.68')]
    for name, raw, p_lo, i_lo, d_lo in bounds:
        upper = F(raw)
        increment = upper-trace_probe
        deficit = prime_probe-upper
        for x, lo in [(upper, p_lo), (increment, i_lo), (deficit, d_lo)]:
            cents(x, lo)
        if name == '2048':
            assert increment > diff
        else:
            assert increment < diff
        print(name, 'total price, increment upper, deficit, fixed-prime ratio:',
              upper, increment, deficit, prime_probe/upper, flush=True)


if __name__ == '__main__':
    price(*baseline())
