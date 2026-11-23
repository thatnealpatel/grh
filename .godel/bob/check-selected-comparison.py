"""Run with SageMath Python. Intervals enclose real ranges."""
from fractions import Fraction
from sage.all import QQ, RealIntervalField, prime_range

if not __debug__:
    raise RuntimeError("run with assertions enabled")

R = RealIntervalField(120)
q = QQ
def dec(s):
    return QQ(Fraction(s))

unit = R(-1, 1)
# Complete dense signed scans, including the cells touching the block ends.
V, g = 86, 64
a, eta = dec('0.587'), q(1)/2
primes = list(prime_range(100))
logs = [R(p).log() for p in primes]
wv = [l*(R(V).log()-l).max(R(0))/V for l in logs]

def X(y):
    return (3*y.log())**2

def scan(mode):
    j = abs(mode)
    ends = [2*j*R(Q)**(q(3)/5) for Q in [176, 220]]
    first, last = [int((t*g).lower().floor()) for t in ends]
    assert all(n < t*g < n+1 for t, n in zip(ends, [first, last]))
    block = R(q(first)/(g*2*j), q(last+1)/(g*2*j))
    xb = X(block)
    assert V < X(ends[0]/(2*j)) < V+1 and V < xb < 100
    # Bound slopes in log X including prime entry at zero weight.
    xbroad = R(V, xb.upper())
    price = sum(l*abs(1-xbroad.log()+l)/V for p, l in zip(primes, logs) if p <= xb.upper())
    err = price*(xb/V).log() + sum(w*l for w, l in zip(wv, logs))/g
    assert err < eta/2
    marks = []
    for n in range(first, last+1):
        v = R(n)/g
        stat = sum(w*(v*l).cos() for w, l in zip(wv, logs) if w != 0)
        if mode < 0:
            stat = -stat
        assert stat+err < a
        if stat >= a-eta/2:
            marks.append(n)
        else:
            assert stat < a-eta/2
    return marks

def successor(y, P, l):
    x = X(y)
    D = x.log()
    z = [D-t for t in l]
    Z = sum(z)
    H = 40*D
    F, dernum, pools = R(0), R(0), {}
    dD = 2/(y*y.log())
    for i in range(1,len(P)):
        v = l[i]-l[i-1]
        c = (y*v).cos()
        f = ((1+abs(c))/2).sqrt()
        sign = 1 if c>0 else -1 if c<0 else unit
        F += z[i]*f/Z
        dernum += dD*f-z[i]*sign*(y*v).sin()*v/(4*f)
        if i < 2:
            continue
        d = P[i]-P[i-2]
        assert d < H
        E = z[i]*l[i]*l[i-2]*(2*y*(l[i]-l[i-2])).cos()/x
        pools[d] = pools.get(d,0)+E
    charges = {d: 2*(1-d/H)/H*E.max(R(0)) for d,E in pools.items()}
    assert charges[6]+charges[8] > dec('0.0035')
    B = sum(charges.values())
    return F,B,(dernum-F*len(P)*dD)/Z

def compare(j, marks, direct_limit):
    Y = R(q(marks[0])/(g*2*j), q(marks[-1]+1)/(g*2*j))
    y0 = R(q(marks[0]+marks[-1]+1)/(2*g*2*j))
    # Exact inverse of the connected union on the integer q grid.
    named = [Q for Q in range(176,221) if marks[0]**5 <= (g*2*j)**5*Q**3 <= (marks[-1]+1)**5]
    assert named == ([187] if j == 9 else [])
    x = X(Y)
    assert x < 100 and x*R(-8).exp() < 2
    P = [p for p in primes if p < x]
    assert all(p < x or p > x for p in primes)
    l = [R(p).log() for p in P]
    assert sum(t*(x.log()-t)/x for t in l) < dec('0.76')
    F0, B0, _ = successor(y0, P, l)
    _, B, der = successor(Y, P, l)
    F = F0+(Y-y0)*der
    assert F < dec('0.9005') and B > dec('0.0057')
    assert F.upper()-F.lower() < dec('0.001') and B.upper()-B.lower() < dec('0.001')

    # Direct table on the same cluster, evaluated only at entries looked up.
    # Each quarter-cell uses its midpoint to choose a mesh entry. Periodicity in
    # theta need not be used because this short cluster does not wrap the carrier.
    x0 = X(y0)
    D0 = x0.log()
    w = [t*(D0-t)/x0 for t in l]
    cut = abs((x/x0).log())*sum(t*abs(1-x.log()+t)/x for t in l)
    step = q(1)/100000
    r = q(1)/(8*g*2*j)  # quarter-cell half width in y
    left = R(q(marks[0])/(g*2*j))
    for n in marks:
        for i in range(4):
            yc = R(q(8*n+2*i+1)/(8*g*2*j))
            h = yc-left
            H = R(int((h/step).center().round()))*step
            T = R(int((h*D0/step).center().round()))*step
            entry = sum(wt*abs((left*t+H*(t-D0)+T).cos()) for wt,t in zip(w,l))
            error = (cut+abs(h-H)*sum(wt*(D0-t) for wt,t in zip(w,l))
                     +abs(h*D0-T)*sum(w)+r*sum(wt*t for wt,t in zip(w,l)))
            bound = entry+unit*error
            assert bound.upper()-bound.lower() < dec('0.001') and bound < direct_limit
    print(j, 'midpoint', F0, B0, 'F range', F.endpoints(), 'budget range', B.endpoints(),
          'direct upper bound', direct_limit)

runs = {-9: (26563, 26586, '0.523'), -14: (40346, 40368, '0.465'), -20: (60595, 60607, '0.54')}
for mode in (1, -3, 6, -9, 11, -14, 17, -20):
    marks = scan(mode)
    if mode in runs:
        first, last, bound = runs[mode]
        assert marks == list(range(first, last+1))
        compare(abs(mode), marks, dec(bound))
    else:
        assert not marks
