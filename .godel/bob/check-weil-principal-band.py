"""Price the two translated Weil tests. SageMath 10.9 Python + NumPy."""
from math import isqrt
import numpy as np
from sage.all import RealIntervalField, prime_range, QQ

if not __debug__:
    raise RuntimeError('assertions required')
I = RealIntervalField(100)
pi, log2 = I.pi(), I(2).log()
Z, K, N = I(0), 10**7, 512
logs = [(int(p), I(p).log()) for p in prime_range(7001)]
# At the equally spaced nodes in [0,pi], store cos(m theta) to 1/K.
def quant(x):
    z = int((K*x.center()).round())
    assert abs(K*x-z) < 1
    return z

cosine = np.array([[quant((m*i*pi/N).cos()) for i in range(N+1)]
                   for m in range(1,14)], dtype=np.int64)
assert int(abs(cosine).max()) <= K

def poly(row):
    # Round each coefficient, charging its full interval radius about
    # the chosen rational. At an interior maximum the derivative is zero.
    ns = [int((K*x.center()).round()) for x in row]
    assert len(ns) <= len(cosine) and sum(map(abs,ns))*K < 2**62
    peak = int((np.array(ns, dtype=np.int64) @ cosine[:len(ns)]).max())
    err = sum(abs(x-I(n)/K) + I(abs(n))/K**2 for x,n in zip(row,ns))
    curvature = sum(m*m*abs(x) for m,x in enumerate(row,1))
    return I(peak)/K**2 + err + curvature*(pi/(2*N))**2/2

def prices(X,tmax,tmin, free_phase=False):
    D, R = X.log(), X.sqrt()
    assert 6 < D and D < 9 and X < 7000
    assert tmin >= 3000 and tmax <= 28*10**11
    base = ((1-1/R)*(tmax/(2*pi)).log()+I(44)/2000)/R
    out = [base,base]
    free = base
    for p,l in logs:
        if p > R.upper(): break  # all higher powers absent; w=C for primes
        n, v, m = p, l, 1
        rows = [[],[]]
        while n <= X.upper():
            A = 2*l/R*(1/I(n)-1/R).max(Z)
            delta = (l/X*(D-2*v).max(Z) if m == 1 else
                     -l/X*v.min((D-v).max(Z)))
            if free_phase:
                free += abs(delta)+A
            else:
                for row, sign in zip(rows,(1,-1)):
                    row.append(sign*delta-A)
            n, v, m = n*p, v+l, m+1
        if not free_phase:
            for s,row in enumerate(rows): out[s] += poly(row)
    return free if free_phase else out

def Rof(k): return 9*log2*k/5
def yof(k): return (3*log2*I(k)/5).exp()
a = QQ(587)/1000
# Moving cutoff, no lattice or freezing. Both signs at every frequency
# between the extreme harmonics (the gamma-term bound increases with t).
def moving():
    top, lowmass, signed = -1, 1, -1
    for i in range(18*32,67*32):
        k = I(i,i+1)/32
        X = Rof(k)**2
        tlo, thi = 2*yof(k.lower()), 2*yof(k.upper())
        if i < 60*32:
            u = max(p.upper() for p in prices(X,20*thi,tlo))
            assert u < QQ(585948)/10**6, (i,u)
            top = max(top,u)
        U = prices(X,thi,tlo,free_phase=True)
        D = X.log()
        M = sum(l*(D-l).max(Z)/X for p,l in logs if p <= X.upper())
        P = (M*(M+U)/2).sqrt()
        assert P < QQ(823572)/10**6, (i,P)
        signed = max(signed,P.upper())
        if i >= 19*32:
            assert M > QQ(889556)/10**6, (i,M)
            lowmass = min(lowmass,M.lower())
    print('moving upper', top, 'mass lower from k=19',lowmass,'signed cap',signed)

def frozen():
    gap = 1
    for k in range(42,60):
        # Flooring any rational lower approximation within one unit.
        x = Rof(k)**2
        V = int(x.lower().floor())
        assert x < V+1
        u = max(p.upper() for p in prices(I(V-1,V),40*yof(k+1)+1,2*yof(k)-1))
        margin = a-QQ(5)/(8*isqrt(k+1))-u
        assert margin > QQ(1029)/10**7, (k,margin)
        gap = min(gap, margin)
    print('buffered dyadic node margin', gap)

moving()
frozen()
