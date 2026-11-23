"""Rule out .587 marks on the complete block Q=2^19, J=Q."""
import numpy as np
from sage.all import QQ, RealIntervalField, prime_range

if not __debug__:
    raise RuntimeError('run with assertions enabled')
R = RealIntervalField(96)
Q = 2**19
def cutoff(q):
    return (9*R(q).log()/5)**2
V = 561
assert V < cutoff(Q) < V+1
# Mass is nontrivial throughout, including between prime entries.
lo, hi = V, int(cutoff(2*Q).upper().ceil())
l = [R(p).log() for p in prime_range(hi+1)]
for k in range(lo,hi):
    assert sum(t*(R(k).log()-t).max(R(0))/(k+1) for t in l) > QQ(8)/9
x = R(V,hi)
freeze = (x/V).log()*sum(t*abs(1-x.log()+t)/V for t in l)
l = [t for t in l if t < R(V).log()]
w = [t*(R(V).log()-t)/V for t in l]
M = sum(w)
# Round downward to an integer within one unit of the true scaled value.
K = 10**6
def fixed(x):
    n = int((K*x).lower().floor())
    assert K*x < n+1 or K*x == n+1
    return n

# Each block has length 4, with nodes every 1/32, including both ends.
N = 128
C = np.array([[fixed((R(i)*t/32).cos()) for i in range(N+1)] for t in l], dtype=np.int64)
S = np.array([[fixed((R(i)*t/32).sin()) for i in range(N+1)] for t in l], dtype=np.int64)
assert np.abs(C).max() <= K and np.abs(S).max() <= K
# Per product (w cos)*cos or (w sin)*sin the error is <= (1+w)/K:
# vary the first factor against the rounded trig factor, then the second
# factor against the exact weighted factor. No floating-point dot products.
err = 2*(len(w)+M)/K + sum(a*t for a,t in zip(w,l))/64
for mode in (1,-3,6,-9,11,-14,17,-20):
    j = abs(mode)
    # Include padding for the left nodes of all cells touching the block.
    first = int(((2*j*R(Q)**(QQ(3)/5)-1)/4).lower().floor())
    last = int(((2*j*R(2*Q)**(QQ(3)/5)+1)/4).upper().floor())
    top = -K*K
    for b in range(first,last+1,256):
        A, B = [], []
        for n in range(b,min(last+1,b+256)):
            A.append([fixed(a*(4*n*t).cos()) for a,t in zip(w,l)])
            B.append([fixed(a*(4*n*t).sin()) for a,t in zip(w,l)])
        A, B = np.array(A,dtype=np.int64), np.array(B,dtype=np.int64)
        assert np.abs(A).max() <= K and np.abs(B).max() <= K and 2*len(w)*K*K < 2**62
        scores = (1 if mode > 0 else -1)*(A@C-B@S)
        top = max(top,int(scores.max()))
    bound = QQ(top)/(K*K)+err
    print(mode, 'uniform frozen upper bound', bound, flush=True)
    assert bound+freeze < QQ(48)/100
    assert bound+QQ(1)/32 < QQ(587)/1000-QQ(1)/8
