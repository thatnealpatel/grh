#!/usr/bin/env python3
# Run with the Python from SageMath 10.9. NumPy/SciPy only propose L;
# all acceptance tests use Arb enclosures or exact integers.
import argparse
from sage.all import RealBallField, ComplexBallField, ZZ, matrix
import numpy as np
from scipy.linalg import cholesky

R, C = RealBallField(100), ComplexBallField(100)
pi = R.pi()
parser = argparse.ArgumentParser(description="Certify the chi4 form at support diameter two.")
parser.add_argument("--period", type=int, choices=[14, 16], default=14)
p = parser.parse_args().period
if p == 14:
    q, K, cn, cd = 50, 80000, 5, 1
    even_num, even_den, even_target = 5818, 10**10, 5817
    image_limit = R(61)/10**9
else:
    q, K, cn, cd = 52, 150000, 11, 2
    even_num, even_den, even_target = 59295, 10**11, 5929
    image_limit = R(31)/10**10
D = 1 << q  # Dyadic denominator, not support diameter.
c = R(cn)/cd
ln = [R(n).log() for n in (3, 5, 7)]
a = [t/R(n).sqrt() for t,n in zip(ln,(3,5,7))]
c0 = pi/2 - R.euler_constant() - (2*pi).log()
ycut = 2*pi*(K+1)/p
hc = c0 + (1 + (2*ycut/3)**2).log()/2 - 2*sum(a)
assert hc > c
r = R(3)/2
assert 4*(-r*(p-2)).exp()/(1-(-2*R(p-2)).exp())/(1-(-r*p).exp()) < image_limit
assert R(1)/6000 - image_limit > R(even_target)/10**10
# Digamma recurrence, then four terms of Euler--Maclaurin.
# The error for all k is at most 1/(240*(32+3/4)^8) < 1/10^14.
err = R(1)/10**14
assert 1/(240*(32+R(3)/4)**8) < err
A = R(3)/4
B = [C(R(1)/12), C(-R(1)/120), C(R(1)/252), C(-R(1)/240)]
logcond = (4/pi).log()
yfac = 2*pi/p
freq = [yfac*t for t in ln]
ls = [2*a[0],-2*a[1],2*a[2]]
J = []; W=[]
for k in range(K+1):
    z = C(A,yfac*k/2)
    Z = z+32
    v = 1/Z
    v2 = v*v
    dg = Z.log() - v/2 - (((B[3]*v2+B[2])*v2+B[1])*v2+B[0])*v2
    for i in range(32):
        dg -= 1/(z+i)
    # m >= m_lower, as a real comparison certified by the ball.
    m_lower = dg.real() + logcond + sum(b*(f*k).cos() for b,f in zip(ls,freq)) - err
    if m_lower > c:
        continue
    d_upper = c-m_lower
    # Propose a weight using the midpoint; check the exact dyadic square.
    w = max(1, round(float(d_upper.mid())**0.5*D)) if d_upper.mid()>0 else 1
    while not R(ZZ(w*w))/D**2 > d_upper:
        w += 1
    assert 0 < w < 3*D
    J.append(k); W.append(w)
assert J[0] == 0
print('K, positive deficient indices incl. zero, last:', K,len(J),J[-1],flush=True)
print('cutoff lower enclosure:', hc,flush=True)

def rnd(x):
    b = round(float(x.mid())*D)
    assert abs(x-R(b)/D) < R(1)/D
    return b
sines = [(2*pi*i/p).sin() for i in range(p)]
g = [rnd(R(2)/p)] + [rnd(sines[k%p]/(pi*k)) for k in range(1,2*J[-1]+1)]
r2 = rnd(R(2).sqrt())
assert abs(R(r2)/D) < R(3)/2

def rshift(x, bits):
    return (x+(1 << (bits-1))) >> bits

def verify(parity, num, den):
    # sigma=num/den. U consists of rounded entries of D*((c-sigma)I-H).
    positive = parity==1
    start = 0 if positive else 1
    js, ws = J[start:], W[start:]
    n = len(js)
    off = ((cn*den-cd*num)*D*2+cd*den)//(2*cd*den)
    U = []
    for i,(j,w) in enumerate(zip(js,ws)):
        for k,(l,v) in enumerate(zip(js,ws)):
            if positive and (j==0 or l==0):
                if j==l:
                    s = rshift(w*v*g[0],2*q)
                else:
                    s = rshift(w*v*g[j+l]*r2,3*q)
            else:
                s = rshift(w*v*(g[abs(j-l)]+parity*g[j+l]),2*q)
            U.append((off if i==k else 0)-s)
    npu = np.asarray(U,dtype=np.float64).reshape(n,n)/D
    L = cholesky(npu,lower=True)
    Li = np.rint(L*D)
    assert np.isfinite(Li).all() and np.max(np.abs(Li)) < 2**62
    Lv = matrix(ZZ,n,n,Li.astype(np.int64).ravel().tolist())
    Uv = matrix(ZZ,n,n,U)
    Hmax = (D*Uv-Lv*Lv.transpose()).height()
    # Each unscaled-interval entry of B-U/D differs by less than 20/D.
    # Hence B>= -epsilon I, even if the proposed Cholesky is inaccurate.
    from sage.all import QQ
    epsilon = n*(QQ(20)/D + QQ(Hmax)/D**2)
    target = QQ(even_target)/10**10 if positive else QQ(1)/6000
    assert QQ(num)/den - epsilon > target
    print('parity, n, exact residual height, epsilon upper via ball, certified circle floor:',
          parity,n,Hmax,R(epsilon),target,flush=True)

verify(1,even_num,even_den)
verify(-1,1,5000)
print('Certified line floor >', even_target, '/ 10^10.', flush=True)
