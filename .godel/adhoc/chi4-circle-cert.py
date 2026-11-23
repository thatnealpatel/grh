#!/usr/bin/env python3
"""Whole-window certificate for chi4 at diameters 2, 11/5, and 9/4.
Run with SageMath 10.9's Python (not the Sage preparser), assertions enabled.
SciPy Cholesky and rounding by float are only proposals. The certificate
uses Arb for analytic quantities and exact integers/rationals for the residual.
"""
import argparse
if not __debug__:
    raise RuntimeError("run without Python optimization so that certificate assertions execute")
import numpy as np
from scipy.linalg import cholesky
from sage.all import RealBallField, ComplexBallField, ZZ, QQ, matrix

R, C = RealBallField(100), ComplexBallField(100)
pi = R.pi()
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--period', type=int, choices=[14,16,17], default=14,
                    help='14 and 16 certify diameter two; 17 certifies diameter 11/5')
parser.add_argument('--nine-fourths', action='store_true',
                    help='use diameter 9/4 instead of 11/5 with period 17')
args = parser.parse_args()
P = args.period
if args.nine_fourths and P != 17:
    parser.error('--nine-fourths requires --period 17')
if P == 17:
    diameter, K, c_exact, q = QQ(11)/5, 247000, QQ(263)/50, 52
    even_sigma, even_floor = QQ(44)/10**10, QQ(4368)/10**12
    odd_sigma, odd_floor, image_upper = QQ(3)/10**6, QQ(2)/10**6, QQ(1005)/10**12
    if args.nine_fourths:
        diameter = QQ(9)/4
        even_sigma, even_floor = QQ(57)/50_000_000_000, QQ(11)/10**10
        odd_sigma, odd_floor, image_upper = QQ(1)/10**6, QQ(9)/10**7, QQ(7)/6250000000
else:
    diameter = QQ(2)
    odd_sigma, odd_floor = QQ(1)/5000, QQ(1)/6000
    if P == 14:
        K, c_exact, q, image_upper = 80000, QQ(5), 50, QQ(61)/10**9
        even_sigma, even_floor = QQ(5818)/10**10, QQ(5817)/10**10
    else:
        K, c_exact, q, image_upper = 150000, QQ(11)/2, 52, QQ(31)/10**10
        even_sigma, even_floor = QQ(59295)/10**11, QQ(5929)/10**10
D = 1 << q  # Dyadic denominator, not support diameter.
d, c = R(diameter), R(c_exact)
t = [R(n).log() for n in (3, 5, 7)]
b = [2*t[0]/R(3).sqrt(), -2*t[1]/R(5).sqrt(), 2*t[2]/R(7).sqrt()]
if P == 17:
    t.append(R(9).log())
    b.append(-2*t[0]/3)
    assert t[-1] < d < R(11).log()
else:
    assert t[-1] < d < R(9).log()
assert d+t[-1] < P
A = R(3)/4
h0 = pi/2 - R.euler_constant() - (2*pi).log()
yfac = 2*pi/P
ycut = yfac*(K+1)
cutoff_floor = h0 + (1 + (ycut/(2*A))**2).log()/2 - sum(map(abs,b))
assert cutoff_floor > c
u = P-d
image = 2*d*(-3*u/2).exp()/(1-(-2*u).exp())/(1-(-R(3)*P/2).exp())
assert image < R(image_upper)
print('P, d, c, K, cutoff lower bound, image penalty bound:', P, d, c_exact, K, cutoff_floor, image, flush=True)

J = []
W = []
logcond = (4/pi).log()
freq = [yfac*x for x in t]
for k in range(K+1):
    m = C(A,yfac*k/2).psi().real() + logcond + sum(bi*(fi*k).cos() for bi,fi in zip(b,freq))
    if m > c:
        continue
    deficit = c-m
    w = max(1,round(max(0.,float(deficit.mid()))**0.5*D))
    while not R(ZZ(w*w))/D**2 > deficit:
        w += 1
    assert 0 < w < 3*D
    J.append(k)
    W.append(w)
assert J[0] == 0
print('retained nonnegative indices, last:',len(J),J[-1],flush=True)

def rnd(x):
    h = round(float(x.mid())*D)
    assert abs(x-R(h)/D) < R(1)/D
    return h

cycle = int(2*diameter.denominator()*P)
sines = [(pi*d*i/P).sin() for i in range(cycle)]
g = [rnd(d/P)] + [rnd(sines[k%cycle]/(pi*k)) for k in range(1,2*J[-1]+1)]
r2 = rnd(R(2).sqrt())
assert abs(R(r2)/D) < R(3)/2
assert d/P < R(1)/2

def rshift(x,bits):
    return (x+(1 << (bits-1))) >> bits

def verify(parity,sigma,target):
    # U approximates D*((c-sigma)*I-H), where the Gram weights are
    # W/D exactly, not rounded approximations to be backed out later.
    start = int(parity == -1)
    js,ws = J[start:],W[start:]
    n = len(js)
    off = int(((c_exact-sigma)*D+QQ(1)/2).floor())
    U = np.empty((n,n),dtype=np.int64)
    for i,(j,w) in enumerate(zip(js,ws)):
        row = []
        for l,v in zip(js[:i+1],ws[:i+1]):
            if j == 0:  # j=l=0, since this is lower triangular
                s = rshift(w*v*g[0],2*q)
            elif l == 0:  # exactly one index zero
                s = rshift(w*v*g[j]*r2,3*q)
            else:
                s = rshift(w*v*(g[j-l]+parity*g[j+l]),2*q)
            row.append(-s)
        row[-1] += off
        assert -(1 << 63) <= min(row) and max(row) < (1 << 63)
        U[i,:i+1] = row
        U[:i,i] = row[:-1]
    print('assembled parity, n:',parity,n,flush=True)
    proposal = np.array(U,dtype=np.float64,order='F')
    proposal /= D
    L = cholesky(proposal,lower=True,overwrite_a=True,check_finite=False)
    del proposal
    L *= D
    np.rint(L,out=L)
    assert np.isfinite(L).all() and L.max() < 2**62 and L.min() > -2**62
    Li = L.astype(np.int64)
    del L
    Lv = matrix(ZZ,n,n,Li.ravel().tolist())
    del Li
    Lt = Lv.transpose()
    # Exact, in row panels to bound peak space for large integer entries.
    height = ZZ(0)
    block = 384
    for lo in range(0,n,block):
        hi = min(lo+block,n)
        Uv = matrix(ZZ,hi-lo,n,U[lo:hi,:].ravel().tolist())
        residual = D*Uv - Lv[lo:hi,:]*Lt
        height = max(height,residual.height())
        del Uv,residual
    epsilon = n*(QQ(20)/D + QQ(height)/D**2)
    assert sigma-epsilon > target
    print('parity, n, sigma, residual height, epsilon, circle floor:',
          parity,n,sigma,height,R(epsilon),target,flush=True)
    return target

verify(1, even_sigma, even_floor)
verify(-1, odd_sigma, odd_floor)
# Paired archimedean images are PSD on even tests. Only odd pays this cost.
assert odd_floor-image_upper > even_floor
print('certified normalized line bound:',even_floor,R(even_floor),flush=True)
