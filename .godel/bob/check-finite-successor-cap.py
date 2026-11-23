"""Certify the finite two-statistic implication on 25107 <= X <= 25108."""
import numpy as np
from sage.all import QQ, RealIntervalField, prime_range

if not __debug__:
    raise RuntimeError('run with assertions enabled')
R = RealIntervalField(120)
x = R(25107, 25108)
D = x.log()
H = 40*D
P = list(prime_range(25109))
assert P[-1] < 25107 and 7 < x*R(-8).exp() < 11
l = [R(p).log() for p in P]
z = [D-t for t in l]
w = [t*v/x for t, v in zip(l, z)]
M = sum(w)
assert P[4] == 11
P, l, z, w = P[4:], l[4:], z[4:], w[4:]
Z = sum(z)
# The deficit not accounted for by pairs of consecutive edges.
delta = (1-QQ(9005)/10000-z[0]/Z
         -(z[1]+z[-1])/(2*Z)*(1-1/R(2).sqrt()))
alpha, beta = QQ(873)/1000, QQ(956)/1000

# Exact integer upper dot products, after rounding outward. Trig functions
# are only evaluated on this fixed grid, never at an unknown prime phase.
N = 48
h = R.pi()/(2*N)
h2 = h*h
K = 10**7
L = 10**10

def down(x, scale):
    return int((x*scale).lower().floor())

def up(x, scale):
    return int((x*scale).upper().ceil())

tab = []
for j in range(N+1):
    a = j*h
    for k in range(-N, N+1):
        b = k*h
        # Squared radii for the four consistent flank signs.
        ca, cb, cab = a.cos(), b.cos(), (a+b).cos()
        U = max(((34+24*s*ca+24*t*cb+18*s*t*cab)/100).max(R(0)).sqrt().upper()
                for s in (1,-1) for t in (1,-1))
        tab.append((min(0, up(R(U)-1, K)), up(1-(a/2).cos(), K),
                    up(1-(b/2).cos(), K), up(-(2*(a+b)).cos(), K)))
uv, da, db, negcos = np.array(tab, dtype=np.int64).T
pos = np.maximum(negcos, 0)
neg = np.minimum(negcos, 0)
assert max(int(np.abs(v).max()) for v in (uv, da, db, pos, neg)) <= K+1
assert da.min() >= 0 and db.min() >= 0
# One cutoff-independent majorant on the same angle grid. In units of 1/(2000 K)
# this grid maximum bounds U-1 + .946*(D(a)+D(b))/2 - .0315*r.
slope, cost = QQ(946)/1000, QQ(315)/10000
mesh = int(np.max(2000*uv+946*(da+db)+63*negcos))
constant = 1-slope+QQ(mesh)/(2000*K)+h2*(QQ(3)/5+slope/4+8*cost)/8
assert constant < QQ(27)/1000
m = 1-9*R(-8).exp()
intercept = 1-m+m*(QQ(27)/1000+slope*QQ(9005)/10000+cost/20)
assert intercept+20*cost*QQ(2389)/10**6 < QQ(882315)/10**6
assert (QQ(8)/9-intercept)/(20*cost) > QQ(12825)/10**6

err = R(0)
num = 0
for i in range(1, len(P)-1):
    c = w[i-1].min(w[i]).min(w[i+1])
    A, B = alpha*z[i]/(2*Z), alpha*z[i+1]/(2*Z)
    d = P[i+1]-P[i-1]
    T = beta*(2/H)*(1-d/H).max(R(0))*z[i+1]*l[i-1]*l[i+1]/x
    C, J, G, Tp, Tm = down(c,L), up(A,L), up(B,L), up(T,L), down(T,L)
    assert min(C,J,G,Tp,Tm) >= 0 and (C+J+G+Tp+Tm)*(K+1) < 2**62
    v = C*uv + J*da + G*db + Tp*pos + Tm*neg
    num += int(v.max())
    # Separate linear interpolation in the two angles, then convexity
    # of the norm. See finite-successor-cap.md for the derivative bounds.
    err += h2*((QQ(3)/5*c+(A+B)/4+8*T)/8)
cap = M-alpha*delta+beta*QQ(2389)/10**6+QQ(num)/(L*K)+err
print('upper certificate expression',cap, 'interpolation allowance',err)
assert cap < QQ(8877)/10000 < QQ(8)/9
