"""Certify a retained-shift overshoot. Run with Sage Python, without -O."""
from bisect import bisect_right

from sage.all import ComplexIntervalField, QQ, RealIntervalField, prime_range

if not __debug__:
    raise RuntimeError('the certificate requires assertions')
R = RealIntervalField(192)
C = ComplexIntervalField(192)
d, n = 18, 24
q = 2**127-1
t = 2 * R(q)**(QQ(3)/5)
X = (3*(t/2).log())**2
D = X.log()
L = X/D
assert 11 < 9*t.log()/(4*D) and 9*t.log()/(4*D) < 12
assert D < d and d < 4*D

def floor_cert(y):
    k = y.lower().floor()
    assert k <= y and y < k+1
    return k

bottom, top = floor_cert(X*R(-8).exp())+1, floor_cert(X)
assert bottom-1 < X*R(-8).exp()
starts = [p for p in prime_range(bottom, top-d+1) if (p+d).is_prime()]
w = [(X/p).log()*R(p).log()*R(p+d).log()/X for p in starts]
omega = [(1+R(d)/p).log() for p in starts]
r = floor_cert(D**2)
pairs = [(i, j) for i, p in enumerate(starts) for j, s in enumerate(starts) if abs(p-s) <= r]
pressure = n*n*sum(w[i]*w[j] for i, j in pairs)
assert QQ(6099)/100 < pressure and pressure < 61
# Preflight for the asymptotic two-resolution screen. On this fixture
# even one bin has too large a diagonal for its coarse threshold.
assert sum(b*b for b in w) > QQ(11)/1000 > QQ(1)/(8*16**2)
assert t < X**8

offset = 1296287232
v = 9*t/8 + offset
# Add the interval at high precision; at ordinary double precision this
# width is lost even before taking trigonometric functions.
u = v + R(-1, 1)/32
assert t+L < u and u < 5*t/4-L
angles = [u*f for f in omega]
c = [b*C(y.cos(), y.sin()) for b, y in zip(w, angles)]
z = sum(c)
s = abs(z)
a = R(1)/16
assert s > X**(-QQ(1)/10)
excess = n*(s/a).log()-R(n).log()/2
x = [(ci/z).real() for ci in c]
E = -R(n*n)/2*sum(x[i]*x[j] for i, j in pairs)
y = R.pi()*(u/t-1)
ratio = ((y.sin()/y)**2*(s/a)**n*E.exp())/(16*L)
for label, val in [('n²C',pressure), ('s',s), ('excess',excess), ('interval budget ratio',ratio)]:
    print(label, RealIntervalField(32)(val).str(style='brackets'))
cut = floor_cert(n*D**2)
# Reverse cumulative mass on the truly far pairs; indices are sorted.
suffix = [C(0)]*(len(c)+1)
for i in range(len(c)-1, -1, -1):
    suffix[i] = c[i]+suffix[i+1]
far = 2*sum((ci*suffix[bisect_right(starts,p+cut)].conjugate()).real() for p, ci in zip(starts,c))
print('far pairs', RealIntervalField(32)(far).str(style='brackets'))
assert QQ(4286)/10000 < s and s < QQ(4311)/10000
assert QQ(446)/10 < excess and excess < QQ(448)/10
assert 155000000 < ratio and ratio < 1240000000
assert QQ(966)/10000 < far and far < QQ(982)/10000
