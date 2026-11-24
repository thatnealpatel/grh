"""SageMath Python without -O. Verify the raw-order-two conditional chord witness."""
from sage.all import QQ, RealBallField

if not __debug__:
    raise SystemExit('Run without -O.')
F = RealBallField(128)
z = [QQ(j)/10 for j in range(-4, 9)]
a = [QQ(v)/100000 for v in (-88932, -100000, -100000, -100000, -58442, 34040,
     66435, 71453, 67715, 64682, 62872, 61717, 57755)]
assert len(z) == len(a) and all(abs(v) <= 1 for v in a)
mean = sum(F((1+a[j])/2).sqrt()*((1+t)*F(-t).exp() - ((1+z[j+1])*F(-z[j+1]).exp()
           if j+1 < len(z) else 0)) for j, t in enumerate(z) if t >= 0)
assert mean > F(8)/9
jumps = [(v-(a[j-1] if j else 0))*F(-z[j]/2).exp() for j, v in enumerate(a)]
c = F('1.5797')


def verify(lo, hi, level=0):
    mid = (lo+hi)/2
    x = F(mid, (hi-lo)/2)
    real = sum(y*(x*t).cos() for y, t in zip(jumps, z))
    imag = sum(y*(x*t).sin() for y, t in zip(jumps, z))
    if real**2+imag**2 < (c.cosh()/3)**2*(F(1)/4+x**2):
        return
    assert level < 22
    verify(lo, mid, level+1)
    verify(mid, hi, level+1)


# Even numerator modulus, period 20*pi, and increasing denominator.
assert 10*F.pi() < 32
verify(QQ(0), QQ(32))
L = F(0)
S = F(0)
for t, u in zip(z, jumps):
    for s, v in zip(z, jumps):
        h = abs(t-s)
        l = t+s
        pos = max(0, l)
        L += u*v*(2+h)*F(-h/2).exp()
        S += u*v*(1+pos+QQ(pos)**2/2)*F(-abs(l)/2).exp()
X, Y = (L+S)/2, (L-S)/2
print('Angular mean, real and imaginary energies, and each energy cap:', mean, X, Y, c.cosh()**2/18)
assert X < c.cosh()**2/18 and Y < c.cosh()**2/18
