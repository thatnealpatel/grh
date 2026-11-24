"""Run with SageMath Python, without -O. All interval tests must succeed on whole boxes."""
from sage.all import QQ, RealBallField

if not __debug__:
    raise SystemExit("Run without -O.")

F = RealBallField(128)
s = F('0.50001')
h = [QQ(j)/10 for j in range(-5, 4)]
p = [QQ(j)/100 for j in (1, 4, 8, 12, 15, 16, 17, 17, 10)]
assert sum(p) == 1
shifts = [(a+b, pa*pb) for a, pa in zip(h, p) for b, pb in zip(h, p)]
knots = sorted({-t for t, v in shifts if t <= 0})


def tail(z, d):
    # Integral from z to infinity of y^2 exp(-y)/(y+d), z+d > 0.
    return (-z).exp()*(1+z-d) + d**2*d.exp()*F(0).gamma_inc(z+d)


L = F(0)
for j, left in enumerate(knots):
    mass = sum(v for t, v in shifts if t >= -left)
    offset = F(sum(t*v for t, v in shifts if t >= -left)/mass)
    piece = tail(F(left), offset)
    if j+1 < len(knots):
        piece -= tail(F(knots[j+1]), offset)
    L += piece/mass
P = 2*(F(8)/9)**2/L - sum(v*F(t).exp() for t, v in shifts)
# N(z) = sum r[k] cos(k*z/10), on the real and complex axes.
r = [sum((1 if k == 0 else 2)*p[j]*p[j+k]*F((h[j]+h[j+k])/2).exp()
         for j in range(len(p)-k)) for k in range(len(p))]
I = 2*s*sum(y*(-s*k/10).exp() for k, y in enumerate(r))
margin = P - I*F('1.22').cosh()/3
print('P, I, margin:', P, I, margin, flush=True)
assert margin > F('.00026')
assert P-I*F('1.216').cosh()/3 > F('.00212')


def cover(lo, hi, test, level=0):
    mid = (lo+hi)/2
    if not test(F(mid, (hi-lo)/2)):
        assert level < 26, (lo, hi)
        cover(lo, mid, test, level+1)
        cover(mid, hi, test, level+1)


# Boundary b=1/2. For x >= 1 write x=10 theta mod 20 pi,
# 0 <= theta <= 2 pi. The skew term costs <= |Im N|/max(10 theta,1).
A = [y*(F(k)/20).cosh() for k, y in enumerate(r)]
B = [y*(F(k)/20).sinh() for k, y in enumerate(r)]
assert sum(a*(1-(F(k)/10)**2/2) for k, a in enumerate(A)) > sum(
    b*k/10 for k, b in enumerate(B))  # |x| <= 1, sinc bound


def strip(theta):
    real = sum(a*(k*theta).cos() for k, a in enumerate(A))
    imag = sum(b*(k*theta).sin() for k, b in enumerate(B))
    return real > 0 and (real > abs(imag) or real*10*theta > abs(imag))


assert F(7) > 2*F.pi()
cover(QQ(0), QQ(7), strip)

# Upper witness. a=0 to the left, and a[-1] persists forever.
a = [QQ(v)/100000 for v in (3248, -32580, 81424, -31044, -100000, 29735,
     100000, 74329, -100000, -100000, -100000, -100000, -71726, 7164, 45180,
     59132, 63442, 64892, 60720)]
z = [QQ(j)/8 for j in range(-12, 7)]
assert all(abs(v) <= 1 for v in a)
mean = sum(((1+z[j])*F(-z[j]).exp() - ((1+z[j+1])*F(-z[j+1]).exp()
           if j+1 < len(z) else 0))*F((1+a[j])/2).sqrt()
           for j in range(len(z)) if z[j] >= 0)
assert mean > F(8)/9
jumps = [(v-(a[j-1] if j else 0))*F(-z[j]/2).exp() for j, v in enumerate(a)]


def spectrum(x):
    real = sum(y*(t*x).cos() for t, y in zip(z, jumps))
    imag = sum(y*(t*x).sin() for t, y in zip(z, jumps))
    return real**2 + imag**2 < F('.6167')**2*(F(1)/4 + x**2)


assert F(26) > 8*F.pi()
cover(QQ(0), QQ(26), spectrum)
assert F('.6167') < F('1.226').cosh()/3
print('Full-strip positivity, witness mean, and all-frequency ceiling passed.')
