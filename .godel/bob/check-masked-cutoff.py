"""Run with SageMath's Python, without -O. All prices use Arb intervals."""
from sage.all import QQ, RealBallField

if not __debug__:
    raise SystemExit('Run without -O.')
F = RealBallField(160)
step = QQ(1)/5
r = {j: QQ(3-abs(j))/9 for j in range(-2, 3)}
assert sum(r.values()) == 1
for j in r:
    assert r[j] == QQ(sum(a-b == j for a in range(3) for b in range(3)))/9
A = {j: r[j]*F(-j*step/2).exp() for j in r}
I = sum(r[j]*F(-abs(j)*step/2).exp() for j in r)
K = sum(r[j]*r[l]*F(-abs(j+l)*step/2).exp() for j in r for l in r)
assert 0 < I**2 < K < 1


def tail(z, v):
    # Integral of u^2 exp(-u)/(u+v) above z; only z+v must be positive.
    assert z+v > 0
    return (-z).exp()*(1+z-v) + v**2*v.exp()*F(0).gamma_inc(z+v)


def first_floor(A, step):
    knots = sorted({-j*step for j in A if j <= 0} | {QQ(0)})
    L = 0
    for k, left in enumerate(knots):
        active = [j for j in A if left+j*step >= 0]
        mass = sum(A[j] for j in active)
        v = sum(A[j]*j*step for j in active)/mass
        term = tail(F(left), v)
        if k+1 < len(knots):
            term -= tail(F(knots[k+1]), v)
        L += term/mass
    return 2*(F(8)/9)**2/L - sum(A[j]*F(j*step).exp() for j in A)


P = first_floor(A, step)
print('First prime price, mask mass, and squared mask mass:', P, I, K)
assert P > F('.5578122')
for depth, raw, masked in [('1.54', '-.235', '-.394'),
                            ('1.574', '-.002', '-.180'),
                            ('1.60', None, '-.0062')]:
    c = F(depth)
    raw_limit = (2*c).cosh()/3*(1-2*(3*P/c.cosh())**2/K)
    mask_limit = I*(2*c).cosh()/3*(1-2*(3*P/(I*c.cosh()))**2)
    print('Depth, raw and masked upper limits:', depth, raw_limit, mask_limit)
    assert raw is None or raw_limit < F(raw)
    assert mask_limit < F(masked)

p = F(47)/81
assert 3*p/F('1.574').cosh() < 1/F(2).sqrt()
assert (2*F('1.574')).cosh()/3*(1-2*(3*p/F('1.574').cosh())**2) > F('.16')
for depth, n, bound in [('1.90', 7, '-.00092'), ('1.95', 15, '-.000044')]:
    ratio = 3*P/(I*F(depth).cosh())
    assert 2*(F.pi()/(n+1)).cos()*ratio < 1
    price = I/3*(1-2*(F.pi()/(n+2)).cos()*ratio)
    assert price < F(bound)
    print('Masked prefix price:', depth, n, price)
assert F('1.968').cosh() < 6*P/I < F('1.969').cosh()

# Difference shifts: the real line mask |A(1/2+ix)|^2, not A(1/2+ix)^2.
p = dict(zip(range(-5, 4), [QQ(v)/100 for v in (1, 4, 8, 12, 15, 16, 17, 17, 10)]))
assert sum(p.values()) == 1
h = QQ(1)/10
D = {s: sum(p[i]*p[j]*F(j*h).exp() for i in p for j in p if i-j == s)
     for s in range(-8, 9)}
I17 = sum(p[i]*p[j]*F(min(i, j)*h).exp() for i in p for j in p)
P17 = first_floor(D, h)
c = F('1.6065')
W = I17*(2*c).cosh()/3*(1-2*(3*P17/(I17*c.cosh()))**2)
assert P17 > F('.55279649') and I17 < F('.90445972') and W < F('-.00028')
ratio = 3*P17/(I17*F('1.95').cosh())
assert 2*ratio*(F.pi()/14).cos() < 1
price = I17/3*(1-2*ratio*(F.pi()/15).cos())
assert price < F('-.00012')
print('Difference-shift floor, mass, second and order-13 prices:', P17, I17, W, price)
