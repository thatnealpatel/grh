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


L = 0
for k in range(3):
    mass = sum(A[j] for j in r if j >= -k)
    v = sum(A[j]*j*step for j in r if j >= -k)/mass
    term = tail(F(k*step), v)
    if k < 2:
        term -= tail(F((k+1)*step), v)
    L += term/mass
P = 2*(F(8)/9)**2/L - sum(A[j]*F(j*step).exp() for j in r)
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
