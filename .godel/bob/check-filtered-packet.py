"""Scalar certificate for the combined three-tent test (SageMath Python)."""
from sage.all import RealBallField

F = RealBallField(128)
l, h, s, delta = map(F, ['0.02', '0.15', '0.5001', '0.001'])
c = F('1.20')


def tail(v, d):
    # Integral from v to infinity of exp(-z) z^2/(z+d).
    return (-v).exp()*(v+1-d) + d**2*d.exp()*F(0).gamma_inc(v+d)


v, d = 2*h-l, l+2*h/3
L = (tail(F(0), d)-tail(v, d))*4/3 + tail(v, l)
P = 2*(F(8)/9)**2/L - l.exp()*h.cosh()**2
I = s*(l/2).exp()*(h.cosh()+delta+(-2*h*s).exp())
assert h.sinh()**2/32 < delta
assert 8*h < F.pi()/2 and 2*h*h.sinh() < 1
assert F('0.57285') < P and I < F('0.94608')
assert P-I*c.cosh()/3 > F('0.00184')
I0 = (l/2).exp()*(h.exp()+3*(-h).exp())/4
assert (F(8)/9)/L < F('0.91')
assert 3*P < I0*F('1.205').cosh()
K0 = 2*(l/2).exp()*(h.cosh()+1)
E0 = K0 + 2*(l/2).exp()*delta
assert c.exp()*K0-c.cosh()*E0 > F('6.12')
assert P-I*c.cosh()/3 < F('0.00186')
old_floor = P/(1+F(-80).exp())-I*c.cosh()/6
assert F('0.2873') < old_floor and old_floor < F('0.2874')
print('Prime price, strip constants, packet margin, and reflection benchmarks passed.')
