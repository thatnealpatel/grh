"""Scalar estimates for the chi4 periodized-pulse transfer (SageMath 10.9)."""
from sage.all import QQ, RealBallField

if not __debug__:
    raise RuntimeError('run with assertions enabled')
R = RealBallField(100)
pi = R.pi()
A = QQ(3)/4
a, h, T = QQ(1)/10**4, QQ(1)/10**11, 10**6
gamma = QQ(11)/10**10
n = 224000000000
arch0 = pi/2 - R.euler_constant() - (2*pi).log()
atoms = [(R(k).log(), 2*R(b).log()/R(k).sqrt())
         for k, b in [(3, 3), (5, 5), (7, 7), (9, 3)]]
B = sum(p for t, p in atoms)
assert arch0-B > -QQ(585)/100 and arch0+B+1/A < 6
curvature = 4*((2*A)**-3 + 1/(4*(2*A)**2)) + sum(p*t*t for t, p in atoms)
assert curvature < 17
assert n*h == QQ(224)/100 and (n-1)*h + 32*a < QQ(9)/4
assert -QQ(585)/100 + R(2000/QQ(3)).log() > gamma
edge = pi/h
assert -QQ(585)/100 + (2*edge/3).log() > 19
alias = 256/a**4 * (h/pi)**3 * QQ(3)/2
assert alias < QQ(2)/10**16
central = 12*(a*1000)**16
err = QQ(2)/10**14
assert central + alias < err
split = 10**5
assert gamma + 6 + R(1+split).log() + alias < 18
assert 64/(a*split)**4 < 1
loss = err + 17*pi**2/(2*T**2) + QQ(1)/(2*10**13)
assert gamma-loss > QQ(1)/10**9
print('Curvature, alias upper, floor after coefficient rounding:',
      curvature, alias, gamma-loss)
