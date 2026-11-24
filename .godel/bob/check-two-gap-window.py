"""Two-translate capacity bounds using the common 152-slab law."""
from runpy import run_path

from sage.all import QQ, RealBallField

if not __debug__:
    raise SystemExit('Run with assertions enabled.')
spacing = run_path('.godel/bob/check-shift-spacing.py')
F = RealBallField(128)
V, P, K, lam = (QQ(50574)/100000, QQ(476)/1000, QQ(7)/10, QQ(48)/100)
assert spacing['mass'] > V and (spacing['P'], spacing['K'], spacing['lam']) == (P, K, lam)
assert spacing['M'] == (QQ(19)/50) and spacing['eta'] == (QQ(1)/1000000)
q = F(-QQ(3)/32).exp()
small = 2/F.pi()*(1+2*sum((-1)**(k-1)*q**k/(4*k*k-1) for k in range(1,17)))
assert small > (QQ(9711)/10000) > 1-V+P
assert 4/F.pi()-1 < (QQ(137)/500) and 1-8/(3*F.pi()) < (QQ(19)/125)
assert (1-spacing['M']-7*spacing['eta'])/2 > (QQ(309)/1000)
assert (1+spacing['M']+14*spacing['eta'])/2 < (QQ(691)/1000)
assert lam*K**2/P > (QQ(309)/1000)/2 and lam < QQ(1)/2
q = F(-2).exp()
L = (QQ(309)/1000)*q-K**2/P*F(-4*lam).exp()
Q = V/4-(QQ(309)/1000)*(QQ(19)/125)*q-(QQ(691)/1000)*(QQ(213)/500)*q**2
assert Q > 0 and V-P-L**2/(4*Q) > (QQ(379)/100000)
print('Small-gap truncation, large-gap uniform surplus:', small, V-P-L**2/(4*Q))
