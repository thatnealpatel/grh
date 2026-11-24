"""SageMath: Can the unchanged second cutoff replace the new mask at 3t?"""
import runpy
from pathlib import Path
from sage.all import QQ, RealBallField

if not __debug__:
    raise SystemExit('Run with assertions enabled.')
F = RealBallField(128)
root = Path('.godel/bob')
# Replay the all-frequency certificates and common-law normalization.
left = runpy.run_path(str(root/'check-two-height-radial-witness.py'))
right = runpy.run_path(str(root/'check-translated-step-11-1.py'))
a, b = (QQ(5999)/6000*t for t in (QQ(89)/200, QQ(111)/200))
p = a*left['mean']+b*(right['mean_margin']+F(8)/9)+(1-a-b)*(F(1)/2).sqrt()
c = F(QQ(39)/20)
cap = c.cosh()/(6*(F.pi()/12).cos())
mA = a*left['cap']+b*right['cap_A']
mB = a*left['cap']+b*right['cap_B']
assert p-F(8)/9 > F('.000013') and mA < cap and mB < c.cosh()/3
# Add the jumps of the two B profiles on the union of the rational knots.
jumps = {}
for coef, z, B in [(a, left['z'], left['b']), (b, right['z'], right['B'])]:
    for t, l, r in zip(z, [0]+B, B):
        jumps[t] = jumps.get(t, 0)+coef*(r-l)
points = [(F(t), F(j)*F(-t/2).exp()) for t, j in jumps.items() if j != 0]
L = F(0)
S = [F(0), F(0)]
for i, (z, j) in enumerate(points):
    for k, (w, l) in enumerate(points[:i+1]):
        wt = j*l*(1 if i == k else 2)
        h = abs(z-w)
        L += wt*(2+h)*(-h/2).exp()
        for s in [0, 1]:
            u = z+w+s
            up = u if u > 0 else F(0)  # z,w are exactly dyadic
            S[s] += wt*(1+up+up**2/2)*(-abs(u)/2).exp()
limit = c.cosh()**2/18
print('Angular surplus, A cap slack, B cap slack:', p-F(8)/9, cap-mA, c.cosh()/3-mB)
for s in [0, 1]:
    print('Shift, real energy, imaginary energy, cutoff:', s, (L+S[s])/2, (L-S[s])/2, limit)
assert (L+abs(S[0]))/2 < F('.71211') < limit
assert (L+S[1])/2 > F('.78831') > limit
