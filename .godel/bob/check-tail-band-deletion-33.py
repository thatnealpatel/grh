"""Price the contribution of A on [24,30] to the full-release delete-33 bound."""
import json
from pathlib import Path
from runpy import run_path

base = Path(__file__).resolve().parent
joint = run_path(str(base/'check-tail-deletion-33.py'))
F = joint['F']
laws = base/'deletion-laws'
z,A,B,U = joint['unfold']['lattice']['prime_rows']((laws/'delete-33-tail-baseline.txt').read_text())
data = json.loads((laws/'delete-33-full-negative-dual.json').read_text(),parse_float=str)
den = 2400
pts = range(24*den,30*den+1)
aa,bb,*_ = joint['tail_data'](z,B,data,pts,den)
# Relax the clipped field to the full box [0,1] x [-1,cap] x [-1,1] (U,A,B).
# Remove the signed integral above the cap by clipping A to cap.
cap = F('0.715')
drop, fixed = [], []
for j,a,b in zip(pts,aa,bb):
    t = F(j)/den
    m = t*(-t).exp()
    # Either endpoint atom lower-bounds the old (Bernstein) upper price.
    old = max(a+b,m-a-b)
    plus,minus = (abs(a)+a)/2,(abs(a)-a)/2
    drop.append(old - (m+plus+cap*minus+abs(b)))
    fixed.append(old - (m-a*A[-1]+abs(b)))

def needed(xs):
    # Full den=2400 trapezoid price, with its interpolation and remote
    # allowances included, is < 7.814e-8 (check-tail-deletion-33.py).
    return (sum(xs[1:-1])+(xs[0]+xs[-1])/2)/den-F('7.814e-8')
print('Required signed A change relative to reference:',needed(fixed))
print('Required signed A excess over clipped field:',needed(drop))
assert needed(fixed)>F('5.70e-8')
assert needed(drop)>F('6.73e-10')
# The phase factor in each A cut has unit modulus. A positive signed
# excess can only come from {a<0, A>cap}, where it is <= L*(1-cap).
L = (-F(12)).exp()*sum(F(row[-1]) for row in data if row[0]==0)/joint['Ct']
length = needed(drop)/(L*(1-cap))
print('Required measure of negative-density upper excursions:', length)
assert length>F('.00147')
