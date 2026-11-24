"""Price the removal of any subset of the finite-slab constancy conditions."""
from hashlib import sha256
import json
from pathlib import Path
from runpy import run_path

from sage.all import QQ

base = Path(__file__).resolve().parent
laws = base/'deletion-laws'
costs = run_path(str(base/'release-costs-33.py'))
s = costs['s']
F = s['F']
ref = (laws/'delete-33-tail-baseline.txt').read_bytes()
rows = (laws/'delete-33-full-release.json').read_bytes()
if not __debug__:
    raise SystemExit("Run with assertions enabled.")
assert sha256(ref).hexdigest() == '7be0449af83f2b264894d0b0074108139ada0badc0c34a26edc6731d81baaa5c'
assert sha256(rows).hexdigest() == '5588f79dd45b98f4e50a8c38a0dd7103421c336917001dca2522e1c61098ce2e'
z, A, B, U = s['unfold']['lattice']['prime_rows'](ref.decode())
data = json.loads(rows, parse_float=str)
old = {}

def retain(t, upper, a, b, m, w):
    old[t] = upper

off, gains, _ = s['price'](z,A,B,U,data,omit={z[-1]},slab_check=retain)
P = off + sum(gains) + s['continuous_tail'](z,A,B,U,data,den=4800)
print('Original slab price:',P,flush=True)
assert P < F('-6.6728e-9')
extra = costs['release_costs'](z,B,data,old)

late = sum(y for t,y in zip(z,extra) if t >= QQ(1)/2)
ranked = sorted(zip(extra,z[:-1]),reverse=True)
protected = ranked[:179]
rest = sum(y for y,t in ranked[179:])
print('Free after 1/2:',P+late,'; protect 179:',P+rest)
print('Protected left knots in units of 1/400:',sorted(int(400*t) for y,t in protected))
assert QQ(1)/2 in z and P+late < F('-3.985e-9') and P+rest < F('-2.34e-10')

# One new midpoint. Price the two half-slabs from the primitives and
# test just one rational atom on each. This is NOT a primal witness.
aa,bb,*_ = s['tail_data'](z,B,data,[0,1,2],400,primitive=True)
assert z[z.index(0)+1] == QQ(2)/400
mass = [s['step'](QQ(i)/400,0)-s['step'](QQ(i+1)/400,0) for i in (0,1)]
a = [x-y for x,y in zip(aa,aa[1:])]
b = [x-y for x,y in zip(bb,bb[1:])]
score = F(0)
for i,u in enumerate((QQ(14)/1000,QQ(41)/1000)):
    x = 2*u*u-1
    score += mass[i]*u-a[i]*x-b[i]*(4*x**3-3*x)
print('Midpoint: two-atom increment over old upper',score-old[0])
assert P+score-old[0] > F('3.53e-8')

# Keep the quadratic remainder of the single second cut. It must be
# paid out of this same local budget, even for a non-step tail.
(sigma,) = [F(row[-1]) for row in data if len(row)==3]
untied = sum(s['bern_upper'](ai,bi,mi,F('1e-14')) for ai,bi,mi in zip(a,b,mass))
assert sigma>0
curvature_budget = (P+untied-old[0])/sigma
print('Midpoint: difference curvature budget',curvature_budget)
assert curvature_budget < F('5.027e-5')

# S_L+S_R <= H(k) + k*(Y_R-Y_L), where H(k) prices the left
# atom with +kY and the right with -kY. For nonnegative surplus
# the old cap P then requires k*(Y_R-Y_L) >= old[0]-P-H(k).
for field, plus, minus, low, high in (
    ('U','2.818e-6','-2.823e-6','.00226','.05243'),
    ('A','2.5804e-5','-1.6844e-5','.000249','.00666'),
    ('B','2.878e-6','-1.9064e-6','.00223','.05937'),
):
    for weight, limit in ((plus,low),(minus,high)):
        k = F(weight)
        price = F(0)
        for i,tilt in enumerate((k,-k)):
            price += s['bern_upper'](a[i]-(tilt if field=='A' else 0),
                                     b[i]-(tilt if field=='B' else 0),
                                     mass[i]+(tilt if field=='U' else 0), F('1e-14'))
        # Test the cutoff without dividing by the signed multiplier.
        bound = P+price-old[0]+k*F(limit)
        print('Excluded jump boundary:',field,limit,'surplus upper',bound)
        assert bound < 0

# Change only the first and quadratic right hand sides, in fixed c0 units.
r = F(QQ(1950000042)/10**9).cosh()/F(QQ(39)/20).cosh()
W = sum(F(row[-1]) for row in data if len(row)==5)
second = F(0)
for row in data:
    if len(row)==3:
        q = s['second_majorant'](list(map(F,row[1])))
        d = q[0]+2*sum(a*(-F(j)*13/50).exp() for j,a in enumerate(q[1:],1))
        assert d>0
        second += F(row[-1])*d
larger = P+(r-1)*W+(r*r-1)*second
print('Original slabs at depth 1.950000042:',larger)
assert larger < 0
