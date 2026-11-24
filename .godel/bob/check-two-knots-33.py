"""Bound independent slab laws with any two additional real knots."""
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
from runpy import run_path

from sage.all import QQ

base = Path(__file__).resolve().parent
costs = run_path(str(base/'release-costs-33.py'))
s, F = costs['s'], costs['F']
laws = base/'deletion-laws'
if not __debug__:
    raise SystemExit('Run with assertions enabled.')
ref = (laws/'delete-33-tail-baseline.txt').read_bytes()
assert sha256(ref).hexdigest() == '7be0449af83f2b264894d0b0074108139ada0badc0c34a26edc6731d81baaa5c'
z,A,B,U = s['unfold']['lattice']['prime_rows'](ref.decode())
assert len(z)==1257 and z[0]==-QQ(144)/25 and z[-1]==QQ(29)/5
rows = (laws/'delete-33-two-knots.json').read_bytes()
assert sha256(rows).hexdigest() == 'a3ced5854e517cd271f2d5b8eabc942cfe6645e7d58fbe7b86337679d65761b3'
data = json.loads(rows,parse_float=str)
assert isinstance(data, list) and data
for row in data:
    assert isinstance(row, list) and len(row) in (3, 5)
    assert type(row[0]) is int and row[0] in (0, 1)
    assert Fraction(row[-1]) >= 0
    if len(row) == 5:
        f, re, im = map(Fraction, row[1:-1])
        assert f >= 0 and (re != 0 or im != 0)
    else:
        assert row[0] == 1 and len(row[1]) == 3
        tuple(map(Fraction, row[1]))
print('Dual SHA-256:',sha256(rows).hexdigest(),flush=True)
old = {}
def retain(t, upper, a, b, m, w):
    old[t] = upper

off, gains, _ = s['price'](z,A,B,U,data,omit={z[-1]},slab_check=retain)
P = off + sum(gains) + s['continuous_tail'](z,A,B,U,data,den=3600)
print('Original slab price:',P,flush=True)
# The first three positive slabs are [0,2), [2,4), [4,6) in
# units of 1/400. Keep their integrated half-scores for the tests below.
first = z.index(0)
assert z[first:first+4] == [QQ(j)/400 for j in (0,2,4,6)]
aa,bb,*_ = s['tail_data'](z,B,data,list(range(7)),400,primitive=True)
W = [s['step'](QQ(j)/400,0) for j in range(7)]
halves = [(aa[i]-aa[i+1],bb[i]-bb[i+1],W[i]-W[i+1]) for i in range(6)]
def atom_upper(v):
    return s['bern_upper'](*v,F('1e-14'))

half_bounds = list(map(atom_upper,halves))
mid = P-old[0]+sum(half_bounds[:2])
print('Midpoint price:',mid,flush=True)
assert mid < F('-2.3016e-8')
extra = costs['release_costs'](z,B,data,old)
ranked = sorted(zip(extra,z[:-1]),reverse=True)
print('Largest measurable release costs (left endpoint, upper increment):',
      [(t,float(y)) for y,t in ranked[:6]],flush=True)
print('Any one measurable release:',P+ranked[0][0],flush=True)
assert P+ranked[0][0] < F('-8.1396e-9')

# Exact pair comparison, using the rounded-up cost of each release.
limit = -P.upper().exact_rational()
unpaid = []
for i,(a,t) in enumerate(ranked):
    for b,r in ranked[i+1:]:
        if a+b < limit:
            break
        unpaid.append(tuple(sorted((int(400*t),int(400*r)))))
print('Unpaid fully measurable pairs (left endpoints in units of 1/400):',sorted(unpaid))

# Price one knot at an arbitrary real position. Only reprice slabs
# whose fully measurable increment is too large to use directly.
split = list(extra)
h = QQ(1)/1600
large = [i for i,y in enumerate(extra) if y > QQ(37)/10**9]
points = sorted({j for i in large for j in range(int(3200*z[i]),int(3200*z[i+1])+1)})
aa,bb,_,_,curv = s['tail_data'](z,B,data,points,3200,primitive=True)
# The mass primitive is step(t,0), including on t<0.
prim = {j:(a,b,s['step'](QQ(j)/3200,0)) for j,a,b in zip(points,aa,bb)}

for i in large:
    t,r = z[i:i+2]
    j0,j1 = int(3200*t),int(3200*r)
    def score(v):
        left = [a-b for a,b in zip(prim[j0],v)]
        right = [a-b for a,b in zip(v,prim[j1])]
        return atom_upper(left)+atom_upper(right)

    # On each cell bound the quadratic interpolant by its three
    # controls, pricing the two atom choices at each control jointly
    # in their shared knot coordinate. This bound is uniform in both.
    vals = [score(prim[j]) for j in range(j0,j1+1,2)]
    for j in range(j0+1,j1,2):
        v = [2*b-(a+c)/2 for a,b,c in zip(prim[j-1],prim[j],prim[j+1])]
        vals.append(score(v))
    # curv already accounts for differences of two laws in A and B.
    # |(t*exp(-t))''| <= 2 exp(-t/2) for t>=0, |delta U|<=1.
    rem = (curv+(2 if t>=0 else 0))*(-F(t)/2).exp()*h**3/(72*F(3).sqrt())
    split[i] = min(extra[i],max(0,(F(max(y.upper() for y in vals))+rem-old[t]).upper().exact_rational()))

worst = sorted(zip(split,z[:-1]),reverse=True)[:3]
print('Largest single-knot increments (left endpoint, upper increment):',
      [(t,float(y)) for y,t in worst],flush=True)
two = P+worst[0][0]+worst[1][0]
print('Two knots on distinct slabs:',two,flush=True)
assert two < 0

# Test how this price fails: Add all three early midpoints. A single
# rational atom on each half lower-bounds the new local support scores.
base3 = P-sum(old[z[first+i]] for i in range(3))
price3 = base3
for (a,b,m),n in zip(halves,(1403690,4138937,6760354,9255633,11619710,13853201)):
    u = QQ(n)/10**8
    x = 2*u*u-1
    price3 += m*u-a*x-b*(4*x**3-3*x)
print('Three early midpoints: lower on repriced upper using six atoms',price3)
assert price3 > F('2e-8')

# For each split in isolation price the half-scores at +kY, -kY.
# If the surplus is nonnegative this bounds k*(Y_R-Y_L) from below.
for i,ks in enumerate((('2.76e-5','3.08e-6','3.07e-6'),
                       ('9.26e-6','1.07e-6','2.97e-6'),
                       ('5.64e-6','6.85e-7','2.88e-6'))):
    for y,k in zip(('A','B','U'),map(F,ks)):
        tilted = base3+sum(half_bounds[:2*i]+half_bounds[2*i+2:])
        for (a,b,m),v in zip(halves[2*i:2*i+2],(k,-k)):
            tilted += atom_upper((a-(v if y=='A' else 0),b-(v if y=='B' else 0),
                                  m+(v if y=='U' else 0)))
        jump = -tilted/k
        print('Necessary jump at',2*i+1,'/400 in',y,': at least',jump,flush=True)
        assert jump > 0
