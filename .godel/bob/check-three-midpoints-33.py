"""Exclude three added delete-33 knots with a moved quadratic tangent."""
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
from runpy import run_path

from sage.all import QQ

base = Path(__file__).resolve().parent
if not __debug__:
    raise SystemExit('Run with assertions enabled.')
costs = run_path(str(base/'release-costs-33.py'))
neg, s, F = costs['neg'], costs['s'], costs['F']
laws = base/'deletion-laws'
ref = (laws/'delete-33-tail-baseline.txt').read_bytes()
assert sha256(ref).hexdigest() == '7be0449af83f2b264894d0b0074108139ada0badc0c34a26edc6731d81baaa5c'
z, _, B, _ = s['unfold']['lattice']['prime_rows'](ref.decode())
assert len(z)==1257 and z[0]==-QQ(144)/25 and z[-1]==QQ(29)/5
raw = (laws/'delete-33-three-midpoints.json').read_bytes()
assert sha256(raw).hexdigest() == '2716981104b65b67c01c1b8e2306f43a6328145b3425dfaee040b18dd35a13ec'
cert = json.loads(raw,parse_float=str)
data = cert['cuts']
second = [r for r in data if len(r)==3]
assert len(second)==1 and second[0][0]==1
for row in data:
    assert F(row[-1]) >= 0
    if len(row)!=3:
        j,x,re,im,_ = row
        assert j in (0,1) and F(x)>=0 and abs(s['K'](F(re),F(im)))>0

# Perturb raw B jumps, not the normalized Fourier coefficients. This
# center need not be realizable and is never used as a primal law.
bump = {QQ(k)/400:QQ(Fraction(v)) for k,v in cert['jumps']}
assert len(bump)==len(cert['jumps']) and bump.keys()<=set(z)
shift = 0
center = []
for t,y in zip(z,B):
    shift += bump.get(t,0)
    center.append(y+shift)
_, lam, sigma = second[0]
lam = list(map(F,lam))
q = s['second_majorant'](lam)
bc = s['jumps'](z,center,s['C'])
d,v = s['second_tangent'](z,bc,lam,q)
qc = sum(x*y for x,y in zip(bc,v))
constant = -F(8)/9 + sum(F(r[-1]) for r in data if len(r)==5) + F(sigma)*(d+qc)
mesh = sorted([int(400*t) for t in z]+[1,3,5])
assert all(t*400==int(400*t) for t in z) and len(set(mesh))==1260
ap,bp,*_ = s['tail_data'](z,center,data,mesh,400,primitive=True)
W = [s['step'](QQ(k)/400,0) for k in mesh]
def upper(a,b,m):
    return s['bern_upper'](a,b,m,F('1e-14'))
supports = [upper(a-b,c-d0,e-f) for a,b,c,d0,e,f in
             zip(ap,ap[1:],bp,bp[1:],W,W[1:])]
finite = sum(supports)
print('Constant plus finite atom supports:',constant+finite,flush=True)

# Integrate the raw atom score, not a difference relative to the
# (possibly unbounded by one) auxiliary center. All branch points
# are on the 1/400 mesh. Use quadratic Bernstein interpolation on it.
den = 400
lo,hi = int(z[-1]*den),48*den
pts = range(2*lo,2*hi+1)
a,b,size,_,_ = s['tail_data'](z,center,data,pts,2*den)
m = [F(j)/(2*den)*(-F(j)/(2*den)).exp() for j in pts]
ends = [upper(a[i],b[i],m[i]) for i in range(0,len(m),2)]
controls = sum(upper(*(2*v[i]-(v[i-1]+v[i+1])/2 for v in (a,b,m)))
               for i in range(1,len(m),2))
tail = (2*sum(ends)-ends[0]-ends[-1]+controls)/(3*den)
# The shared curved_error includes the integral of exp(-t/2) on
# [z[0],0]. Reuse its derivative coefficient on the positive tail.
scale = neg['curved_error'](z,center,data,den)/(2*((-F(z[0])/2).exp()-1))
scale += 3*(F(1)/(2*den)).exp()/(192*den**3)  # |(t exp(-t))'''| <= 3 exp(-t/2)
err = 2*scale*((-F(z[-1])/2).exp()-F(-24).exp())
remote = s['step'](QQ(48),0)+2*size*F(-24).exp()
bound = constant+finite+tail+err+remote
print('Integrated tail atom support, interpolation, remote:',tail,err,remote,flush=True)
print('Three fixed midpoints, surplus upper:',bound,flush=True)
assert bound < F('-2.51350e-8')

# Price the best three real split positions, not merely these midpoints.
old = dict(zip([QQ(k)/400 for k in mesh],supports))
for j in (0,2,4):
    i = mesh.index(j)
    old[QQ(j)/400] = upper(ap[i]-ap[i+2],bp[i]-bp[i+2],W[i]-W[i+2])
original = constant+sum(old[t] for t in z[:-1])+tail+err+remote
extra = costs['release_costs'](z,center,data,old)
print('Original price and top measurable increments:',original,
      sorted(zip(extra,z[:-1]),reverse=True)[:5],flush=True)
split = list(extra)
h = QQ(1)/1600
large = [i for i,y in enumerate(extra) if y > QQ(32)/10**9]
points = sorted({j for i in large for j in range(int(3200*z[i]),int(3200*z[i+1])+1)})
aa,bb,_,_,curv = s['tail_data'](z,center,data,points,3200,primitive=True)
# The mass primitive is step(t,0), including on t<0.
prim = {j:(a,b,s['step'](QQ(j)/3200,0)) for j,a,b in zip(points,aa,bb)}

for i in large:
    t,r = z[i:i+2]
    j0,j1 = int(3200*t),int(3200*r)
    def score(v):
        left = [a-b for a,b in zip(prim[j0],v)]
        right = [a-b for a,b in zip(v,prim[j1])]
        return upper(*left)+upper(*right)

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
distinct = original + sum(y for y,_ in worst)
# If two or more knots land on one slab, release it completely. The
# remaining knot may split another slab or land on the released slab.
repeated = original+max(e+max(split[:i]+split[i+1:]) for i,e in enumerate(extra))
print('Three distinct slabs; repeated slab:',distinct,repeated,flush=True)
assert distinct < F('-1.46808e-8') and repeated < F('-3.83716e-8')

# If there is no limit on the subdivisions in each of three chosen
# slabs, which triples are not already excluded by the measurable price?
rank = sorted(zip(extra,z[:-1]),reverse=True)
unpaid = []
for i,(e,t) in enumerate(rank[:-2]):
    if original+3*e < 0:
        break
    for j in range(i+1,len(rank)-1):
        f,r = rank[j]
        if original+e+2*f < 0:
            break
        for g,v in rank[j+1:]:
            if original+e+f+g < 0:
                break
            unpaid.append(sorted(int(400*x) for x in (t,r,v)))
print('Unpaid measurable triples (left endpoints in units 1/400):',sorted(unpaid),flush=True)

# Restore the quadratic remainder; also test one contrast per moment
# on each refined slab. Delta is the mean on its right four pieces
# minus the mean on its left four pieces (equal widths).
coeff = [[x-y for x,y in zip(prim[j],prim[j+2])] for j in range(0,48,2)]
unit = [upper(*v) for v in coeff]
free = original-sum(old[QQ(t)/400] for t in (0,2,4))+sum(unit)
print('Eight-piece upper price; necessary Q(V_B-Z) upper:',free,free/F(sigma),flush=True)
for i in (0,8,16):
    gains = []
    for col in range(3):
        lows = []
        for n in range(-30,-7):
            k = F(2)**n
            total = free-sum(unit[i:i+8])
            for j in range(8):
                v = coeff[i+j][:]
                # The score has coefficients (-a,-b,+m).
                v[col] += (1 if (col==2)==(j<4) else -1)*k/4
                total += upper(*v)
            lows.append((-total/k).lower())
        gains.append(float(max(lows)))
    print('Necessary right-minus-left four-piece means (A,B,U), slab',i//8,':',gains,flush=True)

# Preflight the retained *linear* functional on step tails as well.
# bern_upper returns best+eps with best attained or exceeded by a
# sampled atom. Integrate interpolants before maximizing for a lower
# bound (one atom per coarse cell); subtract the uniform errors.
def lower(a,b,m):
    return upper(a,b,m)-F('1e-14')

cells = []
for v in (a,b,m):
    cells.append([(l+4*mid+r)/(6*den) for l,mid,r in zip(v[::2],v[1::2],v[2::2])])
rest = original-tail-err-remote-sum(old[QQ(t)/400] for t in (0,2,4))
# 1,253 retained finite slab bounds, each within eps of its support.
rest -= (len(z)-1-3)*F('1e-14')
for width in (40,20,10,1):
    tail_lower = sum(lower(*(sum(v[i:i+width]) for v in cells)) for i in range(0,len(cells[0]),width))-err-remote
    # Fixed equal subdivisions on all three slabs; no optimization of
    # their positions. Bound the true unpenalized-by-caps atom support
    # of the raw linear price from below, not the objective surplus.
    for pieces in (4,8):
        stride = 16//pieces
        early = sum(lower(*(x-y for x,y in zip(prim[j],prim[j+stride]))) for j in range(0,48,stride))
        print('Linear price lower, finite pieces per released slab and tail step:',pieces,QQ(width)/den,rest+early+tail_lower,flush=True)
    if rest+early+tail_lower > 0:
        break
