"""Price the removal of any subset of the finite-slab constancy conditions."""
from hashlib import sha256
import json
from pathlib import Path
from runpy import run_path

from sage.all import QQ

base = Path(__file__).resolve().parent
laws = base/'deletion-laws'
neg = run_path(str(base/'check-measurable-negative-deletion-33.py'))
s = neg['shared']
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
# Integrate the competitor's atom price only. The signed reference
# correction is exactly the same in the cell and slab bounds.
den = 1600
h = QQ(1)/den
lo, hi = int(2*den*z[0]), int(2*den*z[-1])
assert all((t*400).is_integer() for t in z)
a, b, *_ = s['tail_data'](z,B,data,range(lo,hi+1),2*den)
m = [F(max(0,j))*h/2*(-F(max(0,j))*h/2).exp() for j in range(lo,hi+1)]

def upper(a,b,m,negative):
    if negative:
        assert m.is_zero()
        return neg['atom_upper'](a,b)
    return s['bern_upper'](a,b,m,F('1e-12'))

# curved_error includes h^3 exp(h/2)/192 and the negative envelope integral.
scale = neg['curved_error'](z,B,data,den)/(2*((-F(z[0])/2).exp()-1))
mass_scale = 3*h**3*(F(h)/2).exp()/192
extra = []
for t,r in zip(z,z[1:]):
    l0, r0 = int(2*den*t)-lo, int(2*den*r)-lo
    negative = t < 0
    ends = [upper(a[j],b[j],m[j],negative) for j in range(l0,r0+1,2)]
    controls = [upper(*(2*v[j]-(v[j-1]+v[j+1])/2 for v in (a,b,m)),negative)
                for j in range(l0+1,r0,2)]
    val = h/3*(2*sum(ends)-ends[0]-ends[-1]+sum(controls))
    rem = (scale+(0 if negative else mass_scale))*2*((-F(t)/2).exp()-(-F(r)/2).exp())
    # If removing constancy slightly improves the computed upper due to
    # enclosure precision, use zero when accounting for optional releases.
    extra.append(max(0,(val+rem-old[t]).upper().exact_rational()))

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
score = F(0)
for i,u in enumerate((QQ(14)/1000,QQ(41)/1000)):
    x = 2*u*u-1
    mass = s['step'](QQ(i)/400,0)-s['step'](QQ(i+1)/400,0)
    score += mass*u-(aa[i]-aa[i+1])*x-(bb[i]-bb[i+1])*(4*x**3-3*x)
print('Midpoint: two-atom increment over old upper',score-old[0])
assert P+score-old[0] > F('3.53e-8')

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
