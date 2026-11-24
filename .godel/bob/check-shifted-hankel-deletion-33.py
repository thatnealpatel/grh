"""Price positive-side and shifted Hankel cuts at the exact comparison depth."""
from math import comb, factorial
from pathlib import Path
from runpy import run_path

from sage.all import QQ

if not __debug__:
    raise SystemExit('Run with assertions enabled.')
base = Path(__file__).resolve().parent
old = run_path(str(base/'check-unfolded-deletion-33.py'))
F, Ct = old['F'], old['Ct']
z, A, B, U = old['lattice']['prime_rows']((base/'deletion-laws/delete-33-unfolded-seed.txt').read_text())
j = z.index(0)
z,A,U = z[j:],list(map(F,A[j:])),list(map(F,U[j:]))
assert z[-1]==QQ(22)/5
atom = (F(B[-1]).arccos()/3).cos()
new = A[:-1]+[atom]


def jumps(v):
    return [a-b for a,b in zip(v,[0]+v)]


def square_form(y, left, knots, vals):
    """Shifted, normalized form for f=exp(-s/2) sum y_i L_i(s)."""
    norm = sum(a*a for a in y)
    c = [sum(a*b for i,a in enumerate(y) for j,b in enumerate(y) if i+j==k)
         for k in range(2*len(y)-1)]
    total = F(0)
    for x,dy in zip(knots,jumps(vals)):
        t = x-left
        assert t >= 0
        v = [QQ(0),QQ(1)]  # L_{-1}=0, L_0=1
        for k in range(len(c)):
            v.append(((2*k+1-t)*v[-1]-k*v[-2])/(k+1))
        total += dy*F(-t-left/2).exp()*sum(q*(2*b-a-d) for q,a,b,d in zip(c,v,v[1:],v[2:]))
    return total/norm


# HS^2 = integral z exp(-z) A(z)^2 dz. Price the eigenvalue of each
# sign against at least one eigenvalue of the opposite sign.
hs = sum(F(-x).exp()*(1+x)*da for x,da in zip(z,jumps([a*a for a in new])))
neg = square_form([1,6,6,6],QQ(0),z,new)
pos = square_form([1],QQ(0),z,new)
bound = (hs-neg**2).sqrt()
assert neg<0<pos and pos>-neg and bound<F('.617782')<Ct
print('Full upper-branch tail, unshifted: HS^2, signed forms, operator norm upper:',hs,neg,pos,bound)

# Certify a fixed sign of f on [0,3/5], using exact Bernstein coefficients.
y = [-917,245,197,157,124,95,72,52,36,23,12,4,-2,-7,-10,-12,-13,-14,-14,-13,-12,-11,-10,-8,-7,-5,-4,-3,-1,0,1,2]
left = -QQ(3)/5
deg = len(y)-1
p = [sum(y[i]*comb(i,k) for i in range(k,deg+1))*left**k/factorial(k) for k in range(deg+1)]
ber = [sum(p[k]*QQ(comb(i,k))/comb(deg,k) for k in range(i+1)) for i in range(deg+1)]
assert max(ber)<0
v0 = square_form(y,left,[left]+z,[F(-1)]+A)
v1 = square_form(y,left,[left]+z,[F(-1)]+new)
assert v1>v0
limit = (Ct-v0)/(v1-v0)
ms = [F(-x).exp()*(1+x) for x in z]
m0 = sum(d*u for d,u in zip([a-b for a,b in zip(ms,ms[1:]+[0])],U))
gain = ms[-1]*(((1+atom)/2).sqrt()-U[-1])
required = (F(8)/9-m0)/gain
assert 0<required<F('.0031')<limit<F('.121')
assert Ct-(v0+required*(v1-v0))>F('.00049')
print('Shifted negative-side floor, seed and full replacement:',v0,v1)
print('Mixture thresholds, mean requires more than, cap allows at most:',required,limit)
