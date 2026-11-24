"""Check the early-score refit and its failure of the full quadratic at c=39/20."""
import json
from pathlib import Path
from runpy import run_path

from sage.all import QQ, matrix, vector

base = Path(__file__).resolve().parent
laws = base/'deletion-laws'
joint = run_path(str(base/'check-tail-deletion-33.py'))
F,K,C,Ct,step,jumps = (joint[k] for k in ('F','K','C','Ct','step','jumps'))
z0,A0,B0,U0 = joint['unfold']['lattice']['prime_rows']((laws/'delete-33-tail-baseline.txt').read_text())
data = json.loads((laws/'delete-33-full-negative-dual.json').read_text(), parse_float=str)
triples = {row[0]:row[1:] for row in (list(map(int,s.split())) for s in
           (laws/'delete-33-tail-fiber.triples').read_text().splitlines())}
rows = [list(map(int,s.split())) for s in (laws/'delete-33-early-refit.txt').read_text().splitlines()]
assert [row[0] for row in rows] == [int(t*400) for t in z0[:-1]]+list(range(2320,14400,40))
z,A,B,U = [],[],[],[]
Ar,Br,Ur = [],[],[]
for i,(k,*pairs) in enumerate(rows+[[14400,-1,1]]):
    j = min(i,len(z0)-1)
    ref = vector(QQ,[A0[j],B0[j],U0[j]])
    assert pairs and len(pairs)%2 == 0 and min(pairs[1::2]) > 0
    v = vector(QQ,[0,0,0])
    for n,w in zip(pairs[::2],pairs[1::2]):
        if n == -1:
            atom = ref
        elif n == -2:
            us = vector(QQ,[QQ(h)/10**9 for h in triples[min(k,2320)]])
            assert len(us)==3 and all(0<=u<=1 for u in us)
            xx = [2*u*u-1 for u in us]
            H = matrix(QQ,[[1]*3,xx,[4*x**3-3*x for x in xx]])
            p = H.solve_right(vector(QQ,[1,ref[0],ref[1]]))
            assert min(p)>=0
            atom = vector(QQ,[ref[0],ref[1],p*us])
        else:
            u = QQ(n)/10**9
            assert 0<=u<=1
            x = 2*u*u-1
            atom = vector(QQ,[x,4*x**3-3*x,u])
        v += w*atom
    # A small uniform retreat makes all nominally active inequalities strict.
    v = (999*v/sum(pairs[1::2])+ref)/1000
    for out,y in zip((A,B,U,Ar,Br,Ur),list(v)+list(ref)):
        out.append(y)
    z.append(QQ(k)/400)

def integ(t,ys):
    return sum((a-b)*y for a,b,y in zip(t,t[1:]+[0],ys))

def value(x,b):
    return sum(y*K(0,x*t).exp() for t,y in zip(z,b))/K(F(1)/2,x)

mass = [step(t,0) for t in z]
surplus = integ(mass,U)-F(8)/9
E = [int(0<=t<1) for t in z]
score = integ(mass,[(u-r)*e for u,r,e in zip(U,Ur,E)])
ba,bb,bs = jumps(z,A,Ct),jumps(z,B,C),jumps(z,Br,C)
# Jumps of differences confined to the early band, including the right endpoint.
be = [jumps(z,[(u-r)*e for u,r,e in zip(Y,R,E)],D) for Y,R,D in [(A,Ar,Ct),(B,Br,C)]]
slacks = []
for j,*args in data:
    if len(args)==4:
        x,re,im,sig = map(F,args)
        g = K(re,im); g /= abs(g)
        slacks.append(1-(g.conjugate()*value(x,[ba,bb][j])).real())
        score -= sig*(g.conjugate()*value(x,be[j])).real()
    else:
        lam,sig = list(map(F,args[0])),F(args[1])
        q = joint['second_majorant'](lam)
        d,v = joint['second_tangent'](z,bs,lam,q)
        Qref = sum(y*t for y,t in zip(bs,v))
        Qlin = Qref+2*sum((y-r)*t for y,r,t in zip(bb,bs,v))
        slacks.append(d-Qlin)
        score -= 2*sig*sum(y*t for y,t in zip(be[1],v))
        _,vv = joint['second_tangent'](z,bb,lam,q)
        Qtrial = sum(y*t for y,t in zip(bb,vv))
        curvature = Qtrial-Qlin
print('Surplus, early score, minimum cut slack:', surplus,score,min(slacks))
print('Full Q-d, difference-field Q:',Qtrial-d,curvature)
# The unmajorized disk inequality (q = |L|) fails as well. Since
# |p^2-|L|^2| <= e < 1e-8, p > 0, and |L| > .1, 0 <= q-|L| < 2e-7.
_,vnorm = joint['second_tangent'](z,bb,[F(0)]*3,[F(1)])
norm2 = sum(y*t for y,t in zip(bb,vnorm))
raw_lower = Qtrial-d-F('2e-7')*norm2
print('Weighted squared norm, unmajorized Q-d lower bound:',norm2,raw_lower)
assert raw_lower>F('.428')
assert surplus>F('6.39e-8') and score>F('9.77e-8') and min(slacks)>0
assert Qtrial-d>F('.428') and curvature>F('.428')
a,b = abs(value(F('36.202'),ba)),abs(value(F('34.121'),bb))
print('Cap lower bounds at the two specified frequencies:',a,b)
assert a>F('5.9') and b>F('2.52')
