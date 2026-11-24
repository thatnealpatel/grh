"""One balanced mask against all constant mixtures of the six tabulated profiles."""
import os
from runpy import run_path

from sage.all import QQ, RealBallField

if not __debug__:
    raise SystemExit('Run with assertions enabled.')
F = RealBallField(128)
root = '.godel/bob/'
os.environ['TWO_TERM_LAW'] = 'regional'
regional = run_path(root+'check-two-term-10-2.py')
os.environ['TWO_TERM_LAW'] = 'hard-pair'
hard = run_path(root+'check-two-term-10-2.py')
single = run_path(root+'check-single-shift-10-2.py')
radial = run_path(root+'check-two-height-radial-witness.py')
step = run_path(root+'check-translated-step-11-1.py')
C1 = hard['C1']

def jumps(law, key):
    return {t: b/C1 for t,b in hard['jump_terms'](law[key], law['z'])}

laws = [single, regional, hard, radial, step]
beta = [jumps(law, 'b' if law is radial else 'B') for law in laws]+[{}]
g = [2*sum(jumps(law, 'a' if law is radial else 'A').values()) for law in laws]+[F(0)]
u = [law['mean_margin'] for law in laws[:3]]+[radial['mean']-F(8)/9,
     step['mean_margin'], (F(1)/2).sqrt()-F(8)/9]
cap = hard['C10']/C1
s, d = QQ(1)/20, QQ(51)/100
N = 256
eps = QQ(1)/10**12

def combine(weights):
    assert sum(weights) == 1 and min(weights) >= 0 and len(weights) == len(beta)
    result = {}
    for a, points in zip(weights, beta):
        if a:
            for t,b in points.items():
                result[t] = result.get(t,0)+a*b
    return result

# Evaluate the signed upper bound J=C-Re int H m^2, NOT a lower
# bound for capacity. The error of the truncated C is below eps.
def signed(weights):
    points = combine(weights)
    we, ws = {}, {}
    for t,b in points.items():
        for p,a in points.items():
            we[t-p] = we.get(t-p,0)+a*b
            ws[t+p] = ws.get(t+p,0)+a*b
    E = hard['prefix_kernel'](we, [2,-1], [2,1])
    S = hard['prefix_kernel'](ws, [1], [1,1,QQ(1)/2])
    def R(t):
        return F(-t/2).exp()-E(t)
    price = (S(s)+S(s+d))/2
    C = (2*R(QQ(0))+4*sum(QQ((-1)**(j-1))/(4*j*j-1)*R(j*d)
                            for j in range(1,N+1)))/F.pi()
    D = max(we, default=0)
    L = sum(abs(b) for b in points.values())
    y = (N+1)*d
    assert y>D and 2+y+D>6
    tail = (4/F.pi())/(4*(N+1)**2-1)*(F(-y/2).exp()/(1-F(-d/2).exp())
            +L**2*(2+y+D)*F(-(y-D)/2).exp()/(1-F(-d/3).exp()))
    assert tail < eps
    return C-price, price

old = [QQ(n)/10**7 for n in (5710000,0,4195798,94000,0,202)]
jold, center = signed(old)
assert center > 0 and jold+eps < 0
print('Half-gap mixture: normalized balanced slack (additional tail < 1e-12):', jold)

# A tangent to a concave quadratic is an upper bound even if its
# base point does not meet the mean or cap constraints.
v = [QQ(n)/10**8 for n in (52129715,0,46988009,880383,0,1893)]
jv, _ = signed(v)
lam, nu = QQ(15733448)/10**5, QQ(45821570)/10**5
for i, name in enumerate(('single','regional','hard','radial','step','zero')):
    e = [QQ(i==j) for j in range(len(v))]
    je, _ = signed(e)
    mid, _ = signed([(a+b)/2 for a,b in zip(e,v)])
    tangent = 4*mid-2*jv-je
    upper = tangent+lam*(cap-g[i])+nu*u[i]+7*eps
    print(name, 'corrected tangent upper:', upper, flush=True)
    assert upper < -QQ(12)/10**6
