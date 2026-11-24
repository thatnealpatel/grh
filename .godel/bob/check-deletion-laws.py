"""SageMath 10.9: Repair the rounded primal laws on every first index |l| <= 192."""
from functools import cache
from runpy import run_path
from pathlib import Path
from sage.all import ComplexBallField, QQ, RealBallField

if not __debug__:
    raise SystemExit('Run with assertions enabled.')
# The forward interval recurrence loses up to ~246 bits at degree 192.
F = RealBallField(384)
K = ComplexBallField(384)
pi = F.pi()
C = F(QQ(39)/20).cosh()/3
Ct = C/(2*(pi/12).cos())
unit = 10**9
indices = list(range(-192,193))
n = 512
sites = [-7,6,19,33]
base = Path(__file__).parent/'deletion-laws'

def pairs(v):
    assert len(v) and len(v)%2 == 0 and min(v[1::2]) > 0
    return list(zip(v[::2],v[1::2])), sum(v[1::2])

@cache
def angle(j):
    return K(0, 2*pi*QQ(j)/unit).exp()

# Integrals of exp(ik phi) on the folded cells. The CDF already counts
# the two halves; use conjugate moments for the negative indices.
phi = [pi*(QQ(i)/n)**2 for i in range(n+1)]
r = (-F(1)/50).exp()
edge = [K(0,x).exp() for x in phi]
D = [1+r*r-2*r*z.real() for z in edge]
cdf = [F(0)]+[2/pi*((x/2).tan()/(F(1)/100).tanh()).arctan() for x in phi[1:-1]]+[F(1)]
J = []
for i in range(n):
    mass = cdf[i+1]-cdf[i]
    assert mass > 0
    row = [K(mass), K(((1+r*r)*mass-(1-r*r)*(phi[i+1]-phi[i])/pi)/(2*r),
                      (1-r*r)*(D[i+1]/D[i]).log()/(2*r*pi))]
    for k in range(1,192):
        flat = (edge[i+1]**k-edge[i]**k)/K(0,k)
        row.append(((1+r*r)*row[-1]-(1-r*r)*flat/pi)/r-row[-2])
    J.append([row[l] if l>=0 else row[-l].conjugate() for l in indices])

# G^{-1}v from the quadratic form v0^2 + sum (vi-q*vprev)^2/(1-q^2).
def repair(v, sites):
    out = [v[0]]+[F(0) for _ in sites[1:]]
    for i in range(1,len(sites)):
        q = F(QQ(sites[i-1]-sites[i])/50).exp()
        d = (v[i]-q*v[i-1])/(1-q*q)
        out[i] += d
        out[i-1] -= q*d
    return sum(map(abs,out))

finite_t = run_path(str(Path(__file__).with_name('check-four-shift-10-2.py')))['finite_t']

def check_extension(file, jumps, delta, omit):
    # Test the first t profile on H = X*conj(Y); Cauchy-Schwarz
    # bounds its disk price by Ct*||X||_2*||Y||_2.
    rows = [list(map(int,l.split())) for l in file.read_text().splitlines()]
    assert len(rows)==257 and all(len(row)==2 for row in rows)
    x,y = zip(*rows)
    def product(x,y):
        return [sum(x[i]*y[i-k] for i in range(max(0,k),min(257,257+k))) for k in range(-256,257)]
    expo = [F(QQ(-abs(k))/50).exp() for k in range(-256,257)]
    def norm(v): return sum(a*b for a,b in zip(expo,product(v,v))).sqrt()
    jumps = [(z,d,F(-z).exp()) for z,d in jumps]
    dot = F(0)
    mask = dict(zip(range(-256,257),product(x,y)))
    for k,h in mask.items():
        s = QQ(k)/25; b = F(s/2).exp()
        # Exact integral of each step 1_[z,infty) against the ramp.
        dot += h*sum(d*(b if z+s<=0 else ez*(1+z+s)/b) for z,d,ez in jumps)
    value = abs((1-delta)*dot)
    ratio = value/(Ct*norm(x)*norm(y))
    assert ratio > F('1.00026')
    prices = [value/finite_t(mask,L) for L in [8192,2048]]
    print('extended t probe ratios: Cauchy, finite 8192, finite 2048:',ratio,*prices,flush=True)
    assert prices[0] > F('1.00019')
    assert prices[1] > 1 if omit==6 else prices[1] < 1

for omit in sites:
    S = [k for k in sites if k!=omit]
    lines = [s for s in (base/f'delete-{omit}.txt').read_text().splitlines() if s and not s.startswith('#')]
    j = lines.index('trace'); assert lines[0]=='prime' and len(lines[j+1:])==n
    prime, trace = ([list(map(int,l.split())) for l in rows] for rows in (lines[1:j],lines[j+1:]))
    z = [row[0] for row in prime]
    assert sorted(set(z))==z and {-16*l for l in indices}<=set(z)
    At, B3 = [[F(0) for _ in indices] for _ in range(2)]
    scale = [F(-QQ(l)/50).exp() for l in indices]
    mean = F(0); jumps = []; prev = F(0)
    for i,row in enumerate(prime):
        a = QQ(z[i])/400; b = QQ(z[i+1])/400 if i+1<len(z) else None
        ea = F(-a).exp(); eb = F(-b).exp() if b is not None else F(0)
        mass = ea-eb; zmass = (1+a)*ea-((1+b)*eb if b is not None else 0)
        atoms,total = pairs(row[1:]); A=B=U=QQ(0)
        for h,p in atoms:
            assert 0<=h<=unit
            u=QQ(h)/unit; x=2*u*u-1
            U+=p*u; A+=p*x; B+=p*(4*x**3-3*x)
        if a>=0: mean += zmass*(U/total)
        aa,bb = F(A/total),F(B/total)
        jumps.append((a,aa-prev)); prev=aa
        for j,l in enumerate(indices):
            if z[i]+16*l>=0:
                ramp = scale[j]*(zmass+mass*(QQ(l)/25))
                At[j] += ramp*aa; B3[j] += ramp*bb
    R2 = [F(0) for _ in S]
    for row,cell in zip(trace,J):
        x,y = row[:2]; assert x*x+y*y<=unit**2
        t = K(x,y)/unit
        atoms,total = pairs(row[2:]); m1=m2=K(0)
        for h,p in atoms:
            w=angle(h); m1+=p*w; m2+=p*w*w
        m1/=total; m2/=total
        for j,v in enumerate(cell):
            At[j] -= Ct*(v*t).real(); B3[j] -= C*(v*m1).real()
        for j,k in enumerate(S): R2[j] -= (cell[k+192]*m2).real()
    et,e3,e2 = repair(At,indices)/Ct, repair(B3,indices)/C, repair(R2,S)
    delta = QQ(1)/10**6
    assert (1-delta)*et < delta and 2*(1-delta)*(e3+e2) < delta
    surplus = (1-delta)*mean+delta*(F(1)/2).sqrt()-F(8)/9
    print('omitted index, repaired surplus, t/3t/second repair costs:',omit,surplus,et,e3,e2,flush=True)
    assert surplus > F('0.000016')
    # Extension uses X=0 before the first row, final row forever.
    check_extension(base/f'delete-{omit}.probe',jumps,delta,omit)
