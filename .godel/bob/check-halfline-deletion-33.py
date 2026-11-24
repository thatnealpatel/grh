"""SageMath 10.9: extend a delete-33 witness along the positive lattice tail."""
import argparse
from pathlib import Path
from sage.all import ComplexBallField, QQ, RealBallField

if not __debug__:
    raise SystemExit('Run with assertions enabled.')
F, K = RealBallField(1280), ComplexBallField(1280)
pi = F.pi()
h, r = F(1)/25, (-F(1)/50).exp()
cl, cr = h.exp()-1-h, (-h).exp()-1+h
C = F(QQ(39)/20).cosh()/3
Ct = C/(2*(pi/12).cos())
N, end, unit = 512, 800, 10**9
ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--minus320', action='store_true', help='check the refit on [-320,256] instead')
args = ap.parse_args()
left = -320 if args.minus320 else -256
file = Path(__file__).with_name('deletion-laws')/('delete-33-minus320.txt' if args.minus320 else 'delete-33-bilateral.txt')
lines = [x for x in file.read_text().splitlines() if x and not x.startswith('#')]
split = lines.index('trace')
prime, trace = ([list(map(int, x.split())) for x in rows] for rows in
                (lines[1:split], lines[split+1:]))
assert lines[0] == 'prime' and len(trace) == N

def pairs(row):
    assert row and len(row)%2 == 0 and min(row[1::2]) > 0
    return list(zip(row[::2], row[1::2])), sum(row[1::2])

# When computing the zero-extension increment p257-r*p256 all original
# slabs lie above the two ramp knots, so only their exponential masses enter.
z = [QQ(row[0])/400 for row in prime]
assert z[0] == -QQ(256)/25 and sorted(set(z)) == z
edges = [F(-x).exp() for x in z]+[F(0)]
inc = [F(0), F(0)]
for i, row in enumerate(prime):
    atoms, total = pairs(row[1:])
    for u, w in atoms:
        assert 0 <= u <= unit
        x = 2*(QQ(u)/unit)**2-1
        for j, y in enumerate([x, 4*x**3-3*x]):
            inc[j] += (edges[i]-edges[i+1])*(w*y/total)
inc = [v*r**257*h for v in inc]

ks = [left-1,left,left+1]+list(range(256,end+1))
mom = [{k:F(0) for k in ks} for _ in inc]
phi = [pi*(QQ(i)/N)**2 for i in range(N+1)]
e = [K(0,x).exp() for x in phi]
d = [1+r*r-2*r*x.real() for x in e]
cdf = ([F(0)]+[2/pi*((x/2).tan()/(F(1)/100).tanh()).arctan()
               for x in phi[1:-1]]+[F(1)])
for i,row in enumerate(trace):
    a,b = row[:2]; assert a*a+b*b <= unit**2
    atoms,total = pairs(row[2:])
    v = [K(a,b)/unit,sum(w*K(0,2*pi*QQ(u)/unit).exp() for u,w in atoms)/total]
    m = cdf[i+1]-cdf[i]; assert m > 0
    J = [K(m), K(((1+r*r)*m-(1-r*r)*(phi[i+1]-phi[i])/pi)/(2*r),
                 (1-r*r)*(d[i+1]/d[i]).log()/(2*r*pi))]
    lo,hi = K(1),K(1)
    for k in range(1,end):
        lo *= e[i]; hi *= e[i+1]
        flat = (hi-lo)/K(0,k)
        J.append(((1+r*r)*J[-1]-(1-r*r)*flat/pi)/r-J[-2])
    for k in ks:
        x = J[k] if k >= 0 else J[-k].conjugate()
        for t,M in zip(v,mom):
            M[k] += (x*t).real()

solutions = []
for M,D,v,neg_floor in zip(mom,[Ct,C],inc,([41,39] if args.minus320 else [40,190])):
    # Gram endpoint correction is geometric on the positive tail.
    s = [(D*(M[257]-r*M[256])-v)*r**255/cl]
    for l in range(257,end):
        rhs = D*r**l*(M[l+1]/r-2*M[l]+r*M[l-1])
        s.append((rhs-cr*s[-1])/cl)
    solutions.append(s)
    assert abs(s[-1]) < QQ(1)/8 and 0 < cr < cl
    assert D*r**end*(1/r+2+r) < (cl-cr)/8
    # On the opposite side the Gram correction need not drop out. Price
    # its full possible error by the verified pre-dilution uniform bound.
    neg = D*r**left*(abs(M[left+1]/r-2*M[left]+r*M[left-1])
                         - F('4e-8' if args.minus320 else '2.1e-8')*(1/r+2+r))/(cl+cr)
    assert (1-QQ(1)/10**6)*neg > neg_floor
    if not args.minus320:
        displacement = (neg_floor-1)*(cl+cr)/(D*r**left*(1-r*r)/r)
        assert displacement > (QQ(15)/1000 if neg_floor == 40 else QQ(37)/1000)
    print('lower estimate for absolute normalized negative curvature:',neg)
gauge = max(((abs(2*a+b)+2*abs(a-b))/3).upper() for a,b in zip(*solutions))
assert gauge < (QQ(81)/10000 if args.minus320 else QQ(122)/1000)
print('new slab gauge through index 800:',gauge)
