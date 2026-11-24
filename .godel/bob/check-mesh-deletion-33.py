"""Upper-price every atom law on the indicated delete-33 meshes."""
from functools import cache
from math import comb
from pathlib import Path
from runpy import run_path

from sage.all import ComplexBallField, PolynomialRing, QQ, RealBallField

if not __debug__:
    raise SystemExit('Run with assertions enabled.')
base = Path(__file__).resolve().parent
F, K = RealBallField(128), ComplexBallField(128)
P = PolynomialRing(F, 'y')
fft = run_path(str(base/'check-four-shift-10-2.py'))['fft']
C = (F(39)/20).cosh()/3
Ct = C/(2*(F.pi()/12).cos())
seed = [int(s.split()[0]) for s in (base/'deletion-laws/delete-33-unfolded-seed.txt').read_text().splitlines()[1:]]
lo, hi = min(seed), max(seed)
J = hi-lo
n = J+1


@cache
def e(i):
    return (F(-abs(i))/800).exp()


def first_and_probe():
    """Price first disks and form cumulative slab coefficients at 1/400 knots."""
    fields = [[F(0)]*n for _ in range(2)]
    cost = F(0)
    q = [F(0)]*n
    for line in (base/'deletion-laws/delete-33-mesh.dual').read_text().splitlines()[1:]:
        tag, *v = line.split()
        if tag == 'F':
            j, i, a, b = map(int,v)
            x, d = F(i)/10**9, K(a,-b)/10**13
            cost += abs(d)
            p = K(-F(1)/2,x)/400
            h = p.exp()
            coef = d/(K(F(1)/2,x)*[Ct,C][j])
            for k in range(n):
                if k%48 == 0:
                    term = coef*(p*(k+lo)).exp()
                fields[j][k] += term.real()
                term *= h
        else:
            assert tag == 'Q'
            i, a = map(int,v)
            q[i-lo] = F(a)/10**13
    return fields, cost, q


def majorant():
    """Return the checked Laurent coefficients, disk direction, and majorant integral."""
    # Positive majorant of |L|: This makes the test quadratic positive
    # semidefinite, and preserves necessity since the first disk holds.
    lam = [F(73)/100,F(98)/100,F(1)]
    N, D = 2048, 192
    roots = [K(0,i*2*F.pi()/N).exp() for i in range(N)]
    cs = [v.real()/N for v in fft([abs(lam[0]*w.conjugate()+lam[1]+w) for w in roots])[:D+1]]
    p = P(cs[:0:-1]+cs)
    err = sum(abs(v) for v in (p*p-P.gen()**(2*D-2)*P(lam)*P(lam[::-1])).list())
    # |Re L|>.5 if |cos theta|>.9, and |Im L|>.1 otherwise.
    assert err < F('1e-14') and p(F(1))>0
    cs[0] += F('1e-12')  # |p-|L|| = |p^2-|L|^2|/(p+|L|) < 1e-13
    rhs = cs[0]+2*sum(c*e(208*j) for j,c in enumerate(cs[1:],1))
    return cs, lam, rhs


def quadratic(q):
    cs, lam, rhs = majorant()

    @cache
    def kd(i):
        return (2+F(abs(i))/400)*e(i)

    def ks(i):
        u = F(max(0,i))/400
        return (1+u+u*u/2)*e(i)

    diff = [cs[0]*kd(i)+sum(c*(kd(i-208*j)+kd(i+208*j)) for j,c in enumerate(cs[1:],1)) for i in range(n)]
    su = [sum(c*ks(i+s) for c,s in zip(lam,[-112,96,304])) for i in range(2*lo,2*hi+1)]
    ds = (P(diff[:0:-1]+diff)*P(q)).list()
    ss = (P(su)*P(q[::-1])).list()
    lin = [a+b for a,b in zip(ds[J:J+n],ss[J:J+n])]
    assert len(lin)==n
    return lin, (rhs*sum(a*b for a,b in zip(q,lin))).sqrt()


# Convert the three atom basis functions from power to Bernstein coordinates.
def controls(power):
    return [sum(QQ(v)*comb(k,j)/comb(6,j) for j,v in enumerate(power[:k+1])) for k in range(7)]


basis = list(zip(controls([0,1]), controls([-1,0,2]), controls([-1,0,18,0,-48,0,32])))


def maximum(w,a,b,offset=0,incumbent=None,*,lower=False):
    """Bound offset + max_u w*u + a*X + b*T(X) (jointly with incumbent if given)."""
    assert not lower or incumbent is None
    bez = [offset+w*x+a*y+b*z for x,y,z in basis]
    best = max(bez[0].lower(),bez[-1].lower())
    stack = [bez]
    tol = F('1e-13')
    cutoff = (F(best)+tol).lower()
    if incumbent is not None:
        cutoff = max(incumbent,cutoff)
    while stack:
        row = stack.pop()
        if max(x.upper() for x in row) <= cutoff:
            continue
        left, right = [], []
        while row:
            left.append(row[0])
            right.append(row[-1])
            row = [(x+y)/2 for x,y in zip(row,row[1:])]
        best = max(best,left[-1].lower())
        cutoff = max(cutoff,(F(best)+tol).lower())
        stack.extend([left,right[::-1]])
    if lower:
        return F(best)
    upper = F(best)+tol
    return upper if incumbent is None else F(max(incumbent,upper.upper()))


if __name__=='__main__':
    (fa,fb),cost,q = first_and_probe()
    lin,price = quadratic(q)
    fb = [a+b*(F(-k)/800).exp()/C for k,a,b in zip(range(lo,hi+1),fb,lin)]
    mass = [(1+F(max(k,0))/400)*e(2*max(k,0)) for k in range(lo,hi+1)]

    @cache
    def slab(i,j):
        def coeff(seq):
            return seq[i-lo]-(seq[j-lo] if j<=hi else 0)
        return maximum(coeff(mass),coeff(fa),coeff(fb))

    for zz,threshold in [(seed,'-.00000183'),(sorted(set(seed)|set(range(lo,1))|set(range(8,hi+1))),'-.00000021')]:
        upper = cost+price+sum(slab(i,j) for i,j in zip(zz,zz[1:]+[hi+1]))-F(8)/9
        print(len(zz),'slabs, upper surplus',upper,flush=True)
        assert upper < F(threshold)
