"""Check continuous first caps and an unfolded three-site disk price."""
from functools import cache
from math import comb, factorial
from pathlib import Path
from runpy import run_path

from sage.all import ComplexBallField, PolynomialRing, QQ, RealBallField

if not __debug__:
    raise SystemExit('Run with assertions enabled.')
base = Path(__file__).resolve().parent
F, K = RealBallField(128), ComplexBallField(128)
P = PolynomialRing(F, 'y')
fft = run_path(str(base/'check-four-shift-10-2.py'))['fft']
lattice = run_path(str(base/'check-full-deletion-33.py'))
read, step = lattice['read'], lattice['step']
C = (F(39)/20).cosh()/3
Ct = C/(2*(F.pi()/12).cos())
S = [-7, 6, 19]  # units 1/25


def jumps(z, Y, c):
    return [F(y-p)*(-F(t)/2).exp()/c for t,y,p in zip(z,Y,[0]+Y)]


def cap(z, b, bound):
    # |sum b exp(ixt)|^2 - bound^2(1/4+x^2). Enclose its Taylor
    # polynomial locally, with a global fourth derivative bound.
    D = [sum(abs(a)*abs(t)**k for t,a in zip(z,b)) for k in range(5)]
    X = int((D[0]/bound).upper().ceil())+1
    assert D[0]/X < bound
    M = sum(comb(4,j)*D[j]*D[4-j] for j in range(5))/24
    bs = [[K(a)*K(0,t)**j for a,t in zip(b,z)] for j in range(4)]
    stack = [(QQ(X)/2, QQ(X)/2)]
    boxes = 0
    while stack:
        x, r = stack.pop()
        v = [K(0,x*t).exp() for t in z]
        n = [sum(a*p for a,p in zip(row,v)) for row in bs]
        q = [sum(comb(k,j)*(n[j]*n[k-j].conjugate()).real() for j in range(k+1))
             - bound**2*d for k,d in enumerate([x*x+QQ(1)/4,2*x,2,0])]
        if q[0]+sum(abs(q[k])*r**k/factorial(k) for k in range(1,4))+M*r**4 < 0:
            boxes += 1
        else:
            assert r > QQ(1)/2**28, (x,q[0])
            stack.extend([(x-r/2,r/2),(x+r/2,r/2)])
    print('First norm below', bound, '; boxes:',boxes,'; tail starts at',X,flush=True)


def kernels(z, b):
    # All indices below are exact integers in units 1/400.
    k = [int(400*t) for t in z]
    assert all(j==400*t for j,t in zip(k,z))
    J = k[-1]-k[0]
    bp = P(dict(zip([j-k[0] for j in k],b)))
    bm = P(dict(zip([k[-1]-j for j in k],b)))
    su = list(enumerate((bp*bp).list(),2*k[0]))
    di = list(enumerate((bp*bm).list(),-J))

    @cache
    def E(i):
        return (F(-abs(i))/800).exp()

    def center(s):
        def term(i,a):
            u = F(max(i+s,0))/400
            return a*(1+u+u*u/2)*E(i+s)
        return sum(term(i,a) for i,a in su)

    # For s >= J, every |s+i|=s+i and the sum is affine times e^-s/800.
    tail0 = sum(a*(2+F(i)/400)*(F(-i)/800).exp() for i,a in di)
    tail1 = sum(a*(F(-i)/800).exp() for i,a in di)

    @cache
    def rad(j):
        s = abs(j)*208  # the frequency step 13/25
        if s >= J:
            return E(s)*(1-tail0-F(s)/400*tail1)
        return E(s)-sum(a*(2+F(abs(s+i))/400)*E(s+i) for i,a in di)
    return [center(16*s) for s in S], rad


def folded_kernels(z, Y, d):
    # f(k) are the first replies. The Laurent coefficients a_i have one
    # geometric tail. Integrating the OTHER first field via f allows us
    # to sum the folded quadratic kernels without a double truncation.
    lo, hi = int(-d*z[-1]), int(-d*z[0])
    assert lo==-d*z[-1] and hi==-d*z[0] and d%25==0
    r = (F(-1)/(2*d)).exp()
    b = [F(y-p)/C for y,p in zip(Y,[0]+Y)]
    tab = [sum(step(t,k,d)*a for t,a in zip(z,b)) for k in range(lo,hi+1)]
    slope = sum(F(-t).exp()*a for t,a in zip(z,b))/d
    offset = tab[-1]/r**hi-slope*hi
    last = F(Y[-1])/C

    @cache
    def f(k):
        if k<lo:
            return last*r**(-k)
        if k>hi:
            return r**k*(offset+slope*k)
        return tab[k-lo]

    a = [((1+r*r)*f(i)-r*(f(i-1)+f(i+1)))/(1-r*r) for i in range(lo,hi+1)]
    def center(s):
        t = max(hi+1,s-lo)
        return (sum(v*f(s-i) for i,v in enumerate(a,lo))
                +sum(slope*r**i*f(s-i) for i in range(hi+1,t))
                +slope*last*r**(2*t-s)/(1-r*r))
    def rad(j):
        s, t = abs(j)*(13*d//25), hi+1
        tail = slope*r**(2*t+s)/(1-r*r)*(offset+slope*(t+s+r*r/(1-r*r)))
        return r**s-sum(v*f(s+i) for i,v in enumerate(a,lo))-tail
    return [center(s*(d//25)) for s in S], rad


def half_step_price():
    z,A,B,U,_ = read(base/'deletion-laws/delete-33-half-step.txt')
    b = jumps(z,B,C)
    cap(z,b,F('.9985'))
    lam = [F(74)/100,F(90)/100,F(1)]
    # H=e^{i(6/25)x} L(theta), L=lambda_- e^{-i theta}+lambda_0+lambda_+ e^{i theta}.
    # Manufacture a short *verified* uniform approximation p to |L|.
    N, degree = 1024, 144
    vals = [abs(sum(a*K(0,j*i*2*F.pi()/N).exp() for j,a in zip([-1,0,1],lam))) for i in range(N)]
    coeff = [v.real()/N for v in fft(vals)[:degree+1]]
    p = P(coeff[:0:-1]+coeff)  # y^degree p(theta)
    L = P(lam)
    err2 = sum(abs(v) for v in (p*p-P.gen()**(2*degree-2)*L*P(lam[::-1])).list())
    # If |cos(theta)|>.9 the real part of L has modulus >.6;
    # otherwise |Im L| >= .26 sqrt(.19) > .1.
    assert err2 < F('.01') and p(F(1)) > 0
    # p cannot cross zero, and ||p|-|L|| <= sqrt(err2).
    for name, (centers,rad), floor in [
            ('unfolded', kernels(z,b), '.000022'),
            ('k/100', folded_kernels(z,B,100), '.00000294')]:
        radius_upper = (coeff[0]*rad(0)+2*sum(v*rad(j) for j,v in enumerate(coeff[1:],1))
                        +err2.sqrt()*rad(0))
        gap = sum(a*c for a,c in zip(lam,centers))-radius_upper
        print(name, 'center minus upper radius:',gap,flush=True)
        assert gap > F(floor)


def complete(z,b,lam):
    centers,R = kernels(z,b)
    N, D = 2048, 192
    # g = exp(-6ix/25) sum v_k exp(-ik theta). Nominate v by a
    # finite transform. There is no analytic truncation assumption.
    roots = [K(0,j*2*F.pi()/N).exp() for j in range(N)]
    H = [lam[0]*w.conjugate()+lam[1]+lam[2]*w for w in roots]
    V = fft([h.conjugate()/(1+abs(h)**2).sqrt() for h in H])
    v = {k:V[k%N].real()/N for k in range(-D,D+1)}
    sites = [-1,0,1]
    x,y,zr = [s-sum(a*R(j-k) for k,a in v.items()) for j,s in zip(sites,centers)]
    a,b,c = R(0),R(1),R(2)
    # Weighted Gram, not the bare Poisson Gram. Solve for sum,
    # difference, and middle coefficient of the exact correction.
    assert a>0 and a-c>0 and a*(a+c)-2*b*b>0
    total = (a*(x+zr)-2*b*y)/(a*(a+c)-2*b*b)
    diff = (x-zr)/(a-c)
    corr = [(total+diff)/2,(y-b*total)/a,(total-diff)/2]
    print('Weighted Gram correction l1:',sum(abs(h) for h in corr),flush=True)
    for k,h in zip(sites,corr):
        v[k] += h
    N = 16384
    grid = lattice['eval_grid'](v,N)
    chord = (2*F.pi()/N)**2/8*sum(k*k*abs(h) for k,h in v.items())
    slack = 1-F(max(abs(h).upper() for h in grid))-chord
    print('Repaired multiplier slack:',slack,flush=True)
    assert slack > F('.00001')


def polish_bound(z, A, B):
    # An upper affine price on u for each nonnegative slab. Check the
    # degree-six majorization on [0,1] exactly in the Bernstein basis.
    rows = (base/'deletion-laws/delete-33-unfolded-Udual.txt').read_text().splitlines()[1:]
    rows = [list(map(int, r.split())) for r in rows]
    idx = [i for i,t in enumerate(z) if t>=0]
    assert [row[0] for row in rows] == [400*z[i] for i in idx]
    den = 10**12

    def nonpositive(b, depth=0):
        if max(b)<=0:
            return True
        if depth==32 or b[0]>0 or b[-1]>0:
            return False
        left, right = [], []
        for j in range(7):
            left.append(b[0] << (6-j))
            right.append(b[-1] << (6-j))
            b = [x+y for x,y in zip(b,b[1:])]
        return nonpositive(left,depth+1) and nonpositive(right[::-1],depth+1)

    total = F(0)
    for (_,a,b,c,pad),i in zip(rows,idx):
        # den*u - (a+pad+b*X+c*T3(X)) in increasing power order.
        q = [-a-pad+b+c,den,-2*b-18*c,0,48*c,0,-32*c]
        assert nonpositive([sum(q[j]*comb(k,j)*(60//comb(6,j)) for j in range(k+1))
                            for k in range(7)])
        mass = step(z[i],0) - (step(z[i+1],0) if i+1<len(z) else 0)
        total += mass*(a+pad+b*A[i]+c*B[i])/den
    print('Seed fixed-A,B upper surplus:',total-F(8)/9,flush=True)
    assert total-F(8)/9 < F('-.0000032574')


def joint():
    seed = base/'deletion-laws/delete-33-unfolded-seed.txt'
    z,A,B,U = lattice['prime_rows'](seed.read_text())
    zz,AA,BB,UU,_ = read(base/'deletion-laws/delete-33-half-step.txt')
    assert zz==z
    polish_bound(z,A,B)
    # The half-step t cap is already proved. For the mixed law use its
    # convex combination with the folded all-real t field of the seed.
    cap(z,jumps(z,A,Ct),F('.999999'))
    for name,c,lam,eps in [
            ('mixed',QQ(39)/20,[43.64026901,53.85626217,59.12375559],None),
            ('nearby',QQ(39001)/20000,[9.94303758,13.46875651,13.74329816],QQ(3)/100000)]:
        print(name,'depth',c,flush=True)
        def mix(Y,YY):
            if eps is None:
                return [(3*y+17*yy)/20 for y,yy in zip(Y,YY)]
            return [(1-eps)*y+eps if t>=0 else y for t,y in zip(z,Y)]
        a,b,u = mix(A,AA),mix(B,BB),mix(U,UU)
        surplus = (sum((step(t,0)-step(s,0))*q for t,s,q in zip(z,z[1:],u))
                   +step(z[-1],0)*u[-1]-F(8)/9)
        print('Failure surplus:',surplus,flush=True)
        assert surplus > F('.00000024' if eps is None else '.000000065')
        # Distinguish the nearby depth or the t lattice from a full
        # real-shift match at depth 39/20, for THESE exact primes.
        test_x = QQ(91)/10 if eps is None else QQ(0)
        test_v = sum(v*K(0,t*test_x).exp() for v,t in zip(jumps(z,a,Ct),z))/K(QQ(1)/2,test_x)
        print('Unfolded t norm at depth 39/20, x =',test_x,':',abs(test_v),flush=True)
        assert abs(test_v) > F('1.00210' if eps is None else '1.0000457')
        scale = F(c).cosh()/3
        if eps is not None:
            cap(z,jumps(z,a,scale/(2*(F.pi()/12).cos())),F('.999999'))
        coeff = jumps(z,b,scale)
        cap(z,coeff,F('.99999'))
        complete(z,coeff,[F(str(h)) for h in lam])


if __name__=='__main__':
    half_step_price()
    joint()
