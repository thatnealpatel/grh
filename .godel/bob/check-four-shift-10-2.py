"""Check the finite (10,2) lattice separator with 128-bit Sage balls."""
import argparse
from pathlib import Path
from sage.all import ComplexBallField, QQ, RealBallField

if not __debug__:
    raise SystemExit('Run with assertions enabled.')
F, K = RealBallField(128), ComplexBallField(128)
pi = F.pi()
c1 = (F(39)/20).cosh()/3
ct = c1/(2*(pi/12).cos())
eta = F(1)/50


def fft(values):
    """Unnormalized positive-sign DFT; each output is a complex ball."""
    n = len(values)
    assert n and n & (n-1) == 0
    roots = [K(0, (2*pi/n)*j).exp() for j in range(n//2)]
    def rec(x):
        m = len(x)
        if m == 1:
            return x
        a, b = rec(x[::2]), rec(x[1::2])
        t = [roots[j*(n//m)]*v for j, v in enumerate(b)]
        return [x+y for x,y in zip(a,t)]+[x-y for x,y in zip(a,t)]
    return rec(values)


def eval_grid(columns, n):
    a = [K(0)] * n
    for j, v in columns.items():
        a[j % n] += v
    return fft(a)


def finite_t(at, L):
    """The actual folded 2L-point deconvolution price, not its ideal limit."""
    assert L >= 2
    n = 2*L
    assert all(abs(k) < L and abs(k)+L-1 < n for k in at)
    alpha = pi/(L+1)
    d = [((L-j)*(j*alpha).cos()+((j+1)*alpha).sin()/alpha.sin())/(L+1)
         for j in range(L)]
    assert all(v > 0 for v in d)
    w = {0: F(1)}
    for j in range(1,L):
        w[j] = w[-j] = d[j]*(-j*eta).exp()
    mass = [v.real() for v in eval_grid(w, n)[:L+1]]
    assert all(v > 0 for v in mass)
    V = eval_grid({k:b/d[abs(k)] for k,b in at.items()}, n)
    return ct/n*sum((1 if j in (0,L) else 2)*w*abs(V[j]) for j,w in enumerate(mass))


def chop_max(vals, init_error, tol, midpoint):
    """Enclose a scalar upper bound for a maximum on the entire mesh domain.

    A cell is either bisected or proved to lie below incumbent + tol by
    the endpoint chord with a uniform second-derivative error. Already
    pruned cells remain covered since the incumbent only increases.
    """
    incumbent = max(v.lower() for v in vals)
    stack = [(j, j+1, vals[j], vals[j+1], init_error, 0) for j in range(len(vals)-1)]
    while stack:
        x,y,a,b,err,d = stack.pop()
        if F(max(a.upper(), b.upper()))+err <= F(incumbent)+tol:
            continue
        m = midpoint(x,y,d)
        incumbent = max(incumbent,m.lower())
        stack.extend(((2*x,x+y,a,m,err/4,d+1),(x+y,2*y,m,b,err/4,d+1)))
    return F(incumbent)+tol


def prime_floor(at, a3, res, end=18):
    # Knots are exact rationals; below the first knot all ramps vanish.
    knots = {-QQ(l)/25 for c in (at,a3) for l in c}|{QQ(0)}
    left = min(knots); end=max(QQ(end),max(knots))
    weights = [{l:b*(-l*eta).exp() for l,b in c.items()} for c in (at,a3)]
    base = 16
    table = {}
    def row(j,d):
        u = QQ(j)/(base*2**d)
        if u not in table:
            v=F(u); a=2*v*v-1
            table[u] = v,a,4*a**3-3*a
        return table[u]
    initial = [row(j,0) for j in range(base+1)]
    def minimum(f,g,v):
        if f==g==v==0:
            return F(0)
        def value(r):
            u,a,b=r
            return v*u-f*a-g*b
        # A'' = 4; B'' = 960u^4 - 576u^2 + 36 has |B''| <= 420.
        m = 4*abs(f)+420*abs(g)
        tol = F('1e-9')*(abs(f)+abs(g)+abs(v))
        return -chop_max([value(p) for p in initial], m/(8*base**2), tol,
                         lambda x, y, d: value(row(x+y, d+1)))
    def price(z):
        return minimum(*(sum((b*max(0,z+QQ(l)/25) for l,b in col.items()),F(0))
                         for col in weights),F(max(0,z)))
    mesh = set(knots)|{end}
    for a,b,k in [(left,min(end,QQ(-2)),res//12), (max(left,QQ(-2)),min(end,QQ(2)),res),
                  (max(left,QQ(2)),min(end,QQ(5)),res//2), (max(left,QQ(5)),min(end,QQ(9)),res//4),
                  (max(left,QQ(9)),end,res//12)]:
        mesh.update(QQ(j)/k for j in range((a*k).ceil(),(b*k).floor()+1))
    mesh = sorted(mesh)
    vals = [price(z) for z in mesh]
    # On each cell all ramps are affine, so the minimized function lies
    # above the chord of its endpoint lower bounds.
    floor = F(8)/9
    for x,y,a,b in zip(mesh,mesh[1:],vals,vals[1:]):
        width = F(y-x); e = (-width).exp(); mass = 1-e
        floor += F(-x).exp()*(mass*a+(mass/width-e)*(b-a))
    # Beyond the last knot use the endpoint floor and the least slope.
    return floor+F(-end).exp()*(vals[-1]+minimum(*(sum(col.values()) for col in weights),F(1)))


def third_cost(a3, h, N):
    # The folded measure is on all of [0, pi]; its CDF includes the
    # contribution of every period of the original real-line integral.
    e = [K(0, j*pi/N).exp() for j in range(N+1)]
    density = [eta.sinh()/(pi*(eta.cosh()-w.real())) for w in e]
    cdf = [F(0)]+[2/pi*((j*pi/(2*N)).tan()/(eta/2).tanh()).arctan() for j in range(1,N)]+[F(1)]
    mass = [b-a for a,b in zip(cdf,cdf[1:])]
    assert all(w > 0 for w in mass)
    skew = [pi/(8*N)*(a-b) for a,b in zip(density,density[1:])]
    p = eval_grid(a3,2*N)[:N+1]
    q = eval_grid(h,2*N)[:N+1]
    base=16
    table={}
    def row(j,d):
        frac = QQ(j)/(base*2**d)
        if frac not in table:
            e=K(0,2*pi*frac).exp()
            table[frac]=e,e*e
        return table[frac]
    initial = [row(j,0) for j in range(base+1)]
    def upper(p,q):
        def value(r):
            a,b=r
            return (a*p+b*q).real()
        m = abs(p)+4*abs(q)
        return chop_max([value(r) for r in initial], m*(2*pi/base)**2/8, F('1e-9'),
                        lambda x, y, d: value(row(x+y, d+1)))
    u = [upper(a,b) for a,b in zip(p,q)]
    # Apply the spatial chord bound separately at every fixed phase,
    # then maximize. This does not differentiate an optimizing phase.
    curv = sum(j*j*abs(b) for col in (a3,h) for j,b in col.items())
    return c1*(sum(w*(a+b)/2+d*abs(a-b) for w,d,a,b in zip(mass,skew,u,u[1:]))+curv*(pi/N)**2/8)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('table',type=Path,nargs='?',default=Path(__file__).with_name('four-shift-10-2.txt'))
    ap.add_argument('--L',type=int,default=8192)
    ap.add_argument('--N',type=int,default=32768)
    ap.add_argument('--res',type=int,default=1500)
    ap.add_argument('--margin',default='0.00000048')
    a=ap.parse_args()
    assert a.N >= 1 and a.res >= 12
    rows = [tuple(map(int,l.split())) for l in a.table.read_text().splitlines() if l and not l.startswith('#')]
    assert all(len(row)==4 for row in rows)
    shifts,*cols=zip(*rows)
    assert len(set(shifts))==len(shifts)
    at,a3,h=({k:F(a)/10**10 for k,a in zip(shifts,col) if a} for col in cols)
    assert len(h)==4
    print('Support:',sorted(h),'L:',a.L,'N_phi:',a.N,'radial resolution:',a.res,flush=True)
    floor=prime_floor(at,a3,a.res)
    print('Prime floor:',floor,flush=True)
    cost=finite_t(at,a.L)
    print('Finite t allowance:',cost,flush=True)
    third=third_cost(a3,h,a.N)
    print('3t allowance upper bound:',third,flush=True)
    m=floor-cost-third
    print('Finite signed margin, lower bound:',m,flush=True)
    assert m>F(a.margin)>0

if __name__=='__main__':
    main()
