"""Certify the delete-33 obstruction for both entire first lattices."""
import argparse
from pathlib import Path
from runpy import run_path
from sage.all import ComplexBallField, QQ, RealBallField

if not __debug__:
    raise SystemExit('Run with assertions enabled.')
F = RealBallField(128)
base = Path(__file__).resolve().parent
eval_grid = run_path(str(base/'check-four-shift-10-2.py'))['eval_grid']
C = F(QQ(39)/20).cosh()/3
Ct = C/(2*(F.pi()/12).cos())
ORIGINAL = base/'deletion-laws/delete-33-full.txt'


def read(table):
    prime, second = table.read_text().split('# Second:')
    rows = [list(map(int, line.split())) for line in prime.splitlines() if not line.startswith('#')]
    z, A, B, U = [], [], [], []
    for start, *pairs in rows:
        assert pairs and len(pairs) % 2 == 0
        u = [QQ(i)/10**9 for i in pairs[::2]]
        p = pairs[1::2]
        assert all(0 <= v <= 1 for v in u) and min(p) >= 0 and sum(p) > 0
        x = [2*v*v-1 for v in u]
        z.append(QQ(start)/400)
        for out, values in [(A,x), (B,[4*t**3-3*t for t in x]), (U,u)]:
            out.append(sum(w*v for w,v in zip(p,values))/sum(p))
    assert all(a < b for a,b in zip(z,z[1:])) and 0 in z
    j0, den, *vals = map(int, ' '.join(second.splitlines()[1:]).split())
    assert den > 0
    return z, A, B, U, {j:F(v)/den for j,v in enumerate(vals,j0)}


def step(z,k,d=25):
    """Integral of the kth prime kernel on [z,infinity)."""
    x = max(z+QQ(k)/d, 0)
    return (1+x)*F(QQ(k)/(2*d)-x).exp()


def stencil(z,Y,D,d):
    r = F(-QQ(1)/(2*d)).exp()
    l, K = -d*z[-1], -d*z[0]
    assert l.denominator() == K.denominator() == 1 and l < 0 < K
    l, K = int(l), int(K)
    jumps = [F(v-u)/D for v,u in zip(Y,[0]+Y)]
    p = {k:sum(step(t,k,d)*b for t,b in zip(z,jumps)) for k in range(l-1,K+2)}
    a = {k:((1+r*r)*p[k]-r*(p[k-1]+p[k+1]))/(1-r*r) for k in range(l,K+1)}
    slope = sum(F(-t).exp()*b for t,b in zip(z,jumps))/d
    return r, a, K, slope


def first(z,Y,D,d):
    r, a, K, slope = stencil(z,Y,D,d)
    # For k>K the infinite stencil gives slope*r^k exactly. Truncate
    # for the GRID calculation only, bounding the omitted sup norm.
    J = 1536*(d//25)
    assert J > K
    a.update({k:slope*r**k for k in range(K+1,J+1)})
    T = J+1
    e = abs(slope)*r**T/(1-r)
    # Geometric tail moments, degrees 0 through 2.
    q = r/(1-r)
    norms = [sum(abs(v)*abs(k)**i for k,v in a.items())+tail for i,tail in
             enumerate([e,e*(T+q),e*(T*T+2*T*q+q+2*q*q)])]
    return a, e, norms


def repair(n,d):
    # Equal spacing makes the 3-by-3 Gram inverse tridiagonal.
    r = F(-QQ(1)/(2*d)).exp()
    S = [k*(d//25) for k in (-7,6,19)]
    p = r**(S[1]-S[0])
    x,y,z = [sum(b*r**abs(k-j) for j,b in n.items()) for k in S]
    correction = [(x-p*y)/(1-p*p), ((1+p*p)*y-p*(x+z))/(1-p*p), (z-p*y)/(1-p*p)]
    for k,b in zip(S,correction):
        n[k] = n.get(k,0)-b
    return sum(abs(b) for b in correction)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--table', type=Path, help='default: accepted table for this denominator')
    parser.add_argument('--denominator', type=int, choices=(25,50), default=25)
    args = parser.parse_args()
    d = args.denominator
    reference = ORIGINAL if d == 25 else base/'deletion-laws/delete-33-half-step.txt'
    table = args.table or reference
    original = d == 25 and table.resolve() == ORIGINAL.resolve()
    z,A,B,U,n = read(table)
    surplus = sum((step(t,0)-step(s,0))*u for t,s,u in zip(z,z[1:],U))+step(z[-1],0)*U[-1]-F(8)/9
    # The omitted left ray has X=0 and lies entirely below zero.
    print('Failure surplus:',surplus,flush=True)
    half = d == 50 and table.resolve() == reference.resolve()
    threshold = '0.00001683' if original else '0.0000008709' if half else '0'
    assert surplus > F(threshold)
    a,ea,T = first(z,A,Ct,d)
    b,eb,M = first(z,B,C,d)
    print('Second Gram repair l1:',repair(n,d),flush=True)
    N = 131072*(d//25)**2
    chord = (2*F.pi()/N)**2/8
    # eval_grid uses exp(+ij phi); simultaneous reflection of all fields
    # merely reverses the order in which we visit the circle.
    def sample(c):
        return eval_grid(c,N)[:N//2+1]
    tmax = max(abs(v).upper() for v in sample(a))
    tgap = 1-F(tmax)-ea-chord*T[2]
    print('Uniform first t slack lower bound:',tgap,flush=True)
    assert tgap > (F('0.00006') if original else 0)
    # For each fixed unit h bound |m|^2 + Re(h*(n-m^2))
    # by endpoint interpolation plus a uniform second derivative bound.
    n2 = sum(k*k*abs(v) for k,v in n.items())
    loss = chord*(n2+4*M[1]**2+4*M[0]*M[2])
    # m is truncated at the nodes. Each of |m|^2 and m^2 changes by
    # at most eb*(2*M[0]+eb).
    mvals = sample(b)
    vmax = max((abs(m)**2+abs(v-m*m)).upper() for m,v in zip(mvals,sample(n)))
    gap = 1-F(vmax)-loss-2*eb*(2*M[0]+eb)
    print('Uniform second disk slack lower bound:',gap,flush=True)
    assert gap > (F('0.00003') if original else 0)

    # Test the same prime law, not a refit, on the next finer lattice.
    if half:
        E = ComplexBallField(128)
        # Canonical quarter-step t field at one frequency, not a refit.
        rho, av, J, slope = stencil(z,A,Ct,100)
        w = E(0,-2*F.pi()*1898/131072).exp()
        v = sum(b*w**j for j,b in av.items())+slope*(rho*w)**(J+1)/(1-rho*w)
        print('Quarter-step first t norm:', abs(v), flush=True)
        assert abs(v) > F('1.00181')
        # Unfolded first field for the same primes, using weighted jumps.
        x = 200*F.pi()*1901/131072
        jumps = [F(a-b) for a,b in zip(A,[0]+A)]
        g = sum(b*E(-F(t)/2,x*F(t)).exp() for t,b in zip(z,jumps))/(Ct*E(F(1)/2,x))
        print('Continuous first t norm:', abs(g), flush=True)
        assert abs(g) > F('1.00251')
    if not original:
        return
    E = ComplexBallField(128)
    for Y,D,i,threshold in [(A,Ct,2734,'1.012'), (B,C,923,'1.0015')]:
        rho, a, J, slope = stencil(z,Y,D,50)
        w = E(0,-2*F.pi()*i/65536).exp()
        v = sum(b*w**j for j,b in a.items())+slope*(rho*w)**(J+1)/(1-rho*w)
        print('Half-step first norm at node',i,':',abs(v),flush=True)
        assert abs(v) > F(threshold)


if __name__ == '__main__':
    main()
