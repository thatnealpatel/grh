"""Replay the all-translate first caps and enclose the named scalar extremum."""
from collections import defaultdict
from math import comb, factorial
from pathlib import Path

from sage.all import ComplexBallField, QQ, RealBallField

if not __debug__:
    raise SystemExit('Run with assertions enabled.')
F, K = RealBallField(128), ComplexBallField(128)
C = (F(39)/20).cosh()/3
CT = C/(2*(F.pi()/12).cos())


def read_law(path):
    den, scale = 128, 10**8
    z, A, B, U = [], [], [], []
    for line in path.read_text().splitlines():
        if not (line := line.partition('#')[0].strip()):
            continue
        knot, *row = map(int, line.split())
        assert row and len(row) % 2 == 0
        x, p = row[::2], row[1::2]
        assert all(abs(a) <= scale for a in x)
        assert all(a > 0 for a in p) and sum(p) == scale
        atoms = [(QQ(a)/scale, QQ(b)/scale) for a, b in zip(x, p)]
        z.append(QQ(knot)/den)
        A.append(sum(b*a for a, b in atoms))
        B.append(sum(b*(4*a**3-3*a) for a, b in atoms))
        U.append(sum(b*F((1+a)/2).sqrt() for a, b in atoms))
    assert len(z) == 408 and z[0] == -10 and 0 in z and z[-1] == 16
    assert all(x < y for x, y in zip(z, z[1:]))
    tails = [(1+t)*F(-t).exp() if t >= 0 else F(1) for t in z]+[F(0)]
    surplus = sum((a-b)*u for a, b, u in zip(tails, tails[1:], U))-F(8)/9
    assert surplus > F('4.03e-7')
    print('mean surplus:', surplus, flush=True)
    return z, A, B


def jumps(z, Y):
    return [(k, F(v-u)*F(-k/2).exp()) for k, v, u in zip(z, Y, [0]+Y) if v != u]


def check_representer(z, Y, jump):
    for x in (QQ(0), QQ(3)/5, QQ(11)/7):
        w = K(QQ(1)/2, x)
        by_slab = sum(F(a)*((-w*s).exp()-(-w*t).exp())
                      for a, s, t in zip(Y, z, z[1:])) + F(Y[-1])*(-w*z[-1]).exp()
        by_jump = sum(K(b)*K(0, x*s).exp() for s, b in jump)
        assert by_slab.conjugate().overlaps(by_jump)


def first_cap(jump, cap):
    # Center numerator about -2, changing only its phase.
    t = [z+2 for z, _ in jump]
    D = [sum(abs(b)*abs(q)**k for q, (_, b) in zip(t, jump)) for k in range(5)]
    m4 = sum(comb(4, j)*D[j]*D[4-j] for j in range(5))
    X = QQ(64)
    assert D[0]/X < cap
    coeff = [[K(b)*K(0, q)**k for q, (_, b) in zip(t, jump)] for k in range(4)]
    stack, count = [(QQ(0), X, 0)], 0
    while stack:
        a, b, depth = stack.pop()
        mid, rad = (a+b)/2, F((b-a)/2)
        e = [K(0, q*mid).exp() for q in t]
        N = [sum(c*d for c, d in zip(row, e)) for row in coeff]
        v = [sum(comb(k,j)*(N[j]*N[k-j].conjugate()).real() for j in range(k+1))
             - cap**2*d for k,d in enumerate([QQ(1)/4+mid**2, 2*mid, 2, 0])]
        if v[0]+sum(abs(v[k])*rad**k/factorial(k) for k in range(1,4))+m4*rad**4/24 < 0:
            count += 1
        else:
            assert depth < 24, (a, b, v[0])
            stack.extend(((a,mid,depth+1),(mid,b,depth+1)))
    print('first cap:', cap, '; boxes:', count, '; tail bound:', D[0]/X, flush=True)


def moments(jump):
    plus, diff = defaultdict(F), defaultdict(F)
    beta = [(z,b/C) for z,b in jump]
    for i,(z,b) in enumerate(beta):
        for j,(k,d) in enumerate(beta[:i+1]):
            plus[z+k] += (1 if i == j else 2)*b*d
            diff[z-k] += b*d
    def S(s):
        return sum(a*(1+max(q+s,QQ(0))+max(q+s,QQ(0))**2/2)*F(-abs(q+s)/2).exp()
                   for q,a in plus.items())
    def E(t):
        return F(-abs(t)/2).exp()
    def J(t):
        return (2+abs(t))*E(t)
    def R(t):
        return E(t)-sum(a*(J(q+t)+(J(t-q) if q else 0)) for q,a in diff.items())
    return S, R


def named_price(S, R):
    # At u=13x/25, |H|=sqrt(q(u)), q=a+2b cos u+2d cos(2u).
    h = [QQ(k)/12 for k in [3,5,4]]
    a, b, d = sum(k*k for k in h), h[1]*(h[0]+h[2]), h[0]*h[2]
    minq = a-2*d-b*b/(4*d)
    rho = F(1)/20
    analytic_change = 2*b*(rho.cosh()-1)+2*d*((2*rho).cosh()-1)
    assert minq > analytic_change and 1+analytic_change < 4
    n = 1024
    r = (-rho).exp()
    err = 8*r**(n//2)/(1-r)
    assert err < F('1.3e-9')
    pi = F.pi()
    roots = [K(0, 2*pi*j/n).exp() for j in range(n//2)]
    def fft(vals):
        m = len(vals)
        if m == 1:
            return vals
        a, b = fft(vals[::2]), fft(vals[1::2])
        c = [roots[j*(n//m)]*v for j,v in enumerate(b)]
        return [x+y for x,y in zip(a,c)]+[x-y for x,y in zip(a,c)]
    q = [(a+2*b*(2*pi*j/n).cos()+2*d*(4*pi*j/n).cos()).sqrt() for j in range(n)]
    p = fft(list(map(K, q)))
    cap = p[0].real()/n*R(QQ(0))+sum(2*p[j].real()/n*R(QQ(13*j)/25) for j in range(1,n//2))
    center = sum(w*S(QQ(k)/25) for k,w in zip((-7,6,19),h))
    print('center:', center, '; capacity enclosure:', (cap-err, cap+err), flush=True)
    return center-cap, err


def main():
    z, A, B = read_law(Path(__file__).with_name('triple-named-refit.txt'))
    za, zb = jumps(z, A), jumps(z, B)
    check_representer(z, A, za)
    check_representer(z, B, zb)
    pad = F('1e-7')
    first_cap(za, CT-pad)
    first_cap(zb, C-pad)
    response, err = named_price(*moments(zb))
    assert F('0.00061834386') < response-err < response+err < F('0.00061834637')
    print('minimum named response:', (response-err, response+err), flush=True)


if __name__ == '__main__':
    main()
