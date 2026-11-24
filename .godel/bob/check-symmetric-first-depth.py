"""SageMath: certify the two signed first-mask depth test (no optimizer)."""
from pathlib import Path
from sage.all import QQ, RealBallField, ComplexBallField

if not __debug__:
    raise SystemExit('Run without -O.')
F, K = RealBallField(128), ComplexBallField(128)


def first_masks(path, denominator):
    rows = [tuple(map(int, line.split())) for line in path.read_text().splitlines()
            if line.strip() and not line.lstrip().startswith('#')]
    assert all(len(row) == 3 for row in rows)
    assert len({row[0] for row in rows}) == len(rows)
    return [{row[0]: QQ(row[j])/denominator for row in rows if row[j]} for j in (1, 2)]


def prime_floor(cols, h, subdivisions=250, M=1536):
    weights = [{l: F(b)*F(-l*h/2).exp() for l, b in col.items()} for col in cols]
    u = [F(j)/M for j in range(M+1)]
    A = [2*x*x-1 for x in u]
    B = [4*a**3-3*a for a in A]

    def lower(f, g, v):
        sampled = F(min((f*a+g*b-v*x).lower() for a, b, x in zip(A, B, u)))
        return sampled - (4*abs(f)+420*abs(g))/(8*M**2)

    knots = {-l*h for col in cols for l in col} | {QQ(0)}
    left, end = min(knots), max(QQ(9), max(knots))
    mesh = sorted(knots | {QQ(i)/subdivisions for i in
                          range((left*subdivisions).ceil(), (end*subdivisions).floor()+1)} | {end})
    vals = [lower(*(sum(b*max(0, z+l*h) for l, b in col.items()) for col in weights),
                  F(max(0, z))) for z in mesh]
    price = F(8)/9
    for x, y, a, b in zip(mesh, mesh[1:], vals, vals[1:]):
        width = F(y-x)
        e = (-width).exp()
        mass = 1-e
        wr = mass/width-e
        price += F(-x).exp()*((mass-wr)*a+wr*b)
    return price + F(-end).exp()*(vals[-1]+lower(*(sum(col.values()) for col in weights), F(1)))


def norm_upper(cols, h, N=32768):
    # Fold the Cauchy probability to the half-circle in theta=h*x.
    eta = F(h/2)
    pi = F.pi()
    step = pi/N
    roots = [K(0, j*step).exp() for j in range(2*N)]
    density = [eta.sinh()/(pi*(eta.cosh()-roots[j].real())) for j in range(N+1)]
    cdf = [F(0)] + [2/pi*((j*step/2).tan()/(eta/2).tanh()).arctan()
                     for j in range(1, N)] + [F(1)]
    masses = [b-a for a, b in zip(cdf, cdf[1:])]
    assert all(w > 0 for w in masses)
    skew = [step*(a-b)/8 for a, b in zip(density, density[1:])]
    out = []
    for col in cols:
        terms = [(l, F(b)) for l, b in col.items()]
        values = [abs(sum(b*roots[(l*j) % (2*N)] for l, b in terms)) for j in range(N+1)]
        curvature = F(sum(l*l*abs(b) for l, b in col.items()))
        out.append(sum(w*(a+b)/2+d*abs(a-b)
                       for a, b, w, d in zip(values, values[1:], masses, skew))
                   + curvature*step**2/8)
    return out


def verify(cols, h, c, min_floor, max_t, max_3t, margin):
    floor = prime_floor(cols, h)
    nt, n3 = norm_upper(cols, h)
    cap = F(c).cosh()/3
    excess = floor-cap*(nt+n3)
    print('lattice spacing and depth:', h, c)
    print('common prime floor lower bound:', floor)
    print('full norm upper bounds (t, 3t):', nt, n3)
    print('priced upper bound and signed margin lower bound:', cap*(nt+n3), excess)
    assert floor > F(min_floor) and nt < F(max_t) and n3 < F(max_3t)
    assert excess > F(margin) > 0
    return floor, nt, n3


def verify_phase_bands(cols, h):
    # Bound the signed multiplier along the whole real half-strip, then
    # move by ix, |x| <= .01, with the same absolute derivative bound.
    for col, sign, min_real, max_deriv in zip(
            cols, (1, -1), ('.25', '.0028'), ('.081', '.0048')):
        deriv = sum(F(abs(l*h*b))*F(max(0, l*h/2)).exp() for l, b in col.items())
        assert deriv < F(max_deriv)
        assert sign*sum(col.values())-deriv/2 > F(min_real)
        move = deriv/100
        assert move/(F(min_real)-move) < F('.018')
    # Remaining phase errors: w^-2 and the signed smoothing factor.
    assert F('.25')*F('.0025').sinh() < F('.001')
    assert F('1.5')+F('.018')+F('.04')+F('.001') < F.pi()/2


if __name__ in ('__main__', 'sage.all'):
    base = Path('.godel/bob')
    verify(first_masks(base/'paired-10-2.txt', 10**7), QQ(1)/25, '1.23627',
           '.16405890', '.25979062', '.00388180', '.0000013')
    h = QQ(1)/100
    cols = first_masks(base/'symmetric-first-depth.txt', 10**10)
    floor, nt, n3 = verify(cols, h, '1.23684', '.16546278', '.26142997',
                           '.004371324', '.00000099')
    verify_phase_bands(cols, h)
    asymmetric = floor-(nt*F('1.226').cosh()+n3*F('1.72').cosh())/3
    assert asymmetric > F('.0000033')
    print('Phase-band strip signs verified; asymmetric margin lower bound:', asymmetric)
