"""Certify the witness in dilated-harmonic-ceiling.md with Sage real balls."""
from sage.all import RealBallField

R = RealBallField(128)
# Left endpoints in hundredths of z. The final slab extends to infinity.
knots = [-30, -5, 0, 12, 45, 130]
# (U in hundredths, mass in hundred-thousandths), before angular blurring.
rows = [[(50, 100000)], [(17, 32244), (18, 67756)], [(53, 100000)],
        [(74, 100000)], [(84, 53100), (85, 46900)],
        [(91, 49351), (92, 31124), (100, 19525)]]
h = R(21)/200


def sinc(x):
    return x.sin()/x


def weights(k):
    # l=k/100. Integral on each slab, not a radial quadrature.
    l = R(k)/100
    starts = [R(max(a, -k))/100 for a in knots]
    tails = [(-l/2-s).exp()*(1+l+s) for s in starts] + [0]
    return [a-b for a, b in zip(tails, tails[1:])]


def chebyshev(j, u):
    x = 2*u*u-1
    a, b = R(1), x
    for _ in range(1, j):
        a, b = b, 2*x*b-a
    return b  # T_j(2u^2-1) = T_{2j}(u)


def main():
    assert len(rows) == len(knots) and knots == sorted(set(knots))
    assert all(sum(m for _, m in row) == 100000 for row in rows)
    assert all(0 <= u <= 100 and m > 0 for row in rows for u, m in row)
    laws = [[(R(u)/100, R(m)/100000) for u, m in row] for row in rows]
    mean = sinc(h/2)*sum(w*sum(p*u for u, p in row)
                          for w, row in zip(weights(0), laws))
    assert mean > R(8)/9

    cap = R(59084)/100000
    s = R(knots[0])/100
    peak_mass = 2*((-1-s)/2).exp()
    assert peak_mass/(24*h) < cap  # all j >= 24
    assert (-R(6)/10).exp() < cap  # l <= -1.2
    assert (-3-s).exp()*(7+s) < cap  # l >= 6, decreasing
    curvature = 2*(-s/2).exp()+peak_mass/4
    assert curvature < 3
    moments = [[sinc(j*h)*sum(p*chebyshev(j, u) for u, p in row)
                for row in laws] for j in range(1, 24)]
    grid_cap = R(59080)/100000
    assert grid_cap + R(3)/(8*100**2) < cap
    for k in range(-120, 601):
        w = weights(k)
        for row in moments:
            assert abs(sum(x*y for x, y in zip(w, row))) < grid_cap
    assert cap < (R(1175)/1000).cosh()/3
    print('Mean > 8/9; all grid, curvature, and tail checks passed; cap < cosh(1.175)/3.')


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without -O.')
    main()
