"""Small exact tests for row-determinant-mask.md (ordinary Python, no -O)."""
from itertools import permutations
from math import gcd, lcm


def part(n, mask):
    result = 1
    while (g := gcd(n, mask)) > 1:
        result *= g
        n //= g
    return result


def row_test():
    # Enumerate primitive row equations. These small rows are not required
    # to have the asymptotic eligible-prime or prefix structure.
    pairs = overlap = masked = 0
    q = 7
    for c in range(2, 16):
        for d in range(2, 16):
            if gcd(c, d) != 1 or c*d % q == 0:
                continue
            rows = []
            for x in range(1, 39):
                for y in range(1, 39):
                    gap, rem = divmod(c*x-d*y, q)
                    if rem == 0 and gap and gcd(c*x, d*y) == 1:
                        rows.append((x, y, gap))
            for (a, b, u), (x, y, v) in permutations(rows, 2):
                t, rem = divmod(a*y-b*x, q)
                assert rem == 0 and t
                A, G, R = gcd(a, x), gcd(b, y), gcd(u, v)
                quotient, rem = divmod(abs(t), R*A*G)
                assert rem == 0
                E = part(quotient, c*d*a*b*abs(u))
                overlap += gcd(E, R*A*G) > 1
                mx, my = part(x//A, a*b*c*d), part(y//G, a*b*c*d)
                masked += E > 1 and mx*my > 1
                # All splits are divisors of the maximal split, so testing
                # coprimality there also checks it for the smaller splits.
                assert gcd(a//A*(y//G), b//G*(x//A)) == 1
                assert ((a//A)*my*(y//(G*my)) - (b//G)*mx*(x//(A*mx))) % (q*R*E) == 0
                pairs += 1
    assert overlap and masked
    print(f'{pairs} row pairs; {overlap} overlapping E; {masked} mixed row/determinant masks')


def index_test():
    q, c, d, F1, F2 = 17, 29, 8, 3, 5

    def direction(c, h1, y1, h2, y2):
        a, b = c*F1*h1-d*y1, c*F2*h2-d*y2
        assert a % q == b % q == 0
        assert gcd(c*F1*h1, d*y1) == gcd(c*F2*h2, d*y2) == 1
        R, j = gcd(a, b)//q, gcd(h1, h2)
        n = h2//j*(a//(q*R)), h1//j*(b//(q*R))
        T, rem = divmod(F2*n[0]-F1*n[1], d)
        assert rem == 0
        return n, T

    n, T = direction(c, 7, 74, 5, 114)
    v, T0 = direction(7, 1, 26, 7, 54)
    Dp, rem = divmod(n[0]*v[1]-n[1]*v[0], d)
    assert rem == 0 and F2*Dp == T*v[1]-T0*n[1]
    G, e = gcd(74, 114), gcd(d, Dp)
    E = part(abs(T)//G, d)
    I = lcm(E, e//gcd(e, G))
    assert (T, T0, E, e, I) == (32, -4, 16, 4, 16)
    gamma, m1, m2 = G, 5, 7
    M, N = d*E*gamma, d*e
    period = lcm(M, N)
    hits = sum((F2*m1*x-F1*m2*y) % M == (m1*x*v[1]-m2*y*v[0]) % N == 0
               for x in range(period) for y in range(period))
    assert hits*256 == period**2 and 256 < M*N
    assert 256 >= d*gamma*I
    print(f'coordinate-lattice joint index 256, product {M*N}')


if __name__ == '__main__':
    assert __debug__
    row_test()
    index_test()
