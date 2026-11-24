"""Price the invisible (fixed A, B) law changes of the 1,257-knot reference."""
from pathlib import Path
from runpy import run_path

from sage.all import QQ, matrix, vector

base = Path(__file__).resolve().parent
joint = run_path(str(base/'check-tail-deletion-33.py'))
F, step, bern_upper = (joint[k] for k in ('F', 'step', 'bern_upper'))
laws = base/'deletion-laws'


def bounds(a, b, u, sites):
    t = vector(QQ, [QQ(n)/10**9 for n in sites])
    assert len(t) == 3 and 0 <= t[0] < t[1] < t[2] <= 1
    x = [2*v*v-1 for v in t]
    H = matrix(QQ, [[1]*3, x, [4*y**3-3*y for y in x]])
    p = H.solve_right(vector(QQ, [1, a, b]))
    assert min(p) >= 0 and H*p == vector(QQ, [1, a, b])
    lower = max(u, p*t)
    _, alpha, beta = H.transpose().solve_right(t)
    # Add the FULL atom maximum, not just the intercept on the three sites.
    h = bern_upper(F(alpha), F(beta), F(1), F('1e-11'))
    upper = h+F(alpha*a+beta*b)
    return lower, upper


def main():
    table = (laws/'delete-33-tail-baseline.txt').read_text()
    z, A, B, U = joint['unfold']['lattice']['prime_rows'](table)
    assert len(z) == 1257 and 0 in z and 1 in z and z[-1] == QQ(29)/5
    triples = {}
    for row in (laws/'delete-33-tail-fiber.triples').read_text().splitlines():
        k, *sites = map(int, row.split())
        t = QQ(k)/400
        assert t >= 0 and t not in triples
        triples[t] = sites
    depth = QQ(19500036)/10**7
    early, lower, upper = F(0), -F(8)/9, -F(8)/9
    for i, t in enumerate(z):
        if t < 0:
            continue
        lo, hi = bounds(A[i], B[i], U[i], triples.pop(t))
        m = step(t, 0) - (step(z[i+1], 0) if i+1 < len(z) else 0)
        if t < 1:
            early += m*(lo-U[i])
        if t == QQ(49)/25:
            r = z[i+1]
            assert r == QQ(393)/200 and -1 < B[i] < 1
            # The top branch of T(x)=B[i] gives one B-preserving atom.
            x = (F(B[i]).arccos()/3).cos()
            v = ((1+x)/2).sqrt()
            fraction = QQ(53)/1000
            extra = fraction*m*(v-lo)
            cost = (fraction*abs(x-A[i])*2*((-F(t)/2).exp()-(-F(r)/2).exp())
                    /joint['Ct'])
        lower += m*lo
        upper += m*hi
    assert not triples
    print('Early gain at fixed fields:', early)
    print('Attained surplus:', lower, '; fiber upper price:', upper)
    assert early > F('5.4531e-8') and lower > F('-4.62710e-7') and upper < F('-4.62477e-7')
    ratio = F(QQ(39)/20).cosh()/F(depth).cosh()
    assert x > A[z.index(QQ(49)/25)]
    zero = 2*sum(joint['jumps'](z, A, joint['Ct']))+cost
    print('Modified t field at zero frequency and target depth:', zero)
    assert zero > 1
    modified_cap = (F('.9999998')+cost)*ratio
    print('Nearby depth:', depth, '; surplus:', lower+extra, '; t cap:', modified_cap)
    assert lower+extra > F('9e-9') and modified_cap < 1 and 0 < ratio < 1


if __name__ == '__main__':
    main()
