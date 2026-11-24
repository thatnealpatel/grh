"""SageMath 10.9: certify the delete-33 bilateral first-span law."""
from functools import cache
from pathlib import Path
from sage.all import ComplexBallField, QQ, RealBallField

if not __debug__:
    raise SystemExit('Run with assertions enabled.')

# The forward Poisson recurrence amplifies ball widths at high degrees.
F, K = RealBallField(512), ComplexBallField(512)
pi = F.pi()
r = (-F(1)/50).exp()
C = F(QQ(39)/20).cosh()/3
Ct = C/(2*(pi/12).cos())
unit = 10**9
n = 512
radius = 256
indices = list(range(-radius, radius+1))
second = [-7, 6, 19]


def pairs(row):
    assert row and len(row)%2 == 0 and min(row[1::2]) > 0
    return zip(row[::2], row[1::2]), sum(row[1::2])


@cache
def phase(h):
    assert 0 <= h < unit
    return K(0, 2*pi*QQ(h)/unit).exp()


def characters():
    """J[k]=integral of exp(i*k*phi) on each folded Poisson cell."""
    phi = [pi*(QQ(i)/n)**2 for i in range(n+1)]
    edge = [K(0, x).exp() for x in phi]
    D = [1+r*r-2*r*q.real() for q in edge]
    cdf = ([F(0)] + [2/pi*((x/2).tan()/(F(1)/100).tanh()).arctan()
                        for x in phi[1:-1]] + [F(1)])
    for i in range(n):
        mass = cdf[i+1]-cdf[i]
        assert mass > 0
        J = [K(mass), K(((1+r*r)*mass-(1-r*r)*(phi[i+1]-phi[i])/pi)/(2*r),
                        (1-r*r)*(D[i+1]/D[i]).log()/(2*r*pi))]
        for k in range(1, radius):
            flat = (edge[i+1]**k-edge[i]**k)/K(0, k)
            J.append(((1+r*r)*J[-1]-(1-r*r)*flat/pi)/r-J[-2])
        yield [J[k] if k >= 0 else J[-k].conjugate() for k in indices]


def repair_norm(v, sites):
    """l1 norm of the exact solution of G a=v, G_ij=r^|i-j| on sites."""
    out = [v[0]] + [F(0) for _ in sites[1:]]
    for i in range(1, len(sites)):
        p = r**(sites[i]-sites[i-1])
        d = (v[i]-p*v[i-1])/(1-p*p)
        out[i] += d
        out[i-1] -= p*d
    return sum(map(abs, out))


def prime_answers(prime):
    # Each ramp knot (and zero for the failure weight) is a slab boundary.
    starts = [row[0] for row in prime]
    assert starts[0] == -16*radius and starts == sorted(set(starts))
    assert {-16*k for k in indices} <= set(starts)
    z = [QQ(a)/400 for a in starts]
    mass = [F(-a).exp() for a in z] + [F(0)]
    moment = [(1+a)*b for a, b in zip(z, mass)] + [F(0)]
    At, B3 = [[F(0) for _ in indices] for _ in range(2)]
    mean = F(0)
    s = [QQ(k)/25 for k in indices]
    scale = [F(-v/2).exp() for v in s]
    for i, row in enumerate(prime):
        atoms, total = pairs(row[1:])
        A = B = U = QQ(0)
        for h, p in atoms:
            assert 0 <= h <= unit
            u = QQ(h)/unit
            X = 2*u*u-1
            A += p*X
            B += p*(4*X**3-3*X)
            U += p*u
        a, b = F(A/total), F(B/total)
        w = mass[i]-mass[i+1]
        wz = moment[i]-moment[i+1]
        if z[i] >= 0:
            mean += wz*(U/total)
        for j, k in enumerate(indices):
            if starts[i]+16*k >= 0:
                wj = scale[j]*(wz+s[j]*w)
                At[j] += wj*a
                B3[j] += wj*b
    return At, B3, mean


def main():
    table = Path(__file__).with_name('deletion-laws')/'delete-33-bilateral.txt'
    lines = [s for s in table.read_text().splitlines() if s and not s.startswith('#')]
    split = lines.index('trace')
    assert lines[0] == 'prime' and len(lines[split+1:]) == n
    prime, trace = ([list(map(int, row.split())) for row in part]
                    for part in (lines[1:split], lines[split+1:]))

    At, B3, mean = prime_answers(prime)
    R2 = [F(0) for _ in second]
    for row, cell in zip(trace, characters()):
        x, y = row[:2]
        assert x*x+y*y <= unit**2
        t0 = K(x, y)/unit
        atoms, total = pairs(row[2:])
        m, n2 = K(0), K(0)
        for h, p in atoms:
            w = phase(h)
            m += p*w
            n2 += p*w*w
        m /= total
        n2 /= total
        for j, J in enumerate(cell):
            At[j] -= Ct*(t0*J).real()
            B3[j] -= C*(m*J).real()
        for j, k in enumerate(second):
            R2[j] -= (n2*cell[k+radius]).real()
    et = repair_norm(At, indices)/Ct
    e3 = repair_norm(B3, indices)/C
    e2 = repair_norm(R2, second)

    # Correct the exact residuals using the Gram right inverse, not by
    # treating their ball enclosures as zero. See bilateral-deletion-33.md.
    delta = QQ(1)/10**6
    assert (1-delta)*et < delta
    assert 2*(1-delta)*(e3+e2) < delta
    surplus = (1-delta)*mean + delta*(F(1)/2).sqrt() - F(8)/9
    print('pre-repair max absolute residuals (t, 3t, second):',
          *(max(abs(x).upper() for x in v) for v in (At, B3, R2)))
    print('correction norm bounds (t, 3t, second):', et, e3, e2)
    print('dilution:', delta, 'repaired failure surplus:', surplus)
    assert surplus > QQ(3146)/10**8


if __name__ == '__main__':
    main()
