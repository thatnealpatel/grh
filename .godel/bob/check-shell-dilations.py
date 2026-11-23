"""Certify two genuine-height intervals without an in-band higher harmonic.

Run with a Sage Python interpreter (no -O).
"""
from sage.all import ComplexIntervalField, QQ, RealIntervalField, prime_range

if not __debug__:
    raise RuntimeError('the certificate requires assertions; run without -O')

R = RealIntervalField(100)
C = ComplexIntervalField(100)
t = 2 * R(100000007)**(QQ(3)/5)
X = (3*(t/2).log())**2
D = X.log()
assert 1099 < X and X < 1100 and X*R(-8).exp() < 1
assert 49 < D**2 and D**2 < 50 and 3 < 9*t.log()/(4*D) < 4
starts = [p for p in prime_range(1100-26) if (p+26).is_prime()]
w = [(X/p).log()*R(p).log()*R(p+26).log()/X for p in starts]
omega = [(1+R(26)/p).log() for p in starts]
cut = X**(-QQ(1)/10)
outer = t**(QQ(13)/8)
t_budget = X/D / 16**8


def terms(v):
    angles = (v*om for om in omega)
    return [b*C(y.cos(), y.sin()) for b, y in zip(w, angles)]


def exclude(k, a, b, depth=0):
    # Bisection refines the enclosure, not the set of tested heights.
    if abs(sum(terms(k*R(a, b)))) < cut:
        return
    assert depth < 16, (k, a, b)
    m = (a+b)/2
    exclude(k, a, m, depth+1)
    exclude(k, m, b, depth+1)


def check(a, b):
    a, b = QQ(a)/100000, QQ(b)/100000
    v = R(a, b)
    assert t < v and v < 5*t/4
    c = terms(v)
    z = sum(c)
    s = abs(z)
    assert s > cut
    x = [(ci/z).real() for ci in c]
    E = -32*sum(xi*xj for p, xi in zip(starts, x) for q, xj in zip(starts, x)
                if abs(p-q) <= 49)
    y = R.pi()*(v/t-1)
    relative = R(b-a)*(y.sin()/y)**2*s**8*E.exp()/t_budget
    top = (outer/a).upper().floor()
    assert (top+1)*a > outer
    for k in range(2, top+1):
        exclude(k, a, b)
    print(f'Checked k = 2 through {top}; mass ratio in {relative.str(style="brackets")}')
    return relative


mass = check(13230465395, 13230465485) + check(13363809295, 13363809355)
assert mass > 1
print('Nonreplicating high-branch shell mass on two intervals, in unit budgets:', mass.str(style='brackets'))
