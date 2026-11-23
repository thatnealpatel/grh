"""Separating controls for the affine bound in finite-successor-cap.md."""
from sage.all import QQ, ZZ, RealIntervalField, prime_range

if not __debug__:
    raise RuntimeError('run with assertions enabled')

R = RealIntervalField(180)
q = ZZ(170141183460547116246349746877629464647)
assert q.is_prime(proof=True)
y = R(q)**(QQ(3)/5)
x = (3*y.log())**2
assert 25107 < x < 25108 and 7 < x*R(-8).exp() < 11
primes = list(prime_range(25109))
assert primes[:5] == [2, 3, 5, 7, 11] and primes[-1] < 25107
logs = [R(p).log() for p in primes]
z = [x.log()-l for l in logs]
w = [l*v/x for l, v in zip(logs, z)]
M = sum(w)
assert M > QQ(8)/9


def price(f, t):
    # Upper expression with the same fixed uniform intercept in both tests.
    return (QQ(8877)/10000 + QQ(873)/1000*(f-QQ(9005)/10000)
            + QQ(956)/1000*(t-QQ(2389)/10**6))


def test(phi, model):
    modes = [1, -3, 6, -9, 11, -14, 17, -20]
    if model:
        # For the residue array the 17th doubled harmonic equals one identically.
        assert sum(a*(34*b).cos() for a,b in zip(w,phi)) > QQ(98)/100
    else:
        for j in modes:
            val = sum(a*(2*j*b).cos() for a,b in zip(w,phi))
            assert (val if j > 0 else -val) < QQ(1)/10

    H = 40*x.log()
    F, pools = R(0), {}
    Z = sum(z[4:])
    # The clip starts at prime index 4, so its first edge ends at 5.
    for i in range(5,len(primes)):
        c = (phi[i]-phi[i-1]).cos()
        F += z[i]*((1+abs(c))/2).sqrt()/Z
        if i >= 6:
            d = primes[i]-primes[i-2]
            t = 2/H*(1-d/H).max(R(0))*z[i]*logs[i]*logs[i-2]/x
            pools[d] = pools.get(d, R(0)) + t*(2*(phi[i]-phi[i-2])).cos()
    B = sum(a.max(R(0)) for a in pools.values())
    S = sum(pools.values())
    assert B > QQ(2389)/10**6 and price(F,B) > QQ(8)/9
    if model:
        assert pools[6] > QQ(2389)/10**6 and F < QQ(9005)/10000
        assert price(F,S) < QQ(879)/1000
    else:
        assert F > QQ(9005)/10000 and price(F,S) < QQ(88873)/100000
    print('residue model' if model else 'named phases', F, B, S, price(F,B), price(F,S))


test([y*l for l in logs], False)
test([R.pi()*(6*p % 17)/17 for p in primes], True)
