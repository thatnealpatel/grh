# Run with the Python interpreter from SageMath 10.9.
from sage.all import RealIntervalField, QQ, prime_range

if not __debug__:
    raise RuntimeError('assertions must be enabled')
I = RealIntervalField(100)
Z, l2 = I(0), I(2).log()
T = 2**40
c = QQ(587)/1000 - QQ(5)/64
cap0 = QQ(470001)/10**6
assert (9*l2*67/5)**2 - 2 > 83**2
b = (20/I.pi()).log() + 3*l2/5
assert b + QQ(1)/(3*83) + QQ(1)/T < QQ(7)/3
# Analytic tail evaluated with rational majorants log(400)<6,
# 400^(1/3)>7. The individual bounding functions are decreasing.
assert I(400).log() < 6 and 7**3 < 400
assert QQ(1)/3 + QQ(38)/400 + QQ(72)/(400*7) + QQ(2)/T < cap0

primes = [(int(p), I(p).log()) for p in prime_range(401)]
worst = (I(0).upper(), None)
for r in range(83, 400):
    u = r+1
    R = I(r,u)
    X = R**2
    D = 2*R.log()
    E = I(0)
    for p,l in primes:
        if p > u: break
        E += l/X*(D-2*l).max(Z)   # Delta_p
        n,m = p,1
        while n <= u*u:
            E += 2*l/R*(1/I(n)-1/R).max(Z)  # A_{p^m}
            if m >= 2:
                E += l/X*(m*l).min((D-m*l).max(Z))  # C_{p^m}
            n,m = n*p,m+1
    cap = I(1)/3 + I(2)/r + I(2)/T + E
    assert cap < cap0, (r, cap)
    if cap.upper() > worst[0]:
        worst = (cap.upper(), r)
print('largest transition cap, left R:', worst)
print('certified uniform normalized margin >', c - cap0)
