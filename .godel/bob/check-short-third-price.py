"""SageMath Python, without -O: Pay for an order-11 test with the short third harmonic."""
from sage.all import QQ, RealBallField

if not __debug__:
    raise SystemExit('Run without -O.')
F = RealBallField(128)
lam, eta = QQ(348)/100, QQ(147)/10000
shift = {l: QQ(l)/10 + QQ(1)/25 for l in range(-5, 6)}
r = {l: QQ(6-abs(l))/36 for l in shift}
A = {l: r[l]*F(-s/2).exp() for l, s in shift.items()}
I = sum(r[l]*F(-abs(QQ(l))/20).exp() for l in shift)

# Lower bound for min_u f*T2(u) - v*(lam*u+eta*T6(u)).
N = 512
u = [QQ(i)/N for i in range(N+1)]
t2 = [2*x*x-1 for x in u]
w = [lam*x + eta*(4*t**3-3*t) for x, t in zip(u, t2)]


def lower(f, v):
    # -T6''(u) = -960*u^4 + 576*u^2 - 36 <= 252/5.
    grid = min((f*t-v*k).lower() for t, k in zip(t2, w))
    return F(grid) - (4*f+51*eta*v)/(8*N*N)


# Include all knots of f and z_+. The minimum is concave on each piece.
mesh = sorted({QQ(j)/100 for j in range(-54, 501)} | {-s for s in shift.values()})
assert mesh[0] == -max(shift.values()) and mesh[-1] >= -min(shift.values())
vals = [lower(sum(A[l]*max(0, z+s) for l, s in shift.items()), max(0, z)) for z in mesh]
price = F(lam*8/9)
for x, y, left, right in zip(mesh, mesh[1:], vals, vals[1:]):
    h = F(y-x)
    mass = 1-(-h).exp()
    first = mass-h*(-h).exp()
    price += F(-x).exp()*(left*mass+(right-left)*first/h)
price += F(-mesh[-1]).exp()*(vals[-1] + lower(sum(A.values()), QQ(1)))
c = F('1.95')
s1 = 2*(F.pi()/13).cos()
B = I/3 - s1*price/c.cosh()
coef = s1*eta/c.cosh()
print('Floor on first price minus eta*C3; combined upper price; coefficient of C3:', price, B, coef)
print('Upper price of S11 at C3 >= -.72:', B+coef*F('.72'))
assert price > F('.57082929')
assert B+coef*F('.72') < F('-.0002068')
assert F('1.40').cosh()/3 < F('.72')
