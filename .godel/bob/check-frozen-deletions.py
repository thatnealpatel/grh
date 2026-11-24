"""SageMath 10.9: No coefficient refit on a frozen deletion with the old first masks."""
from pathlib import Path
import numpy as np
import scipy.sparse as sp
from scipy.optimize import linprog
from sage.all import ComplexBallField, QQ, RealBallField

if not __debug__:
    raise SystemExit('Run with assertions enabled.')
F = RealBallField(192)
K = ComplexBallField(192)
pi = F.pi()
c1 = F(QQ(39)/20).cosh()/3
rows = [list(map(int, s.split())) for s in Path('.godel/bob/paired-10-2.txt').read_text().splitlines()
        if s.strip() and not s.startswith('#')]
assert len({l for l, _, _ in rows}) == len(rows)
six = [-23, -9, 5, 19, 33, 55]

# A constant trial u on each interval gives an UPPER price, not a floor.
# Include every first knot and zero; all ramps are affine also on the last tail.
knots = sorted({-QQ(l)/25 for l, _, _ in rows} | {QQ(0)})
mesh = sorted(set(knots) | {QQ(i)/100 for i in range(-160, 801)})
assert mesh[0] <= knots[0] and mesh[-1] >= knots[-1]
primes = [(F(l)/25, F(-QQ(l)/50).exp()*a/10**7, F(-QQ(l)/50).exp()*b/10**7)
          for l, a, b in rows]
grid = np.arange(4097)/4096
A = 2*grid**2-1
B = 4*A**3-3*A

def trial(z):
    ramp = [max(F(0), z+t) for t, a, b in primes]
    f = sum(w*a for w, (t, a, b) in zip(ramp, primes))
    g = sum(w*b for w, (t, a, b) in zip(ramp, primes))
    v = max(z, F(0))
    j = int(np.argmin(float(f)*A+float(g)*B-float(v)*grid))
    u = QQ(j)/4096
    a = 2*u*u-1
    return f*a+g*(4*a**3-3*a)-v*u

p_upper = F(8)/9
for a, b in zip(mesh, mesh[1:]):
    w = F(b-a)
    mass = (-F(a)).exp()-(-F(b)).exp()
    p_upper += mass*trial(F(a)+1-w/(w.exp()-1))
p_upper += (-F(mesh[-1])).exp()*trial(F(mesh[-1])+1)
assert p_upper < F('.164063')

# Exact cell integrals of exp(ik*phi) against the folded trace density.
# Twice the real part is NOT needed: The density already includes the fold.
n, m = 384, 96
phi = [pi*(QQ(i)/n)**2 for i in range(n+1)]
r = (-F(1)/50).exp()
assert (-F(14)/50).exp() < F('.8')
edge = [K(0, x).exp() for x in phi]
D = [1+r*r-2*r*z.real() for z in edge]
cdf = [F(0)]+[2/pi*((x/2).tan()/(F(1)/100).tanh()).arctan() for x in phi[1:-1]]+[F(1)]
indices = [l for l, _, _ in rows]+six
mom = []
for i in range(n):
    J0 = cdf[i+1]-cdf[i]
    assert J0 > 0
    J1 = K(((1+r*r)*J0-(1-r*r)*(phi[i+1]-phi[i])/pi)/(2*r),
           (1-r*r)*(D[i+1]/D[i]).log()/(2*r*pi))
    J = [K(J0), J1]
    for k in range(1, max(map(abs, indices))):
        unweighted = (edge[i+1]**k-edge[i]**k)/K(0, k)
        J.append(((1+r*r)*J[-1]-(1-r*r)*unweighted/pi)/r-J[-2])
    mom.append({k: J[k] if k >= 0 else J[-k].conjugate() for k in set(indices+[0])})

ht = [sum(cell[l]*a for l, a, b in rows)/10**7 for cell in mom]
h3 = [sum(cell[l]*b for l, a, b in rows)/10**7 for cell in mom]
t_lower = c1/(2*(pi/12).cos())*sum(abs(x) for x in ht)
assert t_lower > F('.160721')
angles = [K(0, 2*j*pi/m).exp() for j in range(m)]
unit = np.asarray([complex(z) for z in angles])
weights = np.asarray([float(cell[0].real()) for cell in mom])
F0 = np.asarray([complex(z) for z in h3])[:, None]*unit
C = (np.asarray([[complex(cell[k]) for cell in mom] for k in six])[:, :, None]*unit**2).real
I = -sp.kron(sp.eye(n), np.ones((m, 1)), format='csr')
print('Prime upper and ideal t lower:', p_upper, t_lower, flush=True)
for omit in range(6):
    keep = [j for j in range(6) if j != omit]
    s = [six[j] for j in keep]
    assert min(b-a for a, b in zip(s, s[1:])) >= 14
    # HiGHS nominates a distribution of angles in each cell. Neither the
    # solver's claimed objective nor an approximate equality is trusted.
    mass = np.repeat(weights, m)
    mat = sp.hstack([C[keep].reshape(5, -1).T/mass[:, None], I], format='csr')
    sol = linprog(np.r_[np.zeros(5), weights], A_ub=mat, b_ub=-F0.real.ravel()/mass,
                  bounds=(None, None), method='highs',
                  options={'dual_feasibility_tolerance': 1e-10, 'primal_feasibility_tolerance': 1e-10})
    assert sol.success
    probs = -sol.ineqlin.marginals.reshape(n, m)/weights[:, None]
    linear = F(0)
    residual = [F(0) for k in s]
    for p, cell, h in zip(probs, mom, h3):
        v = [(int(j), int(round(10**12*p[j]))) for j in np.flatnonzero(p > 1e-12)]
        total = sum(z for j, z in v)
        assert total > 0 and all(z > 0 for j, z in v)
        u1, u2 = [sum(z*angles[a*j % m] for j, z in v)/total for a in (1, 2)]
        linear += (h*u1).real()
        for j, k in enumerate(s):
            residual[j] += (cell[k]*u2).real()
    err = F(max(abs(z).upper() for z in residual))
    assert err < F('1e-9')
    u_lower = c1*linear/(1+45*err)
    margin = p_upper-t_lower-u_lower
    print('Deleted index, 3t lower, margin upper:', six[omit], u_lower, margin, flush=True)
    assert margin < F('-.000010')
