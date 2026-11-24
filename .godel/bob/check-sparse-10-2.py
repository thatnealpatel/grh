"""SageMath 10.9, from the repo root: sparse signed (10,2) separator."""
from pathlib import Path
from runpy import run_path
from sage.all import ComplexBallField, RealBallField

if not __debug__:
    raise SystemExit('Run with assertions enabled.')
F, K = RealBallField(128), ComplexBallField(128)
base = Path('.godel/bob')
c1 = (F(39)/20).cosh()/3
ct = c1/(2*(F.pi()/12).cos())
eta = F(1)/50  # spacing/2, in the folded Cauchy density


def roots(n):
    step = 2*F.pi()/n
    return [K(0, k*step).exp() for k in range(n)]


def osc(col, j, e):
    return sum(b*e[(k*j) % len(e)] for k, b in col.items())


def finite_t(at, L):
    N = 2*L
    assert all(abs(k) < L and abs(k)+L-1 < N for k in at)
    alpha = F.pi()/(L+1)
    d = [((L-j)*(j*alpha).cos()+((j+1)*alpha).sin()/alpha.sin())/(L+1)
         for j in range(L)]
    assert all(v > 0 for v in d)
    e = roots(N)
    a = {k: b/d[abs(k)] for k, b in at.items()}
    w = {k: d[k]*(-k*eta).exp() for k in range(1, L)}
    cost = F(0)
    for j in range(N//2+1):
        mass = 1+2*osc(w, j, e).real()
        assert mass > 0
        cost += (1 if j in (0, N//2) else 2)*mass*abs(osc(a, j, e))
    return ct*cost/N


M = 1024
angle = roots(M)
angle2 = [angle[2*j % M] for j in range(M)]
angular_error = (F.pi()/M)**2/2


def support_upper(H, b):
    node = max((H*u+b*v).real().upper() for u, v in zip(angle, angle2))
    return F(node)+(abs(H)+4*abs(b))*angular_error


def curvature(col):
    return sum(k*k*abs(b) for k, b in col.items())


# Fold all x, including tails, to 0 <= phi = (x/25) mod sign <= pi.
# Use exact cell mass, a chord surplus K*step^2/8, and a bound for the
# small skew of the endpoint weights under the decreasing density.
N = 8192
step = F.pi()/N
e = roots(2*N)
density = [eta.sinh()/(F.pi()*(eta.cosh()-e[j].real())) for j in range(N+1)]
cdf = [F(0)] + [2/F.pi()*((j*step/2).tan()/(eta/2).tanh()).arctan()
                for j in range(1, N)] + [F(1)]
masses = [b-a for a, b in zip(cdf, cdf[1:])]
assert all(w > 0 for w in masses)
skew = [step*(a-b)/8 for a, b in zip(density, density[1:])]


def trace_upper(upper_at_nodes, second_derivative):
    return sum(w*(a+b)/2+d*abs(a-b) for a, b, w, d in
               zip(upper_at_nodes, upper_at_nodes[1:], masses, skew)) + second_derivative*step**2/8


def trace_abs_lower(nodes, second_derivative):
    return sum(w*abs((a+b)/2)-d*abs(a-b) for a, b, w, d in
               zip(nodes, nodes[1:], masses, skew)) - second_derivative*step**2/8


def third_cost(a3, b3):
    return c1*trace_upper([support_upper(osc(a3, j, e), osc(b3, j, e)) for j in range(N+1)],
                          curvature(a3)+curvature(b3))


# The Sage CLI evaluates .py files in the sage.all namespace.
if __name__ in ('__main__', 'sage.all'):
    first = run_path(str(base / 'check-paired-10-2.py'), run_name='__main__')
    assert first['h'] == 1/first['QQ'](25) and first['c'] == first['QQ'](39)/20
    floor = first['floor']
    at, a3 = first['cols']
    rt2 = F(2).sqrt()
    # Real coefficients of h in the circle support function, before the
    # -cosh(c)/cosh(2c) conversion to the measured multiplier.
    terms = [(-23, -18844), (-9, -25047), (5, -57437), (19, -33872),
             (33, -43702), (55, 7938)]
    assert len(terms) == len({k for k, v in terms}) == 6 and all(v for k, v in terms)
    b3 = {k: F(v)/10**8 for k, v in terms}
    Ht = [osc(at, j, e) for j in range(N+1)]
    H3 = [osc(a3, j, e) for j in range(N+1)]
    t_ideal = ct*trace_upper([abs(z) for z in Ht], curvature(at))
    third_ideal = c1/rt2*trace_upper([abs(z) for z in H3], curvature(a3))
    t_ideal_lo = ct*trace_abs_lower(Ht, curvature(at))
    third_ideal_lo = c1/rt2*trace_abs_lower(H3, curvature(a3))
    third = third_cost(a3, b3)
    # This is the exact finite t allowance, not the unattained ideal price.
    tfinite = finite_t(at, 1024)
    margin = floor-tfinite-third
    print('Ideal bounds at t:', t_ideal_lo, t_ideal)
    print('Ideal bounds at 3t:', third_ideal_lo, third_ideal)
    print('Ideal margin over the paired first-price floor:', floor-t_ideal-third_ideal)
    print('Finite t allowance and overhead bound:', tfinite, tfinite-t_ideal_lo)
    print('Sparse 3t allowance and overhead bound:', third, third-third_ideal_lo)
    print('Finite signed margin, lower bound:', margin)
    assert floor > F('0.16405490')
    assert floor-t_ideal-third_ideal > F('0.000052039')
    assert tfinite-t_ideal_lo < F('0.000001476')
    assert third-third_ideal_lo < F('0.000049426')
    assert tfinite < F('0.16072313') and third < F('0.00332990')
    assert margin > F('0.00000188')
