"""Two upper certificates on exterior-cosine minorants, not on window floors.
Run with the SageMath 10.9 Python, assertions enabled; no optimizer is used.
"""
from math import comb
from pathlib import Path
from sage.all import QQ, RealBallField, ComplexBallField

if not __debug__:
    raise RuntimeError('run with assertions enabled')
R, C = RealBallField(100), ComplexBallField(100)
pi, I = R.pi(), C(0, 1)
D, h = QQ(11)/5, QQ(1)/12
atoms = [(R(n).log(), 2*sign*R(base).log()/R(n).sqrt())
         for n, base, sign in [(3,3,1), (5,5,-1), (7,7,1), (9,3,-1)]]
a0 = (4/pi).log()

def data(name):
    path = Path(__file__).with_name('chi4-exterior-' + name + '.txt')
    rows = [tuple(map(int,line.split())) for line in path.read_text().splitlines()
            if line.strip() and not line.startswith('#')]
    k, numer = zip(*rows)
    assert min(numer) >= 0 and sum(numer) > 0
    return k, [QQ(n)/sum(numer) for n in numer]

# Archimedean expectation against the cubic spline from four uniforms.
def arch(y0):
    y0=C(y0)
    def fun(j):
        def f(x, analytic):
            z=(y0+h*x)/2
            zp=3/QQ(4)+I*z; zm=3/QQ(4)-I*z
            if analytic and (not zp.real()>0 or not zm.real()>0):
                return C('nan')
            K=sum((-1)**l*comb(4,l)*(x+4-2*l)**3 for l in range(j+1))/96
            return K*(zp.psi()+zm.psi())/2
        return f
    return sum(C.integral(fun(j),2*j-4,2*j-2,abs_tol=2**-65,rel_tol=2**-65,depth_limit=90) for j in range(4)).real()

def spline():
    k, w = data('spline')
    y = [QQ(j)/64 for j in k]
    yw, ww = list(map(R,y)), list(map(R,w))
    def moment(t):
        th = t*R(h)
        return (th.sin()/th)**4 * sum(v*(t*z).cos() for v,z in zip(ww,yw))
    cost = a0 + sum(v*arch(z) for v,z in zip(ww,yw))
    cost += sum(b*moment(t) for t,b in atoms)
    m2 = sum(v*z*z for v,z in zip(w,y)) + 4*h*h/3
    n, T = 1024, 110
    peak = max(abs(moment(R(QQ(j)/n))).upper() for j in range(int(D*n),T*n+1))
    rho = R(max((R(peak)+R(m2/(8*n*n))).upper(), R(1/(h*T)**4).upper()))
    assert cost + 54*rho < -QQ(21004827)/10**11
    print('All exterior shifts: cost, absolute moment bound, cap-54 upper:',
          cost, rho, cost+54*rho, flush=True)

def lattice():
    k, w = data('lattice')
    y, w = [pi*30*j/72383 for j in k], list(map(R,w))
    def arch_at(z):
        return a0 + C(R(3)/4,z/2).psi().real()
    cost = sum(v*(arch_at(z)+sum(b*(t*z).cos() for t,b in atoms)) for v,z in zip(w,y))
    js = range(67,481)
    moments = [sum(v*(z*j/30).cos() for v,z in zip(w,y)) for j in js]
    # H=2 sum moment_j cos(jy/30); bound sup H by mesh interpolation.
    L, n = 30*pi, 2048
    curvature = 2*sum(abs(r)*(R(j)/30)**2 for r,j in zip(moments,js))
    peak = max((2*sum(r*(pi*g*j/n).cos() for r,j in zip(moments,js))).upper()
               for g in range(n+1))
    U = R((R(peak)+curvature*(L/n)**2/8).upper())
    assert U > 0
    norm_h = (2*sum(r*r for r in moments)).sqrt()
    mean_m = arch_at(L) + sum(abs(b)/(t*L) for t,b in atoms)
    norm_m = R(max(arch_at(L).upper(),(-arch_at(R(0))).upper())) + sum(abs(b) for _,b in atoms)
    bound = (cost+U*mean_m+norm_m*norm_h)/(1+U)
    assert bound < -QQ(8023015)/10**8
    print('Lattice through 16: cost, cap-free upper:', cost, bound, flush=True)

spline()
lattice()
