"""Same-sign two-shift certificate by chords in squared coefficient imbalance."""
from functools import lru_cache
from os import environ
from runpy import run_path

from sage.all import QQ, RealBallField

if not __debug__:
    raise SystemExit('Run with assertions enabled.')
F = RealBallField(128)
root = '.godel/bob/'


def strip(beta, d0, d1, H, s_min=None):
    """beta: list of (knot, normalized B jump), already first-cap certified."""
    we, ws = {}, {}
    for t, a in beta:
        for p, b in beta:
            we[t-p] = we.get(t-p, 0)+a*b
            ws[t+p] = ws.get(t+p, 0)+a*b
    kernel = H['prefix_kernel']
    E = kernel(we, [2,-1], [2,1])
    S = lru_cache(None)(kernel(ws, [1], [1,1,QQ(1)/2]))
    T = sum(b*(QQ(1)/2-abs(t)/4)*F(-abs(t)/2).exp() for t,b in we.items())
    D = max(we)
    TV = sum(abs(b) for t,b in beta)
    assert min(t for t,b in beta) >= -12 and max(t for t,b in beta) <= 16
    assert abs(S(-32)) < F('.02') and H['exponential_tail'](S,QQ(24),True) < F('.02')
    assert F(max(abs(S(QQ(i)/32)).upper() for i in range(-1024,769) if abs(i)>=256))+T/(8*32**2) < F('.02')

    @lru_cache(None)
    def R(t):
        return F(-t/2).exp()-E(t)

    N = 200
    err = F('1e-8')
    # Balanced masks: absolute Fourier tail uniform for d>=d0.
    t = (N+1)*d0
    assert t>D and 2+t+D>6
    tail = (4/F.pi())/(4*(N+1)**2-1)*(F(-t/2).exp()/(1-F(-d0/2).exp())
        +TV**2*(2+t+D)*F(-(t-D)/2).exp()/(1-F(-d0/3).exp()))
    assert tail < err
    # The second derivative of the kth R(k*d) without its k^2 factor.
    curv = []
    for j in range(N+1):
        y = j*d0
        bound = T
        if y>D and y+D>0:
            bound = min(T.upper(), (TV**2*(QQ(1)/2+(y+D)/4)*F(-(y-D)/2).exp()).upper())
        curv.append(j*j*(F(bound)+F(-y/2).exp()/4))

    eta = [QQ(i)/16 for i in range(17)]
    rows = []
    for h in eta:
        if h == 0:
            co = [2/F.pi()]+[4*QQ((-1)**(j-1))/(F.pi()*(4*j*j-1)) for j in range(1,N+1)]
        else:
            q = (1-h)/(1+h)
            n = 1
            while 3*q**(n+1)/(1-q) >= QQ(1)/10**8:
                n += 1
            assert n<=N
            c, er = H['binomial_price_data'](q,n)
            assert er < err
            co = [(2 if j else 1)*v/(1+q) for j,v in enumerate(c)]
        rows.append(co)
    M = max(sum(abs(b)*v for b,v in zip(row,curv)).upper() for row in rows)

    @lru_cache(None)
    def caps(d):
        v = [R(j*d) for j in range(N+1)]
        return [sum(a*b for a,b in zip(row,v))-err for row in rows]

    @lru_cache(None)
    def test(s,d):
        p,v = S(s),S(s+d)
        floor = F(1).lower()
        c = caps(d)
        A, B = abs(p+v)/2, abs(p-v)/2
        for l,u,cl,cu in zip(eta,eta[1:],c,c[1:]):
            # Pointwise concavity in h^2. Minimize the resulting
            # quadratic minus the worst of the two oriented prices.
            b = (cu-cl)/(u**2-l**2)
            assert b>0
            x = F(max(l,min(u,(B/(2*b)).center())))
            # Tangent at x is affine; its minimum is at an endpoint.
            lo = cl+b*(x*x-l*l)-A-B*x
            slope = 2*b*x-B
            floor = min(floor,(lo+slope*(l-x)).lower(),(lo+slope*(u-x)).lower())
        return floor

    slack = QQ(1)/100000
    left = -QQ(8)-d1 if s_min is None else s_min
    assert left < 8
    stack = [(left,QQ(8),d0,d1)]
    boxes = 0
    while stack:
        a,b,l,u = stack.pop()
        es,ed = T*(b-a)**2/8,(F(M)+T)*(u-l)**2/8
        if all(F(test(s,d))>slack+es+ed for s in (a,b) for d in (l,u)):
            boxes += 1
        else:
            assert min(b-a,u-l)>QQ(1)/10**7, (a,b,l,u,test(a,l))
            if es>ed:
                m=(a+b)/2; stack.extend([(a,m,l,u),(m,b,l,u)])
            else:
                m=(l+u)/2; stack.extend([(a,b,l,m),(a,b,m,u)])
    # At outer shifts both centers cost < .02. Balanced capacity is
    # the minimum over imbalance for same-sign coefficients.
    n=64
    assert F(min(caps(d0+j*(d1-d0)/n)[0].lower() for j in range(n+1)))-F(M)*((d1-d0)/n)**2/8 > F('.02')+slack
    print('Squared-imbalance chords:',d0,d1,'boxes',boxes,'slack >',slack,flush=True)


def jumps(H,law):
    return [(t,b/H['C1']) for t,b in H['jump_terms'](law['B'],law['z'])]

if __name__ in ('__main__', 'sage.all'):
    environ['TWO_TERM_LAW']='hard-pair'
    H=run_path(root+'check-two-term-10-2.py')
    hs=jumps(H,H)
    strip(hs,QQ(39)/50,QQ(47)/50,H)
    # For the long-gap strip test a mixture instead of paying the larger
    # high-gap threshold from the envelope of the 152-slab law.
    environ['TWO_TERM_LAW']='regional'
    reg=run_path(root+'check-two-term-10-2.py')
    single=run_path(root+'check-single-shift-10-2.py')
    mix={}
    for weight,points in [(QQ(2)/5,hs),(QQ(2)/5,jumps(H,reg)),(QQ(1)/5,jumps(H,single))]:
        for t,b in points:
            mix[t]=mix.get(t,0)+weight*b
    strip(sorted(mix.items()),QQ(37)/20,QQ(4),H)
