"""Certify joint second answers for all gaps up to 13/25 at depth 39/20."""
import os
from bisect import bisect_right
from functools import lru_cache
from runpy import run_path

from sage.all import QQ, RealBallField

if not __debug__:
    raise SystemExit('Run with assertions enabled.')
F = RealBallField(128)
root = '.godel/bob/'
os.environ['TWO_TERM_LAW'] = 'hard-pair'
H = run_path(root+'check-two-term-10-2.py')
L = run_path(root+'check-two-height-radial-witness.py')
J = run_path(root+'check-single-shift-10-2.py')
r, h, radial, zero = (QQ(n)/10**7 for n in (5710000, 4195798, 94000, 202))
assert r+h+radial+zero == 1
surplus = (r*J['mean_margin']+h*H['mean_margin']+radial*(L['mean']-F(8)/9)
           +zero*((F(1)/2).sqrt()-F(8)/9))
assert surplus > F('0.00000009')
z = sorted(set(J['z']+H['z']+L['z']))

def mixprofile(key):
    out = []
    for t in z:
        v = QQ(0)
        for wt, law, name in ((r,J,key),(h,H,key),(radial,L,key.lower())):
            j = bisect_right(law['z'],t)-1
            if j >= 0:
                v += wt*law[name][j]
        out.append(v)
    return out

A, B = mixprofile('A'), mixprofile('B')
H['certify_cap']('mixed A', A, QQ(6186604)/10**7, z)
assert QQ(6186604)/10**7 < H['C10']
assert r*J['cap_B']+h*H['cap_B']+radial*L['cap'] < H['C1']

def check_strip(profile, d0, d1):
    beta = [(t,b/H['C1']) for t,b in H['jump_terms'](profile, z)]
    we, ws = {}, {}
    for t,b in beta:
        for p,a in beta:
            we[t-p] = we.get(t-p,0)+a*b
            ws[t+p] = ws.get(t+p,0)+a*b
    E = lru_cache(maxsize=None)(H['prefix_kernel'](we, [2,-1], [2,1]))
    S = lru_cache(maxsize=None)(H['prefix_kernel'](ws, [1], [1,1,QQ(1)/2]))
    T = sum(b*(QQ(1)/2-abs(t)/4)*F(-abs(t)/2).exp() for t,b in we.items())
    assert 0 < T < 3
    @lru_cache(maxsize=None)
    def R(u):
        return F(-u/2).exp()-E(u)

    # Uniform band for outer s. Both shifts have magnitude >= 8 there.
    assert z[0] == -12 and z[-1] == 16
    assert abs(S(-32)) < F('.02') and H['exponential_tail'](S,QQ(24),True) < F('.02')
    assert F(max(abs(S(QQ(j)/32)).upper() for j in range(-32*32,24*32+1) if abs(j)>=256))+T/(8*32**2) < F('.02')
    # Truncated cosine capacity and uniform truncation error for d >= d0.
    N = 600
    c = [QQ((-1)**(j-1))/(4*j*j-1) for j in range(1,N+1)]
    D = max(we)
    TV = sum(abs(b) for t,b in beta)
    u = (N+1)*d0
    assert u>D and 2+u+D>6
    err = (4/F.pi())/(4*(N+1)**2-1)*(F(-u/2).exp()/(1-F(-d0/2).exp())
           +TV**2*(2+u+D)*F(-(u-D)/2).exp()/(1-F(-d0/3).exp()))
    assert err < F('1e-17')
    C2 = 4/F.pi()*sum(abs(a)*j*j*(T+F(-j*d0/2).exp()/4) for j,a in enumerate(c,1))
    @lru_cache(maxsize=None)
    def C(d):
        return (2*R(QQ(0))+4*sum(a*R(j*d) for j,a in enumerate(c,1)))/F.pi()

    # Four corners suffice after chord errors for each fixed eta, price sign.
    @lru_cache(maxsize=None)
    def test(s,d):
        k=(R(QQ(0))-R(d))/4
        assert k>0
        p,v=S(s),S(s+d)
        # Relax eta to the full real line when minimizing the quadratic.
        # Also bound the possible loss by b since |eta| <= 1.
        b=abs(p-v)/2
        cost = F(min((b*b/(4*k)).upper(), b.upper()))
        same = C(d)-abs(p+v)/2-cost
        # For opposite signs the real-part capacity and each signed center
        # are affine up to the sign switch. Check equal weights and singles.
        return min(x.lower() for x in (same, 2*k-b, R(QQ(0))-F(max(abs(p).upper(),abs(v).upper()))))

    floor=F('0.000005')
    stack=[(-QQ(8)-d1,QQ(8),d0,d1)]
    boxes=0
    while stack:
        a,b,l,u=stack.pop()
        es=T*(b-a)**2/8
        ed=(C2+T+(T+F(1)/4)/2)*(u-l)**2/8
        loss=err+es+ed
        if all(F(test(s,d))>floor+loss for s in (a,b) for d in (l,u)):
            boxes+=1
            continue
        assert min(b-a,u-l)>QQ(1)/10**7
        if es>ed:
            m=(a+b)/2;stack.extend([(a,m,l,u),(m,b,l,u)])
        else:
            m=(l+u)/2;stack.extend([(a,b,l,m),(a,b,m,u)])
    # Tail s: both centers have magnitude <.02. Check the two capacities.
    M=128
    assert F(min(C(d0+j*(d1-d0)/M).lower() for j in range(M+1)))-err-C2*((d1-d0)/M)**2/8 > F('.4')
    assert F(min((R(QQ(0))-R(d0+j*(d1-d0)/M)).lower() for j in range(M+1)))-(T+F(1)/4)*((d1-d0)/M)**2/8 > F('.04')
    print('All directions covered:', (d0,d1), '; finite cells, slack, tail error:', boxes,floor,err)

    def balanced_upper(s, d):
        assert d >= d0  # The same uniform Fourier tail applies.
        return C(d)+err-abs(S(s)+S(s+d))/2
    return balanced_upper


print('Strict failure surplus, mixed B cap:',surplus,r*J['cap_B']+h*H['cap_B']+radial*L['cap'])
check_strip(B, QQ(3)/16, QQ(1)/2)

# Replace X on this negative block by a variable in {-1,1} with
# the same mean A. Here 4X^3-3X=X; the failure integral is unchanged.
left, right = -QQ(3)/2, -QQ(11)/8
assert left in z and right in z
changed = [a if left <= t < right else b for t,a,b in zip(z,A,B)]
H['certify_cap']('block B', changed, QQ(119)/100, z)
assert QQ(119)/100 < H['C1']
block_upper = check_strip(changed, QQ(1)/2, QQ(13)/25)
upper = block_upper(QQ(7)/100, QQ(11)/20)
print('Block law at (.07,.62), normalized balanced slack upper:', upper)
assert upper < -QQ(44)/10**5
