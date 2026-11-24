"""Shared rigorous mesh prices for the moved delete-33 tangents."""
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
from runpy import run_path

from sage.all import QQ


base = Path(__file__).resolve().parent
if not __debug__:
    raise SystemExit('Run with assertions enabled.')
costs = run_path(str(base/'release-costs-33.py'))
neg, s, F = costs['neg'], costs['s'], costs['F']
laws = base/'deletion-laws'
ref = (laws/'delete-33-tail-baseline.txt').read_bytes()
assert sha256(ref).hexdigest() == '7be0449af83f2b264894d0b0074108139ada0badc0c34a26edc6731d81baaa5c'
z, _, B, _ = s['unfold']['lattice']['prime_rows'](ref.decode())
assert len(z)==1257 and z[0]==-QQ(144)/25 and z[-1]==QQ(29)/5

hashes = {'three-midpoints': '2716981104b65b67c01c1b8e2306f43a6328145b3425dfaee040b18dd35a13ec',
          'first-fit': 'ebb8ba76b9be482c9bf4b7c254891a16106c539b30e9c5069abf048c38f1db4e',
          'eight-piece': '163e7c8da104a89855147b0a996b5968b26765d0596a24c70682f566b458890c',
          'six-knots': '79face742e0aee44229823c08c2c32d53ac66aabdac39e918a6b58c2af1dd51f',
          'seven-two-negative': '472b9f8f60de6a6799706829167ef977ba6500e0b06d7f1b6b5a29dd1c9edffa',
          'seven-minus-216': '9ef8f4fb733a4c16085a2e3825687942835da9843afbaabfcd48bf12b1c6d9cc',
          'seven-minus-2304': '8e9cbfdf62149fefda84be7a9ea06e38c62b631c7e5f3b9a197d6aeebda60340',
          'seven-nonnegative': 'b6044feb1a430d6a5633df9afc18128b5547623af4198f8165a73ce9d668a568'}


def load_certificate(case):
    raw = (laws/f'delete-33-{case}.json').read_bytes()
    assert sha256(raw).hexdigest() == hashes[case]
    return json.loads(raw,parse_float=str)


def upper(a,b,m):
    return s['bern_upper'](a,b,m,F('1e-14'))


def single_knot_costs(z, center, data, old, extra, threshold, den=1600):
    """Price one arbitrary real knot per slab; use release on cheap slabs."""
    split = list(extra)
    assert den > 0 and den % 400 == 0
    h = QQ(1)/den
    mid = 2*den
    large = [i for i,y in enumerate(extra) if y > threshold]
    points = sorted({j for i in large for j in range(int(mid*z[i]),int(mid*z[i+1])+1)})
    aa,bb,_,_,curv = s['tail_data'](z,center,data,points,mid,primitive=True)
    # The mass primitive is step(t,0), including on t<0.
    prim = {j:(a,b,s['step'](QQ(j)/mid,0)) for j,a,b in zip(points,aa,bb)}

    for i in large:
        t,r = z[i:i+2]
        j0,j1 = int(mid*t),int(mid*r)
        def score(v):
            left = [a-b for a,b in zip(prim[j0],v)]
            right = [a-b for a,b in zip(v,prim[j1])]
            return upper(*left)+upper(*right)

        # On each cell bound the quadratic interpolant by its three
        # controls, pricing the two atom choices at each control jointly
        # in their shared knot coordinate. This bound is uniform in both.
        vals = [score(prim[j]) for j in range(j0,j1+1,2)]
        for j in range(j0+1,j1,2):
            v = [2*b-(a+c)/2 for a,b,c in zip(prim[j-1],prim[j],prim[j+1])]
            vals.append(score(v))
        # curv already accounts for differences of two laws in A and B.
        # |(t*exp(-t))''| <= 2 exp(-t/2) for t>=0, |delta U|<=1.
        rem = (curv+(2 if t>=0 else 0))*(-F(t)/2).exp()*h**3/(72*F(3).sqrt())
        split[i] = min(extra[i],max(0,(F(max(y.upper() for y in vals))+rem-old[t]).upper().exact_rational()))

    return split, prim


def tangent_data(cert):
    data = cert['cuts']
    second = [r for r in data if len(r)==3]
    assert len(second)==1 and second[0][0]==1
    for row in data:
        assert F(row[-1]) >= 0
        if len(row)!=3:
            j,x,re,im,_ = row
            assert j in (0,1) and F(x)>=0 and abs(s['K'](F(re),F(im)))>0

    # Perturb raw B jumps, not the normalized Fourier coefficients. This
    # center need not be realizable and is never used as a primal law.
    bump = {QQ(k)/400:QQ(Fraction(v)) for k,v in cert['jumps']}
    assert len(bump)==len(cert['jumps']) and bump.keys()<=set(z)
    shift = 0
    center = []
    for t,y in zip(z,B):
        shift += bump.get(t,0)
        center.append(y+shift)
    _, lam, sigma = second[0]
    lam = list(map(F,lam))
    q = s['second_majorant'](lam)
    bc = s['jumps'](z,center,s['C'])
    d,v = s['second_tangent'](z,bc,lam,q)
    qc = sum(x*y for x,y in zip(bc,v))
    constant = -F(8)/9 + sum(F(r[-1]) for r in data if len(r)==5) + F(sigma)*(d+qc)
    return data, center, sigma, constant


def mesh_prices(data, center, constant, finite_den, added, tail_end=48):
    assert all(t*400==int(400*t) for t in z)
    mesh = sorted([int(finite_den*t) for t in z]+added)
    assert len(set(mesh))==len(z)+len(added)
    ap,bp,*_ = s['tail_data'](z,center,data,mesh,finite_den,primitive=True)
    W = [s['step'](QQ(k)/finite_den,0) for k in mesh]
    supports = [upper(a-b,c-d0,e-f) for a,b,c,d0,e,f in
                 zip(ap,ap[1:],bp,bp[1:],W,W[1:])]
    finite = sum(supports)
    print('Constant plus finite atom supports:',constant+finite,flush=True)

    # Integrate the raw atom score, not a difference relative to the
    # (possibly unbounded by one) auxiliary center. All branch points
    # are on the 1/400 mesh. Use quadratic Bernstein interpolation on it.
    den = 400
    lo,hi = int(z[-1]*den),tail_end*den
    pts = range(2*lo,2*hi+1)
    a,b,size,_,_ = s['tail_data'](z,center,data,pts,2*den)
    m = [F(j)/(2*den)*(-F(j)/(2*den)).exp() for j in pts]
    ends = [upper(a[i],b[i],m[i]) for i in range(0,len(m),2)]
    controls = sum(upper(*(2*v[i]-(v[i-1]+v[i+1])/2 for v in (a,b,m)))
                   for i in range(1,len(m),2))
    tail = (2*sum(ends)-ends[0]-ends[-1]+controls)/(3*den)
    # The shared curved_error includes the integral of exp(-t/2) on
    # [z[0],0]. Reuse its derivative coefficient on the positive tail.
    scale = neg['curved_error'](z,center,data,den)/(2*((-F(z[0])/2).exp()-1))
    scale += 3*(F(1)/(2*den)).exp()/(192*den**3)  # |(t exp(-t))'''| <= 3 exp(-t/2)
    err = 2*scale*((-F(z[-1])/2).exp()-(-F(tail_end)/2).exp())
    remote = s['step'](QQ(tail_end),0)+2*size*(-F(tail_end)/2).exp()
    bound = constant+finite+tail+err+remote
    print('Integrated tail atom support, interpolation, remote:',tail,err,remote,flush=True)
    # Restore the actual unsplit atom bounds for measurable-release accounting.
    indices = dict(zip(mesh,range(len(mesh))))
    ends = [indices[int(t*finite_den)] for t in z]
    old = {t: (supports[i] if j==i+1 else upper(ap[i]-ap[j],bp[i]-bp[j],W[i]-W[j]))
           for t,i,j in zip(z,ends,ends[1:])}
    original = constant+sum(old.values())+tail+err+remote
    return bound, original, old, (a, b, m, den, tail, err, remote)
