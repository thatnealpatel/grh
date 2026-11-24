"""Exclude the exceptional two-site B-covariance case at depth 39/20."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
from runpy import run_path
from sage.all import QQ

base = Path(__file__).resolve().parent
c = run_path(str(base/'check-five-release-joint-refit-33.py'))
p, z, s, F = (c[k] for k in ('p','z','s','F'))
EPS = F('1e-18')
ctrl = c['control']
SITES = c['SITES']
FLAT = (0,2,16)


def sup(a,b,m):
    return s['bern_upper'](a,b,m,EPS)


def midpoint(a,b):
    return tuple((x+y)/2 for x,y in zip(a,b))


def subintegrate(a,b,c,n):
    # Integral of an upper on H of the coefficient quadratic, over [0,1].
    if not n:
        return (sup(*a)+sup(*b)+sup(*c))/3
    a1,c1 = midpoint(a,b),midpoint(b,c)
    mid = midpoint(a1,c1)
    return (subintegrate(a,a1,mid,n-1)+subintegrate(mid,c1,c,n-1))/2


def curv(data,center,den,mass):
    v = p['neg']['curved_error'](z,center,data,den)/(2*((-F(z[0])/2).exp()-1))
    return v + (3*(F(1)/(2*den)).exp()/(192*den**3) if mass else 0)


def correction(new, original, mean):
    return new + (mean-original)


def load(name, digest):
    raw = (base/'deletion-laws'/f'delete-33-five-release-{name}.json').read_bytes()
    assert sha256(raw).hexdigest() == digest
    return json.loads(raw,parse_float=str)


def self_test():
    # Signed middle control, but the quadratic stays positive on [0,1].
    # For a=b=0 the maximum is therefore attained at u=1 throughout.
    v = [tuple(map(F,(0,0,x))) for x in (1,-1,4)]
    bound = subintegrate(*v,4)
    assert F(4)/3 < bound < F(4)/3+2*EPS
    # The raw objective is minus the B coefficient times the atom B.
    # A correction subtracts the old covariance, leaving arbitrary B.
    primitives = [QQ(4),QQ(1),QQ(0)]
    law = [QQ(1)/3,-QQ(1)/2]
    coefs = [-x+y for x,y in zip(primitives[1:],primitives)]
    mean = sum(coefs)/2
    new = [QQ(-1),QQ(7)]
    old_cov = -sum((b-mean)*v for b,v in zip(coefs,law))
    assert old_cov < 0
    raw = -sum(b*v for b,v in zip(new,law))
    corr = -sum(correction(a,b,mean)*v for a,b,v in zip(new,coefs,law))
    assert corr+old_cov == raw
    print('Pair support reference checks passed',flush=True)


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument('--self-test',action='store_true')
    args = cli.parse_args()
    self_test()
    if args.self_test:
        return
    cert = load('pair','595e14a39f60cf01cdf8094774bd163d94c41ba185a28fdca14bb4bc695dcdb8')
    cert0 = load('joint-refit',
                 '0b288072bc772e52fc7fb42aea4ca8544cc2d5e40d90e19d1d18e2de47bb54e2')
    assert [r[:2] for r in cert['cuts']] == [r[:2] for r in cert0['cuts']]
    data, center, _, co = p['tangent_data'](cert)
    previous, origin, _, _ = p['tangent_data'](cert0)
    pts = [int(t*400) for t in z]
    assert all(k in pts and pts[pts.index(k)+1]==k+2 for k in SITES)
    a,b,*_ = s['tail_data'](z,center,data,pts,400,primitive=True)
    m = [s['step'](t,0) for t in z]
    fi = co+sum(sup(a[i]-a[i+1],b[i]-b[i+1],m[i]-m[i+1])
                for i in range(len(z)-1) if pts[i] not in SITES)
    print('Finite outside',fi,flush=True)
    _,orig_b,*_ = s['tail_data'](z,origin,previous,pts,400,primitive=True)
    means = {k:200*(orig_b[pts.index(k)]-orig_b[pts.index(k)+1]) for k in FLAT}

    den = 6400
    assert den % 400 == 0  # Kernel branch points lie on the original mesh.
    h = QQ(1)/den
    spans = {k:range(2*k*(den//400),2*(k+2)*(den//400)+1) for k in SITES}
    nodes = sorted(set(j for span in spans.values() for j in span))
    a,b,*_ = s['tail_data'](z,center,data,nodes,2*den)
    m = [(F(j)/(2*den))*(-F(j)/(2*den)).exp() for j in nodes]
    values = dict(zip(nodes,zip(a,b,m)))
    nodes0 = sorted(set(j for k in FLAT for j in spans[k]))
    _,bo,*_ = s['tail_data'](z,origin,previous,nodes0,2*den)
    prior = dict(zip(nodes0,bo))
    cv, cv0 = curv(data,center,den,True), curv(previous,origin,den,False)
    rel = F(0)
    for k,span in spans.items():
        abc = [values[j] for j in span]
        if k in FLAT:
            abc = [(x,correction(y,prior[j],means[k]),m) for j,(x,y,m) in zip(span,abc)]
        upper = h*sum(subintegrate(a,tuple(ctrl(*v) for v in zip(a,b,c)),c,5)
                      for a,b,c in zip(abc[::2],abc[1::2],abc[2::2]))
        upper += 2*(cv + (cv0 if k in FLAT else 0))*((-F(k)/800).exp()-(-F(k+2)/800).exp())
        rel += upper
        print('Release upper',k,upper,flush=True)

    end = 68
    tail, err = F(0), F(0)
    # Keep the convolution and interval arrays bounded. No truncation is
    # introduced in the kernels: Each call contains the whole jump support.
    for l,r,den in [(QQ(29)/5,10,3200),(10,14,2400),(14,20,1600),
                    (20,26,800),(26,end,400)]:
        assert den % 400 == 0
        j0,j1 = int(l*den),int(r*den)
        assert QQ(j0)/den == l and QQ(j1)/den == r
        nodes = range(2*j0,2*j1+1)
        a,b,size,*_ = s['tail_data'](z,center,data,nodes,2*den)
        m = [(F(j)/(2*den))*(-F(j)/(2*den)).exp() for j in nodes]
        e = [sup(a[j],b[j],m[j]) for j in range(0,len(m),2)]
        v = sum(sup(*(ctrl(v[j-1],v[j],v[j+1]) for v in (a,b,m))) for j in range(1,len(m),2))
        tail += (2*sum(e)-e[0]-e[-1]+v)/(3*den)
        err += 2*curv(data,center,den,True)*((-F(l)/2).exp()-(-F(r)/2).exp())
        print('Tail prefix',r,tail,'total so far',fi+rel+tail,flush=True)
    remote = s['step'](QQ(end),0)+2*size*(-F(end)/2).exp()
    bound = fi+rel+tail+err+remote
    print('Pair upper',bound,'tail error and remote',err,remote,flush=True)
    assert bound < F('-7e-13')


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run with assertions enabled.')
    main()
