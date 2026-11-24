"""Check localized repairs of the unfolded seed and price its one-atom family."""
from pathlib import Path
from runpy import run_path
from sage.all import QQ

base = Path(__file__).resolve().parent
old = run_path(str(base/'check-unfolded-deletion-33.py'))
F, step, jumps, cap, complete = (old[k] for k in ('F','step','jumps','cap','complete'))
laws = base/'deletion-laws'
z,A,B,U = old['lattice']['prime_rows']((laws/'delete-33-unfolded-seed.txt').read_text())
mass = [step(t,0)-step(s,0) for t,s in zip(z,z[1:])] + [step(z[-1],0)]
cosine = (F.pi()/12).cos()


def mean(u):
    return sum(w*y for w,y in zip(mass,u))


def price():
    deficit = F(8)/9-mean(U)
    raw = 2*sum(jumps(z,A,1))  # unnormalized G_A(0)
    direction = [1-a if t>=0 else 0 for t,a in zip(z,A)]
    uniform = raw + deficit/(1-mean(U))*2*sum(jumps(z,direction,1))
    ratios = []
    for j,(t,a,u) in enumerate(zip(z,A,U)):
        if t<0:
            continue  # 0 is a knot
        if a==1:
            assert u==1
            continue
        s = max(t,2) if j+1==len(z) else max(t,min(z[j+1],2))
        # On the last slab the maximizer is max(t,2).
        ratios.append(F(s)*(-F(s)/2).exp()*(1-u)/(1-a))
    eta = F(max(r.upper() for r in ratios))
    assert 0 < deficit and 0 < eta < F('.194884')
    for label,required,floor in [('uniform',uniform,'1.95004662'),
                                 ('localized',raw+deficit/eta,'1.95002400')]:
        depth = (6*cosine*required).arccosh()
        print(label,'necessary depth under unfolded cap:',depth,flush=True)
        assert depth > F(floor)


def check_t(c,a,u,lower,beta):
    surplus = mean(u)-F(8)/9
    print('Depth:',c,'failure surplus:',surplus,flush=True)
    assert surplus > F(lower)
    cap(z,jumps(z,a,F(c).cosh()/(6*cosine)),F(beta))


def check_three(c,b,lam,beta):
    coeff = jumps(z,b,F(c).cosh()/3)
    cap(z,coeff,F(beta))
    complete(z,coeff,[F(h) for h in lam.split()])


def pair_refit(name):
    # Replace fraction q of a seed row with the B-preserving pair (i,j).
    a,u = A.copy(),U.copy()
    seen = set()
    for line in (laws/f'delete-33-{name}.pairs').read_text().splitlines():
        knot,i,j,q = map(int,line.split())
        assert knot not in seen and 0<=i<j<=10**9 and 0<q<=10**12
        seen.add(knot)
        k = z.index(QQ(knot)/400)
        i,j,q = QQ(i)/10**9, QQ(j)/10**9, QQ(q)/10**12
        x,y = 2*i*i-1,2*j*j-1
        b,d = 4*x**3-3*x,4*y**3-3*y
        p = (B[k]-d)/(b-d)
        assert 0<=p<=1 and p*b+(1-p)*d==B[k]
        a[k] += q*(p*x+(1-p)*y-a[k])
        u[k] += q*(p*i+(1-p)*j-u[k])
    return a,u


if __name__=='__main__':
    price()
    c = QQ(78001)/40000
    def local(Y):
        return [v+QQ(37)/100000*(1-v) if QQ(47)/25<=t<QQ(11)/5 else v for t,v in zip(z,Y)]
    check_t(c,local(A),local(U),'3.1431e-8','.9999997')
    check_three(c,local(B),'10.57997344 14.33439582 14.62093771','.99999')
    # Check the invariant B at the smaller depth; dilute by Haar above it.
    check_three(QQ(39)/20,B,'24.27245431 32.87489962 33.45808225','.99990')
    for name,c,floor in [('six',QQ(97501)/50000,'5.9999e-8'),('front',QQ(4875043)/2500000,'2e-8')]:
        assert c >= QQ(39)/20
        check_t(c,*pair_refit(name),floor,'.999999775')
