"""Numerical fixed-support dual search; SciPy/NumPy/Clarabel (not a certificate)."""
import argparse
import itertools
from pathlib import Path
import numpy as np
import scipy.sparse as sp
import clarabel as cl
from numpy.polynomial.legendre import leggauss

C = np.cosh(1.95)/3
CT = C/(2*np.cos(np.pi/12))
H = .04
TR = np.pi/H
BASE = Path(__file__).parent


def nodes_z(k, dz, chord=False):
    end = max(10., -min(k))
    # Once past the last knot, every function in the minimum is affine in z.
    z = np.unique(np.round(np.r_[0, -k, np.arange(-1.2, 1.65, dz),
                                 np.arange(1.65, 4, 4*dz),
                                 np.arange(4, end, 12*dz), end], 10))
    z = z[z >= min(0, min(-k))-1e-10]
    a = np.diff(z)
    w = -np.expm1(-a)
    wr = np.exp(-z[:-1])*(w/a-np.exp(-a))
    wl = np.exp(-z[:-1])*w-wr
    if chord:
        ww = np.r_[wl, 0]+np.r_[0, wr]
        # An affine lower bound on the tail: minimum at end plus minimum slope.
        ww[-1] += np.exp(-end)
        p = np.r_[np.maximum(z[:, None]+k, 0), np.ones((1, len(k)))]*np.exp(-k/2)
        return p, np.r_[np.maximum(z, 0), 1.], np.r_[ww, np.exp(-end)]
    # Jensen: evaluate each cell at its e^-z barycenter, plus the tail at end+1.
    zs = np.r_[z[:-1]+a*wr/(wr+wl), end+1]
    return np.maximum(zs[:, None]+k, 0)*np.exp(-k/2), np.maximum(zs, 0), np.r_[wr+wl, np.exp(-end)]


def nodes_x(shifts, dx, jensen=True):
    edges = [0.]
    for a,b,f in [(0,3,1),(3,8,2),(8,18,3),(18,38,4),(38,TR,6)]:
        edges.extend(np.linspace(a,b,1+int(np.ceil((b-a)/(f*dx))))[1:])
    edges=np.array(edges)
    # 12-point Gauss in each cell; numerical quadrature, not enclosed.
    n,w = leggauss(12)
    widths=np.diff(edges)
    x=edges[:-1,None]+widths[:,None]*(n+1)/2
    wt=(widths[:,None]/2)*w*(H/np.pi)*np.sinh(H/2)/(np.cosh(H/2)-np.cos(H*x))
    if not jensen:
        return np.exp(1j*x.ravel()[:,None]*shifts), wt.ravel()
    mass=wt.sum(axis=1)
    return np.einsum('ij,ijk->ik',wt,np.exp(1j*x[:,:,None]*shifts))/mass[:,None], mass


def prime_min(f, g, v, samples=256):
    u=np.linspace(0,1,samples+1)
    A=2*u*u-1; B=4*A**3-3*A
    J=f[:,None]*A+g[:,None]*B-v[:,None]*u
    mask=(J[:,1:-1]<=J[:,:-2])&(J[:,1:-1]<=J[:,2:])
    # flat curves have both endpoints already
    mask &= (J[:,1:-1]<J[:,:-2])|(J[:,1:-1]<J[:,2:])
    i,j=np.nonzero(mask); q=u[j+1].copy()
    for _ in range(3):
        dd=4*f[i]+g[i]*(960*q**4-576*q*q+36)
        d=4*f[i]*q+g[i]*(192*q**5-192*q**3+36*q)-v[i]
        q-=np.clip(d/np.where(dd>0,dd,np.inf),-1/samples,1/samples)
        q=np.clip(q,u[j],u[j+2]);
    i=np.r_[i, np.arange(len(f)), np.arange(len(f))]
    q=np.r_[q, np.zeros(len(f)),np.ones(len(f))]
    a=2*q*q-1; b=4*a**3-3*a
    vals=f[i]*a+g[i]*b-v[i]*q
    minima=np.full(len(f),np.inf); np.minimum.at(minima,i,vals)
    return minima,i,q,vals


def trace_max(p,h,samples=128):
    theta=np.arange(samples)*(2*np.pi/samples)
    e=np.exp(1j*theta)
    val=(p[:,None]*e+h[:,None]*e**2).real
    v0=np.roll(val,1,axis=1); v1=np.roll(val,-1,axis=1)
    i,j=np.nonzero((val>=v0)&(val>=v1)&((val>v0)|(val>v1)))
    q=theta[j].copy(); step=2*np.pi/samples
    for _ in range(3):
        z=p[i]*np.exp(1j*q); t=h[i]*np.exp(2j*q)
        d=-(z+2*t).imag; dd=-(z+4*t).real
        q-=np.clip(d/np.where(dd<0,dd,np.inf),-step,step)
        q=np.clip(q,theta[j]-step,theta[j]+step)
    q=q%(2*np.pi)
    vals=(p[i]*np.exp(1j*q)+h[i]*np.exp(2j*q)).real
    maxima=np.zeros(len(p)); np.maximum.at(maxima,i,vals)
    return maxima,i,q,vals


def finite_t_nodes(k,L):
    """Fold the actual 2L-point sum, with deconvolution of the first mask."""
    m=np.rint(k/H).astype(int)
    if L < 2 or np.any(abs(m) >= L):
        raise ValueError('need |first shift| < L and L >= 2')
    l=np.arange(L)
    al=np.pi/(L+1)
    d=((L-l)*np.cos(l*al)+np.sin((l+1)*al)/np.sin(al))/(L+1)
    phi=np.arange(L+1)*np.pi/L
    mat=np.exp(1j*phi[:,None]*m)/d[abs(m)]
    wt=(1+2*np.cos(phi[:,None]*l[1:])@(d[1:]*np.exp(-l[1:]/50)))/L
    wt[[0,-1]]/=2
    assert np.all(wt>0)
    return mat,wt


class Price:
    def __init__(self,k,dz,dx,fixed_t=False,shift_bounds=None, L=None, chord=False):
        self.k=k
        self.shift_bounds = shift_bounds
        self.P,self.v,self.wz=nodes_z(k,dz,chord)
        # Only the requested first and second shift columns are needed.
        lo, hi = self.shift_bounds
        self.Z, self.wx = nodes_x(np.arange(lo, hi+1)*H, dx)
        self.Zt = self.Z[:, np.rint(k/H).astype(int)-lo]
        self.fixed_t=fixed_t
        self.Zcost,self.wt=self.Zt,self.wx
        if L is not None:
            self.Zcost,self.wt=finite_t_nodes(k,L)
        if fixed_t:
            l,a,_ = np.loadtxt(BASE/'paired-10-2.txt').T
            self.fixed_k = l*H
            self.fixed_a = a/1e7
            # The fixed-t control uses the same knots for both profiles.
            assert set(np.rint(l).astype(int)) <= set(np.rint(k/H).astype(int))
            ka=np.zeros(len(k)); ka[np.searchsorted(np.rint(k/H).astype(int),l.astype(int))]=self.fixed_a
            self.fixed_f=self.P@ka
            self.fixed_cost=CT*(self.wt@abs(self.Zcost@ka))
        else:
            self.fixed_cost=0.

    def solve(self, s, nit, tol, warm=None, *, return_duals=False):
        """Optionally return ((prime cuts, trace cuts), Clarabel solution) as a third item.

        Cuts here are the sorted rows of the final *solved* model, not the
        next warm sets. Solution.z is in equality, SOC, prime, trace order.
        If the solve was rejected, use the payload for diagnostics only.
        """
        k=self.k; P=self.P; Z=self.Zt
        l,n=len(self.v),len(self.wx); K=len(k); q2=2*K
        ns=len(s); nt=len(self.wt)
        N=q2+ns+3*l+5*n+nt
        f=q2+ns; g=f+l; r=g+l; tr=r+l; br=tr+n; bi=br+n; hr=bi+n; hi=hr+n; tn=hi+n
        z2=self.Z[:,np.rint(np.asarray(s)/H).astype(int)-self.shift_bounds[0]]
        z0=sp.csc_matrix
        xp=[]
        def put(start, mat, j):
            a=sp.coo_matrix(mat); xp.append((a.row+start,a.col+j,a.data));
        def setdiag(start,j,values):
            idx=np.arange(len(values)); xp.append((start+idx,j+idx,values))
        def assemble(rows):
            i,j,v=(np.concatenate(c) for c in zip(*xp)); return sp.csc_matrix((v,(i,j)),shape=(rows,N))
        put(0,P,0); put(l,P,K)
        for i,j in enumerate((f,g)): setdiag(i*l,j,-np.ones(l))
        for i,(j,mat,col) in enumerate(((br,Z.real,K),(bi,Z.imag,K),(hr,z2.real,q2),(hi,z2.imag,q2))):
            start=2*l+i*n; put(start,mat,col); setdiag(start,j,-np.ones(n))
        ne=2*l+4*n
        if self.fixed_t:
            put(ne, np.eye(K), 0); ne+=K
            eqb=np.r_[np.zeros(ne-K),np.zeros(K)]
        else: eqb=np.zeros(ne)
        eq=assemble(ne); xp=[]; const=0.
        if not self.fixed_t:
            # slack vector [tn, Re(H_t), Im(H_t)] in SOC
            setdiag(0,tn,-np.ones(nt)); put(nt,-self.Zcost.real,0); put(2*nt,-self.Zcost.imag,0)
            soc=assemble(3*nt)[np.arange(3*nt).reshape(3,-1).T.ravel(),:]
        else:
            soc=z0((0,N)); const=self.fixed_cost
        obj=np.zeros(N); obj[r:r+l]=-self.wz; obj[tr:tr+n]=C*self.wx
        obj[tn:tn+nt]=CT*self.wt
        if self.fixed_t: obj[tn:tn+nt]=0
        if warm is None:
            U={ (i,j/24) for i in range(l) for j in [0,4,8,12,15,17,19,20,21,22,23,24] }
            W={ (i,j*np.pi/4) for i in range(n) for j in range(8) }
        else: U,W=(a.copy() for a in warm)
        def cuts(U,W):
            i,u=np.array(U).T; i=i.astype(int); a=2*u*u-1; b=4*a**3-3*a
            nu=len(i); sr=np.arange(nu); rhs=-self.v[i]*u
            if self.fixed_t: rhs+=a*self.fixed_f[i]
            wz=sp.csc_matrix((np.r_[-a,-b,np.ones(nu)],(np.tile(sr,3),np.r_[f+i,g+i,r+i])),shape=(nu,N))
            i,u=np.array(W).T; i=i.astype(int); nw=len(i); sr=np.arange(nw)
            wt=sp.csc_matrix((np.r_[np.cos(u),-np.sin(u),np.cos(2*u),-np.sin(2*u),-np.ones(nw)],(np.tile(sr,5),np.r_[br+i,bi+i,hr+i,hi+i,tr+i])),shape=(nw,N))
            return sp.vstack([wz,wt],format='csc'), np.r_[rhs,np.zeros(nw)]
        st=cl.DefaultSettings(); st.verbose=False; st.max_threads=1; st.max_iter=120
        st.direct_solve_method='faer'; st.tol_gap_abs=tol; st.tol_feas=tol; st.tol_gap_rel=tol
        for it in range(nit):
            u_rows, w_rows = sorted(U), sorted(W)
            mat, b=cuts(u_rows,w_rows)
            solver=cl.DefaultSolver(z0((N,N)),obj,sp.vstack([eq,soc,mat],format='csc'),np.r_[eqb,np.zeros(soc.shape[0]),b],
                                    [cl.ZeroConeT(ne)]+[cl.SecondOrderConeT(3)]*(soc.shape[0]//3)+[cl.NonnegativeConeT(len(b))],st)
            result=solver.solve()
            w=np.array(result.x)
            if not np.isfinite(result.obj_val) or result.status not in (cl.SolverStatus.Solved,cl.SolverStatus.AlmostSolved,cl.SolverStatus.MaxIterations,cl.SolverStatus.InsufficientProgress):
                return (None,None,((u_rows,w_rows),result)) if return_duals else (None,None)
            f0=w[f:f+l]+(self.fixed_f if self.fixed_t else 0)
            mm,i,u,vals=prime_min(f0,w[g:g+l],self.v)
            nn,j,t,vals2=trace_max(w[br:br+n]+1j*w[bi:bi+n],w[hr:hr+n]+1j*w[hi:hi+n])
            pr=8/9+self.wz@mm
            price=C*(self.wx@nn)+const+(0 if self.fixed_t else CT*(self.wt@abs(self.Zcost@w[:K])))
            margin=pr-price; cut_obj=8/9-result.obj_val-const
            # cutting at every violated local extremum, not just global (helps sign switches)
            ix=w[r+i]-vals>max(tol*3,1e-11)
            jx=vals2-w[tr+j]>max(tol*3,1e-11)
            U.update(zip(i[ix],np.round(u[ix],8))); W.update(zip(j[jx],np.round(t[jx],8)))
            if cut_obj-margin<max(2*tol,1e-9): break
        coeff=w[:K].copy()
        if self.fixed_t: coeff[np.searchsorted(np.rint(k/H).astype(int),np.rint(self.fixed_k/H).astype(int))]=self.fixed_a
        out = (margin,cut_obj,pr,price,coeff,w[K:2*K],w[q2:q2+ns],str(result.status),it+1,result.r_prim,result.r_dual),(U,W)
        if return_duals:
            return (*out, ((u_rows, w_rows), result))
        return out


def real_roots(coeffs):
    """Floating real roots of a polynomial written in increasing powers."""
    return [r.real for r in np.polynomial.polynomial.polyroots(coeffs)
            if abs(r.imag) < 5e-9*(1+abs(r.real))]


def prime_min_roots(a, b, v):
    out = []
    for f, g, z in zip(a, b, v):
        roots = real_roots([-z, 4*f+36*g, 0, -192*g, 0, 192*g])
        u = np.array([0., 1.] + [r for r in roots if 0 < r < 1])
        A = 2*u*u-1
        out.append(np.min(f*A+g*(4*A**3-3*A)-z*u))
    return np.array(out)


def trace_max_roots(b, h):
    out = []
    for p, q in zip(b, h):
        # Derivative after t=tan(theta/2), times (1+t^2)^2.
        roots = real_roots([-p.imag-2*q.imag, -2*p.real-8*q.real, 12*q.imag,
                            -2*p.real+8*q.real, p.imag-2*q.imag])
        e = np.exp(2j*np.arctan(np.array(roots)))
        # Include theta=pi, whose t-coordinate is infinite.
        out.append(max((-p+q).real, np.max((p*e+q*e**2).real, initial=-np.inf)))
    return np.array(out)


def evaluate(k,A,B,s,h,dz=.005,dx=.0125,L=None):
    P,v,w=nodes_z(k,dz,chord=True); p=8/9+w@prime_min_roots(P@A,P@B,v)
    P,v,w=nodes_z(k,dz,chord=False); pu=8/9+w@prime_min_roots(P@A,P@B,v)
    xshift=np.r_[k,s]; Z,w=nodes_x(xshift,dx,jensen=False); Z2=Z[:,len(k):]; Z=Z[:,:len(k)]
    Zt,wt=finite_t_nodes(k,L) if L is not None else (Z,w)
    costs=(CT*(wt@abs(Zt@A)), C*(w@trace_max_roots(Z@B,Z2@h)))
    return p,pu,costs,p-sum(costs),pu-sum(costs)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--range',type=int,default=40); ap.add_argument('--stride',type=int,default=2)
    ap.add_argument('--taper',action='store_true',help='keep first grid dense within ±2, then use strides .08/.16')
    ap.add_argument('--dz',type=float,default=.03); ap.add_argument('--dx',type=float,default=.18)
    ap.add_argument('--min-shift',type=int,default=-25); ap.add_argument('--max-shift',type=int,default=40)
    ap.add_argument('--shift-step',type=int,default=5); ap.add_argument('--min-gap',type=int,default=15)
    ap.add_argument('--max-gap',type=int,default=55)
    ap.add_argument('--pairs',help='explicit integer supports of any size, separated by semicolons')
    ap.add_argument('--iter',type=int,default=7); ap.add_argument('--tol',type=float,default=1e-9)
    ap.add_argument('--fixed-t',action='store_true'); ap.add_argument('--warm',action='store_true')
    ap.add_argument('--save',type=Path); ap.add_argument('--check',type=Path)
    ap.add_argument('--chord',action='store_true',help='use radial chords in the fit')
    ap.add_argument('--L',type=int,help='price the finite t mask of length L instead of its ideal limit')
    ap.add_argument('--paired-knots',action='store_true',help='use the original paired first-mask lattice sites')
    ap.add_argument('--freeze',type=Path,help='with --check, round and write a rational table (distinct shifts required)')
    ap.add_argument('--control',action='store_true')
    args=ap.parse_args()
    if args.freeze and not args.check:
        ap.error('--freeze requires --check')
    if args.check:
        with np.load(args.check,allow_pickle=False) as data:
            k,A,B,s,h=(data[j] for j in ('k','A','B','s','h'))
            if args.freeze:
                for sites in (k,s):
                    if len(np.unique(np.rint(sites/H))) != len(sites):
                        ap.error('--freeze requires distinct shifts within each mask')
                rows={}
                for j,(sites,coeffs) in enumerate(((k,A),(k,B),(s,h))):
                    for l,v in zip(np.rint(sites/H).astype(int),np.rint(coeffs*10**10).astype(int)):
                        rows.setdefault(l,[0,0,0])[j]=v
                args.freeze.write_text('# l, 10^10*b_t, 10^10*b_3t, 10^10*h\n'+
                                       ''.join(f'{l} {a} {b} {d}\n' for l,(a,b,d) in sorted(rows.items())))
                A,B,h=(np.rint(v*10**10)/10**10 for v in (A,B,h))
            pri_lo,pri_hi,(ct,cb),m_lo,m_hi=evaluate(k,A,B,s,h,L=args.L)
            print('support', np.rint(s/H).astype(int), 'second trace coefficients', h)
            print('prime chord / midpoint, costs t / 3t, margin chord / midpoint')
            print(pri_lo,pri_hi,ct,cb,m_lo,m_hi)
        return
    ii=np.arange(-args.range,args.range+1,args.stride)
    if args.taper:
        ii=ii[(abs(ii)<=50)|((abs(ii)<=125)&(ii%2==0))|(ii%4==0)]
    if args.paired_knots: ii=np.loadtxt(BASE/'paired-10-2.txt')[:,0].astype(int)
    k=H*ii
    if args.fixed_t:
        k=np.sort(np.unique(np.r_[np.rint(k/H),np.loadtxt(BASE/'paired-10-2.txt')[:,0]]))*H
    if args.control:
        k,a,b=np.loadtxt(BASE/'paired-10-2.txt').T
        k = k*H
        P,v,w=nodes_z(k,.005,chord=True)
        p=8/9+w@prime_min(P@(a/1e7),P@(b/1e7),v,samples=512)[0]
        Z,w=nodes_x(k,.0125,jensen=False)
        ct=CT*(w@abs(Z@(a/1e7))); cb=(C/np.sqrt(2))*(w@abs(Z@(b/1e7)))
        print('accepted first weights, arbitrary ideal second:',p,ct,cb,p-ct-cb)
        return
    if args.pairs:
        pairs=[tuple(map(int,j.split(','))) for j in args.pairs.split(';')]
    else:
        pairs=[(s,t) for s,t in itertools.combinations(range(args.min_shift,args.max_shift+1,args.shift_step),2)
               if args.min_gap<=t-s<=args.max_gap]
    if not pairs:
        ap.error('provide at least one nonempty support')
    lo=min(round(min(k)/H), *(v for r in pairs for v in r))
    hi=max(round(max(k)/H), *(v for r in pairs for v in r))
    price=Price(k,args.dz,args.dx,args.fixed_t,(lo,hi),args.L,args.chord)
    print('parameters',vars(args),'nfirst',len(k),'nprime',len(price.v),'ntrace',len(price.wx),'supports',len(pairs),flush=True)
    print('support  cell_margin  cut_objective  prime  total_cost  h...  status  rounds  r_prim  r_dual', flush=True)
    best=-np.inf; warm=None
    for ll in pairs:
        s=H*np.array(ll)
        result,warm=price.solve(s,args.iter,args.tol,warm if args.warm else None)
        if result is None:
            print(ll,'error',flush=True); continue
        a,b,p,c,A,B,h,status,it,rp,rd=result
        print(ll,*(f'{j:.10g}' for j in (a,b,p,c,*h)),status,it,rp,rd,flush=True)
        if a>best:
            best=a
            if args.save: np.savez(args.save,k=k,A=A,B=B,s=s,h=h)


if __name__=='__main__':
    main()
