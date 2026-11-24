#!/usr/bin/env python3
"""Numerical discovery for the two-term prime law; not the certificate."""
import argparse
from pathlib import Path
from time import monotonic

import clarabel as cl
import numpy as np
import scipy.sparse as sp
from scipy.fft import next_fast_len, rfft, irfft
from scipy.optimize import linprog
from scipy.signal import find_peaks
from scipy.spatial import ConvexHull

P = argparse.ArgumentParser()
P.add_argument('--out', required=True)
P.add_argument('--scope', choices=['screen', 'anchors', 'one', 'regional', 'dual', 'dual-regional', 'hard-pair'], default='screen')
P.add_argument('--steps', type=int, default=10)
P.add_argument('--atoms', type=int, default=128)
P.add_argument('--refine', action='store_true')
P.add_argument('--left', type=int, default=8)
P.add_argument('--mean', type=float, default=2e-6)
P.add_argument('--fpad', type=float, default=3e-6)
P.add_argument('--seconds', type=float, default=65)
P.add_argument('--l0', type=float, default=2.)
args = P.parse_args()
hard = args.scope == 'hard-pair'
path = Path('.godel/bob/single-shift-10-2.txt')
rows = [list(map(int, l.split('#')[0].split())) for l in path.read_text().splitlines()
        if l.split('#')[0].strip()]
z = np.unique(np.r_[[row[0]/64 for row in rows], np.arange(-args.left, -8, .25),
                    np.arange(-.75, .5, 1/(128 if hard else 64)) if args.refine else [],
                    np.arange(.5, 3.0 if hard else 2.5, 1/(64 if hard else 32)) if args.refine else []])
n = len(z)
ZDEN = 128 if hard else 64
zind = np.rint((z-z[0])*ZDEN).astype(int)
nfft = next_fast_len(2*zind[-1]+1, real=True)
npos = np.count_nonzero(z >= 0)
zp = z[-npos:]
wmean = (1+zp)*np.exp(-zp)
wmean -= np.r_[wmean[1:], 0.]
scale = np.exp(np.minimum(z+2, 0)/2)
sc = np.exp(-z/2)*scale
dz = np.diff(z)
C1 = np.cosh(1.95)/3
C10 = C1/(2*np.cos(np.pi/12))
CAPS = np.array([C10, C1]) - args.fpad


def mat(x):
    x = np.atleast_1d(x)[:, None]
    w = .5+1j*x
    delta = np.column_stack((-np.expm1(-w*dz), np.ones(len(x))))
    return np.exp(1j*x*z)*delta.conj()*sc/w


# Integration is only for discovery. Price the sign-dependent quadratic directly:
# Q = int (|H||m|^2 + sign Re(H*m^2)). It is PSD, even at cancellation nodes.
step = 1/64
xq = (np.arange(64*(128 if hard else 64))+.5)*step
muq = step/(np.pi*(.25+xq*xq))
M = mat(xq)/C1
zz = np.arange(2*zind[-1]+1)/ZDEN+2*z[0]
ss = np.arange(-500, 801)/40
DS = np.arange(0, 281, 2)
RATIOS = np.r_[0., .25, .5, .65, .8, .9, 1.]


def sum_kernel(v):
    up = np.maximum(0, v)
    return (1+up+up**2/2)*np.exp(-abs(v)/2)


def sum_coeffs(b):
    q = np.zeros(zind[-1]+1)
    q[zind] = np.diff(np.r_[0., b*scale])*np.exp(-z/2)/C1
    return irfft(rfft(q, nfft)**2, nfft)[:len(zz)]


def mask_mass(d, r):
    if not d:
        return abs(1+r)
    k = np.arange(1, 2048)
    if abs(r)==1:
        return 4/np.pi-(8/np.pi)*((-r)**k/(4*k*k-1))@np.exp(-k*d/2)
    grid = np.arange(4096)*(2*np.pi/4096)
    b = rfft(np.abs(1+r*np.exp(1j*grid))).real/4096
    return b[0]+2*b[1:2048]@np.exp(-k*d/2)


def price(b, tests):
    u = muq*abs(M@b)**2
    coeff = sum_coeffs(b)
    return [(mask_mass(d,r)-np.abs(1+r*np.exp(1j*d*xq))@u,
             sum_kernel(zz+s)@coeff + r*sum_kernel(zz+s+d)@coeff)
            for s, d, r in tests]


def fquad(s, d, r, sign):
    H = np.exp(1j*s*xq)*(1+r*np.exp(1j*d*xq))
    W = M*(np.sqrt(2*muq*np.abs(H))*np.exp(.5j*np.angle(sign*H)))[:, None]
    I = mask_mass(d, r)
    lam, v = np.linalg.eigh(W.real.T @ W.real)
    ix = lam > 1e-11
    # Rotated norm epigraph via (I-f,1,sqrt(2)Rx) in the rotated cone.
    return I, (np.sqrt(lam[ix])[:, None]*v[:, ix].T)


# Capacity table for discrete exchange; use the exact S(s) kernel for centers.
SS = sum_kernel(ss[:,None]+zz)
dd = DS/40
cosdx = np.cos(dd[:, None]*xq)
capacity = np.array([np.sqrt(np.maximum(0, 1+r*r+2*e*r*cosdx))
                     for e in [1, -1] for r in RATIOS])
mass = np.array([[mask_mass(d,e*r) for d in dd] for e in [1,-1] for r in RATIOS])


def scan(b):
    m = M@b
    coeff = sum_coeffs(b)
    S = SS@coeff
    cap = mass-capacity@(muq*abs(m)**2)
    vals = []
    for k, e in enumerate([1,-1]):
        for j, r in enumerate(RATIOS):
            for i, delta in enumerate(DS):
                L = len(S)-delta
                q = S[:L]+e*r*S[delta:]
                for sg in [1,-1]:
                    a = np.argmax(sg*q)
                    vals.append((cap[k*len(RATIOS)+j, i]-sg*q[a], ss[a], dd[i], e*r, sg))
    return sorted(vals)


# Exterior facets in (A,B) and upper facets in (A,B,U), respectively.
u = np.linspace(0, 1, args.atoms+1)
xatoms = np.unique(np.r_[np.linspace(-1, 1, args.atoms+1), 2*u*u-1,
                         np.arange(.54, .71, 1/(4*args.atoms)), [-.5, 0, .5]])
X = np.stack((xatoms, 4*xatoms**3-3*xatoms, np.sqrt((1+xatoms)/2)), axis=1)
faces2 = ConvexHull(X[:, :2]).equations
faces3 = ConvexHull(X).equations
faces3 = faces3[faces3[:, 2] > 1e-10]
nu = 2*n+npos
kvar = nu+1


def linear(c2, c3):
    ii, jj, vv, rhs = [], [], [], []
    def add(inds, mat, b):
        mat = np.atleast_2d(mat)
        ii.extend(np.repeat(np.arange(len(rhs), len(rhs)+len(b)), len(inds)))
        jj.extend(np.tile(inds, len(b)))
        vv.extend(mat.ravel())
        rhs.extend(b)
    for j in range(n):
        y2 = faces2[sorted(c2[j])]
        add([j, n+j], y2[:, :2]*scale[j], -y2[:, -1]-(2e-9 if hard else 0.))
        if z[j] >= 0:
            y3 = faces3[sorted(c3[j])]
            add([j, n+j, 2*n+j-(n-npos)], y3[:, :3], -y3[:, -1])
    add(np.arange(2*n, nu), -wmean, [-8/9-args.mean])
    add([nu], [[1]], [.25])
    add([nu], [[-1]], [3.])
    return sp.coo_matrix((vv,(ii,jj)),shape=(len(rhs),kvar)).tocsc(), np.asarray(rhs)


f0 = np.unique(np.r_[np.arange(0, 12, .07), np.arange(12, 32, .33),
                     np.arange(32, 64, 1.0), 64.])
fg = np.arange(0, 72.001, 1/(256 if hard else 128))
Mg = mat(fg)
f = [f0.copy(), f0.copy()]
if args.scope == 'one':
    tests = [(0., 1.25, 1., 1)]
elif args.scope in ['dual','hard-pair']:
    tests = [(.16,1.,.0005809242445/.001018011621,sg) for sg in (-1,1)]
elif args.scope in ['regional','dual-regional']:
    tests = [(0.,d,1.,1) for d in (.875,1.,1.125,1.25,1.5)]
    tests += [(.2,0.,0.,1),(.45,0.,0.,1)]
    if args.scope=='dual-regional':
        tests += [(.16,1.,.0005809242445/.001018011621,sg) for sg in (-1,1)]
elif args.scope == 'anchors':
    tests = [(0., d, 1., 1) for d in (1., 1.25, 1.5)]
else:
    tests = [(0., d, 1., 1) for d in (1., 1.25, 1.5)]
    tests += [(-.5, d, 1., 1) for d in (1., 1.5, 2.)]
    tests += [(s,0.,0.,1) for s in (-1.,0.,.5,1.,2.)]
blocks = {key:fquad(*key) for key in tests}
if args.l0 < 2.:
    lam, v = np.linalg.eigh((M.conj().T @ (muq[:,None]*M)).real)
    ix = lam > 1e-11
    L0 = np.sqrt(lam[ix])[:, None]*v[:, ix].T
settings = cl.DefaultSettings()
settings.verbose = False
settings.max_iter = 120
settings.time_limit = args.seconds
settings.tol_gap_abs = settings.tol_gap_rel = settings.tol_feas = (1e-8 if hard else 6e-8)
settings.max_threads = 2
settings.direct_solve_method = 'faer'
q = np.zeros(kvar)
q[-1] = -1
q[2*n:nu] = -1e-3*wmean
reg = np.r_[np.tile(sc**2*np.minimum(np.r_[dz, 1],1),2)*1e-9,np.zeros(npos+1)]
Q = sp.diags(reg, format='csc')
c2 = [set(range(0,len(faces2),5 if hard else 6))|{len(faces2)-1} for _ in z]
c3 = [set(range(0,len(faces3),15))|{len(faces3)-1} for _ in z]
print('slabs', n, z[0], z[-1], 'atoms', len(X), 'faces', len(faces2), len(faces3), 'caps', CAPS, flush=True)


def recover(sol):
    lines = [f'# {ZDEN}*z then pairs (10^8*X, 10^8*probability)']
    scaleint = 10**8
    for j, (zr, s) in enumerate(zip(z, scale)):
        shrink = (1-1e-8) if hard else 1.
        ans = linprog(-X[:, 2], A_eq=np.r_[np.ones((1,len(X))),X.T[:2]],
                      b_eq=[1, shrink*s*sol[j], shrink*s*sol[n+j]], bounds=(0,None),
                      method='highs', options={'primal_feasibility_tolerance': 1e-9,
                                                 'dual_feasibility_tolerance': 1e-9})
        if not ans.success:
            return False
        ix = np.flatnonzero(ans.x>2e-9)
        xx = np.rint(X[ix,0]*scaleint).astype(int)
        pp = np.rint(ans.x[ix]*scaleint).astype(int)
        pp[np.argmax(pp)] += scaleint-pp.sum()
        lines.append(' '.join(map(str,[round(zr*ZDEN), *np.column_stack((xx[pp>0],pp[pp>0])).ravel()])))
    Path(args.out+'.txt').write_text('\n'.join(lines)+'\n')
    return True


for it in range(args.steps):
    start = monotonic()
    M0, rhs = linear(c2,c3)
    mats = [M0]
    bs = [rhs]
    cones = [cl.NonnegativeConeT(len(rhs))]
    for i, (ff, cap) in enumerate(zip(f,CAPS)):
        a = mat(ff)
        m = np.zeros((3*len(ff),n))
        m[1::3] = -a.real
        m[2::3] = -a.imag
        b = np.zeros(3*len(ff)); b[::3] = cap
        mats.append(sp.hstack([sp.csc_matrix((len(b),i*n)), sp.csc_matrix(m),
                               sp.csc_matrix((len(b),kvar-(i+1)*n))],format='csc'))
        bs.append(b)
        cones.extend([cl.SecondOrderConeT(3)]*len(ff))

    def add_quad(I,R,margin):
        # (I-f+1, I-f-1, 2 R v) in the Lorentz cone.
        k = len(R)+2
        a = np.zeros((k,kvar)); a[:2,-1] = margin; a[2:,n:2*n] = -2*R
        b = np.zeros(k); b[0] = I+1; b[1] = I-1
        mats.append(sp.csc_matrix(a)); bs.append(b); cones.append(cl.SecondOrderConeT(k))
    for I,R in blocks.values():
        add_quad(I,R,I if hard else 1.)
    if args.l0 < 2.:
        add_quad(args.l0,L0,0.)
    run = cl.DefaultSolver(Q,q,sp.vstack(mats, format='csc'),np.concatenate(bs),cones,settings).solve()
    print('it', it, run.status, run.iterations, 'sec', round(monotonic()-start,2),
          run.r_prim, run.r_dual, 'linear', len(rhs), 'quad',len(blocks), flush=True)
    if str(run.status) not in ('Solved','AlmostSolved') and not (run.r_prim<3e-6 and run.r_dual<3e-6):
        break
    sol = np.asarray(run.x)
    b = sol[n:2*n]
    print('margin', sol[-1], 'mean', wmean@sol[2*n:nu]-8/9, 'l0', muq@abs(M@b)**2,
          'conditioning', run.r_prim, run.r_dual, flush=True)
    worst = [] if hard else scan(b)
    print('mask screen worst', worst[:3], flush=True)
    print('anchor prices',price(b, [(0,1,1),(0,1.25,1),(0,1.5,1),(.16,1.,.0005809242445/.001018011621)]), flush=True)
    freq_excess = []
    newf = []
    for i, cap in enumerate(CAPS):
        v = sol[i*n:(i+1)*n]
        y = np.abs(Mg@v)
        ix = np.r_[0,find_peaks(y)[0],len(fg)-1]
        peaks = fg[ix[y[ix]>cap+(2e-9 if hard else 2e-8)]]
        freq_excess.append(max(y)-cap)
        newf.append(np.unique(np.r_[peaks,f[i]]))
    vals2 = np.c_[sol[:n]*scale, b*scale]@faces2[:,:2].T + faces2[:,-1]
    vals3 = np.c_[sol[n-npos:n],b[-npos:],sol[2*n:nu]]@faces3[:,:3].T + faces3[:,-1]
    print('excess freq / faces2 / faces3',freq_excess, vals2.max(), vals3.max(), flush=True)
    if max(freq_excess)<args.fpad*.66 and vals2.max()<3e-9 and vals3.max()<(2e-8 if hard else 6e-8):
        print('reconstructed:', recover(sol), flush=True)
    np.savez(args.out+'.npz',z=z,a=sol[:n]*scale,b=b*scale,u=sol[2*n:nu],worst=worst[:500])
    for j, vv in enumerate(vals2):
        c2[j].update(i for i in np.argsort(vv)[-(7 if hard else 3):]
                     if vv[i]>2e-11 and (not hard or i not in c2[j]))
    for j, vv in enumerate(vals3, n-npos):
        c3[j].update(i for i in np.argsort(vv)[-(7 if hard else 3):] if vv[i]>2e-11)
    f = newf
    if args.scope in ['screen','regional','dual-regional'] and it+1<args.steps:
        if args.scope in ['regional','dual-regional']:
            ia = np.argmin(abs(ss+.05)); iz = np.argmin(abs(ss-.05))+1
            matcap = mask_mass
            exactS = SS@sum_coeffs(b)
            ucap = muq*abs(M@b)**2
            worst = []
            for d in np.arange(.875,1.5001,.025):
                for r in [.9,1.,1.1]:
                    sx=ss[ia:iz]; T = exactS[ia:iz]+r*sum_kernel(sx[:,None]+d+zz)@sum_coeffs(b)
                    F = matcap(d,r)-np.abs(1+r*np.exp(1j*d*xq))@ucap-abs(T)
                    j = np.argmin(F); worst.append((F[j],sx[j],float(d),r,int(np.sign(T[j]))))
            j = np.argmax(abs(exactS)); worst.append((1-ucap.sum()-abs(exactS[j]),ss[j],0.,0.,int(np.sign(exactS[j]))))
            worst.sort(); print('regional worst',worst[:3],flush=True)
        added = []
        for margin, s, d, r, sg in worst:
            if margin > sol[-1]-.00015 or len(added) >= 4:
                break
            key = (s,d,r,sg)
            if key in blocks or any(sg==e and abs(s-a)+abs(d-b)+abs(r-c)<.13
                                    for a,b,c,e in added):
                continue
            added.append(key)
            blocks[key] = fquad(*key)
        print('added',added,flush=True)
