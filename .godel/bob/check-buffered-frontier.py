"""Certify the finite buffered frontier. Use SageMath 10.9 Python and NumPy/BLAS."""
from math import isqrt
import numpy as np
from sage.all import QQ, RealIntervalField, prime_range

if not __debug__:
    raise RuntimeError('assertions required')
I = RealIntervalField(100)
pi, log2 = I.pi(), I(2).log()
# Approximate rotations by the midpoint of a phase bin. The trig table
# and phase increments are certified once, not recomputed by BLAS.
bits, H, W = 13, 128, 32768
B = 2**bits

def nearest(x):
    a = int(x.center().round())
    assert abs(x-a) < 1
    return a

cos = np.array([nearest(H*(pi*(2*i+1)/B).cos()) for i in range(B)], np.int32)
sin = np.roll(cos,B//4)
assert abs(cos).max() <= H

def bins(n,steps):
    # Intentional unsigned arithmetic modulo one turn.
    return (n.astype(np.uint64)[:,None]*steps) >> np.uint64(64-bits)

def block(k,left,right):
    # log2(Q) in [left,right], with bitlength k+1 on [k,k+1).
    x0 = (9*log2*left/5)**2
    x1 = (9*log2*right/5)**2
    v0 = int(x0.lower().floor())-1
    v1 = int(x1.upper().ceil())
    logs = [I(p).log() for p in prime_range(v1+1)]
    # A weight first increases, then decreases, with its sole nonzero
    # interior maximum at e*p. Do not pay numerator and denominator
    # variation separately over this relatively wide cutoff interval.
    ws = []
    for l in logs:
        def endpoint(v):
            return l*(I(v).log()-l).max(I(0))/v
        x,y = endpoint(v0),endpoint(v1)
        lo,hi = x.min(y),x.max(y)
        peak = (l+1).exp()
        if not (peak<v0 or peak>v1): hi = hi.max(l/peak)
        ws.append(I(lo.lower(),hi.upper()))
    # Demodulate near the barycenter to control linear interpolation error.
    d = (sum(l*w for l,w in zip(logs,ws))/sum(ws)).center().round()
    curv = sum(w*(l-d)**2 for w,l in zip(ws,logs))
    pitch = QQ(1)/(4 if k<29 else 2)
    rates = [pitch*(l-d)/(2*pi) for l in logs]
    steps = np.array([nearest(r*2**64)%2**64 for r in rates], np.uint64)
    # Both factors use the same increments; the total index is <2^36.
    # Per factor, the unit rotation differs from its bin midpoint by
    # at most 2*pi/B (including the fixed-point increment error).
    rot = 2*pi/B + I(2).sqrt()/H
    # Fine-table entries approximate W*w*exp(i*n*rate*2*pi) directly.
    # Use a finer trig table than for the unweighted outer factor.
    fineH = 2**16
    ct,st = fine_cos, fine_sin
    L = 1024
    idx = bins(np.arange(L),steps)
    wt = [int((w*2**24).center().round()) for w in ws]
    werr = sum(abs(w-I(a)/2**24) for w,a in zip(ws,wt))
    assert min(wt)>=0 and max(wt)<2**24
    a = np.array(wt,np.int64)
    # W*wt/(2^24*fineH) has denominator 2^25, since W=2^15.
    den = (2**24*fineH)//W
    def fine(tab):
        return ((a*tab[idx]+den//2)//den).T.copy()
    C,S = fine(ct),fine(st)
    # ALL products and partial sums of the two real matrix products
    # are integers of magnitude <2^24, hence exact even in binary32.
    assert H*int((np.abs(C)+np.abs(S)).sum(axis=0).max()) < 2**24
    real = np.concatenate((C,-S)).astype(np.float32)
    imag = np.concatenate((S,C)).astype(np.float32)
    M = sum(ws)
    ferr = werr + sum(wt)*I(1)/2**24*(2*pi/B+I(2).sqrt()/fineH) + len(ws)*I(2).sqrt()/(2*W)
    err = M*rot + (1+rot)*ferr + curv*pitch**2/8
    c = QQ(587)/1000-QQ(5)/(8*isqrt(k+1))
    # Use one squared integer threshold to check all nodes. Each dot
    # product has at most 24 bits, so its squared norm is exact in binary64.
    limit = int((((c-err)*H*W)**2).lower().floor())
    assert c>err and limit<2**52
    top = 0
    lo = 2*I(2)**(3*left/5)-1
    hi = 40*I(2)**(3*(right+1)/5)+1
    first = int((lo/(L*pitch)).lower().floor())
    end = int((hi/(L*pitch)).upper().ceil())+1
    assert 0<=first and end*L<2**36 and 2**36*B<2**63
    for b in range(first,end,512):
        t = bins(L*np.arange(b,min(b+512,end),dtype=np.int64),steps)
        A = np.concatenate((cos[t],sin[t]),axis=1).astype(np.float32)
        re = (A @ real).astype(np.float64)
        im = (A @ imag).astype(np.float64)
        p = int((re*re+im*im).max())
        assert p < limit, (k,left,b,(I(p).sqrt()/(H*W)+err),c)
        top = max(top,p)
    print(k,left,'frozen modulus cap', (I(top).sqrt()/(H*W)+err).upper(),'threshold',c,flush=True)

fine_cos = np.array([nearest(2**16*(pi*(2*i+1)/B).cos()) for i in range(B)],np.int32)
fine_sin = np.roll(fine_cos,B//4)
assert abs(fine_cos).max()<=2**16
for k in range(17,42):
    parts = 4 if k < 21 else 1
    for i in range(parts): block(k,k+QQ(i)/parts,k+QQ(i+1)/parts)
