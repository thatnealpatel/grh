"""Filter the signed modes at k=29..41 and certify the upper frontier. Run with sage -python."""
from math import isqrt
from pathlib import Path
import runpy
import numpy as np

weil = runpy.run_path(str(Path(__file__).with_name('check-weil-principal-band.py')))
I, pi, QQ = (weil[key] for key in ('I','pi','QQ'))
B = 1024                      # phase bins per turn
U = np.uint64

def phase_mask(l,row,rest,cut):
    # hot[b] is necessary on the entire closed bin b, including its edges.
    hot = np.zeros(B,dtype=bool)
    for b in range(B//2):
        theta = 2*pi*I(b,b+1)/B
        hot[b] = hot[B-1-b] = not (rest + sum(r*(m*theta).cos()
                             for m,r in enumerate(row,1)) < cut)
    rate = l/(2*pi)
    step = int((8*rate*2**64).center().round())
    assert abs(8*rate*2**64-step) < 1
    # The fixed-point bin of the anchor differs from the true phase by
    # <1 bin before flooring. Thus [b-1,b+2] encloses it in bin units.
    masks = np.zeros(B,dtype=U)
    for h in range(64):
        drift = B*rate*I(h,h+1)/8
        keep = np.zeros(B,dtype=bool)
        for d in range(-1+int(drift.lower().floor()),3+int(drift.upper().floor())):
            keep |= np.roll(hot,-d)
        masks |= keep.astype(U) << U(h)
    return U(step%(2**64)), masks

def verify(t0,t1,ramp,slope,cut):
    # Use interval phases at the midpoint and a first derivative bound.
    mid = (t0+t1)/2
    val = -sum(w*(mid*l).cos() for w,l in ramp)
    if val + slope*(t1-t0)/2 < cut: return
    assert t1-t0 > QQ(1)/1024, (mid,val)
    verify(t0,mid,ramp,slope,cut)
    verify(mid,t1,ramp,slope,cut)

def frozen(k):
    x = weil['Rof'](k)**2
    v = int(x.lower().floor())
    assert x < v+1
    return I(v-1,v)

def price(k,j):
    V = frozen(k)
    lo = 2*abs(j)*weil['yof'](k)-1
    hi = 2*abs(j)*weil['yof'](k+1)+1
    total = weil['base'](V,hi,lo)
    rows = []
    for p,l,terms in weil['prime_terms'](V):
        row = [(1 if j>0 else -1)*delta-A for A,delta in terms]
        # Use an upper endpoint as a scalar so it can be removed later.
        price = I(weil['poly'](row).upper())
        total += price
        rows.append((l,row,price))
    return lo,hi,total,rows

def sieve(k,lo,hi,total,rows,cut):
    # Called only on negative modes.
    V = frozen(k)
    ramp = [(l*(V.log()-l).max(I(0))/V,l) for p,l in weil['logs'] if p<=V.upper()]
    slope = sum(w*l for w,l in ramp)
    total = I(total.upper())
    masks = []
    for l,row,price in rows:
        step,full = phase_mask(l,row,total-price,cut)
        _,half = phase_mask(l,row,total-price,(cut+total)/2)
        masks.append((step,full,half))
    first = int((lo/8).lower().floor())
    end = 1+int((hi/8).upper().floor())
    assert 0 <= first < end and B*end < 2**64
    count = 0
    for a in range(first,end,2**16):
        n = np.arange(a,min(a+2**16,end),dtype=U)
        keep = np.full(len(n),U(2**64-1))
        seen = np.zeros_like(keep)
        for step,full,half in masks:
            idx = (n*step) >> U(54)  # uint64 arithmetic mod 2^64
            over = ~half[idx]
            keep &= full[idx] & ~(seen & over)
            seen |= over
        for i in np.flatnonzero(keep):
            bits = int(keep[i])
            while bits:
                bit = bits & -bits
                t0 = QQ(8*(a+int(i)))+QQ(bit.bit_length()-1)/8
                verify(t0,t0+QQ(1)/8,ramp,slope,cut)
                bits ^= bit
                count += 1
    print('anchors',end-first,'surviving eighths checked',count)

for k in range(29,42):
    cut = QQ(587)/1000-QQ(5)/(8*isqrt(k+1))
    unresolved = []
    for j in (1,-3,6,-9,11,-14,17,-20):
        lo,hi,total,rows = price(k,j)
        if total < cut: continue
        if (k >= 40 and j == -20) or (k == 39 and j == -14):
            print(k,j,'independent row cap',total,'required',cut)
            sieve(k,lo,hi,total,rows,cut)
        else:
            unresolved.append(j)
    if k <= 34: allowed = [-3,-9,-14,-20]
    elif k <= 36: allowed = [-9,-14,-20]
    elif k <= 38: allowed = [-14,-20]
    elif k == 39: allowed = [-20]
    else: allowed = []
    assert set(unresolved) <= set(allowed), (k,unresolved)
    print(k,'not excluded:',unresolved)
