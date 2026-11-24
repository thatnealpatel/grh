"""Mass below the search band; verified-height cap above the direct scan."""
from math import isqrt
from pathlib import Path
from runpy import run_path
from sage.all import QQ, RealIntervalField, prime_range

if not __debug__:
    raise RuntimeError('assertions required')
I = RealIntervalField(100)
weil = run_path(str(Path(__file__).with_name('check-weil-principal-band.py')))
# Below X=2 no prime has positive weight. Above it, with the prime set
# held constant, M=(A*log(X)-B)/X. Its only interior extremum is at
# log(X)=1+B/A, and is a maximum there.
xmax = int((weil['Rof'](18)**2).upper().ceil())
ps = list(prime_range(xmax+1)) + [xmax+1]
A,B,top = I(0),I(0),I(0)
for p,r in zip(ps,ps[1:]):
    l = I(p).log(); A += l; B += l*l
    def mass(x): return (A*I(x).log()-B)/x
    top = top.max(mass(p)).max(mass(r))
    peak = (1+B/A).exp()
    if not (peak<p or peak>r): top = top.max(A/peak)
assert top < QQ(8)/9
print('low mass cap',top.upper(),flush=True)

# Match each possible integer V to a range of Q before pricing. At the
# left edge k=42 a single coarse interval in V can lose the margin.
# Extend the same 0.044 remainder almost to the verification edge H.
# For H<|gamma|<=2H, each unit interval of positive ordinates has
# count <=3 log(2H+1) by the cited N(T) error. Include both signs.
H, distance = 3*10**12, 10**9
cap = H-distance
oldcap = 28*10**11
assert 3*I(2*H+1).log() < 90
near = 4000*180*(1/I(distance)**2+1/I(distance))
# Beyond 2H we have |gamma-t|>=|gamma|/2; use the old dyadic sum.
far = 16000*4/I(2*H)*(2*I(4*H).log()+2*I(2).log())
assert near+far+8000/I(oldcap)**2 < I(1)/1000
slack, unverified = I(1), I(100)
for k in range(42,67):
    a,b = weil['Rof'](k)**2,weil['Rof'](k+1)**2
    for v in range(int(a.lower().floor())-1,int(b.upper().floor())+1):
        # V <= X(Q) < V+2. log y(Q)=sqrt(X(Q))/3.
        lo = 2*(I(v).sqrt()/3).exp()-1
        full = 40*(I(v+2).sqrt()/3).exp()*I(2)**(QQ(3)/5)+1
        hi = full.min(I(cap))
        cut = hi.min(I(oldcap))
        u = I(max(p.upper() for p in weil['prices'](I(v),cut,lo)))
        # Only the log(tmax) in G changes beyond the old cutoff.
        R = I(v).sqrt()
        u += (1-1/R)*(hi/cut).log()/R
        gap = QQ(587)/1000-QQ(5)/(8*isqrt(k+1))-u
        assert gap > 0, (k,v,gap)
        slack = slack.min(gap)
        if not full < cap:
            assert full < 10**14 and 73 < R and R < 84
            # Additional room above the cap in the UNDIVIDED formula,
            # not an assertion that the translated zero sum is positive.
            room = 2*R*(gap-(1-1/R)*(full/hi).log()/R)
            assert room > QQ(29)/4, (k,v,room)
            unverified = unverified.min(room)
print('undivided room above cap',unverified.lower(),flush=True)
print('verified-node slack',slack.lower(),flush=True)
# Include rounding and a full cell of padding at the upper edge.
for j in (1,3,6,9,11,14): assert 2*j*weil['yof'](61)+1 < cap
for j in (17,20): assert 2*j*weil['yof'](61) > cap
assert 40*weil['yof'](60)+1 < cap
